////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi3reorder.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	One of the challenges of working with AXI3 are the (potentially)
//		out of order writes.  This modules is designed to re-order write
//	beats back into the proper order given by the AW* channel.  Once done,
//	write beats will always be contiguous--only changing ID's after WLAST.
//	Indeed, once done, the WID field can be properly removed and ignored.
//	it's left within for forms sake, but isn't required.
//
// Algorithms:
//	The design currently contains one of three reordering algorithms.
//
//	MTHD_NONE	Is a basic pass-through.  This would be appropriate
//			for AXI3 streams that are known to be in order already.
//
//	MTHD_SHIFT_REGISTER	Uses a shift-register based "FIFO".  (Not block
//				RAM)  All write data goes into this FIFO.  Items
//			are read from this FIFO out of order as required for
//			the given ID.  When any item is read from the middle,
//			the shift register back around the item read.
//
//			This is a compromise implementation that uses less
//			logic than the PER/ID FIFOS, while still allowing some
//			amount of reordering to take place.
//
//	MTHD_PERID_FIFOS	Uses an explicit FIFO for each ID.  Data come
//				into the core and go directly into the FIFO's.
//			Data are read out of the FIFOs in write-address order
//			until WLAST, where the write address may (potentially)
//			change.
//
//			For a small number of IDs, this solution should be
//			*complete*, and lacking nothing.  (Unless you fill the
//			write data FIFO's while needing data from another ID ..)
//
// Implementation notes:
//	This module is intended to be used side by side with other AW* channel
//	processing, and following an (external) AW* skidbuffer.  For this
//	reason, it doesn't use an AW skid buffer, nor does it output AW*
//	information.  External AWREADY handling should therefore be:
//
//		master_awskid_read = reorder_awready && any_other_awready;
//
//	going into a skid buffer, with the proper AWREADY being the upstream
//	skidbuffer's AWREADY output.
//
// Expected performance:
//	One beat per clock, all methods.
//
// Status:
//	This module passes both a Verilator lint check and a 15-20 step formal
//	bounded model check.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	axi3reorder #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 4,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	LGAWFIFO = 3,	// # packets we can handle
		parameter	LGWFIFO = 4,	// Full size of an AXI burst
		parameter	OPT_METHOD = 0,
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter [0:0]	OPT_LOW_LATENCY = 0,
		parameter	NUM_FIFOS = (1<<C_AXI_ID_WIDTH)
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// AXI3 (partial) slave interface
		// {{{
		input	wire			S_AXI3_AWVALID,
		output	wire			S_AXI3_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI3_AWID,
		// input	wire [AW-1:0]	S_AXI3_AWADDR,
		// input	wire	[3:0]	S_AXI3_AWLEN,
		// input	wire	[2:0]	S_AXI3_AWSIZE,
		// input	wire	[1:0]	S_AXI3_AWBURST,
		// input	wire	[1:0]	S_AXI3_AWLOCK,
		// input	wire	[3:0]	S_AXI3_AWCACHE,
		// input	wire	[2:0]	S_AXI3_AWPROT,
		// input	wire	[3:0]	S_AXI3_AWQOS,
		//
		input	wire			S_AXI3_WVALID,
		output	wire			S_AXI3_WREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI3_WID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI3_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI3_WSTRB,
		input	wire			S_AXI3_WLAST,
		// }}}
		// Reordered write data port.  WID may now be discarded.
		// {{{
		output	reg			M_AXI_WVALID,
		input	wire			M_AXI_WREADY,
		output	reg	[C_AXI_ID_WIDTH-1:0]	M_AXI_WID,
		output	reg	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	reg	[C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	reg			M_AXI_WLAST
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	localparam	MTHD_NONE = 0;
	localparam	MTHD_SHIFT_REGISTER = 1;
	localparam	MTHD_PERID_FIFOS = 2;
	localparam	IW = C_AXI_ID_WIDTH;
	localparam	DW = C_AXI_DATA_WIDTH;
	wire			awfifo_full, awfifo_empty;
	wire			read_awid_fifo;
	wire	[IW-1:0]	awfifo_id;
	wire	[LGAWFIFO:0]	awfifo_fill;

	genvar	gk;
	reg			read_beat_fifo;

	reg			cid_valid;
	reg	[IW-1:0]	current_id;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write address ID's go to an address ID FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (OPT_METHOD == MTHD_NONE)
	begin : IGNORE_AW_CHANNEL
		// No write address ID's to keep track of
		// {{{
		// These values are irrelevant.  They are placeholders, put here
		// to keep the linter from complaining.

		assign	awfifo_id = S_AXI3_AWID;
		assign	S_AXI3_AWREADY = 1'b1;
		assign	awfifo_full  = 0;
		assign	awfifo_fill  = 0;
		assign	awfifo_empty = !S_AXI3_AWVALID;
		always @(*)
			cid_valid = S_AXI3_AWVALID;
		always @(*)
			current_id= S_AXI3_AWID;
		assign	read_awid_fifo = 0;

		// Verilator lint_off UNUSED
		wire	none_aw_unused;
		assign	none_aw_unused = &{ 1'b0, awfifo_full, awfifo_fill,
				awfifo_empty, read_awid_fifo, awfifo_id };
		// }}}
	end else begin : AWFIFO
		////////////////////////////////////////////////////////////////
		//
		// Write address ID FIFO
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		sfifo #(
			// {{{
			.BW(IW),
			.LGFLEN(LGAWFIFO),
			.OPT_READ_ON_EMPTY(OPT_LOW_LATENCY)
			// }}}
		) awidfifo(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(S_AXI3_AWVALID && S_AXI3_AWREADY),
				.i_data(S_AXI3_AWID),
				.o_full(awfifo_full),
				.o_fill(awfifo_fill),
				.i_rd(read_awid_fifo),
				.o_data( awfifo_id ),
				.o_empty(awfifo_empty)
			// }}}
		);

		assign	S_AXI3_AWREADY = !awfifo_full;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Current ID -- what ID shall we output next?
		// {{{
		////////////////////////////////////////////////////////////////
		//
		// The current ID is given by the write address channel

		initial	cid_valid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cid_valid <= 1'b0;
		else if (read_awid_fifo)
			cid_valid  <= !awfifo_empty;

		// The current ID is given by the write address channel
		always @(posedge S_AXI_ACLK)
		if (read_awid_fifo)
			current_id <= awfifo_id;

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write data channel processing and reordering
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_METHOD == MTHD_NONE)
	begin : COPY_SW_TO_MW // Copy S_AXI3_W* values to M_AXIW*
		// {{{
		// {{{
		always @(*)
		begin
			M_AXI_WVALID = S_AXI3_WVALID;
			M_AXI_WID    = S_AXI3_WID;
			M_AXI_WDATA  = S_AXI3_WDATA;
			M_AXI_WSTRB  = S_AXI3_WSTRB;
			M_AXI_WLAST  = S_AXI3_WLAST;

			read_beat_fifo = 0;
		end
		// }}}

		assign	S_AXI3_WREADY = M_AXI_WREADY;

		// Keep Verilator happy
		// Verilator lint_off UNUSED
		wire	none_unused;
		assign	none_unused = &{ 1'b0, S_AXI_ACLK, S_AXI_ARESETN,
				current_id, cid_valid, read_beat_fifo };
		// Verilator lint_on  UNUSED
		// }}}
	end else if (OPT_METHOD == MTHD_SHIFT_REGISTER)
	begin : SHIFT_REGISTER
		// {{{

		////////////////////////////////////////////////////////////////
		//
		// Local declarations
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		localparam	NSREG = (1<<LGWFIFO);
		reg	[NSREG-1:0]	sr_advance;
		reg	[NSREG-1:0]	sr_write;
		reg	[NSREG-1:0]	sr_valid;
		reg	[IW-1:0]	sr_id	[0:NSREG];
		reg	[DW-1:0]	sr_data	[0:NSREG];
		reg	[DW/8-1:0]	sr_strb	[0:NSREG];
		reg	[NSREG-1:0]	sr_last;

		integer	ik;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Per-register-station logic
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		for (gk = 0; gk<NSREG; gk=gk+1)
		begin

			// sr_advance
			// {{{
			// Do we copy from the next station into this one or no?
			always @(*)
			begin
				sr_advance[gk] = 0;
				if ((gk > 0)&&(sr_advance[gk-1]))
					sr_advance[gk] = 1;
				if ((!M_AXI_WVALID || M_AXI_WREADY)
					&& cid_valid && current_id == sr_id[gk])
					sr_advance[gk] = 1;
				if (!sr_valid[gk])
					sr_advance[gk] = 0;
			end
			// }}}

			// sw_write
			// {{{
			// Do we write new data into this station?
			always @(*)
			begin
				sr_write[gk] = S_AXI3_WVALID && S_AXI3_WREADY;
				if (sr_valid[gk] && (!sr_advance[gk]
						||(gk < NSREG-1 && sr_valid[gk+1])))
					sr_write[gk] = 0;
				if (gk > 0 && (!sr_valid[gk-1]
					|| (sr_advance[gk-1] && !sr_valid[gk])))
					sr_write[gk] = 0;
			end
			// }}}

			// sr_valid
			// {{{
			initial	sr_valid[gk] = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				sr_valid[gk] <= 0;
			else if (sr_write[gk])
				sr_valid[gk] <= 1;
			else if (sr_advance[gk] && gk<NSREG-1)
				sr_valid[gk] <= sr_valid[gk+1];
			else if (sr_advance[gk])
				sr_valid[gk] <= 0;
			// }}}

			// sr_id, sr_data, sr_strb, sr_last
			// {{{
			always @(posedge S_AXI_ACLK)
			if (OPT_LOWPOWER && !S_AXI_ARESETN)
			begin
				sr_id[gk]   <= 0;
				sr_data[gk] <= 0;
				sr_strb[gk] <= 0;
				sr_last[gk] <= 0;
			end else if (sr_write[gk])
			begin
				sr_id[gk]   <= S_AXI3_WID;
				sr_data[gk] <= S_AXI3_WDATA;
				sr_strb[gk] <= S_AXI3_WSTRB;
				sr_last[gk] <= S_AXI3_WLAST;
			end else if ((gk < NSREG-1) && sr_advance[gk])
			begin
				sr_id[gk]   <= sr_id[gk+1];
				sr_data[gk] <= sr_data[gk+1];
				sr_strb[gk] <= sr_strb[gk+1];
				sr_last[gk] <= sr_last[gk+1];

				if (OPT_LOWPOWER && gk < NSREG-1 && !sr_valid[gk+1])
				begin
					// If we are running in low power,
					// Keep every unused register == 0
					sr_id[gk]   <= 0;
					sr_data[gk] <= 0;
					sr_strb[gk] <= 0;
					sr_last[gk] <= 0;
				end
			end else if ((!OPT_LOWPOWER && !sr_valid[gk])
				|| sr_write[gk])
			begin
				sr_id[gk]   <= S_AXI3_WID;
				sr_data[gk] <= S_AXI3_WDATA;
				sr_strb[gk] <= S_AXI3_WSTRB;
				sr_last[gk] <= S_AXI3_WLAST;
			end
			// }}}
		end
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Pick a register location to output
		// {{{
		////////////////////////////////////////////////////////////////
		//
		reg			known_next;
		reg	[LGWFIFO-1:0]	sr_next;
		always @(*)
		begin
			known_next = 0;
			sr_next = -1;
			for(ik=0; ik<NSREG; ik=ik+1)
			if (!known_next && current_id == sr_id[ik])
			begin
				sr_next = ik[LGWFIFO-1:0];
				known_next = sr_valid[ik];
			end

			if (!cid_valid)
				known_next = 0;
		end

		assign	S_AXI3_WREADY = !sr_valid[NSREG-1];
		// }}}
		////////////////////////////////////////////////////////////////
		//
		//
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		assign read_awid_fifo = (!M_AXI_WVALID || M_AXI_WREADY)
				&& (!cid_valid
				|| (known_next && sr_last[sr_next]));

		always @(*)
			read_beat_fifo = (!M_AXI_WVALID || M_AXI_WREADY)
				&&(known_next);

		initial	M_AXI_WVALID = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			M_AXI_WVALID <= 0;
		else if (!M_AXI_WVALID || M_AXI_WREADY)
			M_AXI_WVALID <= known_next;

		initial	M_AXI_WID   = 0;
		initial	M_AXI_WDATA = 0;
		initial	M_AXI_WSTRB = 0;
		initial	M_AXI_WLAST = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			// {{{
			M_AXI_WID   <= 0;
			M_AXI_WDATA <= 0;
			M_AXI_WSTRB <= 0;
			M_AXI_WLAST <= 0;
			// }}}
		end else if (!M_AXI_WVALID || M_AXI_WREADY)
		begin
			if (OPT_LOWPOWER && !known_next)
			begin
				// {{{
				M_AXI_WID <= 0;
				M_AXI_WDATA <= 0;
				M_AXI_WSTRB <= 0;
				M_AXI_WLAST <= 0;
				// }}}
			end else begin
				// {{{
				M_AXI_WID <= current_id;
				// Verilator lint_off WIDTH
				M_AXI_WDATA <= sr_data[sr_next];
				M_AXI_WSTRB <= sr_strb[sr_next];
				M_AXI_WLAST <= sr_last[sr_next];
				// Verilator lint_on  WIDTH
				// }}}
			end
		end
		// }}}
		// Verilator lint_off UNUSED
		wire	unused_sreg;
		assign	unused_sreg = &{ 1'b0, read_beat_fifo };
		// Verilator lint_on  UNUSED
`ifdef	FORMAL
		always @(*)
		if (S_AXI3_WVALID && S_AXI3_WREADY)
		begin
			assert($onehot(sr_write));
		end else if (S_AXI_ARESETN)
			assert(sr_write == 0);

		always @(*)
			assert(((sr_write << 1) & sr_valid) == 0);

		reg	cvr_sreg_full;

		initial	cvr_sreg_full = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_sreg_full <= 0;
		else if (!S_AXI3_WREADY)
			cvr_sreg_full <= 1;

		always @(*)
			cover(cvr_sreg_full && sr_valid == 0);
		
`endif
		// }}}
	end else if (OPT_METHOD == MTHD_PERID_FIFOS)
	begin : MULTIPLE_FIFOS
		// {{{
		wire	[NUM_FIFOS-1:0]	wbfifo_full, wbfifo_empty, wbfifo_last;
		// wire	[IW-1:0]	wbfifo_id	[0:NUM_FIFOS-1];
		wire	[DW-1:0]	wbfifo_data	[0:NUM_FIFOS-1];
		wire	[DW/8-1:0]	wbfifo_strb	[0:NUM_FIFOS-1];

		////////////////////////////////////////////////////////////////
		//
		// The write beat FIFO
		////////////////////////////////////////////////////////////////
		// {{{
		//
		// Every write beat goes into a separate FIFO based on its ID
		//
		for (gk=0; gk < NUM_FIFOS; gk=gk+1)
		begin
		// {{{
			wire	[LGWFIFO:0]	wbfifo_fill;

			sfifo #(
				.BW(DW+(DW/8)+1),
				.LGFLEN(LGWFIFO),
				.OPT_READ_ON_EMPTY(OPT_LOW_LATENCY)
			) write_beat_fifo (
				.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
				.i_wr(S_AXI3_WVALID && S_AXI3_WREADY && S_AXI3_WID == gk),
				.i_data({ S_AXI3_WDATA, S_AXI3_WSTRB,
					S_AXI3_WLAST }),
				.o_full(wbfifo_full[gk]), .o_fill(wbfifo_fill),
				.i_rd(read_beat_fifo && current_id == gk),
				.o_data({ wbfifo_data[gk],
					wbfifo_strb[gk], wbfifo_last[gk] }),
				.o_empty(wbfifo_empty[gk])
			);

			// Verilator lint_off UNUSED
			wire	unused;
			assign	unused = &{ 1'b0, wbfifo_fill };
			// Verilator lint_on  UNUSED
			// }}}
		end

		assign	S_AXI3_WREADY = !wbfifo_full[S_AXI3_WID];
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Outgoing write data channel
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		assign read_awid_fifo = (!M_AXI_WVALID || M_AXI_WREADY)
				&& (!cid_valid
				|| (read_beat_fifo && wbfifo_last[current_id]));
		// Write packets associated with the current ID can move forward
		always @(*)
			read_beat_fifo = (!M_AXI_WVALID || M_AXI_WREADY)
				&&(cid_valid)&&(!wbfifo_empty[current_id]);

		initial	M_AXI_WVALID = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			M_AXI_WVALID <= 0;
		else if (!M_AXI_WVALID || M_AXI_WREADY)
			M_AXI_WVALID <= read_beat_fifo;

		initial	M_AXI_WID   = 0;
		initial	M_AXI_WDATA = 0;
		initial	M_AXI_WSTRB = 0;
		initial	M_AXI_WLAST = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			// {{{
			M_AXI_WID   <= 0;
			M_AXI_WDATA <= 0;
			M_AXI_WSTRB <= 0;
			M_AXI_WLAST <= 0;
			// }}}
		end else if (!M_AXI_WVALID || M_AXI_WREADY)
		begin
			// {{{
			M_AXI_WID <= current_id;
			M_AXI_WDATA <= wbfifo_data[current_id];
			M_AXI_WSTRB <= wbfifo_strb[current_id];
			M_AXI_WLAST <= wbfifo_last[current_id];

			if (OPT_LOWPOWER && !read_beat_fifo)
			begin
				// {{{
				M_AXI_WID   <= 0;
				M_AXI_WDATA <= 0;
				M_AXI_WSTRB <= 0;
				M_AXI_WLAST <= 0;
				// }}}
			end
			// }}}
		end
		// }}}
		// }}}
	end endgenerate
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, awfifo_fill };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg				f_past_valid;
	reg	[LGAWFIFO+LGWFIFO-1:0]	f_awid_count;
	(* anyconst *) reg	[IW-1:0]	f_const_id;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assume(!S_AXI3_AWVALID);
		assume(!S_AXI3_WVALID);

		assume(!M_AXI_WVALID);
	end else begin
		if ($past(S_AXI3_AWVALID && !S_AXI3_AWREADY))
		begin
			assume(S_AXI3_AWVALID);
			assume($stable(S_AXI3_AWID));
		end

		if ($past(S_AXI3_WVALID && !S_AXI3_WREADY))
		begin
			assume(S_AXI3_WVALID);
			assume($stable(S_AXI3_WID));
			assume($stable(S_AXI3_WDATA));
			assume($stable(S_AXI3_WSTRB));
			assume($stable(S_AXI3_WLAST));
		end

		if ($past(M_AXI_WVALID && !M_AXI_WREADY))
		begin
			assert(M_AXI_WVALID);
			assert($stable(M_AXI_WID));
			assert($stable(M_AXI_WDATA));
			assert($stable(M_AXI_WSTRB));
			assert($stable(M_AXI_WLAST));
		end
	end

	generate if (OPT_METHOD != MTHD_NONE)
	begin : F_FIFO_CHECK
		wire	[LGWFIFO:0]	f_ckfifo_fill;
		wire	[LGWFIFO:0]	f_ckfifo_full, f_ckfifo_empty;
		wire	[IW-1:0]	f_ckfifo_id;
		wire	[DW-1:0]	f_ckfifo_data;
		wire	[DW/8-1:0]	f_ckfifo_strb;
		wire			f_ckfifo_last;

		sfifo #(
			.BW(IW + DW + (DW/8) + 1),
			.LGFLEN(LGWFIFO),
			.OPT_READ_ON_EMPTY(OPT_LOW_LATENCY)
		) f_checkfifo (
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(S_AXI3_WVALID && S_AXI3_WREADY
							&& S_AXI3_WID == f_const_id),
			.i_data({ S_AXI3_WID, S_AXI3_WDATA, S_AXI3_WSTRB, S_AXI3_WLAST }),
			.o_full(f_ckfifo_full), .o_fill(f_ckfifo_fill),
			.i_rd(M_AXI_WVALID && M_AXI_WREADY
						&& M_AXI_WID == f_const_id),
			.o_data({ f_ckfifo_id, f_ckfifo_data, f_ckfifo_strb,
					f_ckfifo_last }),
			.o_empty(f_ckfifo_empty)
		);

		always @(*)
		if (S_AXI_ARESETN && M_AXI_WVALID && M_AXI_WID == f_const_id)
		begin
			assert(!f_ckfifo_empty);
			assert(f_ckfifo_id   == M_AXI_WID);
			assert(f_ckfifo_data == M_AXI_WDATA);
			assert(f_ckfifo_strb == M_AXI_WSTRB);
			assert(f_ckfifo_last == M_AXI_WLAST);
		end
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_awid_count = 0;
	else case({S_AXI3_AWVALID&& S_AXI3_AWREADY && S_AXI3_AWID == f_const_id,
			M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST
			&& M_AXI_WID == f_const_id })
	2'b01: f_awid_count <= f_awid_count - 1;
	2'b10: f_awid_count <= f_awid_count + 1;
	default begin end
	endcase

	always @(*)
	if (M_AXI_WVALID && M_AXI_WID == f_const_id)
		assert(f_awid_count > 0);

	generate if (OPT_LOWPOWER)
	begin : F_LOWPOWER_CHECK
		always @(*)
		if (!S_AXI3_AWVALID)
			assume(S_AXI3_AWID == 0);

		always @(*)
		if (!S_AXI3_WVALID)
		begin
			assume(S_AXI3_WID   == 0);
			assume(S_AXI3_WDATA == 0);
			assume(S_AXI3_WSTRB == 0);
			assume(S_AXI3_WLAST == 0);
		end

		always @(*)
		if (!M_AXI_WVALID)
		begin
			assert(M_AXI_WID   == 0);
			assert(M_AXI_WDATA == 0);
			assert(M_AXI_WSTRB == 0);
			assert(M_AXI_WLAST == 0);
		end

	end endgenerate

`endif
	// }}}
endmodule
