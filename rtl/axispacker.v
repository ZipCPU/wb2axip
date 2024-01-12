////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axispacker
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	AXI-Stream packer: This uses TKEEP to pack bytes in a stream.
//		Bytes with TKEEP clear on input will be removed from the
//	output stream.
//
//	TID, TDEST, and TUSER fields are not (currently) implemented, although
//	they shouldn't be too hard to add back in.
//
//	This design *ASSUMES* that TLAST will only be set if TKEEP is not zero.
//	This assumption is not required by the AXI-stream specification, and
//	should be removed in the future.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	axispacker #(
		parameter	C_AXIS_DATA_WIDTH = 32,
		parameter [0:0]	OPT_LOWPOWER = 1
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		// Incoming slave interface
		// {{{
		input	wire					S_AXIS_TVALID,
		output	wire					S_AXIS_TREADY,
		input	wire	[C_AXIS_DATA_WIDTH-1:0]		S_AXIS_TDATA,
		input	wire	[C_AXIS_DATA_WIDTH/8-1:0]	S_AXIS_TSTRB,
		input	wire	[C_AXIS_DATA_WIDTH/8-1:0]	S_AXIS_TKEEP,
		input	wire					S_AXIS_TLAST,
		// }}}
		// Outgoing AXI-Stream master interface
		// {{{
		output	reg					M_AXIS_TVALID,
		input	wire					M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]		M_AXIS_TDATA,
		output	reg	[C_AXIS_DATA_WIDTH/8-1:0]	M_AXIS_TSTRB,
		output	reg	[C_AXIS_DATA_WIDTH/8-1:0]	M_AXIS_TKEEP,
		output	reg					M_AXIS_TLAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	DW = C_AXIS_DATA_WIDTH;

	wire			pre_tvalid, pre_tready;
	wire	[DW-1:0]	pre_tdata;
	wire	[DW/8-1:0]	pre_tstrb, pre_tkeep;
	wire			pre_tlast;

	localparam	MAX_COUNT  = DW/8;
	localparam	COUNT_BITS = $clog2(MAX_COUNT+1)+1;

	reg	[DW-1:0]	pck_tdata;
	reg	[DW/8-1:0]	pck_tstrb, pck_tkeep;
	reg			pck_tlast;
	reg [COUNT_BITS-1:0]	pck_count;

	reg			axis_ready;

	wire				skd_valid;
	wire	[DW-1:0]		skd_data;
	wire	[DW/8-1:0]		skd_strb, skd_keep;
	wire	[COUNT_BITS-1:0]	skd_count;
	wire				skd_last;

	reg	[COUNT_BITS-1:0]	mid_fill;
	reg	[DW-1:0]		mid_data;
	reg	[DW/8-1:0]		mid_strb, mid_keep;
	reg				mid_last;

	reg	[2*DW-1:0]		w_packed_data;
	reg	[2*DW/8-1:0]		w_packed_strb, w_packed_keep;

	localparam	TRIM_MAX = MAX_COUNT[COUNT_BITS-1:0];
	reg	next_valid, next_last;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This makes it so that we can control VALID && DATA (and so
	// backpressure) with a combinatorial value, something that would
	// otherwise be against protocol.
	//

`ifdef	FORMAL
	// {{{
	assign	pre_tvalid = S_AXIS_TVALID;
	assign	S_AXIS_TREADY = pre_tready;
	assign	pre_tdata = S_AXIS_TDATA;
	assign	pre_tstrb = S_AXIS_TSTRB;
	assign	pre_tkeep = S_AXIS_TKEEP;
	assign	pre_tlast = S_AXIS_TLAST;
	// }}}
`else
	skidbuffer #(
		// {{{
		.DW(DW + DW/8 + DW/8 + 1),
		.OPT_OUTREG(1'b1)
		// }}}
	) slave_skd (
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
		.i_data({ S_AXIS_TDATA, S_AXIS_TSTRB,
						S_AXIS_TKEEP, S_AXIS_TLAST }),
		.o_valid(pre_tvalid), .i_ready(pre_tready),
			.o_data({ pre_tdata, pre_tstrb, pre_tkeep, pre_tlast })
		// }}}
	);
`endif

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Beat packing stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		{ pck_tdata, pck_tstrb, pck_tkeep }
			= pack( pre_tdata, pre_tstrb,
				(pre_tvalid) ? pre_tkeep : {(DW/8){1'b0}} );
		pck_tlast = pre_tlast;
		// Verilator lint_off WIDTH
		pck_count = $countones(pre_tkeep);
		// Verilator lint_on  WIDTH
	end

`ifdef	FORMAL
	// {{{
	assign	skd_valid  = pre_tvalid;
	assign	pre_tready = axis_ready;
	assign	skd_data = pck_tdata;
	assign	skd_strb = pck_tstrb;
	assign	skd_keep = pck_tkeep;
	assign	skd_last = pck_tlast;
	assign	skd_count= pck_count;
	// }}}
`else
	skidbuffer #(
		// {{{
		.DW(DW + DW/8 + DW/8 + 1 + COUNT_BITS),
		.OPT_OUTREG(1'b1)
		// }}}
	) beat_skd (
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(pre_tvalid), .o_ready(pre_tready),
		.i_data({ pck_count, pck_tdata, pck_tstrb,
					pck_tkeep, pck_tlast }),
		.o_valid(skd_valid), .i_ready(axis_ready),
			.o_data({ skd_count, skd_data, skd_strb, skd_keep,
							skd_last })
		// }}}
	);
`endif

	function [DW+DW/8+DW/8-1:0] pack; // (i_data, i_strb, i_keep)
	// {{{
		input	[DW-1:0]	i_data;
		input	[DW/8-1:0]	i_strb;
		input	[DW/8-1:0]	i_keep;

		reg	[DW-1:0]	p_data;
		reg	[DW/8-1:0]	p_strb;
		reg	[DW/8-1:0]	p_keep;

		integer	rounds, ik;
	begin
		p_data = i_data;
		p_strb = i_strb;
		p_keep = i_keep;
		for(ik=0; ik < DW/8; ik=ik+1)
		begin
			if (!p_keep[ik])
			begin
				p_data[ik*8 +: 8]= 8'h00;
				p_strb[ik] = 1'b0;
			end
		end
		for(rounds = 0; rounds < DW/8; rounds = rounds+1)
		begin
			for(ik=0; ik < DW/8-1; ik=ik+1)
			begin
				if (!p_keep[ik])
				begin
					p_data[ik*8 +: 8]=p_data[(ik+1)*8 +: 8];
					p_keep[ik] = p_keep[ik+1];
					p_strb[ik] = p_strb[ik+1];

					p_keep[ik+1] = 0;
					p_data[(ik+1)*8 +: 8] = 0;
					p_strb[ik+1] = 0;
				end
			end
		end

		pack = { p_data, p_strb, p_keep };
/*
		p_data = 0;
		p_strb = 0;
		p_keep = 0;

		for(fill=0; fill<2*DW; fill=fill+1)
		begin
			p_data[(fill *8) +: 8] = i_data[fill*8 +: 8];
			p_strb[ fill         ] = i_strb[fill];
			p_keep[ fill         ] = i_keep[fill];
			if (fill != 0)
				p_keep[ fill         ] = i_keep[fill]
					&& $countones(i_keep[((fill > 0)?(fill-1):0):0]) == fill;
			for(ik=fill; ik<2*DW; ik=ik+1)
			if (i_keep[ik] && $countones(i_keep[ik-1:0]) == fill)
			begin
				p_data[fill*8 +: 8] = i_data[ik*8 +: 8];
				p_strb[fill       ] = i_strb[ik];
				p_keep[fill       ] = i_keep[ik];
			end

			if (!p_keep[fill])
			begin
				p_strb[fill] = 1'b0;
				if (OPT_LOWPOWER)
					p_data[(fill *8) +: 8] = 8'h00;
			end
		end

		pack = { p_data, p_strb, p_keep };
*/
	end endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Word Packing stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// axis_ready
	// {{{
	always @(*)
	begin
		axis_ready = 1;
		if ((mid_last || (skd_count + mid_fill >= TRIM_MAX))
				&&(M_AXIS_TVALID && !M_AXIS_TREADY))
			axis_ready = 0;
		if (!skd_valid)
			axis_ready = 0;
	end
	// }}}

	// mid_fill
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mid_fill <= 0;
	else if (mid_last && (!M_AXIS_TVALID || M_AXIS_TREADY))
		mid_fill <= (axis_ready) ? skd_count : 0;
	else if (skd_valid && skd_last && (!M_AXIS_TVALID || M_AXIS_TREADY))
		mid_fill <= (skd_count + mid_fill <= TRIM_MAX) ? 0 : skd_count + mid_fill - TRIM_MAX;
	else
		mid_fill <= mid_fill + (axis_ready ? skd_count : 0)
			- ((next_valid && (!M_AXIS_TVALID || M_AXIS_TREADY))
				? TRIM_MAX : 0);
	// }}}

	// mid_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mid_last <= 0;
	else if (axis_ready)
	begin
		mid_last <= !next_last || (M_AXIS_TVALID && !M_AXIS_TREADY);
		if (mid_last)
			mid_last <= 1'b1;
		if (!skd_last)
			mid_last <= 1'b0;
	end else if (!M_AXIS_TVALID || M_AXIS_TREADY)
		mid_last <= 0;
	// }}}

	// mid_data, mid_strb, mid_keep
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		mid_data <= 0;
		mid_strb <= 0;
		mid_keep <= 0;
	end else if (mid_last && (!M_AXIS_TVALID || M_AXIS_TREADY))
	begin
		mid_data <= (axis_ready) ? skd_data : 0;
		mid_strb <= (axis_ready) ? skd_strb : 0;
		mid_keep <= (axis_ready) ? skd_keep : 0;
	end else if (skd_valid && skd_last && (!M_AXIS_TVALID || M_AXIS_TREADY))
	begin
		if (skd_count + mid_fill <= TRIM_MAX)
		begin
			mid_data <= 0;
			mid_strb <= 0;
			mid_keep <= 0;
		end else begin
			mid_data <= w_packed_data[2*DW-1:DW];
			mid_strb <= w_packed_strb[2*DW/8-1:DW/8];
			mid_keep <= w_packed_keep[2*DW/8-1:DW/8];
		end
	end else if (axis_ready)
	begin
		if (mid_fill + skd_count >= TRIM_MAX)
		begin
			mid_data <= w_packed_data[2*DW-1:DW];
			mid_strb <= w_packed_strb[2*DW/8-1:DW/8];
			mid_keep <= w_packed_keep[2*DW/8-1:DW/8];
		end else begin
			mid_data <= w_packed_data[DW-1:0];
			mid_strb <= w_packed_strb[DW/8-1:0];
			mid_keep <= w_packed_keep[DW/8-1:0];
		end
	end
	// }}}

	// w_packed_data, w_packed_strb, w_packed_keep
	// {{{
	always @(*)
	begin
		w_packed_data = 0;
		w_packed_strb = 0;

		w_packed_data = { {(DW){1'b0}}, mid_data }
			| ( { {(DW){1'b0}}, skd_data } << (mid_fill * 8));
		w_packed_strb = { {(DW/8){1'b0}}, mid_strb }
			| ( { {(DW/8){1'b0}}, skd_strb } << (mid_fill));
		w_packed_keep = { {(DW/8){1'b0}}, mid_keep }
			| ( { {(DW/8){1'b0}}, skd_keep } << (mid_fill));
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// next_valid
	// {{{
	always @(*)
	begin
		next_valid = skd_valid && (skd_count + mid_fill >= TRIM_MAX);
		if (mid_last || (skd_last && skd_valid))
			next_valid = 1;
		if (skd_count + mid_fill == 0)
			next_valid = 0;
	end
	// }}}

	// next_last
	// {{{
	always @(*)
	begin
		next_last = mid_last;
		if (skd_valid && skd_last && (skd_count + mid_fill <= TRIM_MAX))
			next_last = 1;
		if (!next_valid)
			next_last = 0;
	end
	// }}}

	// M_AXIS_TVALID
	// {{{
	initial	M_AXIS_TVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 0;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
		M_AXIS_TVALID <= next_valid;
	// }}}

	// M_AXIS_TDATA, M_AXIS_TSTRB, M_AXIS_TKEEP, M_AXIS_TLAST
	// {{{
	initial	M_AXIS_TDATA  = 0;
	initial	M_AXIS_TSTRB  = 0;
	initial	M_AXIS_TKEEP  = 0;
	initial	M_AXIS_TLAST  = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
	begin
		M_AXIS_TDATA  <= 0;
		M_AXIS_TSTRB  <= 0;
		M_AXIS_TKEEP  <= 0;
		M_AXIS_TLAST  <= 0;
	end else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		if (mid_last)
		begin
			M_AXIS_TDATA  <= mid_data;
			M_AXIS_TSTRB  <= mid_strb;
			M_AXIS_TKEEP  <= mid_keep;
			M_AXIS_TLAST  <= 1'b1;
		end else begin
			M_AXIS_TDATA  <= w_packed_data[DW-1:0];
			M_AXIS_TSTRB  <= w_packed_strb[DW/8-1:0];
			M_AXIS_TKEEP  <= w_packed_keep[DW/8-1:0];
			M_AXIS_TLAST  <= next_last;
		end


		if (OPT_LOWPOWER && !next_valid)
		begin
			M_AXIS_TDATA <= 0;
			M_AXIS_TSTRB <= 0;
			M_AXIS_TKEEP <= 0;
			M_AXIS_TLAST <= 0;
		end
	end
	// }}}

	// }}}
	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
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
	reg	f_past_valid;
	localparam	F_COUNT = COUNT_BITS + 4 + 16;
	reg	[F_COUNT-1:0]	f_icount, f_ocount, f_ibeat, f_obeat,
				f_mcount, f_mbeat;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming stream assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assume(!S_AXIS_TVALID);
	end else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
		assume($stable(S_AXIS_TSTRB));
		assume($stable(S_AXIS_TKEEP));
		assume($stable(S_AXIS_TLAST));
	end

	// If TKEEP is low, TSTRB must be low as well
	always @(*)
	if (S_AXI_ARESETN)
		assume(((~S_AXIS_TKEEP) & S_AXIS_TSTRB) == 0);

	// TLAST requires at least one beat
	always @(*)
	if (S_AXI_ARESETN && S_AXIS_TVALID && S_AXIS_TLAST)
		assume(S_AXIS_TKEEP != 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing stream assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assert(!M_AXIS_TVALID);
	end else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TSTRB));
		assert($stable(M_AXIS_TKEEP));
		assert($stable(M_AXIS_TLAST));
	end

	// If TKEEP is low, TSTRB must be low as well
	always @(*)
	if (S_AXI_ARESETN && M_AXIS_TVALID)
		assert(((~M_AXIS_TKEEP) & M_AXIS_TSTRB) == 0);

	// Our output requirement is that if TLAST is ever low, TKEEP must
	// be all ones
	always @(*)
	if (S_AXI_ARESETN && M_AXIS_TVALID && !M_AXIS_TLAST)
		assert(&M_AXIS_TKEEP);

	always @(*)
	if (S_AXI_ARESETN && OPT_LOWPOWER && !M_AXIS_TVALID)
	begin
		assert(M_AXIS_TDATA == 0);
		assert(M_AXIS_TSTRB == 0);
		assert(M_AXIS_TKEEP == 0);
		assert(M_AXIS_TLAST == 0);
	end

	// TLAST requires at least one beat
	always @(*)
	if (S_AXI_ARESETN && M_AXIS_TVALID && M_AXIS_TLAST)
		assert(M_AXIS_TKEEP != 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction assertions for the middle
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	genvar	gk;

	always @(*)
	if (S_AXI_ARESETN)
		assert(mid_fill == { 1'b0, $countones(mid_keep) });

	always @(*)
	if (S_AXI_ARESETN && mid_last)
		assert(mid_fill > 0);

	// If TKEEP is low, TSTRB must be low as well
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (mid_fill > 0)
		begin
			assert(((~mid_keep) & mid_strb) == 0);
		end else begin
			// assert(mid_data == 0);
			assert(mid_strb == 0);
		end
	end

	// Our output requirement is that if TLAST is ever low, TKEEP must
	// be all ones
	generate for(gk=1; gk<DW/8; gk=gk+1)
	begin
		always @(*)
		if (S_AXI_ARESETN && mid_fill > 0 && mid_keep[gk])
			assert(&mid_keep[gk-1:0]);
	end endgenerate

	always @(*)
	if (S_AXI_ARESETN && OPT_LOWPOWER && !M_AXIS_TVALID)
	begin
		assert(M_AXIS_TDATA == 0);
		assert(M_AXIS_TSTRB == 0);
		assert(M_AXIS_TKEEP == 0);
		assert(M_AXIS_TLAST == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Pick a byte of the given packet.  Force that byte to have a known
	// value.  Prove that the same byte on the output has the same known
	// value.

	(* anyconst *)	reg	[F_COUNT-1:0]	fc_count;
	(* anyconst *)	reg	[8-1:0]		fc_data;
	(* anyconst *)	reg			fc_strb, fc_last;
	wire	[F_COUNT:0]	f_chk_count;

	// Assume the special input
	// {{{
	generate for(gk=0; gk<DW/8; gk=gk+1)
	begin
		if (gk == 0)
		begin
			always @(*)
			if (S_AXIS_TVALID && S_AXIS_TKEEP[0]
				&& f_icount == fc_count)
			begin
				assume(fc_data == S_AXIS_TDATA[7:0]);
				assume(fc_strb == S_AXIS_TSTRB[0]);
				if (fc_last)
				begin
					assume(S_AXIS_TKEEP[DW/8-1:1] == 0);
					assume(S_AXIS_TLAST);
				end else if (S_AXIS_TLAST)
					assume(S_AXIS_TKEEP[DW/8-1:1] != 0);
			end
		end else begin

			always @(*)
			if (S_AXIS_TKEEP[gk] && (f_icount
				// Verilator lint_off WIDTH
				+ $countones(S_AXIS_TKEEP[gk-1:0]) == fc_count))
				// Verilator lint_on  WIDTH
			begin
				assume(S_AXIS_TDATA[gk*8 +: 8] == fc_data);
				assume(S_AXIS_TSTRB[gk] == fc_strb);
				if (fc_last)
				begin
					if (gk < DW/8-1)
						assume(S_AXIS_TKEEP[DW/8-1:gk+1] == 0);
					assume(S_AXIS_TLAST);
				end else if (gk < DW/8-1)
				begin
					if (S_AXIS_TLAST)
						assume(S_AXIS_TKEEP[DW/8-1:gk+1] != 0);
				end else
					assume(!S_AXIS_TLAST);
			end
		end
	end endgenerate
	// }}}

	// Assert the special output
	// {{{
	generate for(gk=0; gk<DW/8; gk=gk+1)
	begin
		if (gk == 0)
		begin
			always @(*)
			if (S_AXI_ARESETN && M_AXIS_TVALID && M_AXIS_TKEEP[0]
						&& f_ocount == fc_count)
			begin
				assert(M_AXIS_TDATA[7:0] == fc_data);
				assert(M_AXIS_TSTRB[0] == fc_strb);
				if (fc_last)
				begin
					assert(M_AXIS_TKEEP[DW/8-1:1] == 0);
					assert(M_AXIS_TLAST);
				end else if (M_AXIS_TLAST)
					assert(M_AXIS_TKEEP[DW/8-1:1] != 0);
			end
		end else begin

			always @(*)
			if (S_AXI_ARESETN && M_AXIS_TKEEP[gk] &&
				// Verilator lint_off WIDTH
				(f_ocount + $countones(M_AXIS_TKEEP[gk-1:0])
								== fc_count))
				// Verilator lint_on  WIDTH
			begin
				assert(M_AXIS_TDATA[gk*8 +: 8] == fc_data);
				assert(M_AXIS_TSTRB[gk] == fc_strb);
				if (fc_last)
				begin
					if (gk < DW/8-1)
						assert(M_AXIS_TKEEP[DW/8-1:gk+1] == 0);
					assert(M_AXIS_TLAST);
				end else if (gk < DW/8-1)
				begin
					if (M_AXIS_TLAST)
						assert(M_AXIS_TKEEP[DW/8-1:gk+1] != 0);
				end else
					assert(!M_AXIS_TLAST);
			end
		end
	end endgenerate
	// }}}

	// f_icount
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_icount <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
		// Verilator lint_off WIDTH
		f_icount <= f_icount + $countones(S_AXIS_TKEEP);
		// Verilator lint_on  WIDTH
	// }}}

	// f_ocount
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_ocount <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
		// Verilator lint_off WIDTH
		f_ocount <= f_ocount + $countones(M_AXIS_TKEEP);
		// Verilator lint_on  WIDTH
	// }}}

	// Induction assertion(s) on mid_*
	// {{{
	always @(*)
		// Verilator lint_off WIDTH
		f_mcount = f_icount - mid_fill;
		// Verilator lint_on  WIDTH

	generate for(gk=0; gk<DW/8; gk=gk+1)
	begin
		if (gk == 0)
		begin
			always @(*)
			if (S_AXI_ARESETN && mid_fill > 0
						&& f_mcount == fc_count)
			begin
				assert(mid_data[7:0] == fc_data);
				assert(mid_strb[0] == fc_strb);
				assert(mid_keep[0]);
				if (fc_last)
				begin
					assert(mid_fill == 1);
					assert(mid_last);
				end else if (mid_last)
					assert(mid_fill > 1);
			end else if (S_AXI_ARESETN && mid_fill == 0)
			begin
				assert(mid_data[7:0] == 8'h00);
				assert(!mid_strb[0]);
				assert(!mid_keep[0]);
			end
		end else begin

			always @(*)
			if (S_AXI_ARESETN && mid_fill > gk
					&& (f_mcount + gk == fc_count))
			begin
				assert(mid_data[gk*8 +: 8] == fc_data);
				assert(mid_strb[gk] == fc_strb);
				assert(mid_keep[gk]);
				if (fc_last)
				begin
					assert(mid_fill == gk + 1);
					assert(mid_last);
				end else if (gk < DW/8-1)
				begin
					if (mid_last)
						assert(mid_fill > gk + 1);
				end else
					assert(!mid_last);
			end else if (S_AXI_ARESETN && mid_fill <= gk)
			begin
				assert(mid_data[gk*8 +: 8] == 8'h00);
				assert(!mid_strb[gk]);
				assert(!mid_keep[gk]);
			end
		end
	end endgenerate
	// }}}

	// Relate icount to ocount
	// {{{
	// Verilator lint_off WIDTH
	assign	f_chk_count = f_ocount + mid_fill + $countones(M_AXIS_TKEEP);
	// Verilator lint_on  WIDTH

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assume(f_chk_count[F_COUNT] == 1'b0);
		assert(f_icount == f_chk_count[F_COUNT-1:0]);
	end
	// }}}

	// f_ibeat
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_ibeat <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		// Verilator lint_off WIDTH
		f_ibeat <= f_ibeat + $countones(S_AXIS_TKEEP);
		// Verilator lint_on  WIDTH
		if (M_AXIS_TLAST)
			f_ibeat <= 0;
	end
	// }}}

	// f_obeat
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_obeat <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		// Verilator lint_off WIDTH
		f_obeat <= f_obeat + $countones(M_AXIS_TKEEP);
		// Verilator lint_on  WIDTH
		if (M_AXIS_TLAST)
			f_obeat <= 0;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover(M_AXIS_TVALID && M_AXIS_TREADY && M_AXIS_TLAST
			&& $past(M_AXIS_TVALID&& M_AXIS_TREADY&& M_AXIS_TLAST));
			
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover(M_AXIS_TVALID && !M_AXIS_TLAST
			&& $past(M_AXIS_TVALID&& M_AXIS_TREADY&& M_AXIS_TLAST));
			
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover(M_AXIS_TVALID && M_AXIS_TLAST
			&& $past(M_AXIS_TVALID&& M_AXIS_TREADY&&!M_AXIS_TLAST));
			
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_ibeat, f_obeat, f_icount, f_ocount };
	// Verilator lint_on  UNUSED
	// }}}
`endif	// FORMAL
// }}}
endmodule
