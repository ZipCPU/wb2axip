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
// Implementation notes:
//	This module is intended to be used side by side with other AW* channel
//	processing, and following a skidbuffer.  For this reason, it doesn't
//	use an AW skid buffer, nor does it output AW* information.  AWREADY
//	handling should therefore be:
//
//		master_awskid_read = reorder_awready && other_awready;
//
//	going into a skid buffer, with the proper AWREADY being the upstream
//	skidbuffer's AWREADY.
//
// Expected performance:
//	One beat per clock.
//
//	This design is a bit heavy on logic, requiring (at present) one FIFO
//	per potential ID.  Stay tuned for potential alternatives to this.
//
// Status:
//	This module is a *DRAFT*.  It has not (yet) been verified either
//	formally or through any simulations.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
		localparam	IW = C_AXI_ID_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		localparam	NUM_FIFOS = (1<<IW)
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// AXI3 (partial) slave interface
		// {{{
		input	wire			S_AXI3_AWVALID,
		output	wire			S_AXI3_AWREADY,
		input	wire	[IW-1:0]	S_AXI3_AWID,
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
		input	wire	[IW-1:0]	S_AXI3_WID,
		input	wire	[DW-1:0]	S_AXI3_WDATA,
		input	wire	[DW/8-1:0]	S_AXI3_WSTRB,
		input	wire			S_AXI3_WLAST,
		// }}}
		// Reordered write data port.  WID may now be discarded.
		// {{{
		output	reg			M_AXI_WVALID,
		input	wire			M_AXI_WREADY,
		output	reg	[IW-1:0]	M_AXI_WID,
		output	reg	[DW-1:0]	M_AXI_WDATA,
		output	reg	[DW/8-1:0]	M_AXI_WSTRB,
		output	reg			M_AXI_WLAST
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	wire			awfifo_full, awfifo_empty;
	reg			read_awid_fifo;
	wire	[IW-1:0]	awfifo_id;
	wire	[LGAWFIFO:0]	awfifo_fill;

	genvar	gk;
	wire	[NUM_FIFOS-1:0]	wbfifo_full, wbfifo_empty, wbfifo_last;
	reg			read_beat_fifo;
	wire	[IW-1:0]	wbfifo_id	[0:NUM_FIFOS-1];
	wire	[DW-1:0]	wbfifo_data	[0:NUM_FIFOS-1];
	wire	[DW/8-1:0]	wbfifo_strb	[0:NUM_FIFOS-1];

	reg			cid_valid;
	reg	[IW-1:0]	current_id;

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Write address ID's go to an address ID FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	sfifo #(
		// {{{
		.BW(IW),
		.LGFLEN(LGAWFIFO)
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
	////////////////////////////////////////////////////////////////////////
	//
	// The write beat FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Every write beat goes into a separate FIFO based on its ID
	//
	generate for (gk=0; gk < NUM_FIFOS; gk=gk+1)
	begin
		// {{{
		wire	[LGWFIFO:0]	wbfifo_fill;

		sfifo #(
			.BW(IW+DW+(DW/8)+1),
			.LGFLEN(LGWFIFO)
		) write_beat_fifo (
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(S_AXI3_WVALID && S_AXI3_WREADY && S_AXI3_WID == gk),
			.i_data({ S_AXI3_WID, S_AXI3_WDATA, S_AXI3_WSTRB,
				S_AXI3_WLAST }),
			.o_full(wbfifo_full[gk]), .o_fill(wbfifo_fill),
			.i_rd(read_beat_fifo && current_id == gk),
			.o_data({ wbfifo_id[gk], wbfifo_data[gk],
				wbfifo_strb[gk], wbfifo_last[gk] }),
			.o_empty(wbfifo_empty[gk])
		);

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, wbfifo_fill };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	assign	S_AXI3_WREADY = !wbfifo_full[S_AXI3_WID];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Current ID -- what ID shall we output next?
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// The current ID is given by the write address channel
	always @(*)
		read_awid_fifo = (!M_AXI_WVALID || M_AXI_WREADY)
			&& (!cid_valid
				|| (read_beat_fifo && wbfifo_last[current_id]));

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
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing write data channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
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

	always @(posedge S_AXI_ACLK)
	if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		// if (OPT_SUBMAP)
			M_AXI_WID <= wbfifo_id[current_id];
		// else
			// M_AXI_WID <= current_id;
		M_AXI_WDATA <= wbfifo_data[current_id];
		M_AXI_WSTRB <= wbfifo_strb[current_id];
		M_AXI_WLAST <= wbfifo_last[current_id];
	end
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, awfifo_fill };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
