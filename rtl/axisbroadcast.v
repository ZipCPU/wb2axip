////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisbroadcast
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	AXI-Stream broadcaster: one slave input port gets broadcast to
//		multiple AXI-Stream master ports.
//
//	This design does not explicitly implement TLAST, TUSER, TID, or any
//	other T* structure.  These can be implemented by simply incorporating
//	them into TDATA.
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
module	axisbroadcast #(
		parameter	C_AXIS_DATA_WIDTH = 16,
		parameter	NM = 4,	// Number of (outgoing) master ports
		parameter	LGFIFO = 4	// Size of outgoing FIFOs
	) (
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		input	wire					S_AXIS_TVALID,
		output	wire					S_AXIS_TREADY,
		input	wire	[C_AXIS_DATA_WIDTH-1:0]		S_AXIS_TDATA,
		output	wire	[NM-1:0]			M_AXIS_TVALID,
		input	wire	[NM-1:0]			M_AXIS_TREADY,
		output	wire	[NM*C_AXIS_DATA_WIDTH-1:0]	M_AXIS_TDATA
	);

	// Local declarations
	// {{{
	localparam	DW = C_AXIS_DATA_WIDTH;
	genvar				gk;
	wire	[NM-1:0]		fifo_full;
	wire				skd_valid, axis_ready;
	wire	[DW-1:0]		skd_data;
	wire	[NM*(LGFIFO+1)-1:0]	ign_fifo_fill;
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
	skidbuffer #(
		.DW(DW),
		.OPT_OUTREG(1'b0)
	) tskd (
		.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data(S_AXIS_TDATA),
		.o_valid(skd_valid), .i_ready(axis_ready),
			.o_data(skd_data)
	);

	assign	axis_ready = skd_valid && fifo_full == 0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing FIFOs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NM; gk=gk+1)
	begin : OUTGOING_FIFOS
		wire			fifo_empty;
		sfifo #(
			.BW(DW),	
			.LGFLEN(LGFIFO)
		) fifo (
			.i_clk(S_AXI_ACLK),
			.i_reset(!S_AXI_ARESETN),
			.i_wr(axis_ready), .i_data(skd_data),
				.o_full(fifo_full[gk]),
				.o_fill(ign_fifo_fill[gk*(LGFIFO+1)+:LGFIFO+1]),
			.i_rd(M_AXIS_TVALID[gk] && M_AXIS_TREADY[gk]),
				.o_data(M_AXIS_TDATA[gk*DW +: DW]),
				.o_empty(fifo_empty)
		);

		assign	M_AXIS_TVALID[gk] = !fifo_empty;

	end endgenerate
	// }}}
	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_fifo_fill };
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
	localparam	F_LGDEPTH = 31;
	reg	[F_LGDEPTH-1:0]	icount;
	(* anyconst *)	reg	[$clog2(NM)-1:0]	fc_channel;
	reg	[F_LGDEPTH-1:0]	ocount;
	reg		f_past_valid;
	reg	[LGFIFO:0]	fifo_fill;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		icount <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
		icount <= icount + 1;

	assign	fifo_fill = ign_fifo_fill[fc_channel * (LGFIFO+1) +: LGFIFO+1];

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		ocount <= 0;
	else if (M_AXIS_TVALID[fc_channel] && M_AXIS_TREADY[fc_channel])
		ocount <= ocount + 1;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !$past(S_AXI_ARESETN))
		assume(!S_AXIS_TVALID);
	else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (!$past(S_AXI_ARESETN))
			assert(!M_AXIS_TVALID[fc_channel]);
		else if ($past(M_AXIS_TVALID[fc_channel] && !M_AXIS_TREADY[fc_channel]))
		begin
			assert(M_AXIS_TVALID[fc_channel]);
			assert($stable(M_AXIS_TDATA[fc_channel * DW +: DW]));
		end
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(icount == ocount + (S_AXIS_TREADY ? 0:1) + fifo_fill);
	always @(*)
		assume(!icount[F_LGDEPTH-1]);
`endif	// FORMAL
// }}}
endmodule
