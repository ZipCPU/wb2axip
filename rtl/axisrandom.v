////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisrandom
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	An AXI-stream based pseudorandom noise generator
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
//
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
// }}}
//
`default_nettype none
//
module	axisrandom #(
		// {{{
		localparam	C_AXIS_DATA_WIDTH = 32
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		output	reg					M_AXIS_TVALID,
		input	wire					M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]		M_AXIS_TDATA
		// }}}
	);

	localparam	INITIAL_FILL = { 1'b1, {(C_AXIS_DATA_WIDTH-1){1'b0}} };
	localparam	LGPOLY = 31;
	localparam [LGPOLY-1:0]			CORE_POLY = { 31'h00_00_20_01 };
	localparam [C_AXIS_DATA_WIDTH-1:0]	POLY
				= { CORE_POLY, {(C_AXIS_DATA_WIDTH-31){1'b0}} };

	// M_AXIS_TVALID
	// {{{
	initial	M_AXIS_TVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 1'b0;
	else
		M_AXIS_TVALID <= 1'b1;
	// }}}

	// M_AXIS_TDATA
	// {{{
	//
	// Note--this setup is *FAR* from cryptographically random.
	//
	initial	M_AXIS_TDATA = INITIAL_FILL;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TDATA <= INITIAL_FILL;
	else if (M_AXIS_TREADY)
	begin
		M_AXIS_TDATA <= M_AXIS_TDATA >> 1;
		M_AXIS_TDATA[C_AXIS_DATA_WIDTH-1] <= ^(M_AXIS_TDATA & POLY);
	end
	// }}}

	// Verilator lint_off UNUSED
	// {{{
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	// Make certain this polynomial will never degenerate, and so that
	// this random number stream will go on for ever--eventually repeating
	// after 2^LGPOLY-1 (hopefully) elements.
	always @(*)
		assert(M_AXIS_TDATA[C_AXIS_DATA_WIDTH-1
				:C_AXIS_DATA_WIDTH-LGPOLY] != 0);

	// AXI stream has only one significant property
	// {{{
	// Here we'll modify it slightly for our purposes
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!M_AXIS_TVALID);
	else begin
		assert(M_AXIS_TVALID);
		if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
			// Normally I'd assesrt M_AXIS_TVALID here, not above,
			// but this core *ALWAYS* produces data
			assert($stable(M_AXIS_TDATA));
		else if ($past(M_AXIS_TVALID))
			// Insist that the data always changes otherwise
			assert($changed(M_AXIS_TDATA));
	end
	// }}}
`endif
// }}}
endmodule
