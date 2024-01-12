////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fwb_register.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	While it may be fairly easy to verify that a core follows the
//		bus protocol, it's another thing to prove that the answers it
//	returns are the right ones.
//
//	This core is meant to be a complement to the fwb_slave logic, for slaves
//	that consist of a series of registers.  This core will test whether a
//	register can be written to using Wishbone, and/or read back properly
//	later.  It assumes a register having a single clock latency.
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
`default_nettype none
// }}}
module	fwb_register #(
		// {{{
		parameter		AW = 4,
		parameter		DW = 32,
		parameter [AW-1:0]	ADDR = 0,
		parameter [DW-1:0]	MASK = -1
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_wb_stb, i_wb_we,
		input	wire	[AW-1:0]	i_wb_addr,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire	[DW/8-1:0]	i_wb_sel,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_return,
		input	wire	[DW-1:0]	i_register
		// }}}
	);

	// Local register, reset assumption
	// {{{
	reg		f_past_valid;
	reg	[31:0]	freg;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}

	// freg
	// {{{
	always @(posedge i_clk or posedge i_reset)
	if (i_reset)
		freg <= i_register;
	else if (i_wb_stb && i_wb_we && i_wb_addr == ADDR)
	begin
		if (i_wb_sel[0])
			freg[ 7: 0] <= i_wb_data[ 7: 0];
		if (i_wb_sel[1])
			freg[15: 8] <= i_wb_data[15: 8];
		if (i_wb_sel[2])
			freg[23:16] <= i_wb_data[23:16];
		if (i_wb_sel[3])
			freg[31:24] <= i_wb_data[31:24];
	end
	// }}}

	// Comparing freg against i_register
	// {{{
	always @(posedge i_clk)
	if (!i_reset)
		assert(((freg ^ i_register) & MASK) == 0);
	// }}}

	// Verifying wb_ack
	// {{{
	always @(posedge i_clk)
	if (!i_reset && $past(!i_reset && i_wb_stb))
		assert(i_wb_ack);
	else if (!i_reset)
		assert(!i_wb_ack);
	// }}}

	// Verifying i_wb_return
	// {{{
	always @(posedge i_clk)
	if (!i_reset && $past(!i_reset && i_wb_stb && !i_wb_we
			&& i_wb_addr == ADDR))
		assert(i_wb_return == $past(i_register));
	// }}}

endmodule
