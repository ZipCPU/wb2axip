////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fwbc_slave.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This file describes the rules of a wishbone *classic*
//		interaction from the perspective of a wishbone classic slave.
//	These formal rules may be used with SymbiYosys to *prove* that the
//	slave properly handles outgoing responses to (assumed correct)
//	incoming requests.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
module	fwbc_slave #(
		// {{{
		parameter		AW=32, DW=32,
		parameter		F_MAX_DELAY = 4,
		parameter	[0:0]	OPT_BUS_ABORT = 0,
		localparam	DLYBITS= $clog2(F_MAX_DELAY+1)
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Wishbone bus
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(DW/8-1):0]	i_wb_sel,
		input	wire	[2:0]		i_wb_cti,
		input	wire	[1:0]		i_wb_bte,
		//
		input	wire			i_wb_ack,
		input	wire	[(DW-1):0]	i_wb_idata,
		input	wire			i_wb_err,
		input	wire			i_wb_rty
		// }}}
	);

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	// next_addr, for use in calculating the next address within a
	// burst
	reg	[AW-1:0]	next_addr;


	//
	// Wrap the request line in a bundle.  The top bit, named STB_BIT,
	// is the bit indicating whether the request described by this vector
	// is a valid request or not.
	//
	localparam	STB_BIT = 2+AW+DW+DW/8+3+2-1;
	wire	[STB_BIT:0]	f_request;
	assign	f_request = { i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
				i_wb_cti, i_wb_bte };

	//
	// A quick register to be used later to know if the $past() operator
	// will yield valid result
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assertions regarding the initial (and reset) state
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Assume we start from a reset condition
	// {{{
	initial assert(i_reset);
	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(i_reset);
	// }}}

	initial `SLAVE_ASSUME(!i_wb_cyc);
	initial `SLAVE_ASSUME(!i_wb_stb);
	//
	initial	`SLAVE_ASSERT(!i_wb_ack);
	initial	`SLAVE_ASSERT(!i_wb_err);
	initial	`SLAVE_ASSERT(!i_wb_rty);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		`SLAVE_ASSUME(!i_wb_cyc);
		`SLAVE_ASSUME(!i_wb_stb);
		//
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
		`SLAVE_ASSERT(!i_wb_rty);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus requests
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// STB can only be true if CYC is also true
	// {{{
	always @(*)
	if (i_wb_stb)
		`SLAVE_ASSUME(i_wb_cyc);
	// }}}

	// If a request was both outstanding and stalled on the last clock,
	// then nothing should change on this clock regarding it.
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(i_wb_stb))&&(i_wb_cyc)
			&&(!$past(i_wb_ack | i_wb_err | i_wb_rty)))
		`SLAVE_ASSUME(i_wb_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset) && i_wb_cyc)
			&&($past(i_wb_stb))&&!$past(i_wb_ack|i_wb_err|i_wb_rty))
	begin
		`SLAVE_ASSUME(i_wb_stb);
		`SLAVE_ASSUME($stable(i_wb_we));
		`SLAVE_ASSUME($stable(i_wb_addr));
		`SLAVE_ASSUME($stable(i_wb_sel));
		`SLAVE_ASSUME($stable(i_wb_cti));
		`SLAVE_ASSUME($stable(i_wb_bte));
		if (i_wb_we)
			`SLAVE_ASSUME($stable(i_wb_data));
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus responses
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// If STB (or CYC) was low on the last two clock cycles, then both
	// ACK and ERR should be low on this clock cycle.
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wb_stb))&&(!i_wb_stb))
	begin
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
		`SLAVE_ASSERT(!i_wb_rty);
	end else if (f_past_valid && $past(i_wb_ack|i_wb_err|i_wb_rty)
			&& !i_wb_stb)
	begin
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
		`SLAVE_ASSERT(!i_wb_rty);
	end
	// }}}

	// OPT_BUS_ABORT
	// {{{
	// If CYC is dropped, this will abort the transaction in
	// progress.  Not all busses support this option, and it's
	// not specifically called out in the spec.  Therefore, we'll
	// check if this is set (it will be clear by default) and
	// prohibit a transaction from being aborted otherwise
	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !OPT_BUS_ABORT
		&& $past(i_wb_stb && !(i_wb_ack|i_wb_err|i_wb_rty)))
		`SLAVE_ASSUME(i_wb_stb);

	always @(posedge i_clk)
	if (!OPT_BUS_ABORT && f_past_valid && !$past(i_reset)
		&& $past(i_wb_stb) && !$past(i_wb_ack | i_wb_err | i_wb_rty))
		`SLAVE_ASSUME(i_wb_cyc);

	always @(posedge i_clk)
	if (OPT_BUS_ABORT && f_past_valid && $past(i_wb_cyc && i_wb_err))
		`SLAVE_ASSUME(!i_wb_cyc);
	// }}}

	// No more than one of ACK, ERR or RTY may ever be true at a given time
	// {{{
	always @(*)
	begin
		if (i_wb_ack)
			`SLAVE_ASSERT(!i_wb_err && !i_wb_rty);
		else if (i_wb_err)
			`SLAVE_ASSERT(!i_wb_rty);
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Burst address checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Possible cycle types
	localparam [2:0]	C_CLASSIC = 3'b000;
	localparam [2:0]	C_FIXED   = 3'b001;
	localparam [2:0]	C_INCR    = 3'b010;
	localparam [2:0]	C_EOB     = 3'b111;

	// Possible burst types
	localparam [1:0]	B_LINEAR = 2'b00;
	localparam [1:0]	B_WRAP4  = 2'b01;
	localparam [1:0]	B_WRAP8  = 2'b10;
	localparam [1:0]	B_WRAP16 = 2'b11;

	always @(*)
	if (i_wb_stb)
	begin
		// Several designations are reserved.  Using those
		// designations is "illegal".
		`SLAVE_ASSUME(i_wb_cti != 3'b011);
		`SLAVE_ASSUME(i_wb_cti != 3'b100);
		`SLAVE_ASSUME(i_wb_cti != 3'b101);
		`SLAVE_ASSUME(i_wb_cti != 3'b110);
	end

	always @(posedge i_clk)
		next_addr <= i_wb_addr + 1;

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !i_reset
		&& $past(i_wb_stb)&&($past(i_wb_err|i_wb_rty|i_wb_ack))
		&&($past(i_wb_cti != C_CLASSIC))&&($past(i_wb_cti != C_EOB)))
	begin
		`SLAVE_ASSUME(i_wb_stb);
		if ($past(i_wb_cti) == C_FIXED)
		begin
			`SLAVE_ASSUME($stable(i_wb_addr));
			`SLAVE_ASSUME((i_wb_cti == C_FIXED || i_wb_cti == C_EOB));
		end else if ($past(i_wb_cti == C_INCR))
		begin
			`SLAVE_ASSUME($stable(i_wb_bte));
			case(i_wb_bte)
			B_LINEAR: `SLAVE_ASSUME(i_wb_addr == next_addr);
			B_WRAP4: begin
				// 4-beat wrap burst
				`SLAVE_ASSUME(i_wb_addr[1:0] == next_addr[1:0]);
				`SLAVE_ASSUME($stable(i_wb_addr[AW-1:2]));
				end
			B_WRAP8: begin
				// 8-beat wrap burst
				`SLAVE_ASSUME(i_wb_addr[2:0] == next_addr[2:0]);
				`SLAVE_ASSUME($stable(i_wb_addr[AW-1:3]));
				end
			B_WRAP16: begin
				// 16-beat wrap burst
				`SLAVE_ASSUME(i_wb_addr[3:0] == next_addr[3:0]);
				`SLAVE_ASSUME($stable(i_wb_addr[AW-1:4]));
				end
			endcase
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Guarantee a return (if possible)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (F_MAX_DELAY > 0)
	begin : DELAYCOUNT
		//
		// Assume the slave cannnot stall for more than F_MAX_STALL
		// counts.  We'll count this forward any time STB and STALL
		// are both true.
		//
		reg	[(DLYBITS-1):0]		f_stall_count;

		initial	f_stall_count = 0;
		always @(posedge i_clk)
		if ((!i_reset)&&(i_wb_stb)&&(!i_wb_ack && !i_wb_err && !i_wb_rty))
			f_stall_count <= f_stall_count + 1'b1;
		else
			f_stall_count <= 0;

		always @(*)
		if (i_wb_cyc)
			`SLAVE_ASSERT(f_stall_count < F_MAX_DELAY);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Some basic cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	reg	[3:0]	ack_count;

	initial	ack_count = 0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		ack_count <= 0;
	else if (f_past_valid && i_wb_ack)
		ack_count <= ack_count + 1'b1;

	always @(*)
		cover(!i_wb_cyc && ack_count > 4);
	always @(*)
		cover(!i_wb_cyc && ack_count > 3);
	// }}}
endmodule
//
// Lest some other module want to use these macros, we undefine them here
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
