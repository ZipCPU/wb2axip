////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fwbc_slave.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
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
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This file is part of the pipelined Wishbone to AXI converter project, a
// project that contains multiple bus bridging designs and formal bus property
// sets.
//
// The bus bridge designs and property sets are free RTL designs: you can
// redistribute them and/or modify any of them under the terms of the GNU
// Lesser General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
//
// The bus bridge designs and property sets are distributed in the hope that
// they will be useful, but WITHOUT ANY WARRANTY; without even the implied
// warranty of MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with these designs.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
module	fwbc_slave(i_clk, i_reset,
		// The Wishbone bus
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			i_wb_cti, i_wb_bti,
			i_wb_ack, i_wb_idata, i_wb_err);
	parameter		AW=32, DW=32;
	parameter		F_MAX_DELAY = 4;
	localparam	DLYBITS= $clog2(F_MAX_DELAY+1);
	//
	input	wire			i_clk, i_reset;
	// Input/master bus
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	input	wire	[(DW-1):0]	i_wb_data;
	input	wire	[(DW/8-1):0]	i_wb_sel;
	input	wire	[2:0]		i_wb_cti;
	input	wire	[1:0]		i_wb_bti;
	//
	input	wire			i_wb_ack;
	input	wire	[(DW-1):0]	i_wb_idata;
	input	wire			i_wb_err;
	//

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	//
	// Wrap the request line in a bundle.  The top bit, named STB_BIT,
	// is the bit indicating whether the request described by this vector
	// is a valid request or not.
	//
	localparam	STB_BIT = 2+AW+DW+DW/8+3+2-1;
	wire	[STB_BIT:0]	f_request;
	assign	f_request = { i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
				i_wb_cti, i_wb_bti };

	//
	// A quick register to be used later to know if the $past() operator
	// will yield valid result
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(i_reset);
	//
	//
	// Assertions regarding the initial (and reset) state
	//
	//

	//
	// Assume we start from a reset condition
	initial assert(i_reset);
	initial `SLAVE_ASSUME(!i_wb_cyc);
	initial `SLAVE_ASSUME(!i_wb_stb);
	//
	initial	`SLAVE_ASSERT(!i_wb_ack);
	initial	`SLAVE_ASSERT(!i_wb_err);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		`SLAVE_ASSUME(!i_wb_cyc);
		`SLAVE_ASSUME(!i_wb_stb);
		//
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
	end

	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(!i_wb_cyc);

	//
	//
	// Bus requests
	//
	//

	// This core only supports classic CTIs.  Burst types are therefore
	// irrelevant and ignored.
	always @(*)
	if (i_wb_stb)
		`SLAVE_ASSUME(i_wb_cti == 3'b0);

	// STB can only be true if CYC is also true
	always @(*)
	if (i_wb_stb)
		`SLAVE_ASSUME(i_wb_cyc);

	// If a request was both outstanding and stalled on the last clock,
	// then nothing should change on this clock regarding it.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(i_wb_stb))&&(i_wb_cyc)
			&&(!$past(i_wb_ack | i_wb_err)))
		`SLAVE_ASSUME(i_wb_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(i_wb_stb))&&(i_wb_stb))
	begin
		`SLAVE_ASSUME($stable(i_wb_we));
		`SLAVE_ASSUME($stable(i_wb_addr));
		`SLAVE_ASSUME($stable(i_wb_sel));
		`SLAVE_ASSUME($stable(i_wb_cti));
		`SLAVE_ASSUME($stable(i_wb_bti));
		if (i_wb_we)
			`SLAVE_ASSUME($stable(i_wb_data));
	end

	//
	//
	// Bus responses
	//
	//

	// If STB (or CYC) was low on the last two clock cycles, then both
	// ACK and ERR should be low on this clock cycle.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wb_stb))&&(!i_wb_stb))
	begin
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
	end

	// ACK and ERR may never both be true at the same time
	always @(*)
		`SLAVE_ASSERT((!i_wb_ack)||(!i_wb_err));

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
		if ((!i_reset)&&(i_wb_stb)&&(!i_wb_ack && !i_wb_err))
			f_stall_count <= f_stall_count + 1'b1;
		else
			f_stall_count <= 0;

		always @(*)
		if (i_wb_cyc)
			`SLAVE_ASSERT(f_stall_count < F_MAX_DELAY);
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Some basic cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	reg	[3:0]	ack_count;

	initial	ack_count = 0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		ack_count <= 0;
	else if (f_past_valid && $fell(i_wb_stb))
		ack_count <= ack_count + 1;

	always @(*)
		cover(!i_wb_cyc && ack_count > 4);

endmodule
//
// Lest some other module want to use these macros, we undefine them here
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
