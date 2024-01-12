////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbc2pipeline.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Takes a WB classic connection from a master, and converts it
//		to WB pipelined for the slave.
//
//	If you don't see an `ifdef FORMAL section below, then this core hasn't
//	(yet) been formally verified.  Use it at your own risk.
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
`default_nettype	none
// }}}
module	wbc2pipeline #(
		// {{{
		parameter	AW = 12,
				DW = 32
		// }}}
	) (
		// {{{
		//
		input	wire			i_clk, i_reset,
		//
		// Incoming WB classic port
		input	wire			i_scyc, i_sstb, i_swe,
		input	wire	[AW-1:0]	i_saddr,
		input	wire	[DW-1:0]	i_sdata,
		input	wire	[DW/8-1:0]	i_ssel,
		output	reg			o_sack,
		output	reg	[DW-1:0]	o_sdata,
		output	reg			o_serr,
		input	wire	[3-1:0]		i_scti,
		input	wire	[2-1:0]		i_sbte,
		//
		// Outgoing WB pipelined port
		output	reg			o_mcyc, o_mstb, o_mwe,
		output	reg	[AW-1:0]	o_maddr,
		output	reg	[DW-1:0]	o_mdata,
		output	reg	[DW/8-1:0]	o_msel,
		input	wire			i_mstall,
		input	wire			i_mack,
		input	wire	[DW-1:0]	i_mdata,
		input	wire			i_merr
		// }}}
	);

	reg	last_stb;

	// last_stb
	// {{{
	initial	last_stb = 0;
	always @(posedge i_clk)
	if (i_reset || !i_sstb || o_sack || o_serr)
		last_stb <= 0;
	else if (!i_mstall)
		last_stb <= 1;
	// }}}

	// Combinatorial assignments to the downstream port
	// {{{
	always @(*)
	begin
		o_mcyc  = i_scyc && (!o_serr);
		o_mstb  = i_sstb & !last_stb && (!o_serr);
		o_mwe   = i_swe;
		o_maddr = i_saddr;
		o_mdata = i_sdata;
		o_msel  = i_ssel;
	end
	// }}}

	// o_sack, o_serr
	// {{{
	initial	o_sack = 0;
	initial	o_serr = 0;
	always @(posedge i_clk)
	if (i_reset || !i_sstb || o_sack || o_serr)
	begin
		o_sack <= 0;
		o_serr <= 0;
	end else begin
		if (i_mack)
			o_sack <= 1;
		if (i_merr)
			o_serr <= 1;
	end
	// }}}

	// o_sdata
	// {{{
	always @(posedge i_clk)
	if (i_mack)
		o_sdata <= i_mdata;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	[4:0]	unused;
	assign	unused = { i_scti, i_sbte };
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
	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_LGDEPTH = 1;
	reg	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Upstream Wishbone classic slave properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	fwbc_slave #(.AW(AW), .DW(DW)) incoming (i_clk, i_reset,
		i_scyc, i_sstb, i_swe, i_saddr, i_sdata, i_ssel,
			i_scti, i_sbte,
			o_sack, o_sdata, o_serr, 1'b0);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Downstream Wishbone pipeline slave properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	fwb_master #(.AW(AW), .DW(DW),
			.F_MAX_STALL(3),
			.F_MAX_ACK_DELAY(3),
			.F_LGDEPTH(1)) pipelined (i_clk, i_reset,
		o_mcyc, o_mstb, o_mwe, o_maddr, o_mdata, o_msel,
			i_mack, i_mstall, i_mdata, i_merr,
			f_nreqs, f_nacks, f_outstanding);
	// }}}
`endif
// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
