////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbc2pipeline.v
//
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
//
// Copyright (C) 2019-2020, Gisselquist Technology, LLC
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
//
//
`default_nettype	none
//
module	wbc2pipeline(i_clk, i_reset,
		i_mcyc, i_mstb, i_mwe, i_maddr, i_mdata, i_msel,
			o_mack, o_mdata, o_merr,
			i_mcti, i_mbte,
		o_scyc, o_sstb, o_swe, o_saddr, o_sdata, o_ssel,
			i_sstall, i_sack, i_sdata, i_serr);
	parameter	AW = 12,
			DW = 32;
	//
	input	wire			i_clk, i_reset;
	//
	// Incoming WB classic port
	input	wire			i_mcyc, i_mstb, i_mwe;
	input	wire	[AW-1:0]	i_maddr;
	input	wire	[DW-1:0]	i_mdata;
	input	wire	[DW/8-1:0]	i_msel;
	output	reg			o_mack;
	output	reg	[DW-1:0]	o_mdata;
	output	reg			o_merr;
	input	wire	[3-1:0]		i_mcti;
	input	wire	[2-1:0]		i_mbte;
	//
	// Outgoing WB pipelined port
	output	reg			o_scyc, o_sstb, o_swe;
	output	reg	[AW-1:0]	o_saddr;
	output	reg	[DW-1:0]	o_sdata;
	output	reg	[DW/8-1:0]	o_ssel;
	input	wire			i_sstall;
	input	wire			i_sack;
	input	wire	[DW-1:0]	i_sdata;
	input	wire			i_serr;

	reg	last_stb;

	initial	last_stb = 0;
	always @(posedge i_clk)
	if (i_reset || !i_mstb || o_mack || o_merr)
		last_stb <= 0;
	else if (!i_sstall)
		last_stb <= 1;

	always @(*)
	begin
		o_scyc  = i_mcyc && (!o_merr);
		o_sstb  = i_mstb & !last_stb && (!o_merr);
		o_swe   = i_mwe;
		o_saddr = i_maddr;
		o_sdata = i_mdata;
		o_ssel  = i_msel;
	end
	
	initial	o_mack = 0;
	initial	o_merr = 0;
	always @(posedge i_clk)
	if (i_reset || !i_mstb || o_mack || o_merr)
	begin
		o_mack <= 0;
		o_merr <= 0;
	end else begin
		if (i_sack)
			o_mack <= 1;
		if (i_serr)
			o_merr <= 1;
	end

	always @(posedge i_clk)
	if (i_sack)
		o_mdata <= i_sdata;


	// Verilator lint_off UNUSED
	wire	[4:0]	unused;
	assign	unused = { i_mcti, i_mbte };
	// Verilator lint_on  UNUSED
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

	fwbc_slave #(.AW(AW), .DW(DW)) incoming (i_clk, i_reset,
		i_mcyc, i_mstb, i_mwe, i_maddr, i_mdata, i_msel,
			i_mcti, i_mbte,
			o_mack, o_mdata, o_merr, 1'b0);

	fwb_master #(.AW(AW), .DW(DW),
			.F_MAX_STALL(3),
			.F_MAX_ACK_DELAY(3),
			.F_LGDEPTH(1)) pipelined (i_clk, i_reset,
		o_scyc, o_sstb, o_swe, o_saddr, o_sdata, o_ssel,
			i_sack, i_sstall, i_sdata, i_serr,
			f_nreqs, f_nacks, f_outstanding);

//	always @(*)
//	if (f_outstanding)
//		assert(returned);
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
