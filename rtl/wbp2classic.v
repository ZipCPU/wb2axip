////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbp2classic.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Takes a WB pipelined connection from a master, and converts it
//		to WB classic for the slave.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module	wbp2classic(i_clk, i_reset,
		i_mcyc, i_mstb, i_mwe, i_maddr, i_mdata, i_msel,
			o_mstall, o_mack, o_mdata, o_merr,
		o_scyc, o_sstb, o_swe, o_saddr, o_sdata, o_ssel,
			i_sack, i_sdata, i_serr,
			o_scti, o_sbte);
	parameter	AW = 12,
			DW = 32;
	//
	input	wire	i_clk, i_reset;
	//
	// Incoming WB pipelined port
	input	wire			i_mcyc, i_mstb, i_mwe;
	input	wire	[AW-1:0]	i_maddr;
	input	wire	[DW-1:0]	i_mdata;
	input	wire	[DW/8-1:0]	i_msel;
	output	reg			o_mstall, o_mack;
	output	reg	[DW-1:0]	o_mdata;
	output	reg			o_merr;
	//
	// Outgoing WB classic port
	output	reg			o_scyc, o_sstb, o_swe;
	output	reg	[AW-1:0]	o_saddr;
	output	reg	[DW-1:0]	o_sdata;
	output	reg	[DW/8-1:0]	o_ssel;
	input	wire			i_sack;
	input	wire	[DW-1:0]	i_sdata;
	input	wire			i_serr;
	// Extra wires, not necessarily necessary for WB/B3
	output	reg	[2:0]		o_scti;
	output	reg	[1:0]		o_sbte;

	//
	// returned = whether we've received our return value or not.
	reg	returned;

	always @(*)
	begin
		o_scyc  = i_mcyc;
		o_sstb  = i_mstb && !returned;
		o_swe   = i_mwe;
		o_saddr = i_maddr;
		o_sdata = i_mdata;
		o_ssel  = i_msel;

		// Cycle type indicator: Classic
		o_scti = 3'b000;
		// Burst type indicator--ignored for single transaction cycle
		// types, such as the classic type above
		o_sbte = 2'b00; // Linear burst
	end

	initial	returned = 0;
	always @(posedge i_clk)
	if (i_reset)
		returned <= 0;
	else if (!i_mstb || returned)
		returned <= 0;
	else if (i_sack || i_serr)
		returned <= 1;

	always @(*)
		o_mstall = !returned;

	initial	o_mack = 0;
	initial	o_merr = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_mack <= 0;
		o_merr <= 0;
	end else begin
		o_mack <= (i_mcyc) && i_sack;
		o_merr <= (i_mcyc) && i_serr;
	end

	always @(posedge i_clk)
	if (i_sack || i_serr)
		o_mdata <= i_sdata;


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

	fwb_slave #(.AW(AW), .DW(DW),
			.F_MAX_STALL(4),
			.F_MAX_ACK_DELAY(15),
			.F_LGDEPTH(1)) incoming (i_clk, i_reset,
		i_mcyc, i_mstb, i_mwe, i_maddr, i_mdata, i_msel,
			o_mack, o_mstall, o_mdata, o_merr,
			f_nreqs, f_nacks, f_outstanding);

	fwbc_master #(.AW(AW), .DW(DW), .F_MAX_DELAY(3))
	classic (i_clk, i_reset,
		o_scyc, o_sstb, o_swe, o_saddr, o_sdata, o_ssel, o_scti, o_sbte,
			i_sack, i_sdata, i_serr, 1'b0);

	//
	// Disallow bus aborts
	reg	f_ongoing;
	always @(posedge i_clk)
		f_ongoing <= (!i_reset && i_mstb && !(o_mack | o_merr));

	always @(*)
	if (f_ongoing)
		assume(i_mstb);
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
