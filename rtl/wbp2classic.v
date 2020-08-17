////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbp2classic.v
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Takes a WB pipelined connection from a master, and converts it
//		to WB classic for the slave.
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
module	wbp2classic #(
	parameter  AW = 12,
               DW = 32
    ) (

	(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME i_clk, ASSOCIATED_BUSIF S_WBP:M_WBC" *)
	(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 i_clk CLK" *)
	input wire i_clk,
	(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME i_reset, POLARITY ACTIVE_HIGH" *)
	(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 i_reset RST" *)
	input wire i_reset,
	//
	// Incoming WB pipelined port WB4 slave interface
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP CYC" *)
	input	wire			i_mcyc,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP STB" *)
	input	wire			i_mstb,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP WE" *)
	input	wire			i_mwe,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP ADR" *)
	input	wire	[(AW-1):0]	i_maddr,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP DAT_MOSI" *)
	input	wire	[(DW-1):0]	i_mdata,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP SEL" *)
	input	wire	[(DW/8-1):0]	i_msel,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP STALL" *)
	output	reg			o_mstall,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP ACK" *)
	output	reg			o_mack,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP DAT_MISO" *)
	output	reg	[(DW-1):0]	o_mdata,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B4 S_WBP ERR" *)
	output	reg			o_merr,
	
	// We'll share the clock and the reset
	
	// Outgoing WB classic port master ( for convinience labelled as WB4, later use separate interface definition for WB3 classic)
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC CYC" *)
	output	reg			o_scyc,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC STB" *)
	output	reg			o_sstb,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC WE" *)
	output	reg			o_swe,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC ADR" *)
	output	reg	[(AW-1):0]	o_saddr,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC DAT_MOSI" *)
	output	reg	[(DW-1):0]	o_sdata,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC SEL" *)
	output	reg	[(DW/8-1):0]	o_ssel,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC ACK" *)
	input	wire			i_sack,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC DAT_MISO" *)
	input	wire	[(DW-1):0]	i_sdata,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC ERR" *)
	input	wire			i_serr,
	// Extra wires, not necessary for WB/B3
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC CTI" *)
	output	reg	[2:0]		o_scti,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone:B3 M_WBC BTE" *)
	output	reg	[1:0]		o_sbte	
);	
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
