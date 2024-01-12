////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbp2classic.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Takes a WB pipelined connection from a master, and converts it
//		to WB classic for the slave.
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
module	wbp2classic #(
		// {{{
		parameter	AW = 12,
				DW = 32
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		// Incoming WB pipelined port
		input	wire			i_scyc, i_sstb, i_swe,
		input	wire	[AW-1:0]	i_saddr,
		input	wire	[DW-1:0]	i_sdata,
		input	wire	[DW/8-1:0]	i_ssel,
		output	reg			o_sstall, o_sack,
		output	reg	[DW-1:0]	o_sdata,
		output	reg			o_serr,
		//
		// Outgoing WB classic port
		output	reg			o_mcyc, o_mstb, o_mwe,
		output	reg	[AW-1:0]	o_maddr,
		output	reg	[DW-1:0]	o_mdata,
		output	reg	[DW/8-1:0]	o_msel,
		input	wire			i_mack,
		input	wire	[DW-1:0]	i_mdata,
		input	wire			i_merr,
		// Extra wires, not necessarily necessary for WB/B3
		output	reg	[2:0]		o_mcti,
		output	reg	[1:0]		o_mbte
		// }}}
	);

	//
	// returned = whether we've received our return value or not.
	reg	returned;

	// Combinatorial values forwarded downstream
	// {{{
	always @(*)
	begin
		o_mcyc  = i_scyc;
		o_mstb  = i_sstb && !returned;
		o_mwe   = i_swe;
		o_maddr = i_saddr;
		o_mdata = i_sdata;
		o_msel  = i_ssel;

		// Cycle type indicator: Classic
		o_mcti = 3'b000;
		// Burst type indicator--ignored for single transaction cycle
		// types, such as the classic type above
		o_mbte = 2'b00; // Linear burst
	end
	// }}}

	// returned
	// {{{
	initial	returned = 0;
	always @(posedge i_clk)
	if (i_reset)
		returned <= 0;
	else if (!i_sstb || returned)
		returned <= 0;
	else if (i_mack || i_merr)
		returned <= 1;
	// }}}

	// o_sstall
	// {{{
	always @(*)
		o_sstall = !returned;
	// }}}

	// o_sack, o_serr
	// {{{
	initial	o_sack = 0;
	initial	o_serr = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_sack <= 0;
		o_serr <= 0;
	end else begin
		o_sack <= (i_scyc) && i_mack;
		o_serr <= (i_scyc) && i_merr;
	end
	// }}}

	// o_mdata
	// {{{
	always @(posedge i_clk)
	if (i_mack || i_merr)
		o_sdata <= i_mdata;
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
	reg	f_past_valid;
	reg	f_ongoing;
	reg	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Upstream Wishbone pipeline slave properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_slave #(.AW(AW), .DW(DW),
			.F_MAX_STALL(4),
			.F_MAX_ACK_DELAY(15),
			.F_LGDEPTH(1)) incoming (i_clk, i_reset,
		i_scyc, i_sstb, i_swe, i_saddr, i_sdata, i_ssel,
			o_sack, o_sstall, o_sdata, o_serr,
			f_nreqs, f_nacks, f_outstanding);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Downstream Wishbone classic master properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwbc_master #(.AW(AW), .DW(DW), .F_MAX_DELAY(3))
	classic (i_clk, i_reset,
		o_mcyc, o_mstb, o_mwe, o_maddr, o_mdata, o_msel, o_mcti, o_mbte,
			i_mack, i_mdata, i_merr, 1'b0);

	// }}}

	//
	// Disallow bus aborts
	always @(posedge i_clk)
		f_ongoing <= (!i_reset && i_sstb && !(o_sack | o_serr));

	always @(*)
	if (f_ongoing)
		assume(i_sstb);
`endif
// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
