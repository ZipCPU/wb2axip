////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/wbupsz.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Bridge a Wishbone bus from a smaller data width to a wider one.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2025, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module wbupsz #(
		// {{{
		parameter	ADDRESS_WIDTH = 28, // Byte address width
		parameter	WIDE_DW = 64,
		parameter	SMALL_DW = 32,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Incoming small port
		// {{{
		input	wire			i_scyc, i_sstb, i_swe,
		input	wire	[ADDRESS_WIDTH-$clog2(SMALL_DW/8)-1:0]	i_saddr,
		input	wire	[SMALL_DW-1:0]	i_sdata,
		input	wire [SMALL_DW/8-1:0]	i_ssel,
		output	wire			o_sstall,
		output	wire			o_sack,
		output	wire	[SMALL_DW-1:0]	o_sdata,
		output	wire			o_serr,
		// }}}
		// Outgoing, small bus size, port
		// {{{
		output	wire			o_wcyc, o_wstb, o_wwe,
		output	wire	[ADDRESS_WIDTH-$clog2(WIDE_DW/8)-1:0]	o_waddr,
		output	wire	[WIDE_DW-1:0]	o_wdata,
		output	wire	[WIDE_DW/8-1:0]	o_wsel,
		input	wire			i_wstall,
		input	wire			i_wack,
		input	wire	[WIDE_DW-1:0]	i_wdata,
		input	wire			i_werr
		// }}}
		// }}}
	);

	generate if (WIDE_DW == SMALL_DW)
	begin : NO_ADJUSTMENT
		// {{{
		assign	o_wcyc  = i_scyc;
		assign	o_wstb  = i_sstb;
		assign	o_wwe   = i_swe;
		assign	o_waddr = i_saddr;
		assign	o_wdata = i_sdata;
		assign	o_wsel  = i_ssel;

		assign	o_sstall = i_wstall;
		assign	o_sack   = i_wack;
		assign	o_sdata  = i_wdata;
		assign	o_serr   = i_werr;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_clk, i_reset };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end else begin : UPSIZE
		localparam	LGFIFO = 5;
		reg			r_cyc, r_stb, r_we, r_ack, r_err;
		reg	[ADDRESS_WIDTH-$clog2(WIDE_DW/8)-1:0]	r_addr;
		reg	[WIDE_DW-1:0]	r_data, rtn_data;
		reg	[WIDE_DW/8-1:0]	r_sel;
		reg	[$clog2(WIDE_DW/SMALL_DW)-1:0]	r_shift;
		wire			fifo_full, ign_fifo_empty;
		wire	[LGFIFO:0]	ign_fifo_fill;

		wire	[$clog2(WIDE_DW/SMALL_DW)-1:0]	w_shift, fifo_shift;
		wire	[WIDE_DW-1:0]	w_data;
		wire	[WIDE_DW/8-1:0]	w_sel;

		if (OPT_LITTLE_ENDIAN)
		begin : GEN_LILEND
			assign	w_data= {{(WIDE_DW-SMALL_DW){1'b0}}, i_sdata };
			assign	w_sel ={{((WIDE_DW-SMALL_DW)/8){1'b0}},i_ssel };
		end else begin : GEN_BIGEND
			assign	w_data= {i_sdata, {(WIDE_DW-SMALL_DW){1'b0}} };
			assign	w_sel ={i_ssel,{((WIDE_DW-SMALL_DW)/8){1'b0}} };
		end

		assign	w_shift = i_saddr[$clog2(WIDE_DW/SMALL_DW)-1:0];

		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_scyc ||(o_wcyc && i_werr) || o_serr)
			r_cyc <= 1'b0;
		else if (i_scyc && i_sstb)
			r_cyc <= 1'b1;

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_addr  = 0;
		initial	r_data  = 0;
		initial	r_sel   = 0;
		always @(posedge i_clk)
		if (i_reset || !i_scyc || o_serr || (o_wcyc && i_werr))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_addr  <= 0;
			r_data  <= 0;
			r_sel   <= 0;
			r_shift <= 0;
			// }}}
		end else if (i_sstb && !o_sstall) // New request
		begin
			// {{{
			r_stb  <= 1'b1;
			r_we   <= i_swe;
			r_addr <= i_saddr[ADDRESS_WIDTH-$clog2(SMALL_DW/8)-1:$clog2(WIDE_DW/SMALL_DW)];
			if (OPT_LITTLE_ENDIAN)
			begin
				r_data <= w_data <<  (SMALL_DW    * w_shift);
				r_sel  <= w_sel  << ((SMALL_DW/8) * w_shift);
			end else begin
				r_data <= w_data >>  (SMALL_DW    * w_shift);
				r_sel  <= w_sel  >> ((SMALL_DW/8) * w_shift);
			end
			r_shift  <= w_shift;
			// }}}
		end else if (o_wstb && !i_wstall)
			r_stb <= 1'b0;

		assign	o_wcyc  = r_cyc;
		assign	o_wstb  = r_stb && !fifo_full;
		assign	o_wwe   = r_we;
		assign	o_waddr = r_addr;
		assign	o_wdata = r_data;
		assign	o_wsel  = r_sel;

		sfifo #(
			.BW($clog2(WIDE_DW/SMALL_DW)), .LGFLEN(LGFIFO)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_scyc),
			.i_wr(o_wstb && !i_wstall),
				.i_data(r_shift),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_wack), .o_data(fifo_shift),
				.o_empty(ign_fifo_empty)
			// }}}
		);

		// o_sdata&rtn_data, the return (shifted) data in the WIDE space
		// {{{
		initial	r_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (!i_scyc || !o_wcyc || i_werr))
			rtn_data <= 0;
		else if (i_wack)
		begin
			if (OPT_LITTLE_ENDIAN)
				rtn_data <= i_wdata >> (SMALL_DW * fifo_shift);
			else
				rtn_data <= i_wdata << (SMALL_DW * fifo_shift);
		end

		if (OPT_LITTLE_ENDIAN)
		begin : GEN_LILEND_RTNDATA
			assign	o_sdata = rtn_data[SMALL_DW-1:0];
		end else begin : GEN_BIGEND_RTNDATA
			assign	o_sdata = rtn_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
		end
		// }}}

		// o_sack, r_ack
		// {{{
		initial	r_ack = 0;
		always @(posedge i_clk)
			r_ack <= !i_reset && i_scyc && o_wcyc && i_wack;

		assign	o_sack  = r_ack;
		// }}}

		// o_serr, r_err
		// {{{
		initial	r_err = 0;
		always @(posedge i_clk)
			r_err <= !i_reset && i_scyc && o_wcyc && i_werr;

		assign	o_serr  = r_err;
		// }}}

		assign	o_sstall= r_stb && (fifo_full || i_wstall);

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, ign_fifo_empty,
					rtn_data };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

endmodule
