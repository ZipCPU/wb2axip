////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/wbdown.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Downconvert a Wishbone bus from a wider width to a smaller one.
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
module wbdown #(
		// {{{
		parameter	ADDRESS_WIDTH = 28, // Byte address width
		parameter	WIDE_DW = 64,
		parameter	SMALL_DW = 32,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter [0:0]	OPT_LOWLOGIC = 1'b0,
		localparam	WIDE_AW  = ADDRESS_WIDTH-$clog2(WIDE_DW/8),
		localparam	SMALL_AW = ADDRESS_WIDTH-$clog2(SMALL_DW/8)
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Incoming wide port
		// {{{
		input	wire			i_wcyc, i_wstb, i_wwe,
		input	wire	[WIDE_AW-1:0]	i_waddr,
		input	wire	[WIDE_DW-1:0]	i_wdata,
		input	wire	[WIDE_DW/8-1:0]	i_wsel,
		output	wire			o_wstall,
		output	wire			o_wack,
		output	wire	[WIDE_DW-1:0]	o_wdata,
		output	wire			o_werr,
		// }}}
		// Outgoing, small bus size, port
		// {{{
		output	wire			o_scyc, o_sstb, o_swe,
		output	wire	[SMALL_AW-1:0]	o_saddr,
		output	wire	[SMALL_DW-1:0]	o_sdata,
		output	wire [SMALL_DW/8-1:0]	o_ssel,
		input	wire			i_sstall,
		input	wire			i_sack,
		input	wire	[SMALL_DW-1:0]	i_sdata,
		input	wire			i_serr
		// }}}
		// }}}
	);

	// Verilator lint_off UNUSED
	localparam	WBLSB = $clog2(WIDE_DW/SMALL_DW);
	// Verilator lint_on  UNUSED
	generate if (WIDE_DW == SMALL_DW)
	begin : NO_ADJUSTMENT
		// {{{
		assign	o_scyc  = i_wcyc;
		assign	o_sstb  = i_wstb;
		assign	o_swe   = i_wwe;
		assign	o_saddr = i_waddr;
		assign	o_sdata = i_wdata;
		assign	o_ssel  = i_wsel;

		assign	o_wstall = i_sstall;
		assign	o_wack   = i_sack;
		assign	o_wdata  = i_sdata;
		assign	o_werr   = i_serr;

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_clk, i_reset };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
		// }}}
	end else if (OPT_LOWLOGIC)
	begin : CHEAP_DOWNSIZER
		// {{{
		// Local declarations
		// {{{
		localparam	LGFIFO = 5;
		reg			r_cyc, r_stb, r_we, r_ack, r_err;
		reg	[SMALL_AW-1:0]	r_addr;
		reg	[WIDE_DW-1:0]	s_data, r_data;
		reg	[WIDE_DW/8-1:0]	s_sel;
		reg	[WBLSB:0]	s_count;
		wire			fifo_full, ign_fifo_empty, fifo_ack;
		wire	[LGFIFO:0]	ign_fifo_fill;
`ifdef	FORMAL
		wire	[LGFIFO:0]	f_first_addr, f_second_addr;
		wire			f_first_data, f_second_data;
		wire			f_first_in_fifo, f_second_in_fifo;
		wire	[LGFIFO:0]	f_distance_to_first,
					f_distance_to_second;
`endif
		// }}}

		// r_cyc
		// {{{
		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc ||(o_scyc && i_serr) || o_werr)
			r_cyc <= 1'b0;
		else if (i_wcyc && i_wstb)
			r_cyc <= 1'b1;
		// }}}

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_addr  = 0;
		initial	s_data  = 0;
		initial	s_sel   = 0;
		initial	s_count = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_scyc && i_serr))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_addr  <= 0;
			s_data  <= 0;
			s_sel   <= 0;
			s_count <= 0;
			// }}}
		end else if (i_wstb && !o_wstall) // New request
		begin
			// {{{
			r_stb  <= 1'b1;
			r_we   <= i_wwe;
			r_addr <= { i_waddr,
					{($clog2(WIDE_DW/SMALL_DW)){1'b0}} };
			s_data <= i_wdata;
			s_sel  <= i_wsel;
			// Verilator lint_off WIDTH
			s_count <= (WIDE_DW/SMALL_DW);
			// Verilator lint_on  WIDTH
			// }}}
		end else if (o_sstb && !i_sstall)
		begin
			// {{{
			s_count <=  s_count - 1;
			r_stb   <= (s_count > 1);
			r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0]
				<= r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0] + 1;
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_data <= s_data >> SMALL_DW;
				s_sel  <= s_sel >> (SMALL_DW/8);
				// Verilator coverage_on
			end else begin
				s_data <= s_data << SMALL_DW;
				s_sel  <= s_sel << (SMALL_DW/8);
			end
			// }}}
		end

		assign	o_scyc = r_cyc;
		assign	o_sstb = r_stb && !fifo_full;
		assign	o_swe  = r_we;
		assign	o_saddr= r_addr;

		if (OPT_LITTLE_ENDIAN)
		begin : OPT_LILEND_DATA
			// Verilator coverage_off
			assign	o_sdata = s_data[SMALL_DW-1:0];
			assign	o_ssel  = s_sel[SMALL_DW/8-1:0];
			// Verilator coverage_on
		end else begin : OPT_BIGEND_DATA
			assign	o_sdata=s_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
			assign	o_ssel =s_sel[WIDE_DW/8-1:(WIDE_DW-SMALL_DW)/8];
		end

		sfifo #(
			.BW(1), .LGFLEN(LGFIFO),
			.OPT_WRITE_ON_FULL(1'b1), .OPT_READ_ON_EMPTY(1'b1)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_wcyc),
			.i_wr(o_sstb && !i_sstall),
				.i_data({ (s_count == 1) ? 1'b1 : 1'b0 }),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_sack), .o_data(fifo_ack),
				.o_empty(ign_fifo_empty)
`ifdef	FORMAL
			, .f_first_addr(f_first_addr),
			.f_second_addr(f_second_addr),
			.f_first_data(f_first_data),
			.f_second_data(f_second_data),
			.f_first_in_fifo(f_first_in_fifo),
			.f_second_in_fifo(f_second_in_fifo),
			.f_distance_to_first(f_distance_to_first),
			.f_distance_to_second(f_distance_to_second)
`endif
			// }}}
		);

		// r_data
		// {{{
		initial	r_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (!i_wcyc || !o_scyc || i_serr))
			r_data <= 0;
		else if (i_sack)
		begin
			if (OPT_LITTLE_ENDIAN)
				r_data<= { i_sdata, r_data[WIDE_DW-1:SMALL_DW] };
			else
				r_data<={r_data[WIDE_DW-SMALL_DW-1:0], i_sdata };
		end
		// }}}

		// r_ack
		// {{{
		initial	r_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_scyc)
			r_ack <= 1'b0;
		else
			r_ack <= i_sack && fifo_ack;
		// }}}

		// r_err
		// {{{
		initial	r_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_scyc)
			r_err <= 1'b0;
		else
			r_err <= i_serr;
		// }}}

		assign	o_wdata = r_data;
		assign	o_wack  = r_ack;
		assign	o_werr  = r_err;
		assign	o_wstall = (r_stb && (fifo_full || i_sstall))
					|| (s_count > 1);

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, ign_fifo_empty };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		//
		// Formal properties
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		parameter	F_LGDEPTH = LGFIFO+1;
		reg			f_past_valid;
		wire	[F_LGDEPTH-1:0]	fslv_nreqs, fslv_nacks,fslv_outstanding;
		wire	[F_LGDEPTH-1:0]	fmst_nreqs, fmst_nacks,fmst_outstanding;
		wire			f_first_ack, f_second_ack;
		reg	[LGFIFO:0]	f_acks_in_fifo;
		reg	[WBLSB-1:0]	f_first_subaddr, f_second_subaddr,
					f_this_subaddr;
		reg	[WIDE_DW/8-1:0]	f_mask;
		reg			f_subsequent;

		initial	f_past_valid = 0;
		always @(posedge i_clk)
			f_past_valid <= 1;

		always @(*)
		if (!f_past_valid)
			assume(i_reset);

		fwb_slave #(
			.AW(WIDE_AW), .DW(WIDE_DW),
		) fslv (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(i_wcyc), .i_wb_stb(i_wstb), .i_wb_we(i_wwe),
			.i_wb_addr(i_waddr), .i_wb_data(i_wdata),
				.i_wb_sel(i_wsel),
			.i_wb_stall(o_wstall), .i_wb_ack(o_wack),
				.i_wb_idata(o_wdata), .i_wb_err(o_werr),
			//
			.f_nreqs(fslv_nreqs), .f_nacks(fslv_nacks),
			.f_outstanding(fslv_outstanding)
			// }}}
		);

		fwb_master #(
			.AW(SMALL_AW), .DW(SMALL_DW),
		) fmst (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(o_scyc), .i_wb_stb(o_sstb), .i_wb_we(o_swe),
			.i_wb_addr(o_saddr), .i_wb_data(o_sdata),
				.i_wb_sel(o_ssel),
			.i_wb_stall(i_sstall), .i_wb_ack(i_sack),
				.i_wb_idata(i_sdata), .i_wb_err(i_serr),
			//
			.f_nreqs(fmst_nreqs), .f_nacks(fmst_nacks),
			.f_outstanding(fmst_outstanding)
			// }}}
		);

		always @(*)
		if (r_stb)
		begin
			assert(s_count > 0);
		end else begin
			assert(s_count == 0);
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
			assert(ign_fifo_fill == fmst_outstanding);

		always @(*)
		if (!i_reset && !o_scyc && i_wcyc && !o_werr)
			assert(ign_fifo_fill == 0);

		always @(*)
		if (!o_scyc)
			assert(!r_stb);

		always @(*)
		if ((r_stb || fslv_outstanding > 0) && i_wcyc && o_scyc)
			assert(o_swe == i_wwe);

		always @(*)
		if (i_wcyc && fslv_outstanding > 0 && !o_werr)
			assert(o_scyc);

		initial	f_acks_in_fifo = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc)
			f_acks_in_fifo <= 0;
		else case({ o_sstb && !i_sstall && (s_count == 1),
				(i_sack && fifo_ack) })
		2'b01: f_acks_in_fifo <= f_acks_in_fifo - 1;
		2'b10: f_acks_in_fifo <= f_acks_in_fifo + 1;
		endcase

		always @(*)
		if (!i_reset && i_wcyc && o_scyc)
		begin
			assert(f_acks_in_fifo + (s_count > 0 ? 1:0)
				+ (o_wack ? 1:0) == fslv_outstanding);

			if (s_count == 0 && fslv_outstanding > (o_wack ? 1:0))
				assert(f_acks_in_fifo > 0);
		end

		assign	f_first_ack  = f_first_data;
		assign	f_second_ack = f_second_data;

		always @(*)
		begin
			// f_first_subaddr  = f_first_data[WBLSB-1:0];
			// f_second_subaddr = f_second_data[WBLSB-1:0];

			f_first_subaddr = (r_stb ? o_saddr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0]
					+ f_distance_to_first[WBLSB-1:0];

			f_second_subaddr = (r_stb ? o_saddr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0]
					+ f_distance_to_second[WBLSB-1:0];

			f_this_subaddr = (r_stb ? o_saddr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0];
		end

		always @(*)
		begin
			if (!i_reset && o_scyc && i_wcyc && f_first_in_fifo)
			begin
				assert(f_first_ack == (&f_first_subaddr[WBLSB-1:0]));
			end
			if (!i_reset && o_scyc && i_wcyc && f_second_in_fifo)
			begin
				assert(f_second_ack == (&f_second_subaddr[WBLSB-1:0]));
			end
			assert(f_acks_in_fifo <= ign_fifo_fill);
			assert(!ign_fifo_empty || f_acks_in_fifo == 0);
			assert(f_acks_in_fifo >=
				((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0));
			assert(ign_fifo_fill - f_acks_in_fifo >=
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0));

			if (o_scyc && f_first_in_fifo && f_distance_to_first == ign_fifo_fill - 1)
				assert(f_first_ack || s_count > 0);
			if (o_scyc && f_second_in_fifo && f_distance_to_second == ign_fifo_fill - 1)
				assert(f_second_ack || s_count > 0);
			if (!i_reset && i_wcyc && o_scyc
					&& ign_fifo_fill > 0 && s_count == 0)
				assert(f_acks_in_fifo > 0);

			if (o_scyc&& i_wcyc  && f_first_in_fifo && s_count == 0 && !o_werr
				&& f_distance_to_first + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo > (f_first_ack ? 1:0));

			if (o_scyc && i_wcyc && f_second_in_fifo && s_count == 0 && !o_werr
					&& f_distance_to_second + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo >
					((f_first_in_fifo && f_first_ack) ? 1:0)
					+ (f_second_ack ? 1:0));
		end

		always @(*)
		begin
			if (f_second_in_fifo)
				f_subsequent = (f_distance_to_second + 1 < ign_fifo_fill);
			else if (f_first_in_fifo)
				f_subsequent = (f_distance_to_first + 1 < ign_fifo_fill);
			else
				f_subsequent = (f_acks_in_fifo > 0 && s_count == 0);
		end

		always @(*)
		if ((!f_first_in_fifo || f_distance_to_first > 0)
			&&(!f_second_in_fifo || f_distance_to_second > 0)
			&& !ign_fifo_empty)
		begin
			assume(!fifo_ack || (f_acks_in_fifo >
				((f_subsequent) ? 1:0)
				+ ((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0)));
			assume(fifo_ack || (ign_fifo_fill - f_acks_in_fifo >
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0)));
			if (f_acks_in_fifo == 1 && s_count == 0 && ign_fifo_fill > 1)
				assume(!fifo_ack);

			assume(fifo_ack == (&f_this_subaddr));
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
		begin
			if (f_first_in_fifo && f_second_in_fifo)
			begin
				assert(f_second_subaddr > f_first_subaddr
					|| f_first_ack);
			end else if (f_first_in_fifo && !f_first_ack)
			begin
				assert(s_count > 0
					&& o_saddr[WBLSB-1:0] > f_first_subaddr);
			end
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
		begin
			assert(s_count <= (1<<WBLSB));
			if (r_stb)
				assert(s_count+o_saddr[WBLSB-1:0] == (1<<WBLSB));
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc
			&& f_first_in_fifo && f_second_in_fifo)
		begin
			assert(f_second_subaddr > f_first_subaddr
				|| f_first_ack);
		end

		always @(*)
		if (OPT_LITTLE_ENDIAN)
			// Verilator coverage_off
			f_mask = {(WIDE_DW/8){1'b1}} >> (o_saddr[WBLSB-1:0] * SMALL_DW/8);
			// Verilator coverage_on
		else
			f_mask = {(WIDE_DW/8){1'b1}} << (o_saddr[WBLSB-1:0] * SMALL_DW/8);

		always @(*)
		if (s_count > 0)
		begin
			assert((s_sel & (~f_mask)) == 0);
		end
`endif
	// }}}
		// }}}
	end else begin : DOWNSIZE
		// {{{
		// Notes:
		// {{{
		// A "full" and "proper" downsizer would only issue requests
		// for memory requested in o_wb_sel.  It would skip the first
		// address (or two) if necessary to do so, and stop early
		// if necessary--as soon as the full access had been completed.
		// Only one clock cycle would be spent (assuming !i_sstall)
		// for each request.
		//	1st clock cycle:
		//		o_sstb <= (i_wsel != 0)
		//		o_saddr[WBLSB-1:0] matches first i_wsel!=0
		//		o_sdata, o_ssel, also matches first i_wsel != 0
		//	nth clock cycle:
		//		Drops o_sstb once all remaining ssel == 0
		//		s_count == 0 (already, was 1 on cycle prior)
		//
		// However ... this full and "proper" downsizer isn't meeting
		// timing.  So ... let's make some adjustments here for timing.
		// Our new goals:
		//	1st clock cycle:
		//		Activates o_sstb if (and only if) either
		//			i_wstb[SMALL-1:0] != 0 or
		//			i_wstb[] == 0 (an empty request)
		//		Sets o_saddr[WBLSB-1:0] = 0
		//		Sets o_sdata = i_wdata[SMALL-1:0]
		//		Sets o_ssel  = i_wsel[SMALL/8-1:0]
		//
		//	2nd clock cycle:
		//		Activates o_sstb (if i_wsel[WIDE-1:SMALL] != 0)
		//		Sets o_saddr, o_sdata, and o_ssel appropriately
		//			so that it matches the first active
		//			word of the transfer.
		//	nth clock cyle:
		//		Drops o_sstb once remaining wsel == 0.
		//
		// }}}

		// Local declarations
		// {{{
		localparam	LGFIFO = 5;

		reg			r_cyc, r_stb, r_we, r_ack, r_err,
					r_first;
		reg	[SMALL_AW-1:0]	r_addr;
		reg			s_null, s_last;
		reg	[WIDE_DW-1:0]	s_data, r_data, nxt_data;
		reg	[WIDE_DW/8-1:0]	s_sel, nxt_sel;
		reg	[WBLSB-1:0]	r_shift;
		wire	[WBLSB-1:0]	fifo_addr, i_subaddr;
		wire			fifo_full, fifo_empty, fifo_ack;
		wire	[LGFIFO:0]	ign_fifo_fill;
`ifdef	FORMAL
		wire	[LGFIFO:0]	f_first_addr, f_second_addr;
		wire	[WBLSB:0]	f_first_data, f_second_data;
		wire			f_first_in_fifo, f_second_in_fifo;
		wire	[LGFIFO:0]	f_distance_to_first,
					f_distance_to_second;
`endif
		// }}}

		// r_cyc
		// {{{
		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc ||(o_scyc && i_serr) || o_werr)
			r_cyc <= 1'b0;
		else if (i_wcyc && i_wstb)
			r_cyc <= 1'b1;
		// }}}

		// i_subaddr
		assign	i_subaddr = subaddr_fn(i_wsel);

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_first = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_scyc && i_serr))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_first <= 1'b0;
			// }}}
		end else if (i_wstb && !o_wstall) // New request
		begin
			// {{{
			r_we   <= i_wwe;
			if (OPT_LITTLE_ENDIAN)
			begin
				r_stb  <=(i_wsel[SMALL_DW/8-1:0] != 0);
				r_first<=(i_wsel[WIDE_DW/8-1:SMALL_DW/8] != 0);
			end else begin
				r_stb<=(i_wsel[WIDE_DW/8-1:WIDE_DW/8-SMALL_DW/8]!= 0);
				r_first<=(i_wsel[WIDE_DW/8-SMALL_DW/8-1:0] != 0);
			end

			// Assuming i_subaddr == 0
			// }}}
		end else if ((r_first && !o_sstb) || (o_sstb && !i_sstall))
		begin
			// {{{
			r_first <= 1'b0;
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				r_stb <= (s_sel[WIDE_DW/8-1:SMALL_DW/8] != 0);
				// Verilator coverage_on
			end else begin
				r_stb <= (s_sel[WIDE_DW/8-SMALL_DW/8-1:0]!=0);
			end
			// }}}
		end

		// s_null
		// {{{
		initial	s_null  = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_scyc && i_serr))
			s_null  <= 0;
		else if (!o_wstall) // New request
			s_null <= i_wstb && (i_wsel == 0);
		else if (!r_first && (!o_sstb || !i_sstall) && s_last
						&& fifo_empty)
			s_null <= 0;
		// }}}

		// s_last
		// {{{
		initial	s_last  = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_scyc && i_serr))
		begin
			s_last <= 1'b1;
		end else if (!o_wstall)
		begin
			// {{{
			if (OPT_LITTLE_ENDIAN)
			begin
				s_last<=(i_wsel[WIDE_DW/8-1:SMALL_DW/8]==0);
			end else begin
				s_last<=(i_wsel[WIDE_DW/8-SMALL_DW/8-1:0]==0);
			end

			if (!i_wstb)
				s_last <= 1'b1;
			// }}}
		end else if (!o_sstb || !i_sstall)
		begin
			// {{{
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_last<=(nxt_sel[WIDE_DW/8-1:SMALL_DW/8]==0);
				// Verilator coverage_on
			end else begin
				s_last<=(nxt_sel[WIDE_DW/8-SMALL_DW/8-1:0]==0);
			end
			// }}}
		end
		// }}}

		// r_addr
		// {{{
		initial	r_addr  = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wcyc || o_werr
						|| (o_scyc && i_serr)))
			r_addr  <= 0;
		else if (!o_wstall)
		begin
			// Treat the subaddress as zero--even if it isn't
			r_addr <= { i_waddr, {(WBLSB){1'b0}} };
			if (OPT_LOWPOWER && !i_wstb)
				r_addr <= 0;
		end else if ((!r_stb && r_first) || (r_stb && !i_sstall))
			r_addr[WBLSB-1:0] <= r_addr[WBLSB-1:0] + r_shift;
		// }}}

		// r_shift, s_data, s_sel
		// {{{
		if (OPT_LITTLE_ENDIAN)
		begin : DNSHIFT_NXTSEL
			always @(*)
				nxt_sel = s_sel >> (r_shift * SMALL_DW/8);
		end else begin : UPSHIFT_NXTSEL
			always @(*)
				nxt_sel = s_sel << (r_shift * SMALL_DW/8);
		end

		initial	s_data  = 0;
		initial	s_sel   = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wcyc || o_werr
						|| (o_scyc && i_serr)))
		begin
			r_shift <= 0;
			s_data  <= 0;
			s_sel   <= 0;
		end else if (!o_wstall)
		begin
			// {{{
			if (OPT_LITTLE_ENDIAN)
			begin
				r_shift<= (i_wsel[SMALL_DW/8-1:0] != 0) ? 1
							: i_subaddr;
			end else begin
				r_shift<= (i_wsel[WIDE_DW/8-1:WIDE_DW/8-SMALL_DW/8]!= 0)
						? 1 : i_subaddr;
			end

			s_data <= i_wdata;
			s_sel  <= (i_wstb) ? i_wsel : {(WIDE_DW/8){1'b0}};

			if (OPT_LOWPOWER && !i_wstb)
				{ r_shift, s_data } <= 0;
			// }}}
		end else if (!o_sstb || !i_sstall)	// && !s_last
		begin
			// {{{
			r_shift <= 1;
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_data <= s_data >> (r_shift * SMALL_DW);
				// Verilator coverage_on
			end else begin
				s_data <= s_data << (r_shift * SMALL_DW);
			end
			s_sel  <= nxt_sel;
			// }}}
		end
		// }}}

		assign	o_scyc = r_cyc;
		assign	o_sstb = r_stb && !fifo_full;
		assign	o_swe  = r_we;
		assign	o_saddr= r_addr;

		if (OPT_LITTLE_ENDIAN)
		begin : OPT_LILODATA
			assign	o_sdata = s_data[SMALL_DW-1:0];
			assign	o_ssel  = s_sel[SMALL_DW/8-1:0];
		end else begin : OPT_BIGODATA
			assign	o_sdata =s_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
			assign	o_ssel  =s_sel[WIDE_DW/8-1:(WIDE_DW-SMALL_DW)/8];
		end

		sfifo #(
			.BW(1+WBLSB), .LGFLEN(LGFIFO),
			.OPT_WRITE_ON_FULL(1'b1), .OPT_READ_ON_EMPTY(1'b1)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_wcyc),
			.i_wr(o_sstb && !i_sstall),
				.i_data({ {(s_last) ? 1'b1 : 1'b0 },
					o_saddr[WBLSB-1:0] }),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_sack),
				.o_data({ fifo_ack, fifo_addr }),
				.o_empty(fifo_empty)
`ifdef	FORMAL
			, .f_first_addr(f_first_addr),
			.f_second_addr(f_second_addr),
			.f_first_data(f_first_data),
			.f_second_data(f_second_data),
			.f_first_in_fifo(f_first_in_fifo),
			.f_second_in_fifo(f_second_in_fifo),
			.f_distance_to_first(f_distance_to_first),
			.f_distance_to_second(f_distance_to_second)
`endif
			// }}}
		);

		// nxt_data, r_data
		// {{{
		always @(*)
		begin
			nxt_data = r_data;
			if (o_wack)
				nxt_data = 0;
			if (i_sack)
			begin
				if (OPT_LITTLE_ENDIAN)
				begin
					// Verilator coverage_off
					nxt_data = nxt_data
						| ({ {(WIDE_DW-SMALL_DW){1'b0}}, i_sdata } << (fifo_addr * SMALL_DW));
					// Verilator coverage_on
				end else begin
					nxt_data = nxt_data
						| ({ i_sdata, {(WIDE_DW-SMALL_DW){1'b0}} } >> (fifo_addr * SMALL_DW));
				end
			end
		end

		initial	r_data = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_scyc || i_serr)
			r_data <= 0;
		else
			r_data <= nxt_data;
		// }}}

		// r_ack
		// {{{
		initial	r_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_scyc)
			r_ack <= 1'b0;
		else if (!fifo_empty)
			r_ack <= fifo_ack && i_sack;
		else
			r_ack <= s_null;
		// }}}

		// r_err
		// {{{
		initial	r_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_scyc)
			r_err <= 0;
		else
			r_err <= i_serr;
		// }}}

		assign	o_wdata = r_data;
		assign	o_wack  = r_ack;
		assign	o_werr  = r_err;
		assign	o_wstall= r_first || (r_stb && (fifo_full || i_sstall))
					|| (s_null && !fifo_empty)
					|| (!s_last);

		function [WBLSB-1:0]	subaddr_fn(input [WIDE_DW/8-1:0] sel);
			// {{{
			integer	fnk, fm;
		begin
			subaddr_fn = 0;
			for(fnk=0; fnk<WIDE_DW/SMALL_DW; fnk=fnk+1)
			begin
				fm = WIDE_DW/SMALL_DW-1-fnk;
				if (OPT_LITTLE_ENDIAN)
				begin
					// Verilator coverage_off
					if (sel[fm*SMALL_DW/8 +: SMALL_DW/8] != 0)
						subaddr_fn = fm[WBLSB-1:0];
					// Verilator coverage_on
				end else begin
					if (sel[fnk*SMALL_DW/8 +: SMALL_DW/8] != 0)
						subaddr_fn = fm[WBLSB-1:0];
				end
			end
		end endfunction
		// }}}

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, fifo_empty };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		//
		// Formal properties
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		parameter	F_LGDEPTH = LGFIFO+1;
		reg			f_past_valid;
		wire	[F_LGDEPTH-1:0]	fslv_nreqs, fslv_nacks,fslv_outstanding;
		wire	[F_LGDEPTH-1:0]	fmst_nreqs, fmst_nacks,fmst_outstanding;
		wire			f_first_ack, f_second_ack;
		reg	[LGFIFO:0]	f_acks_in_fifo;
		wire	[WBLSB-1:0]	f_first_subaddr, f_second_subaddr;
		reg	[WIDE_DW/8-1:0]	f_mask;
		reg			f_subsequent;
		//
		reg			f_we;
		reg	[WIDE_AW-1:0]	f_addr;
		reg	[WIDE_DW-1:0]	f_data;
		reg	[WIDE_DW/8-1:0]	f_sel;

		initial	f_past_valid = 0;
		always @(posedge i_clk)
			f_past_valid <= 1;

		always @(*)
		if (!f_past_valid)
			assume(i_reset);

		fwb_slave #(
			.AW(WIDE_AW), .DW(WIDE_DW),
		) fslv (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(i_wcyc), .i_wb_stb(i_wstb), .i_wb_we(i_wwe),
			.i_wb_addr(i_waddr), .i_wb_data(i_wdata),
				.i_wb_sel(i_wsel),
			.i_wb_stall(o_wstall), .i_wb_ack(o_wack),
				.i_wb_idata(o_wdata), .i_wb_err(o_werr),
			//
			.f_nreqs(fslv_nreqs), .f_nacks(fslv_nacks),
			.f_outstanding(fslv_outstanding)
			// }}}
		);

		fwb_master #(
			.AW(SMALL_AW), .DW(SMALL_DW),
		) fmst (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(o_scyc), .i_wb_stb(o_sstb), .i_wb_we(o_swe),
			.i_wb_addr(o_saddr), .i_wb_data(o_sdata),
				.i_wb_sel(o_ssel),
			.i_wb_stall(i_sstall), .i_wb_ack(i_sack),
				.i_wb_idata(i_sdata), .i_wb_err(i_serr),
			//
			.f_nreqs(fmst_nreqs), .f_nacks(fmst_nacks),
			.f_outstanding(fmst_outstanding)
			// }}}
		);

		always @(*)
		if (r_stb)
		begin
			assert(s_count > 0);
			assert(o_ssel  != 0);
			if (r_first)
				assert(o_saddr[WBLSB-1:0] == 0);
		end else if (r_first)
		begin
			assert(o_saddr[WBLSB-1:0] == 0);
			if (OPT_LITTLE_ENDIAN)
			begin
				assert(s_sel[SMALL_DW/8-1:0]   == 0);
				// assert(s_count == 0);
			end else begin
				assert(s_sel[WIDE_DW/8-1:SMALL_DW/8] == 0);
			end
		end else begin
			assert(s_sel   == 0);
			assert(s_count == 0);
		end

		always @(posedge i_clk)
		if (i_wstb && !o_wstall)
		begin
			f_we   <= i_wwe;
			f_addr <= i_waddr;
			f_data <= i_wdata;
			f_sel  <= i_wsel;
		end

		always @(*)
			assert(!r_stb || !s_null);

		always @(*)
		if (r_stb)
		begin
			assert(o_ssel != 0);

			if (OPT_LITTLE_ENDIAN)
			begin
				assert((s_count == 1) == (s_sel[WIDE_DW/8-1:SMALL_DW/8] == 0));
			end else begin
				assert((s_count == 1) == (s_sel[WIDE_DW/8-SMALL_DW/8-1:0] == 0));
			end
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
			assert(ign_fifo_fill == fmst_outstanding);

		always @(*)
		if (!i_reset && !o_scyc && i_wcyc && !o_werr)
			assert(ign_fifo_fill == 0);

		always @(*)
		if (!o_scyc)
			assert(!r_stb);

		always @(*)
		if ((r_stb || fslv_outstanding > 0) && i_wcyc && o_scyc)
			assert(o_swe == i_wwe);

		always @(*)
		if (i_wcyc && fslv_outstanding > 0 && !o_werr)
			assert(o_scyc);

		always @(*)
		if (i_wcyc && !o_wack && fmst_outstanding == 0 && s_count == 0)
			assert(r_data == 0);

		initial	f_acks_in_fifo = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc)
			f_acks_in_fifo <= 0;
		else case({ o_sstb && !i_sstall && (s_count == 1),
				(i_sack && fifo_ack) })
		2'b01: f_acks_in_fifo <= f_acks_in_fifo - 1;
		2'b10: f_acks_in_fifo <= f_acks_in_fifo + 1;
		endcase

		always @(*)
		if (!i_reset && i_wcyc && o_scyc)
		begin
			assert(f_acks_in_fifo + (s_count > 0 ? 1:0)
				+ (s_null ? 1:0)
				+ (o_wack ? 1:0) == fslv_outstanding);

			if (s_count == 0 && fslv_outstanding > (s_null ? 1:0) + (o_wack ? 1:0))
				assert(f_acks_in_fifo > 0);
		end

		assign	f_first_ack  = f_first_data[WBLSB];
		assign	f_second_ack = f_second_data[WBLSB];

		assign	f_first_subaddr  = f_first_data[WBLSB-1:0];
		assign	f_second_subaddr = f_second_data[WBLSB-1:0];

		always @(*)
		begin
			assert(f_acks_in_fifo <= ign_fifo_fill);
			assert(!fifo_empty || f_acks_in_fifo == 0);
			assert(f_acks_in_fifo >=
				((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0));
			assert(ign_fifo_fill - f_acks_in_fifo >=
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0));

			if (o_scyc && f_first_in_fifo && f_distance_to_first == ign_fifo_fill - 1)
				assert(f_first_ack || s_count > 0);
			if (o_scyc && f_second_in_fifo && f_distance_to_second == ign_fifo_fill - 1)
				assert(f_second_ack || s_count > 0);
			if (!i_reset && i_wcyc && o_scyc
					&& ign_fifo_fill > 0 && s_count == 0)
				assert(f_acks_in_fifo > 0);

			if (o_scyc&& i_wcyc  && f_first_in_fifo && s_count == 0 && !o_werr
				&& f_distance_to_first + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo > (f_first_ack ? 1:0));

			if (o_scyc && i_wcyc && f_second_in_fifo && s_count == 0 && !o_werr
					&& f_distance_to_second + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo >
					((f_first_in_fifo && f_first_ack) ? 1:0)
					+ (f_second_ack ? 1:0));
		end

		always @(*)
		begin
			if (f_second_in_fifo)
				f_subsequent = (f_distance_to_second + 1 < ign_fifo_fill);
			else if (f_first_in_fifo)
				f_subsequent = (f_distance_to_first + 1 < ign_fifo_fill);
			else
				f_subsequent = (f_acks_in_fifo > 0 && s_count == 0);
		end

		always @(*)
		if ((!f_first_in_fifo || f_distance_to_first > 0)
			&&(!f_second_in_fifo || f_distance_to_second > 0)
			&& !fifo_empty)
		begin
			assume(!fifo_ack || (f_acks_in_fifo >
				((f_subsequent) ? 1:0)
				+ ((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0)));
			assume(fifo_ack || (ign_fifo_fill - f_acks_in_fifo >
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0)));
			if (f_acks_in_fifo == 1 && s_count == 0 && ign_fifo_fill > 1)
				assume(!fifo_ack);
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
		begin
			if (f_first_in_fifo && f_second_in_fifo)
			begin
				assert(f_second_subaddr > f_first_subaddr
					|| f_first_ack);
			end else if (f_first_in_fifo && !f_first_ack)
			begin
				assert(s_count > 0
					&& o_saddr[WBLSB-1:0] > f_first_subaddr);
			end
		end

		always @(*)
		if (!i_reset && o_scyc && i_wcyc)
		begin
			assert(s_count <= (1<<WBLSB));
			assert(s_count + o_saddr[WBLSB-1:0] <= (1<<WBLSB));
			if (s_count > 1)
				assert(s_count + o_saddr[WBLSB-1:0]==(1<<WBLSB));
		end

		always @(*)
		if (f_first_in_fifo && f_second_in_fifo)
		begin
			assert(f_second_subaddr > f_first_subaddr
				|| f_first_ack);
		end

		always @(*)
		if (OPT_LITTLE_ENDIAN)
			f_mask = {(WIDE_DW/8){1'b1}} >> (o_saddr[WBLSB-1:0] * SMALL_DW/8);
		else
			f_mask = {(WIDE_DW/8){1'b1}} << (o_saddr[WBLSB-1:0] * SMALL_DW/8);

		always @(*)
		if (s_count > 0)
		begin
			assert((s_sel & (~f_mask)) == 0);
		end
`endif
		// }}}
		// }}}
	end endgenerate

endmodule
