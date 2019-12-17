////////////////////////////////////////////////////////////////////////////////
//
// Filename:	afifo.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	A basic asynchronous FIFO.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or (at your
// option) any later version.
//
// The WB2AXIP project is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
// License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module afifo(
	i_wclk, i_wr_reset_n, i_wr, i_wr_data, o_wr_full,
	i_rclk, i_rd_reset_n, i_rd, o_rd_data, o_rd_empty);
	//
	// LGFIFO is the log based-two of the number of entries
	//	in the FIFO, log_2(fifo size)
	parameter	LGFIFO = 3;
	//
	// WIDTH is the number of data bits in each entry
	parameter	WIDTH  = 16;
	//
	// NFF is the number of flip flops used to cross clock domains.
	// 2 is a minimum.  Some applications appreciate the better
	parameter	NFF    = 2;
	//
	// This core can either write on the positive edge of the clock or the
	// negative edge.  Set WRITE_ON_POSEDGE (the default) to write on the
	// positive edge of the clock.
	parameter [0:0]	WRITE_ON_POSEDGE = 1'b1;
	//
	// Many  logic elements can read from memory asynchronously.  This
	// burdens any following logic.  By setting OPT_REGISTER_READS, we
	// force all reads to be synchronous and not burdened by any logic.
	// You can spare a clock of latency by clearing this register.
	parameter [0:0]	OPT_REGISTER_READS = 1'b1;
	//
	// MSB = most significant bit of the FIFO address vector.  It's
	// just short-hand for LGFIFO, and won't work any other way.
	localparam	MSB = LGFIFO;

	//
	// The (incoming) write data interface
	input	wire			i_wclk, i_wr_reset_n, i_wr;
	input	wire	[WIDTH-1:0]	i_wr_data;
	output	reg			o_wr_full;
	//
	// The (incoming) write data interface
	input	wire			i_rclk, i_rd_reset_n, i_rd;
	output	reg	[WIDTH-1:0]	o_rd_data;
	output	reg			o_rd_empty;



	reg	[WIDTH-1:0]		mem	[(1<<LGFIFO)-1:0];
	reg	[LGFIFO:0]		rd_addr, wr_addr,
					rd_wgray, wr_rgray;
	wire	[LGFIFO:0]		next_rd_addr, next_wr_addr;
	reg	[LGFIFO:0]		rgray, wgray;
	(* ASYNC_REG = "TRUE" *) reg	[(LGFIFO+1)*(NFF-1)-1:0]
					rgray_cross, wgray_cross;
	wire				wclk;
	reg	[WIDTH-1:0]		lcl_rd_data;
	reg				lcl_read, lcl_rd_empty;


	generate if (WRITE_ON_POSEDGE)
	begin

		assign	wclk = i_wclk;

	end else begin

		assign	wclk = !i_wclk;

	end endgenerate

	assign	next_wr_addr = wr_addr + 1;
	always @(posedge wclk or negedge i_wr_reset_n)
	if (!i_wr_reset_n)
	begin
		wr_addr <= 0;
		wgray   <= 0;
	end else if (i_wr && !o_wr_full)
	begin
		wr_addr <= next_wr_addr;
		wgray   <= next_wr_addr ^ (next_wr_addr >> 1);
	end

	always @(posedge wclk)
	if (i_wr && !o_wr_full)
		mem[wr_addr[LGFIFO-1:0]] <= i_wr_data;

	assign	next_rd_addr = rd_addr + 1;
	always @(posedge i_rclk or negedge i_rd_reset_n)
	if (!i_rd_reset_n)
	begin
		rd_addr <= 0;
		rgray   <= 0;
	end else if (lcl_read && !lcl_rd_empty)
	begin
		rd_addr <= next_rd_addr;
		rgray   <= next_rd_addr ^ (next_rd_addr >> 1);
	end

	always @(*)
		lcl_rd_data = mem[rd_addr[LGFIFO-1:0]];

	////////////////////////////////////////////////////////////////////////
	//
	// Cross clock domains
	//
	always @(posedge wclk or negedge i_wr_reset_n)
	if (!i_wr_reset_n)
		{ wr_rgray, rgray_cross } <= 0;
	else
		{ wr_rgray, rgray_cross } <= { rgray_cross, rgray };

	always @(posedge i_rclk or negedge i_rd_reset_n)
	if (!i_rd_reset_n)
		{ rd_wgray, wgray_cross } <= 0;
	else
		{ rd_wgray, wgray_cross } <= { wgray_cross, wgray };

	////////////////////////////////////////////////////////////////////////
	//
	// Flag generation
	//

	always @(*)
		o_wr_full = (wr_rgray == { ~wgray[MSB:MSB-1], wgray[MSB-2:0] });

	always @(*)
		lcl_rd_empty = (rd_wgray == rgray);

	generate if (OPT_REGISTER_READS)
	begin

		always @(*)
			lcl_read = (o_rd_empty || i_rd);

		always @(posedge i_rclk or negedge i_rd_reset_n)
		if (!i_rd_reset_n)
			o_rd_empty <= 1'b1;
		else if (lcl_read)
			o_rd_empty <= lcl_rd_empty;
			
		always @(posedge i_rclk)
		if (lcl_read)
			o_rd_data <= lcl_rd_data;
			
	end else begin

		always @(*)
			o_rd_empty = lcl_rd_empty;

		always @(*)
			o_rd_data = lcl_rd_data;

	end endgenerate


`ifdef	FORMAL
	//
	// In the formal proof, F_OPT_DATA_STB includes a series of assumptions
	// associated with a data stribe I/O pin--things like a discontinuous
	// clock--just to make sure the core still works in those circumstances
	parameter [0:0]	F_OPT_DATA_STB = 1'b1;

	(* gclk *)	reg	gbl_clk;
	reg	[LGFIFO:0]	f_fill;
	reg			f_past_valid_gbl, f_past_valid_rd,
				f_rd_in_reset, f_wr_in_reset;

	initial	f_past_valid_gbl = 1'b0;
	always @(posedge gbl_clk)
		f_past_valid_gbl <= 1'b1;

	initial	f_past_valid_rd = 1'b0;
	always @(posedge i_rclk)
		f_past_valid_rd <= 1'b1;

	initial	f_wr_in_reset = 1'b1;
	always @(posedge wclk or negedge i_wr_reset_n)
	if (!i_wr_reset_n)
		f_wr_in_reset <= 1'b1;
	else
		f_wr_in_reset <= 1'b0;

	initial	f_rd_in_reset = 1'b1;
	always @(posedge i_rclk or negedge i_rd_reset_n)
	if (!i_rd_reset_n)
		f_rd_in_reset <= 1'b1;
	else
		f_rd_in_reset <= 1'b0;

	////////////////////////////////////////////////////////////////////////
	//
	// Synchronous signal assumptions
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[WIDTH-1:0]	past_rd_data, past_wr_data;
	reg			past_wr_reset_n, past_rd_reset_n,
				past_rd_empty, past_wclk, past_rclk, past_rd;

	always @(posedge gbl_clk)
	begin
		past_wr_reset_n <= i_wr_reset_n;
		past_rd_reset_n <= i_rd_reset_n;

		past_wclk  <= wclk;
		past_rclk  <= i_rclk;

		past_rd      <= i_rd;
		past_rd_data <= lcl_rd_data;
		past_wr_data <= i_wr_data;

		past_rd_empty<= lcl_rd_empty;
	end

	//
	// Resets are ...
	//	1. Asserted always initially, and ...
	always @(*)
	if (!f_past_valid_gbl)
	begin
		assume(!i_wr_reset_n);
		assume(!i_rd_reset_n);
	end

	//	2. They only ever become active together
	always @(*)
	if (past_wr_reset_n && !i_wr_reset_n)
		assume(!i_rd_reset_n);
	always @(*)
	if (past_rd_reset_n && !i_rd_reset_n)
		assume(!i_wr_reset_n);


	//
	// Read side may be assumed to be synchronous
	always @(*)
	if (f_past_valid_gbl && (past_rclk || !i_rclk)) // if (!$rose(i_rclk))
		assume(i_rd == past_rd);

	always @(*)
	if (f_past_valid_rd && !f_rd_in_reset && !lcl_rd_empty
		&&(past_rclk || !i_rclk))
	begin
		assert(lcl_rd_data == past_rd_data);
		assert(lcl_rd_empty == past_rd_empty);
	end


	generate if (F_OPT_DATA_STB)
	begin

		always @(posedge gbl_clk)
			assume(!o_wr_full);

		always @(posedge gbl_clk)
		if (!i_wr_reset_n)
			assume(!i_wclk);

		always @(posedge gbl_clk)
			assume(i_wr == i_wr_reset_n);

		always @(posedge gbl_clk)
		if ($changed(i_wr_reset_n))
			assume($stable(wclk));

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Fill checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		f_fill = wr_addr - rd_addr;

	always @(*)
	if (!f_wr_in_reset)
		assert(f_fill <= { 1'b1, {(MSB){1'b0}} });


	always @(*)
	if (wr_addr == rd_addr)
		assert(lcl_rd_empty);

	always @(*)
	if ((!f_wr_in_reset && !f_rd_in_reset)
			&& wr_addr == { ~rd_addr[MSB], rd_addr[MSB-1:0] })
		assert(o_wr_full);

	////////////////////////////////////////////////////////////////////////
	//
	// Induction checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (f_wr_in_reset)
	begin
		assert(wr_addr == 0);
		assert(wgray_cross == 0);

		assert(rd_addr == 0);
		assert(rgray_cross == 0);
		assert(rd_wgray == 0);

		assert(lcl_rd_empty);
		assert(!o_wr_full);
	end

	always @(*)
	if (f_rd_in_reset)
	begin
		assert(rd_addr == 0);
		assert(rgray_cross == 0);
		assert(rd_wgray == 0);

		assert(lcl_rd_empty);
	end

	reg	[(LGFIFO+1)*(NFF-1)-1:0]	f_wcross, f_rcross;
	reg	[LGFIFO:0]	f_rd_waddr, f_wr_raddr;

	always @(posedge wclk or negedge i_wr_reset_n)
	if (!i_wr_reset_n)
		{ f_wr_raddr, f_rcross } <= 0;
	else
		{ f_wr_raddr, f_rcross } <= { f_rcross, rd_addr };

	always @(posedge i_rclk or negedge i_rd_reset_n)
	if (!i_rd_reset_n)
		{ f_rd_waddr, f_wcross } <= 0;
	else
		{ f_rd_waddr, f_wcross } <= { f_wcross, wr_addr };

	integer	k;

	always @(*)
	for(k=0; k<NFF-1; k=k+1)
		assert((f_wcross[k*(LGFIFO+1) +: LGFIFO+1]
			^ (f_wcross[k*(LGFIFO+1)+: LGFIFO+1]>>1))
			== wgray_cross[k*(LGFIFO+1) +: LGFIFO+1]);
	always @(*)
	for(k=0; k<NFF-1; k=k+1)
		assert((f_rcross[k*(LGFIFO+1) +: LGFIFO+1]
			^ (f_rcross[k*(LGFIFO+1) +: LGFIFO+1]>>1))
			== rgray_cross[k*(LGFIFO+1) +: LGFIFO+1]);

	always @(*)
		assert((f_wr_raddr ^ (f_wr_raddr >> 1)) == wr_rgray);

	always @(*)
		assert((f_rd_waddr ^ (f_rd_waddr >> 1)) == rd_wgray);

	reg	[LGFIFO:0]	f_rdcross_fill	[NFF-1:0];
	reg	[LGFIFO:0]	f_wrcross_fill	[NFF-1:0];

	always @(*)
	for(k=0; k<NFF-1; k=k+1)
		f_rdcross_fill[k] = f_wcross[k*(LGFIFO+1) +: LGFIFO+1]
				- rd_addr;

	always @(*)
		f_rdcross_fill[NFF-1] = f_rd_waddr - rd_addr;

	always @(*)
	for(k=0; k<NFF; k=k+1)
		assert(f_rdcross_fill[k] <= { 1'b1, {(LGFIFO){1'b0}} });

	always @(*)
	for(k=1; k<NFF; k=k+1)
		assert(f_rdcross_fill[k] <= f_rdcross_fill[k-1]);
	always @(*)
		assert(f_rdcross_fill[0] <= f_fill);

	//
	//
	always @(*)
	for(k=0; k<NFF-1; k=k+1)
		f_wrcross_fill[k] = wr_addr -
			f_rcross[k*(LGFIFO+1) +: LGFIFO+1];

	always @(*)
		f_wrcross_fill[NFF-1] = wr_addr - f_wr_raddr;

	always @(*)
	for(k=0; k<NFF; k=k+1)
		assert(f_wrcross_fill[k] <= { 1'b1, {(LGFIFO){1'b0}} });

	always @(*)
	for(k=1; k<NFF; k=k+1)
		assert(f_wrcross_fill[k] >= f_wrcross_fill[k-1]);
	always @(*)
		assert(f_wrcross_fill[0] >= f_fill);

	////////////////////////////////////////////////////////////////////////
	//
	// Sample check
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyseq *)	reg	pre_wclk, pre_rclk;
			reg	now_wclk, now_rclk;
	always @(posedge gbl_clk)
	begin
		now_wclk <= pre_wclk;
		now_rclk <= pre_rclk;
	end

	always @(*)
	begin
		assume(i_wclk == now_wclk);
		assume(i_rclk == now_rclk);
	end

	always @(posedge gbl_clk)
		assume(i_rclk == $past(pre_rclk));

	always @(*)
	if (!f_past_valid_gbl)
	begin
		assume(!pre_wclk && !wclk);
		assume(!pre_rclk && !i_rclk);
	end

			reg	[WIDTH-1:0]	f_first, f_next;
	(* anyconst *)	reg	[LGFIFO:0]	f_addr;
			reg	[LGFIFO:0]	f_next_addr;
	reg			f_first_in_fifo, f_next_in_fifo;
	reg	[LGFIFO:0]	f_to_first, f_to_next;
	reg	[1:0]	f_state;

	always @(*)
		f_next_addr = f_addr + 1;

	always @(*)
	begin
		f_to_first = f_addr - rd_addr;

		f_first_in_fifo = 1'b1;
		if ((f_to_first >= f_fill)||(f_fill == 0))
			f_first_in_fifo = 1'b0;

		if (mem[f_addr] != f_first)
			f_first_in_fifo = 1'b0;

		//
		// Check the second item

		f_to_next  = f_next_addr - rd_addr;
		f_next_in_fifo = 1'b1;
		if ((f_to_next >= f_fill)||(f_fill == 0))
			f_next_in_fifo = 1'b0;

		if (mem[f_next_addr] != f_next)
			f_next_in_fifo = 1'b0;

	end

	initial	f_state = 0;
	always @(posedge gbl_clk)
	if (!i_wr_reset_n)
		f_state <= 0;
	else case(f_state)
	2'b00: if (($rose(pre_wclk))&& i_wr && !o_wr_full &&(wr_addr == f_addr))
		begin
			f_state <= 2'b01;
			f_first <= i_wr_data;
		end
	2'b01: if ($rose(pre_rclk)&& lcl_read && rd_addr == f_addr)
			f_state <= 2'b00;
		else if ($rose(pre_wclk) && i_wr && !o_wr_full )
		begin
			f_state <= 2'b10;
			f_next  <= i_wr_data;
		end
	2'b10: if ($rose(pre_rclk) && lcl_read && !lcl_rd_empty && rd_addr == f_addr)
		f_state <= 2'b11;
	2'b11: if ($rose(pre_rclk) && lcl_read && !lcl_rd_empty && rd_addr == f_next_addr)
		f_state <= 2'b00;
	endcase
		

	always @(*)
	if (i_wr_reset_n) case(f_state)
	2'b00: begin end
	2'b01: begin
		assert(f_first_in_fifo);
		assert(wr_addr == f_next_addr);
		assert(f_fill >= 1);
		end
	2'b10: begin
		assert(f_first_in_fifo);
		assert(f_next_in_fifo);
		if (!lcl_rd_empty && (rd_addr == f_addr))
			assert(lcl_rd_data == f_first);
		assert(f_fill >= 2);
		end
	2'b11: begin
		assert(rd_addr == f_next_addr);
		assert(f_next_in_fifo);
		assert(f_fill >= 1);
		if (!lcl_rd_empty)
			assert(lcl_rd_data == f_next);
		end
	endcase

	generate if (OPT_REGISTER_READS)
	begin
		reg	past_o_rd_empty;

		always @(posedge gbl_clk)
			past_o_rd_empty <= o_rd_empty;

		always @(posedge gbl_clk)
		if (f_past_valid_gbl && i_rd_reset_n)
		begin
			if ($past(!o_rd_empty && !i_rd && i_rd_reset_n))
				assert($stable(o_rd_data));
		end

		always @(posedge gbl_clk)
		if (!f_rd_in_reset && i_rd_reset_n && i_rclk && !past_rclk)
		begin
			if (past_o_rd_empty)
				assert(o_rd_data == past_rd_data);
			if (past_rd)
				assert(o_rd_data == past_rd_data);
		end

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (i_wr_reset_n && i_rd_reset_n)
	begin
		cover(o_rd_empty);
		cover(!o_rd_empty);
		cover(f_state == 2'b01);
		cover(f_state == 2'b10);
		cover(f_state == 2'b11);
		cover(&f_fill[MSB-1:0]);

		cover(i_rd);
		cover(i_rd && !o_rd_empty);
	end

	generate if (!OPT_DATA_STB)
	begin : COVER_FULL

		reg	cvr_full;

		initial	cvr_full = 1'b0;
		always @(posedge gbl_clk)
		if (!i_wr_reset_n)
			cvr_full <= 1'b0;
		else if (o_wr_full)
			cvr_full <= 1'b1;


		always @(*)
		if (f_past_valid_gbl)
		begin
			cover(o_wr_full);
			cover(o_rd_empty && cvr_full);
			cover(o_rd_empty && f_fill == 0 && cvr_full);
		end

	end else begin : COVER_NEARLY_FULL

		reg	cvr_nearly_full;

		initial	cvr_nearly_full = 1'b0;
		always @(posedge gbl_clk)
		if (!i_wr_reset_n)
			cvr_nearly_full <= 1'b0;
		else if (f_fill == { 1'b0, {(LGFIFO){1'b1} }})
			cvr_nearly_full <= 1'b1;


		always @(*)
		if (f_past_valid_gbl)
		begin
			cover(f_fill == { 1'b0, {(LGFIFO){1'b1} }});
			cover(cvr_nearly_full && i_wr_reset_n);
			cover(o_rd_empty && cvr_nearly_full);
			cover(o_rd_empty && f_fill == 0 && cvr_nearly_full);
		end

	end endgenerate
`endif
endmodule
