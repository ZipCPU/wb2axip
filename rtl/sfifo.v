////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sfifo.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A synchronous data FIFO.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Written and distributed by Gisselquist Technology, LLC
// }}}
// This program is hereby granted to the public domain.
// {{{
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module sfifo #(
		// {{{
		parameter	BW=8,	// Byte/data width
		parameter 	LGFLEN=4,
		parameter [0:0]	OPT_ASYNC_READ = 1'b1,
		parameter [0:0]	OPT_WRITE_ON_FULL = 1'b0,
		parameter [0:0]	OPT_READ_ON_EMPTY = 1'b0,
		localparam	FLEN=(1<<LGFLEN)
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		//
		// Write interface
		input	wire		i_wr,
		input	wire [(BW-1):0]	i_data,
		output	reg 		o_full,
		output	reg [LGFLEN:0]	o_fill,
		//
		// Read interface
		input	wire		i_rd,
		output	reg [(BW-1):0]	o_data,
		output	reg		o_empty	// True if FIFO is empty
		// }}}
	);

	// Register/net declarations
	// {{{
	reg			r_full, r_empty;
	reg	[(BW-1):0]	mem[0:(FLEN-1)];
	reg	[LGFLEN:0]	wr_addr, rd_addr;
	reg	[LGFLEN-1:0]	rd_next;

	wire	w_wr = (i_wr && !o_full);
	wire	w_rd = (i_rd && !o_empty);
	// }}}

	// o_fill
	// {{{
	initial	o_fill = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_fill <= 0;
	else case({ w_wr, w_rd })
	2'b01: o_fill <= o_fill - 1;
	2'b10: o_fill <= o_fill + 1;
	default: o_fill <= wr_addr - rd_addr;
	endcase
	// }}}

	// r_full, o_full
	// {{{
	initial	r_full = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_full <= 0;
	else case({ w_wr, w_rd})
	2'b01: r_full <= 1'b0;
	2'b10: r_full <= (o_fill == { 1'b0, {(LGFLEN){1'b1}} });
	default: r_full <= (o_fill == { 1'b1, {(LGFLEN){1'b0}} });
	endcase

	always @(*)
	if (OPT_WRITE_ON_FULL && i_rd)
		o_full = 1'b0;
	else
		o_full = r_full;
	// }}}
		
	// wr_addr, the write address pointer
	// {{{
	initial	wr_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		wr_addr <= 0;
	else if (w_wr)
		wr_addr <= wr_addr + 1'b1;
	// }}}

	// Write to memory
	// {{{
	always @(posedge i_clk)
	if (w_wr)
		mem[wr_addr[(LGFLEN-1):0]] <= i_data;
	// }}}

	// rd_addr, the read address pointer
	// {{{
	initial	rd_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		rd_addr <= 0;
	else if (w_rd)
		rd_addr <= rd_addr + 1;
	// }}}

	always @(*)
		rd_next = rd_addr[LGFLEN-1:0] + 1;

	// r_empty, o_empty
	// {{{
	initial	r_empty = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		r_empty <= 1'b1;
	else case ({ w_wr, w_rd })
	2'b01: r_empty <= (o_fill <= 1);
	2'b10: r_empty <= 1'b0;
	default: begin end
	endcase

	always @(*)
	if (OPT_READ_ON_EMPTY && i_wr)
		o_empty = 1'b0;
	else
		o_empty = r_empty;
	// }}}

	// Read from the FIFO
	// {{{
	generate if (OPT_ASYNC_READ && OPT_READ_ON_EMPTY)
	begin : ASYNCHRONOUS_READ_ON_EMPTY
		// o_data
		// {{{
		always @(*)
		begin
			o_data = mem[rd_addr[LGFLEN-1:0]];
			if (r_empty)
				o_data = i_data;
		end
		// }}}
	end else if (OPT_ASYNC_READ)
	begin : ASYNCHRONOUS_READ
		// o_data
		// {{{
		always @(*)
			o_data = mem[rd_addr[LGFLEN-1:0]];
		// }}}
	end else begin : REGISTERED_READ
		// {{{
		reg		bypass_valid;
		reg [BW-1:0]	bypass_data, rd_data;

		// Memory read, bypassing it if we must
		// {{{
		initial bypass_valid = 0;
		always @(posedge i_clk)
		if (i_reset)
			bypass_valid <= 0;
		else begin
			bypass_valid <= 1'b0;
			if (!i_wr)
				bypass_valid <= 1'b0;
			else if (r_empty || (i_rd && (o_fill == 1)))
				bypass_valid <= 1'b1;
		end

		always @(posedge i_clk)
			bypass_data <= i_data;

		initial mem[0] = 0;
		initial rd_data = 0;
		always @(posedge i_clk)
			rd_data <= mem[(w_rd)?rd_next : rd_addr[LGFLEN-1:0]];

		always @(*)
		if (OPT_READ_ON_EMPTY && r_empty)
			o_data = i_data;
		else if (bypass_valid)
			o_data = bypass_data;
		else
			o_data = rd_data;
		// }}}
		// }}}
	end endgenerate
	// }}}

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[LGFLEN-1:0]	unused;
	assign	unused = rd_next;
	// verilator lint_on  UNUSED

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// FORMAL METHODS
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
`ifdef	FORMAL

//
// Assumptions about our input(s)
//
//
`ifdef	SFIFO
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg			f_past_valid;
	wire	[LGFLEN:0]	f_fill, f_next, f_empty;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our flags and counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	f_fill = wr_addr - rd_addr;
	assign	f_empty = (wr_addr == rd_addr);
	assign	f_next = rd_addr + 1'b1;

	always @(*)
	begin
		assert(f_fill <= { 1'b1, {(LGFLEN){1'b0}} });
		assert(o_fill == f_fill);

		assert(r_full  == (f_fill == {1'b1, {(LGFLEN){1'b0}} }));
		assert(r_empty == (f_fill == 0));
		assert(rd_next == f_next[LGFLEN-1:0]);

		if (!OPT_WRITE_ON_FULL)
			assert(o_full == r_full);
		else
			assert(o_full == (r_full && !i_rd));

		if (!OPT_READ_ON_EMPTY)
			assert(o_empty == r_empty);
		else
			assert(o_empty == (r_empty && !i_wr));
	end

	always @(posedge i_clk)
	if (!OPT_ASYNC_READ && f_past_valid)
	begin
		if (f_fill == 0)
		begin
			assert(r_empty);
			assert(o_empty || (OPT_READ_ON_EMPTY && i_wr));
		end else if ($past(f_fill)>1)
			assert(!r_empty);
		else if ($past(!i_rd && f_fill > 0))
			assert(!r_empty);
	end

	always @(*)
	if (!r_empty)
		// This also applies for the registered read case
		assert(mem[rd_addr] == o_data);
	else if (OPT_READ_ON_EMPTY)
		assert(o_data == i_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract: (Twin write test)
	// {{{
	// If you write two values in succession, you should be able to read
	// those same two values in succession some time later.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[LGFLEN:0]	f_first_addr;
			reg	[LGFLEN:0]	f_second_addr;
			reg	[BW-1:0]	f_first_data, f_second_data;

	reg	f_first_addr_in_fifo,  f_first_in_fifo;
	reg	f_second_addr_in_fifo, f_second_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second;

	always @(*)
		f_second_addr = f_first_addr + 1;

	always @(*)
	begin
		f_distance_to_first = (f_first_addr - rd_addr);
		f_first_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_first < f_fill))
			f_first_addr_in_fifo = 1;
	end

	always @(*)
	begin
		f_distance_to_second = (f_second_addr - rd_addr);
		f_second_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_second < f_fill))
			f_second_addr_in_fifo = 1;
	end

	always @(posedge i_clk)
	if (w_wr && wr_addr == f_first_addr)
		f_first_data <= i_data;

	always @(posedge i_clk)
	if (w_wr && wr_addr == f_second_addr)
		f_second_data <= i_data;

	always @(*)
	if (f_first_addr_in_fifo)
		assert(mem[f_first_addr] == f_first_data);
	always @(*)
		f_first_in_fifo = (f_first_addr_in_fifo && (mem[f_first_addr] == f_first_data));

	always @(*)
	if (f_second_addr_in_fifo)
		assert(mem[f_second_addr] == f_second_data);

	always @(*)
		f_second_in_fifo = (f_second_addr_in_fifo && (mem[f_second_addr] == f_second_data));

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		case({$past(f_first_in_fifo), $past(f_second_in_fifo)})
		2'b00: begin
				if ($past(w_wr && (!w_rd || !r_empty))
					&&($past(wr_addr == f_first_addr)))
					assert(f_first_in_fifo);
				else
					assert(!f_first_in_fifo);
				//
				// The second could be in the FIFO, since
				// one might write other data than f_first_data
				//
				// assert(!f_second_in_fifo);
			end
		2'b01: begin
				assert(!f_first_in_fifo);
				if ($past(w_rd && (rd_addr==f_second_addr)))
					assert((o_empty&&!OPT_ASYNC_READ)||!f_second_in_fifo);
				else
					assert(f_second_in_fifo);
			end
		2'b10: begin
				if ($past(w_wr)
					&&($past(wr_addr == f_second_addr)))
					assert(f_second_in_fifo);
				else
					assert(!f_second_in_fifo);
				if ($past(!w_rd ||(rd_addr != f_first_addr)))
					assert(f_first_in_fifo);
			end
		2'b11: begin
				assert(f_second_in_fifo);
				if ($past(!w_rd ||(rd_addr != f_first_addr)))
				begin
					assert(f_first_in_fifo);
					if (rd_addr == f_first_addr)
						assert(o_data == f_first_data);
				end else begin
					assert(!f_first_in_fifo);
					assert(o_data == f_second_data);
				end
			end
		endcase
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_was_full;
	initial	f_was_full = 0;
	always @(posedge i_clk)
	if (o_full)
		f_was_full <= 1;

`ifdef	SFIFO
	always @(posedge i_clk)
		cover($fell(f_empty));

	always @(posedge i_clk)
		cover($fell(o_empty));

	always @(posedge i_clk)
		cover(f_was_full && f_empty);

	always @(posedge i_clk)
		cover($past(o_full,2)&&(!$past(o_full))&&(o_full));

	always @(posedge i_clk)
	if (f_past_valid)
		cover($past(o_empty,2)&&(!$past(o_empty))&& o_empty);
`endif
	// }}}
`endif // FORMAL
// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
