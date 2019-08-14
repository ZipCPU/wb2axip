////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sfifo.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	A synchronous data FIFO.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Written and distributed by Gisselquist Technology, LLC
//
// This program is hereby granted to the public domain.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module sfifo(i_clk, i_reset, i_wr, i_data, o_full, o_fill, i_rd, o_data, o_empty);
	parameter	BW=8;	// Byte/data width
	parameter 	LGFLEN=4;
	parameter [0:0]	OPT_ASYNC_READ = 1'b1;
	localparam	FLEN=(1<<LGFLEN);

	//
	//
	input	wire		i_clk;
	input	wire		i_reset;
	//
	// Write interface
	input	wire		i_wr;
	input	wire [(BW-1):0]	i_data;
	output	reg 		o_full;
	output	reg [LGFLEN:0]	o_fill;
	//
	// Read interface
	input	wire		i_rd;
	output	reg [(BW-1):0]	o_data;
	output	reg		o_empty;	// True if FIFO is empty
	// 

	reg	[(BW-1):0]	mem[0:(FLEN-1)];
	reg	[LGFLEN:0]	wr_addr, rd_addr;
	reg	[LGFLEN-1:0]	rd_next;


	wire	w_wr = (i_wr && !o_full);
	wire	w_rd = (i_rd && !o_empty);

	initial	o_fill = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_fill <= 0;
	else case({ w_wr, w_rd })
	2'b01: o_fill <= o_fill - 1;
	2'b10: o_fill <= o_fill + 1;
	default: o_fill <= wr_addr - rd_addr;
	endcase

	initial	o_full = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_full <= 0;
	else case({ w_wr, w_rd})
	2'b01: o_full <= 1'b0;
	2'b10: o_full <= (o_fill == { 1'b0, {(LGFLEN){1'b1}}});
	default: o_full <= (o_fill == { 1'b1, {(LGFLEN){1'b0}} });
	endcase
		
	// Write
	initial	wr_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		wr_addr <= 0;
	else if (w_wr)
		wr_addr <= wr_addr + 1'b1;

	always @(posedge i_clk)
	if (w_wr)
		mem[wr_addr[(LGFLEN-1):0]] <= i_data;

	initial	rd_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		rd_addr <= 0;
	else if (w_rd)
		rd_addr <= rd_addr + 1;

	always @(*)
		rd_next = rd_addr[LGFLEN-1:0] + 1;

	generate if (OPT_ASYNC_READ)
	begin
		always @(*)
			o_empty = (o_fill  == 0);

		always @(*)
			o_data = mem[rd_addr[LGFLEN-1:0]];

	end else begin
		reg		bypass_valid;
		reg [BW-1:0]	bypass_data, rd_data;

		always @(*)
			o_empty = (o_fill  == 0);


		initial bypass_valid = 0;
		always @(posedge i_clk)
		if (i_reset)
			bypass_valid <= 0;
		else begin
			bypass_valid <= 1'b0;
			if (!i_wr)
				bypass_valid <= 1'b0;
			else if (o_empty || (i_rd && (o_fill == 1)))
				bypass_valid <= 1'b1;
		end

		always @(posedge i_clk)
			bypass_data <= i_data;

		initial mem[0] = 0;
		initial rd_data = 0;
		always @(posedge i_clk)
			rd_data <= mem[(w_rd)?rd_next : rd_addr[LGFLEN-1:0]];

		always @(*)
			o_data = (bypass_valid) ? bypass_data : rd_data;

	end endgenerate

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[LGFLEN-1:0]	unused;
	assign	unused = rd_next;
	// verilator lint_on  UNUSED

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
//
//
// FORMAL METHODS
//
//
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

	reg	f_past_valid;

	//
	// Assertions about our outputs
	//
	//

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	wire	[LGFLEN:0]	f_fill, f_next, f_empty;
	assign	f_fill = wr_addr - rd_addr;
	assign	f_empty = (wr_addr == rd_addr);
	assign	f_next = rd_addr + 1'b1;

	always @(*)
	begin
		assert(f_fill <= { 1'b1, {(LGFLEN){1'b0}}});
		assert(o_fill == f_fill);

		assert(o_full  == (f_fill == {1'b1, {(LGFLEN){1'b0}}}));
		if (OPT_ASYNC_READ)
			assert(o_empty == (f_fill == 0));
		assert(rd_next == f_next[LGFLEN-1:0]);
	end

	always @(posedge i_clk)
	if (!OPT_ASYNC_READ && f_past_valid)
	begin
		if (f_fill == 0)
			assert(o_empty);
		else if ($past(f_fill)>1)
			assert(!o_empty);
		else if ($past(!i_rd && f_fill > 0))
			assert(!o_empty);
	end

	always @(*)
	if ((OPT_ASYNC_READ&&f_past_valid) || !o_empty)
		assert(mem[rd_addr] == o_data);


	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract:
	//
	// If you write two values in succession, you should be able to read
	// those same two values in succession some time later.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[LGFLEN:0]	f_first_addr;
			reg	[LGFLEN:0]	f_second_addr;
	(* anyconst *)	reg	[BW-1:0]	f_first_data, f_second_data;

	always @(*)
		f_second_addr = f_first_addr + 1;

	reg	f_first_addr_in_fifo,  f_first_in_fifo;
	reg	f_second_addr_in_fifo, f_second_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second;

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

	always @(*)
		f_first_in_fifo = (f_first_addr_in_fifo && (mem[f_first_addr] == f_first_data));

	always @(*)
		f_second_in_fifo = (f_second_addr_in_fifo && (mem[f_second_addr] == f_second_data));

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		case({$past(f_first_in_fifo), $past(f_second_in_fifo)})
		2'b00: begin
				if ($past(w_wr)
					&&($past(wr_addr == f_first_addr))
					&&($past(i_data == f_first_data)))
					assert(f_first_in_fifo);
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
					&&($past(wr_addr == f_second_addr))
					&&($past(i_data == f_second_data)))
					assert(f_second_in_fifo);
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

	////////////////////////////////////////////////////////////////////////
	//
	//	Cover properties
	//
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

`endif // FORMAL
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
