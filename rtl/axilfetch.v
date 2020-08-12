////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This is a very simple instruction fetch approach based around
//		AXI-lite.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
// }}}
//
//
`default_nettype	none
//
//
module	axilfetch #(
	parameter	C_AXI_ADDR_WIDTH = 32,
	parameter	C_AXI_DATA_WIDTH = 64,
	parameter	DATA_WIDTH=32,
	parameter	FETCH_LIMIT=16,
	parameter [0:0]	SWAP_ENDIANNESS = 1'b1,
	localparam	AW=C_AXI_ADDR_WIDTH,
	localparam	DW=DATA_WIDTH,
	localparam	AXILLSB = $clog2(C_AXI_DATA_WIDTH/8),
	localparam	INSNS_PER_WORD = C_AXI_DATA_WIDTH / DATA_WIDTH
	) (
	input	wire		S_AXI_ACLK,
	input	wire		S_AXI_ARESETN,
	//
	// CPU interaction wires
	input	wire		i_cpu_reset,
	input	wire		i_new_pc,
	input	wire		i_clear_cache,
	input	wire		i_ready,
	input	wire [AW-1:0]	i_pc,	// Ignored unless i_new_pc as well
	output	reg [DATA_WIDTH-1:0]	o_insn,	// Instruction read from bus
	output	reg [AW-1:0]	o_pc,	// Address of that instruction
	output	reg		o_valid,	// If the output is valid
	output	reg		o_illegal,	// Result is from a bus error
	//
	output	reg				M_AXI_ARVALID,
	input	wire				M_AXI_ARREADY,
	output	reg [C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
	output	reg [2:0]			M_AXI_ARPROT,
	//
	input	reg				M_AXI_RVALID,
	output	reg				M_AXI_RREADY,
	input	reg [C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
	input	reg [1:0]			M_AXI_RRESP
	);

	localparam	LGDEPTH = $clog2(FETCH_LIMIT)+4;
	localparam	LGFIFO = $clog2(FETCH_LIMIT);
	localparam	W = LGDEPTH;
	localparam	FILLBITS = $clog2(INSNS_PER_WORD);
			// ($clog2(INSNS_PER_WORD) > 0)
			//			? $clog2(INSNS_PER_WORD) : 1);

	reg	[W:0]			new_flushcount, outstanding,
					next_outstanding, flushcount;
	reg				flushing, flush_request, full_bus;
	reg	[((AXILLSB>2)?(AXILLSB-3):0):0]	shift;
	wire				fifo_reset, fifo_wr, fifo_rd;
	wire				ign_fifo_full, fifo_empty;
	wire	[LGFIFO:0]		ign_fifo_fill;
	wire	[C_AXI_DATA_WIDTH:0]	fifo_data;
	reg				pending_new_pc;
	reg	[C_AXI_ADDR_WIDTH-1:0]	pending_pc;
	reg	[W-1:0]			fill;
	reg [FILLBITS:0]	out_fill;
	reg	[C_AXI_DATA_WIDTH-1:0]	out_data;
	reg	[C_AXI_DATA_WIDTH-1:0]	endian_swapped_rdata;


	assign	fifo_reset = i_cpu_reset || i_clear_cache || i_new_pc;
	assign	fifo_wr = M_AXI_RVALID && !flushing;


	// ARPROT = 3'b100 for an unprivileged, secure instruction access
	// (not sure what unprivileged or secure mean--even after reading the
	//  spec)
	always @(*)
		M_AXI_ARPROT = 3'b100;

	always @(*)
	begin
		next_outstanding = outstanding;

		case({ M_AXI_ARVALID && M_AXI_ARREADY, M_AXI_RVALID })
		2'b10: next_outstanding = outstanding + 1;
		2'b01: next_outstanding = outstanding - 1;
		default: begin end
		endcase
	end

	initial	outstanding = 0;
	initial	full_bus    = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		outstanding <= 0;
		full_bus <= 0;
	end else begin
		outstanding <= next_outstanding;
		full_bus <= (next_outstanding
			// + (((M_AXI_ARVALID && !M_AXI_ARREADY) ? 1:0)
						>= (1<<LGDEPTH)-1);
	end

	initial	fill = 0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		fill <= 0;
	// else if (fo_reset || flushing)
	//	fill <= 0;
	else case({ M_AXI_ARVALID && M_AXI_ARREADY && !flush_request,
				fifo_rd && !fifo_empty })
	2'b10: fill <= fill + 1;
	2'b01: fill <= fill - 1;
	default: begin end
	endcase

	always @(*)
		new_flushcount = outstanding + (M_AXI_ARVALID ? 1:0)
				- (M_AXI_RVALID ? 1:0);

	initial	flushcount = 0;
	initial	flushing   = 0;
	initial	flush_request = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		flushcount <= 0;
		flushing   <= 0;
		flush_request <= 0;
	end else if (fifo_reset)
	begin
		flushcount <= new_flushcount;
		flushing   <= (new_flushcount > 0);
		flush_request <= (M_AXI_ARVALID && !M_AXI_ARREADY);
	end else begin
		if (M_AXI_RVALID && flushcount > 0)
		begin
			flushcount <= flushcount - 1;
			// Verilator lint_off CMPCONST
			flushing   <= (flushcount > 1);
			// Verilator lint_on  CMPCONST
		end

		if (M_AXI_ARREADY)
			flush_request <= 0;
	end

	initial	M_AXI_ARVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_ARVALID <= 1'b0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		M_AXI_ARVALID <= 1;
		if (i_new_pc || pending_new_pc)
			M_AXI_ARVALID <= 1'b1;

		//
		// Throttle the number of requests we make
		if (fill + (M_AXI_ARVALID ? 1:0)
				+ ((o_valid &&(!i_ready || out_fill > 1)) ? 1:0)
				>= FETCH_LIMIT)
			M_AXI_ARVALID <= 1'b0;
		if (i_cpu_reset || i_clear_cache || full_bus)
			M_AXI_ARVALID <= 1'b0;
	end

	always @(*)
		M_AXI_RREADY = 1'b1;

	initial	pending_new_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_clear_cache)
		pending_new_pc <= 1'b0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		pending_new_pc <= 1'b0;
	else if (i_new_pc)
		pending_new_pc <= 1'b1;

	initial	pending_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		pending_pc <= i_pc;

	always @(posedge S_AXI_ACLK)
	if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		if (i_new_pc)
			M_AXI_ARADDR <= i_pc;
		else if (pending_new_pc)
			M_AXI_ARADDR <= pending_pc;
		else if (M_AXI_ARVALID)
		begin
			M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:AXILLSB]
				<= M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:AXILLSB] +1;
			M_AXI_ARADDR[AXILLSB-1:0] <= 0;
		end
	end

	initial	o_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		o_pc <= i_pc;
	else if (o_valid && i_ready && !o_illegal)
	begin
		o_pc[AW-1:2] <= o_pc[AW-1:2] + 1;
		o_pc[1:0] <= 2'b00;
	end

	generate if (AXILLSB > 2)
	begin : BIG_WORD

		always @(*)
		begin
			shift = o_pc[AXILLSB-1:2];

			if (FETCH_LIMIT > 0 && o_valid)
				shift = 0;
		end

	end else begin : NO_SHIFT

		always @(*)
			shift = 0;

	end endgenerate

	generate if (SWAP_ENDIANNESS)
	begin : SWAPPED_ENDIANNESS
		genvar	gw, gb;	// Word count, byte count

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1) // For each bus word
		for(gb=0; gb<4; gb=gb+1) // For each bus byte
		always @(*)
			endian_swapped_rdata[gw*32+(3-gb)*8 +: 8]
				= M_AXI_RDATA[gw*32+gb*8 +: 8];

	end else begin : NO_ENDIAN_SWAP

		always @(*)
			endian_swapped_rdata = M_AXI_RDATA;

	end endgenerate

	generate if (FETCH_LIMIT <= 1)
	begin : NOCACHE
		// No cache

		// assign	fifo_rd    = fifo_wr;
		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		assign	fifo_empty = !fifo_wr; //(out_fill <= (i_aready ? 1:0));
		assign	fifo_data  = { M_AXI_RRESP[1], endian_swapped_rdata };

		assign	ign_fifo_fill = 1'b0;
		assign	ign_fifo_full = 1'b0;
`ifdef	FORMAL
		always @(*)
		if (M_AXI_RVALID || M_AXI_ARVALID || outstanding > 0)
			assert(!o_valid);
`endif	
	end else if (FETCH_LIMIT == 2)
	begin : DBLFETCH
		// Single word cache
		reg				cache_valid;
		reg	[C_AXI_DATA_WIDTH:0]	cache_data;

		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		assign	fifo_empty =(!M_AXI_RVALID && !cache_valid) || flushing;
		assign	fifo_data = cache_valid ? cache_data
					: ({ M_AXI_RRESP[1], endian_swapped_rdata });


		assign	ign_fifo_fill = cache_valid ? 1 : 0;
		assign	ign_fifo_full = cache_valid;

		initial	cache_valid = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (fifo_reset)
			cache_valid <= 1'b0;
		else if (fifo_wr && o_valid && !fifo_rd)
			cache_valid <= 1;
		else if (fifo_rd)
			cache_valid <= 1'b0;

		always @(posedge S_AXI_ACLK)
		if (M_AXI_RVALID)
			cache_data <= { M_AXI_RRESP[1], endian_swapped_rdata };

	end else begin : FIFO_FETCH
		// FIFO cache

		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));

		sfifo #(.BW(1+C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO))
		fcache(.i_clk(S_AXI_ACLK), .i_reset(fifo_reset),
			.i_wr(fifo_wr),
			.i_data({M_AXI_RRESP[1], endian_swapped_rdata }),
			.o_full(ign_fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(fifo_rd),.o_data(fifo_data),.o_empty(fifo_empty));

	end endgenerate

	initial	o_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		o_valid <= 1'b0;
	else if (!o_valid || i_ready)
		o_valid <= (fifo_rd && !fifo_empty)
			|| out_fill > (o_valid ? 1:0);

	initial	out_fill = 0;
	always @(posedge S_AXI_ARESETN)
	if (fifo_reset)
		out_fill <= 0;
	else if (fifo_rd)
		// Verilator lint_off WIDTH
		out_fill <= (fifo_empty) ? 0: (INSNS_PER_WORD - shift);
		// Verilator lint_on  WIDTH
	else if (i_ready && out_fill > 0)
		out_fill <= out_fill - 1;

	always @(posedge S_AXI_ARESETN)
	if (fifo_rd)
		out_data <= fifo_data[C_AXI_DATA_WIDTH-1:0]>>(DATA_WIDTH*shift);
	else if (i_ready)
		out_data <= out_data >> DATA_WIDTH;

	always @(*)
		o_insn = out_data[DATA_WIDTH-1:0];

	initial	o_illegal = 1'b0;
	always @(posedge S_AXI_ARESETN)
	if (fifo_reset)
		o_illegal <= 1'b0;
	else if (!o_illegal && fifo_rd && !fifo_empty)
		o_illegal <= fifo_data[C_AXI_DATA_WIDTH];
	
	// Make verilator happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = & { 1'b0, M_AXI_RRESP[0], ign_fifo_full, ign_fifo_fill };
	// verilator lint_on  UNUSED


`ifdef	FORMAL
	// Formal properties for this module are maintained elsewhere
`endif
endmodule
