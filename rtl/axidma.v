////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axidma.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	To move memory from one location to another, at high speed.
//		This is not a memory to stream, nor a stream to memory core,
//	but rather a memory to memory core.
//
//
// Registers:
//
//	0. Control
//		8b	KEY
//			3'b PROT
//			4'b QOS
//		1b	Abort: Either aborting or aborted
//		1b	Err: Ended on an error
//		1b	Busy
//		1b	Interrupt Enable
//		1b	Interrupt Clear
//		1b	Start
//	1. Unused
//	2-3. Source address, low and then high 64-bit words
//		(Last value read address)
//	4-5. Destination address, low and then high 64-bit words
//		(Next value to write address)
//	6-7. Length, low and then high words
//		(Total number minus successful writes)
//
// Performance goals:
//	100% throughput
//	Stay off the bus until you can drive it hard
// Other goals:
//	Be both AXI3 and AXI4 capable
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
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
// `define			AXI3
// }}}
module	axidma #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		//
		// These two "parameters" really aren't things that can be
		// changed externally.  They control the size of the AXI4-lite
		// port.  Internally, it's defined to have 8, 32-bit registers.
		// The registers are configured wide enough to support 64-bit
		// AXI addressing.  Similarly, the AXI-lite data width is fixed
		// at 32-bits.
		localparam	C_AXIL_ADDR_WIDTH = 5,
		localparam	C_AXIL_DATA_WIDTH = 32,
		//
		// OPT_UNALIGNED turns on support for unaligned addresses,
		// whether source, destination, or length parameters.
		parameter [0:0]	OPT_UNALIGNED = 1'b1,
		//
		// OPT_WRAPMEM controls what happens if the transfer runs off
		// of the end of memory.  If set, the transfer will continue
		// again from the beginning of memory.  If clear, the transfer
		// will be aborted with an error if either read or write
		// address ever get this far.
		parameter [0:0]	OPT_WRAPMEM = 1'b1,
		//
		// LGMAXBURST controls the size of the maximum burst produced
		// by this core.  Specifically, its the log (based 2) of that
		// maximum size.  Hence, for AXI4, this size must be 8
		// (i.e. 2^8 or 256 beats) or less.  For AXI3, the size must
		// be 4 or less.  Tests have verified performance for
		// LGMAXBURST as low as 2.  While I expect it to fail at
		// LGMAXBURST=0, I haven't verified at what value this burst
		// parameter is too small.
`ifdef	AXI3
		parameter	LGMAXBURST=4,	// 16 beats max
`else
		parameter	LGMAXBURST=8,	// 256 beats
`endif
		// LGFIFO: This is the (log-based-2) size of the internal FIFO.
		// Hence if LGFIFO=8, the internal FIFO will have 256 elements
		// (words) in it.  High throughput transfers are accomplished
		// by first storing data into a FIFO, then once a full burst
		// size is available bursting that data over the bus.  In
		// order to be able to keep receiving data while bursting it
		// out, the FIFO size must be at least twice the size of the
		// maximum burst size.  Larger sizes are possible as well.
		parameter	LGFIFO = LGMAXBURST+1,	// 512 element FIFO
		//
		// LGLEN: specifies the number of bits in the transfer length
		// register.  If a transfer cannot be specified in LGLEN bits,
		// it won't happen.  LGLEN must be less than or equal to the
		// address width.
		parameter	LGLEN = C_AXI_ADDR_WIDTH,
		//
		// OPT_LOWPOWER:
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		//
		// OPT_CLKGATE:
		parameter [0:0]	OPT_CLKGATE = OPT_LOWPOWER,
		//
		// AXI uses ID's to transfer information.  This core rather
		// ignores them.  Instead, it uses a constant ID for all
		// transfers.  The following two parameters control that ID.
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_READ_ID = 0,
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_WRITE_ID = 0,
		//
		// The "ABORT_KEY" is a byte that, if written to the control
		// word while the core is running, will cause the data transfer
		// to be aborted.
		parameter	[7:0]			ABORT_KEY  = 8'h6d,
		//
		localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3,
		localparam	AXILLSB= $clog2(C_AXIL_DATA_WIDTH)-3,
		localparam	LGLENW= LGLEN-ADDRLSB
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// AXI low-power interface
		// {{{
		// This has been removed, due to a lack of definition from the
		// AXI standard for these wires.
		// }}}
		//
		// The AXI4-lite control interface
		// {{{
		input	wire				S_AXIL_AWVALID,
		output	wire				S_AXIL_AWREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_AWADDR,
		input	wire 	[2:0]			S_AXIL_AWPROT,
		//
		input	wire				S_AXIL_WVALID,
		output	wire				S_AXIL_WREADY,
		input	wire [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_WDATA,
		input	wire [C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	reg				S_AXIL_BVALID,
		input	wire				S_AXIL_BREADY,
		output	wire	[1:0]			S_AXIL_BRESP,
		//
		input	wire				S_AXIL_ARVALID,
		output	wire				S_AXIL_ARREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_ARADDR,
		input	wire 	[2:0]			S_AXIL_ARPROT,
		//
		output	reg				S_AXIL_RVALID,
		input	wire				S_AXIL_RREADY,
		output	reg [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_RDATA,
		output	wire	[1:0]			S_AXIL_RRESP,
		// }}}
		// The AXI Master (DMA) interface
		// {{{
		output	reg				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	reg	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	reg	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
`ifdef	AXI3
		output	reg	[3:0]			M_AXI_AWLEN,
`else
		output	reg	[7:0]			M_AXI_AWLEN,
`endif
		output	reg	[2:0]			M_AXI_AWSIZE,
		output	reg	[1:0]			M_AXI_AWBURST,
		output	reg				M_AXI_AWLOCK,
		output	reg	[3:0]			M_AXI_AWCACHE,
		output	reg	[2:0]			M_AXI_AWPROT,
		output	reg	[3:0]			M_AXI_AWQOS,
		//
		//
		output	reg				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
`ifdef	AXI3
		output	reg	[C_AXI_ID_WIDTH-1:0]	M_AXI_WID,
`endif
		output	reg	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	reg [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	reg				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		output	reg				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		//
		//
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	reg	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
`ifdef	AXI3
		output	reg	[3:0]			M_AXI_ARLEN,
`else
		output	reg	[7:0]			M_AXI_ARLEN,
`endif
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
		output	wire				M_AXI_ARLOCK,
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP,
		// }}}
		output	reg				o_int
		// }}}
	);

	// Local declarations
	// {{{
	// The number of beats in this maximum burst size is
	// automatically determined from LGMAXBURST, and so its
	// forced to be a power of two this way.
	localparam	MAXBURST=(1<<LGMAXBURST);
	//
	localparam	[2:0]	CTRL_ADDR   = 3'b000,
				// UNUSED_ADDR = 3'b001,
				SRCLO_ADDR  = 3'b010,
				SRCHI_ADDR  = 3'b011,
				DSTLO_ADDR  = 3'b100,
				DSTHI_ADDR  = 3'b101,
				LENLO_ADDR  = 3'b110,
				LENHI_ADDR  = 3'b111;
	localparam		CTRL_START_BIT = 0,
				CTRL_BUSY_BIT  = 0,
				CTRL_INT_BIT   = 1,
				CTRL_INTEN_BIT = 2,
				CTRL_ABORT_BIT = 3,
				CTRL_ERR_BIT   = 4;
	localparam	[1:0]	AXI_INCR = 2'b01, AXI_OKAY = 2'b00;

	wire	gated_clk, clk_active;
	wire	i_clk   = gated_clk;
	wire	i_reset = !S_AXI_ARESETN;

	reg	axil_write_ready, axil_read_ready;
	reg	[2*C_AXIL_DATA_WIDTH-1:0] wide_src, wide_dst, wide_len;
	reg	[2*C_AXIL_DATA_WIDTH-1:0] new_widesrc, new_widedst, new_widelen;

	reg	r_busy, r_err, r_abort, w_start, r_int, r_int_enable,
				r_done, last_write_ack, zero_len;
	reg	[3:0]		r_qos;
	reg	[2:0]		r_prot;
	reg	[LGLEN-1:0]	r_len;	// Length of transfer in octets
	reg	[C_AXI_ADDR_WIDTH-1:0]	r_src_addr, r_dst_addr;

	reg			fifo_reset;
	wire	[LGFIFO:0]	fifo_fill;
	reg	[LGFIFO:0]	fifo_space_available;
	reg	[LGFIFO:0]	fifo_data_available,
				next_fifo_data_available;
	wire			fifo_full, fifo_empty;
	reg	[8:0]		write_count;
	//
	reg				phantom_read, w_start_read,
					no_read_bursts_outstanding;
	reg	[LGLEN:0]		readlen_b;
	reg	[LGLENW:0]		readlen_w, initial_readlen_w;
	reg	[C_AXI_ADDR_WIDTH:0]	read_address;
	reg	[LGLENW:0]		reads_remaining_w,
					read_beats_remaining_w,
					read_bursts_outstanding;
	reg	[C_AXI_ADDR_WIDTH-1:0]	read_distance_to_boundary_b;
	reg				reads_remaining_nonzero;
	//
	reg				phantom_write, w_write_start;
	reg	[C_AXI_ADDR_WIDTH:0]	write_address;
	reg	[LGLENW:0]		writes_remaining_w,
					write_bursts_outstanding;
	reg	[LGLENW:0]		write_burst_length;
	reg				write_requests_remaining;
	reg	[LGLEN:0]		writelen_b;
	reg	[LGLENW:0]		write_beats_remaining;

	wire				awskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	awskd_addr;
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;

	wire	arskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	arskd_addr;
	//
	reg				r_partial_in_valid;
	reg				r_write_fifo, r_read_fifo;
	reg				r_partial_outvalid;
	reg [C_AXI_DATA_WIDTH/8-1:0]	r_first_wstrb,
					r_last_wstrb;
	reg				extra_realignment_write,
					extra_realignment_read;
	reg	[2*ADDRLSB+2:0]		write_realignment;
	reg				last_read_beat;
	reg				clear_read_pipeline;
	reg				last_write_burst;

	//
	// Push some write length calculations across clocks
	reg	[LGLENW:0]		w_writes_remaining_w;
	reg				multiple_write_bursts_remaining,
					first_write_burst;
	reg	[LGMAXBURST:0]		initial_write_distance_to_boundary_w,
					first_write_len_w;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-Lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite control write interface
	// {{{
	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WSTRB, S_AXIL_WDATA }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_strb, wskd_data }));

	always  @(*)
	begin
		axil_write_ready = !S_AXIL_BVALID || S_AXIL_BREADY;
		if (!awskd_valid || !wskd_valid)
			axil_write_ready = 0;
		if (!clk_active)
			axil_write_ready = 0;
	end

	initial	S_AXIL_BVALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		S_AXIL_BVALID <= 1'b0;
	else if (!S_AXIL_BVALID || S_AXIL_BREADY)
		S_AXIL_BVALID <= axil_write_ready;

	assign	S_AXIL_BRESP = AXI_OKAY;

	always @(*)
	begin
		w_start = !r_busy && axil_write_ready && wskd_strb[0]
				&& wskd_data[CTRL_START_BIT]
				&& (awskd_addr == CTRL_ADDR);
		if (r_err && (!wskd_strb[0] || !wskd_data[CTRL_ERR_BIT]))
			w_start = 0;
		if (zero_len)
			w_start = 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		r_err <= 1'b0;
	else if (!r_busy && axil_write_ready)
		r_err <= (r_err) && (!wskd_strb[0] || !wskd_data[CTRL_ERR_BIT]);
	else if (r_busy)
	begin
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			r_err <= 1'b1;
		if (M_AXI_RVALID && M_AXI_RRESP[1])
			r_err <= 1'b1;

		if (!OPT_WRAPMEM && write_address[C_AXI_ADDR_WIDTH]
			&& write_requests_remaining)
			r_err <= 1'b1;
		if (!OPT_WRAPMEM && read_address[C_AXI_ADDR_WIDTH]
			&& reads_remaining_nonzero)
			r_err <= 1'b1;
	end

	initial	r_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy <= 1'b0;
	else if (!r_busy && axil_write_ready)
		r_busy <= w_start;
	else if (r_busy)
	begin
		if (M_AXI_BVALID && M_AXI_BREADY && last_write_ack)
			r_busy <= 1'b0;
		if (r_done)
			r_busy <= 1'b0;
	end

	always @(posedge i_clk)
	if (i_reset || !r_int_enable || !r_busy)
		o_int <= 0;
	else if (r_done)
		o_int <= 1'b1;
	else
		o_int <= (last_write_ack && M_AXI_BVALID && M_AXI_BREADY);

	always @(posedge i_clk)
	if (i_reset)
		r_int <= 0;
	else if (!r_busy)
	begin
		if (axil_write_ready && awskd_addr == CTRL_ADDR
			&& wskd_strb[0])
		begin
			if (wskd_data[CTRL_START_BIT])
				r_int <= 0;
			else if (wskd_data[CTRL_INT_BIT])
				r_int <= 0;
		end
	end else if (r_done)
		r_int <= 1'b1;
	else
		r_int <= (last_write_ack && M_AXI_BVALID && M_AXI_BREADY);

	initial	r_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_abort <= 1'b0;
	else if (!r_busy)
	begin
		if (axil_write_ready && awskd_addr == CTRL_ADDR
			&& wskd_strb[0])
		begin
			if(wskd_data[CTRL_START_BIT]
				||wskd_data[CTRL_ABORT_BIT]
				||wskd_data[CTRL_ERR_BIT])
			r_abort <= 0;
		end
	end else if (!r_abort)
		r_abort <= (axil_write_ready && awskd_addr == CTRL_ADDR)
			&&(wskd_strb[3] && wskd_data[31:24] == ABORT_KEY);

	wire	[C_AXIL_DATA_WIDTH-1:0]	newsrclo, newsrchi,
					newdstlo, newdsthi, newlenlo, newlenhi;

	always @(*)
	begin
		wide_src = 0;
		wide_dst = 0;
		wide_len = 0;

		wide_src[C_AXI_ADDR_WIDTH-1:0] = r_src_addr;
		wide_dst[C_AXI_ADDR_WIDTH-1:0] = r_dst_addr;
		wide_len[LGLEN-1:0] = r_len;

		if (!OPT_UNALIGNED)
		begin
			wide_src[ADDRLSB-1:0] = 0;
			wide_dst[ADDRLSB-1:0] = 0;
			wide_len[ADDRLSB-1:0] = 0;
		end
	end

	assign	newsrclo = apply_wstrb(
			wide_src[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);
	assign	newsrchi = apply_wstrb(
			wide_src[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);
	assign	newdstlo = apply_wstrb(
			wide_dst[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);
	assign	newdsthi = apply_wstrb(
			wide_dst[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);
	assign	newlenlo = apply_wstrb(
			wide_len[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);
	assign	newlenhi = apply_wstrb(
			wide_len[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);

	always @(*)
	begin
		new_widesrc = wide_src;
		new_widedst = wide_dst;
		new_widelen = wide_len;

		if (!awskd_addr[0])
		begin
			new_widesrc[C_AXIL_DATA_WIDTH-1:0] = newsrclo;
			new_widedst[C_AXIL_DATA_WIDTH-1:0] = newdstlo;
			new_widelen[C_AXIL_DATA_WIDTH-1:0] = newlenlo;
		end else begin
			new_widesrc[2*C_AXIL_DATA_WIDTH-1
					:C_AXIL_DATA_WIDTH] = newsrchi;
			new_widedst[2*C_AXIL_DATA_WIDTH-1
					:C_AXIL_DATA_WIDTH] = newdsthi;
			new_widelen[2*C_AXIL_DATA_WIDTH-1
					:C_AXIL_DATA_WIDTH] = newlenhi;
		end

		new_widesrc[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH] = 0;
		new_widedst[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH] = 0;
		new_widelen[2*C_AXIL_DATA_WIDTH-1:LGLEN] = 0;

		if (!OPT_UNALIGNED)
		begin
			new_widesrc[ADDRLSB-1:0] = 0;
			new_widedst[ADDRLSB-1:0] = 0;
			new_widelen[ADDRLSB-1:0] = 0;
		end
	end

	initial	r_len    = 0;
	initial	zero_len = 1;
	initial	r_src_addr = 0;
	initial	r_dst_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		r_len <= 0;
		zero_len <= 1;
		r_prot <= 0;
		r_qos  <= 0;
		r_src_addr <= 0;
		r_dst_addr <= 0;
		r_int_enable <= 0;
		// }}}
	end else if (!r_busy && axil_write_ready)
	begin
		// {{{
		case(awskd_addr)
		CTRL_ADDR: begin
			if (wskd_strb[2])
			begin
				r_prot <= wskd_data[22:20];
				r_qos  <= wskd_data[19:16];
			end
			if (wskd_strb[0])
				r_int_enable <= wskd_data[CTRL_INTEN_BIT];
			end
		SRCLO_ADDR: begin
			r_src_addr <= new_widesrc[C_AXI_ADDR_WIDTH-1:0];
			end
		SRCHI_ADDR: if (C_AXI_ADDR_WIDTH > C_AXIL_DATA_WIDTH) begin
			r_src_addr <= new_widesrc[C_AXI_ADDR_WIDTH-1:0];
			end
		DSTLO_ADDR: begin
			r_dst_addr <= new_widedst[C_AXI_ADDR_WIDTH-1:0];
			end
		DSTHI_ADDR: if (C_AXI_ADDR_WIDTH > C_AXIL_DATA_WIDTH) begin
			r_dst_addr <= new_widedst[C_AXI_ADDR_WIDTH-1:0];
			end
		LENLO_ADDR: begin
			r_len    <= new_widelen[LGLEN-1:0];
			zero_len <= (new_widelen == 0);
			end
		LENHI_ADDR: if (LGLEN > C_AXIL_DATA_WIDTH) begin
			r_len    <= new_widelen[LGLEN-1:0];
			zero_len <= (new_widelen == 0);
			end
		default: begin end
		endcase
		// }}}
	end else if (r_busy)
	begin
		// {{{
		r_dst_addr <= write_address[C_AXI_ADDR_WIDTH-1:0];
		if (writes_remaining_w[LGLENW])
			r_len <= -1;
		else
			r_len <= { writes_remaining_w[LGLENW-1:0],
						{(ADDRLSB){1'b0}} };
		if (OPT_UNALIGNED)
			r_len[ADDRLSB-1:0] <= 0;

		zero_len   <= (writes_remaining_w == 0);

		if (M_AXI_RVALID && M_AXI_RREADY && !M_AXI_RRESP[1])
		begin
			r_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				<= r_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]+1;
			r_src_addr[ADDRLSB-1:0] <= 0;
		end
		// }}}
	end

	function [C_AXIL_DATA_WIDTH-1:0]	apply_wstrb;
	// {{{
		input [C_AXIL_DATA_WIDTH-1:0]	prior_data;
		input [C_AXIL_DATA_WIDTH-1:0]	new_data;
		input [C_AXIL_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXIL_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8] = wstrb[k] ? new_data[k*8 +: 8]
				: prior_data[k*8 +: 8];
		end
	endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite control read interface
	// {{{
	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	always @(*)
	begin
		axil_read_ready = !S_AXIL_RVALID || S_AXIL_RREADY;
		if (!arskd_valid)
			axil_read_ready = 1'b0;
		if (!clk_active)
			axil_read_ready = 1'b0;
	end

	initial	S_AXIL_RVALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		S_AXIL_RVALID <= 1'b0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
		S_AXIL_RVALID <= axil_read_ready;

	always @(posedge i_clk)
	if (i_reset)
		S_AXIL_RDATA <= 0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		S_AXIL_RDATA <= 0;
		case(arskd_addr)
		CTRL_ADDR: begin
			S_AXIL_RDATA[CTRL_ERR_BIT]   <= r_err;
			S_AXIL_RDATA[CTRL_ABORT_BIT] <= r_abort;
			S_AXIL_RDATA[CTRL_INTEN_BIT] <= r_int_enable;
			S_AXIL_RDATA[CTRL_INT_BIT]   <= r_int;
			S_AXIL_RDATA[CTRL_BUSY_BIT]  <= r_busy;
			end
		SRCLO_ADDR:
			S_AXIL_RDATA <= wide_src[C_AXIL_DATA_WIDTH-1:0];
		SRCHI_ADDR:
			S_AXIL_RDATA <= wide_src[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
		DSTLO_ADDR:
			S_AXIL_RDATA <= wide_dst[C_AXIL_DATA_WIDTH-1:0];
		DSTHI_ADDR:
			S_AXIL_RDATA <= wide_dst[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
		LENLO_ADDR:
			S_AXIL_RDATA <= wide_len[C_AXIL_DATA_WIDTH-1:0];
		LENHI_ADDR:
			S_AXIL_RDATA <= wide_len[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
		default: begin end
		endcase

		if (!axil_read_ready)
			S_AXIL_RDATA <= 0;
	end

	assign	S_AXIL_RRESP = AXI_OKAY;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI read processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Read data into our FIFO
	//

	// read_address
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
		read_address <= { 1'b0, r_src_addr };
	else if (phantom_read)
	begin
	// Verilator lint_off WIDTH
		read_address[C_AXI_ADDR_WIDTH:ADDRLSB]
			<= read_address[C_AXI_ADDR_WIDTH:ADDRLSB] +(M_AXI_ARLEN+1);
	// Verilator lint_on WIDTH
		read_address[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// reads_remaining_w, reads_remaining_nonzero
	// {{{
	// Verilator lint_off WIDTH
	always @(posedge i_clk)
	if (!r_busy)
		reads_remaining_w <= readlen_b[LGLEN:ADDRLSB];
	else if (phantom_read)
		reads_remaining_w <= reads_remaining_w - (M_AXI_ARLEN+1);

	always @(posedge i_clk)
	if (!r_busy)
		reads_remaining_nonzero <= 1;
	else if (phantom_read)
		reads_remaining_nonzero
				<= (reads_remaining_w != (M_AXI_ARLEN+1));
	// Verilator lint_on WIDTH
	// }}}

	// read_beats_remaining_w
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
		read_beats_remaining_w <= readlen_b[LGLEN:ADDRLSB];
	else if (M_AXI_RVALID && M_AXI_RREADY)
		read_beats_remaining_w <= read_beats_remaining_w - 1;
	// }}}

	// read_bursts_outstanding, no_read_bursts_outstanding
	// {{{
	initial	read_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		read_bursts_outstanding <= 0;
	end else case({phantom_read,M_AXI_RVALID&& M_AXI_RREADY && M_AXI_RLAST})
	2'b01: read_bursts_outstanding <= read_bursts_outstanding - 1;
	2'b10: read_bursts_outstanding <= read_bursts_outstanding + 1;
	default: begin end
	endcase

	initial	no_read_bursts_outstanding = 1;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		no_read_bursts_outstanding <= 1;
	end else case({phantom_read,M_AXI_RVALID&& M_AXI_RREADY && M_AXI_RLAST})
	2'b01: no_read_bursts_outstanding <= (read_bursts_outstanding == 1);
	2'b10: no_read_bursts_outstanding <= 0;
	default: begin end
	endcase
	// }}}

	// M_AXI_ARADDR
	// {{{
	always @(posedge i_clk)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
		M_AXI_ARADDR <= 0;
	else if (!r_busy)
	begin
		if (!OPT_LOWPOWER || w_start)
			M_AXI_ARADDR <= r_src_addr;
		else
			M_AXI_ARADDR <= 0;
	end else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		M_AXI_ARADDR <= read_address[C_AXI_ADDR_WIDTH-1:0];
		if (OPT_LOWPOWER && !w_start_read)
			M_AXI_ARADDR <= 0;
	end
	// }}}

	// readlen_b
	// {{{
	always @(*)
	if (OPT_UNALIGNED)
		readlen_b = r_len + { {(C_AXI_ADDR_WIDTH-ADDRLSB){1'b0}},
					r_src_addr[ADDRLSB-1:0] }
			+ { {(C_AXI_ADDR_WIDTH-ADDRLSB){1'b0}},
				{(ADDRLSB){1'b1}} };
	else begin
		readlen_b = { 1'b0, r_len };
		readlen_b[ADDRLSB-1:0] = 0;
	end
	// }}}

	// read_distance_to_boundary_b
	// {{{
	always @(*)
	begin
		read_distance_to_boundary_b = 0;
		read_distance_to_boundary_b[ADDRLSB +: LGMAXBURST]
					= -r_src_addr[ADDRLSB +: LGMAXBURST];
	end
	// }}}

	// initial_readlen_w
	// {{{
	always @(*)
	begin
		initial_readlen_w = 0;
		initial_readlen_w[LGMAXBURST] = 1;

		if (r_src_addr[ADDRLSB +: LGMAXBURST] != 0)
			initial_readlen_w[LGMAXBURST:0] = { 1'b0,
				read_distance_to_boundary_b[ADDRLSB +: LGMAXBURST] };
		if (initial_readlen_w > readlen_b[LGLEN:ADDRLSB])
			initial_readlen_w[LGMAXBURST:0] = { 1'b0,
				readlen_b[ADDRLSB +: LGMAXBURST] };
		initial_readlen_w[LGLENW-1:LGMAXBURST+1] = 0;
	end
	// }}}

	// readlen_w
	// {{{
	// Verilator lint_off WIDTH
	always @(posedge i_clk)
	if (!r_busy)
	begin
		readlen_w <= initial_readlen_w;
	end else if (phantom_read)
	begin
		readlen_w <= reads_remaining_w - (M_AXI_ARLEN+1);
		if (reads_remaining_w - (M_AXI_ARLEN+1) > MAXBURST)
			readlen_w <= MAXBURST;
	end
	// Verilator lint_on WIDTH
	// }}}

	// w_start_read
	// {{{
	always @(*)
	begin
		w_start_read = r_busy && reads_remaining_nonzero;
		if (phantom_read)
			w_start_read = 0;
		if (!OPT_WRAPMEM && read_address[C_AXI_ADDR_WIDTH])
			w_start_read = 0;
		if (fifo_space_available < MAXBURST)
			w_start_read = 0;
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			w_start_read = 0;
		if (r_err || r_abort)
			w_start_read = 0;
	end
	// }}}

	// M_AXI_ARVALID, phantom_read
	// {{{
	initial	M_AXI_ARVALID = 1'b0;
	initial	phantom_read  = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		M_AXI_ARVALID <= 0;
		phantom_read  <= 0;
	end else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		M_AXI_ARVALID <= w_start_read;
		phantom_read  <= w_start_read;
	end else
		phantom_read  <= 0;
	// }}}

	// M_AXI_ARLEN
	// {{{
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		M_AXI_ARLEN <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
`ifdef	AXI3
		M_AXI_ARLEN <= readlen_w[3:0] - 4'h1;
`else
		M_AXI_ARLEN <= readlen_w[7:0] - 8'h1;
`endif
		if (OPT_LOWPOWER && !w_start_read)
			M_AXI_ARLEN <= 0;
	end
	// }}}

	assign	M_AXI_ARID    = AXI_READ_ID;
	assign	M_AXI_ARBURST = AXI_INCR;
	assign	M_AXI_ARSIZE  = ADDRLSB[2:0];
	assign	M_AXI_ARLOCK  = 1'b0;
	assign	M_AXI_ARCACHE = 4'b0011;
	assign	M_AXI_ARPROT  = r_prot;
	assign	M_AXI_ARQOS   = r_qos;
		//
	assign	M_AXI_RREADY = !no_read_bursts_outstanding;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The intermediate FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		fifo_reset = i_reset || !r_busy || r_done;

	generate if (OPT_UNALIGNED)
	begin : REALIGNMENT_FIFO
		// {{{
		reg	[ADDRLSB-1:0]		inbyte_shift, outbyte_shift,
						remaining_read_realignment;
		reg	[ADDRLSB+3-1:0]		inshift_down, outshift_down,
						inshift_up, outshift_up;
		reg	[C_AXI_DATA_WIDTH-1:0]	r_partial_inword,
						r_outword, r_partial_outword,
						r_realigned_incoming;
		wire	[C_AXI_DATA_WIDTH-1:0]	fifo_data;
		reg	[ADDRLSB-1:0]		r_last_write_addr;
		reg				r_oneword, r_firstword;


		///////////////////


		always @(posedge i_clk)
		if (!r_busy)
		begin
			inbyte_shift <= r_src_addr[ADDRLSB-1:0];
			inshift_up   <= 0;
			inshift_up[3 +: ADDRLSB] <= -r_src_addr[ADDRLSB-1:0];
		end

		always @(*)
			inshift_down = {  inbyte_shift, 3'b000 };

		always @(*)
			remaining_read_realignment = -r_src_addr[ADDRLSB-1:0];

		// extra_realignment_read will be true if we need to flush
		// the read processor after the last word has been read in an
		// extra write to the FIFO that isn't associated with any reads.
		// In other words, if the number of writes to the FIFO is
		// greater than the number of read beats
		//			- (src_addr unaligned?1:0)
		always @(posedge i_clk)
		if (!r_busy)
		begin
			extra_realignment_read <= (remaining_read_realignment
				>= r_len[ADDRLSB-1:0]) ? 1:0;
			if (r_len[ADDRLSB-1:0] == 0)
				extra_realignment_read <= 1'b0;
			if (r_src_addr[ADDRLSB-1:0] == 0)
				extra_realignment_read <= 1'b0;
		end else if ((!r_write_fifo || !fifo_full) && clear_read_pipeline)
			extra_realignment_read <= 1'b0;

		always @(posedge i_clk)
		if (!r_busy || !extra_realignment_read || clear_read_pipeline)
			clear_read_pipeline <= 0;
		else if (!r_write_fifo || !fifo_full)
			clear_read_pipeline <= (read_beats_remaining_w
						== (M_AXI_RVALID ? 1:0));

`ifdef	FORMAL
		always @(*)
		if (r_busy)
		begin
			if (!extra_realignment_read)
			begin
				assert(!clear_read_pipeline);
			end else if (read_beats_remaining_w > 0)
			begin
				assert(!clear_read_pipeline);
			end else if (!no_read_bursts_outstanding)
			begin
				assert(!clear_read_pipeline);
			end
		end
`endif

		always @(posedge i_clk)
		if (fifo_reset)
			r_partial_in_valid <= (r_src_addr[ADDRLSB-1:0] == 0);
		else if (M_AXI_RVALID)
			r_partial_in_valid <= 1;
		else if ((!r_write_fifo || !fifo_full) && clear_read_pipeline)
			// If we have to flush the final partial valid signal,
			// the do it when writing to the FIFO with clear_read
			// pipelin set.  Actually, this is one clock before
			// that ...
			r_partial_in_valid <= 0;

		always @(posedge i_clk)
		if (fifo_reset || (inbyte_shift == 0))
			r_partial_inword <= 0;
		else if (M_AXI_RVALID)
			r_partial_inword <= M_AXI_RDATA >> inshift_down;

		initial	r_write_fifo = 0;
		always @(posedge i_clk)
		if (fifo_reset)
			r_write_fifo <= 0;
		else if (M_AXI_RVALID || clear_read_pipeline)
			r_write_fifo <= r_partial_in_valid;
		else if (!fifo_full)
			r_write_fifo <= 0;

		always @(posedge i_clk)
		if (fifo_reset)
			r_realigned_incoming <= 0;
		else if (M_AXI_RVALID)
			r_realigned_incoming <= r_partial_inword
					| (M_AXI_RDATA << inshift_up);
		else if (!r_write_fifo || !fifo_full)
			r_realigned_incoming <= r_partial_inword;

		sfifo #(
			// {{{
			.BW(C_AXI_DATA_WIDTH),
			.LGFLEN(LGFIFO),
			.OPT_ASYNC_READ(1'b1)
			// }}}
		) middata(
			// {{{
			i_clk, fifo_reset,
				r_write_fifo, r_realigned_incoming,
					fifo_full, fifo_fill,
				r_read_fifo, fifo_data, fifo_empty
			// }}}
		);

		always @(posedge i_clk)
		if (!r_busy)
		begin
			outbyte_shift <= r_dst_addr[ADDRLSB-1:0];
			outshift_down <= 0;
			outshift_down[3 +: ADDRLSB] <= -r_dst_addr[ADDRLSB-1:0];
		end

		always @(*)
			outshift_up   = {  outbyte_shift, 3'b000 };


		always @(posedge i_clk)
		if (fifo_reset)
			r_partial_outword <= 0;
		else if (r_read_fifo && outshift_up != 0)
			r_partial_outword
				<= (fifo_data >> outshift_down);
		else if (M_AXI_WVALID && M_AXI_WREADY)
			r_partial_outword <= 0;

		always @(posedge i_clk)
		if (fifo_reset)
			r_partial_outvalid <= 0;
		else if (r_read_fifo && !fifo_empty)
			r_partial_outvalid <= 1;
		else if (fifo_empty && M_AXI_WVALID && M_AXI_WREADY)
			r_partial_outvalid <= extra_realignment_write;

		always @(posedge i_clk)
		if (fifo_reset)
			r_outword <= 0;
		else if (!r_partial_outvalid || (M_AXI_WVALID && M_AXI_WREADY))
		begin
			if (!fifo_empty)
				r_outword <= r_partial_outword |
					(fifo_data << outshift_up);
			else
				r_outword <= r_partial_outword;
		end

		always @(*)
			M_AXI_WDATA = r_outword;

		always @(*)
		begin
			r_read_fifo = 0;
			if (!r_partial_outvalid)
				r_read_fifo = 1;
			if (M_AXI_WVALID && M_AXI_WREADY)
				r_read_fifo = 1;

			if (fifo_empty)
				r_read_fifo = 0;
		end

		////////////////////////////////////////////////////////////////
		//
		// Write strobe logic for the unaligned case
		//
		////////////////////////////////////////////////////////////////
		//
		//

		always @(posedge i_clk)
		if (!r_busy)
		begin
			if (r_len[(LGLEN-1):(ADDRLSB+1)] != 0)
				r_oneword <= 0;
			else
				r_oneword <= (({ 2'b0, r_dst_addr[ADDRLSB-1:0]}
					+ r_len[ADDRLSB+1:0]) <=
					{ 2'b01, {(ADDRLSB){1'b0}} } ? 1:0);
		end

		initial	r_first_wstrb = 0;
		always @(posedge i_clk)
		if (!r_busy)
		begin
			if (r_len[LGLEN-1:ADDRLSB] != 0)
				r_first_wstrb <= -1 << r_dst_addr[ADDRLSB-1:0];
			else
				r_first_wstrb <= ((1<<r_len[ADDRLSB-1:0]) -1) << r_dst_addr[ADDRLSB-1:0];
		end

		always @(*)
			r_last_write_addr = r_dst_addr[ADDRLSB-1:0] + r_len[ADDRLSB-1:0];

		always @(posedge i_clk)
		if (!r_busy)
		begin
			if (r_last_write_addr[ADDRLSB-1:0] == 0)
				r_last_wstrb <= -1;
			else
				r_last_wstrb <= (1<<r_last_write_addr)-1;
		end

		always @(posedge i_clk)
		if (!r_busy)
			r_firstword <= 1;
		else if (M_AXI_WVALID && M_AXI_WREADY)
			r_firstword <= 0;

		always @(posedge i_clk)
		if (!M_AXI_WVALID || M_AXI_WREADY)
		begin
			if (r_oneword)
				M_AXI_WSTRB <= r_first_wstrb & r_last_wstrb;
			else if (M_AXI_WVALID && M_AXI_WREADY)
			begin
				if (write_beats_remaining > 2)
					M_AXI_WSTRB <= -1;
				else
					M_AXI_WSTRB <= r_last_wstrb;
			end else if (r_firstword)
				M_AXI_WSTRB <= r_first_wstrb;

			if (r_err || r_abort)
				M_AXI_WSTRB <= 0;
		end
		// }}}
	end else begin : ALIGNED_FIFO
		// {{{
		always @(*)
		begin
			r_first_wstrb = -1;
			r_last_wstrb = -1;
			r_partial_in_valid = 1;
			r_partial_outvalid = !fifo_empty;

			r_write_fifo = M_AXI_RVALID;
			r_read_fifo = M_AXI_WVALID && M_AXI_WREADY;

			clear_read_pipeline = 1'b0;
		end

		sfifo #(
			// {{{
			.BW(C_AXI_DATA_WIDTH),
			.LGFLEN(LGFIFO),
			.OPT_ASYNC_READ(1'b1)
			// }}}
		) middata(
			// {{{
			i_clk, fifo_reset,
				r_write_fifo, M_AXI_RDATA, fifo_full, fifo_fill,
				r_read_fifo,  M_AXI_WDATA, fifo_empty
			// }}}
		);


		initial	M_AXI_WSTRB = -1;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN || !r_busy)
			M_AXI_WSTRB <= -1;
		else if (!M_AXI_WVALID || M_AXI_WREADY)
			M_AXI_WSTRB <= (r_err || r_abort) ? 0 : -1;

		always @(*)
			extra_realignment_read <= 0;
		// }}}
	end endgenerate

	// fifo_space_available
	// {{{
	always @(posedge i_clk)
	if (fifo_reset)
		fifo_space_available <= (1<<LGFIFO)
		// space for r_partial_outvalid
		+ (OPT_UNALIGNED ? 1:0)
		// space for r_partial_in_valid
		+ (OPT_UNALIGNED && (r_src_addr[ADDRLSB-1:0] != 0) ? 1:0);
	else case({ phantom_read, M_AXI_WVALID && M_AXI_WREADY })
	// Verilator lint_off WIDTH
	2'b10: fifo_space_available <= fifo_space_available - (M_AXI_ARLEN+1);
	2'b01: fifo_space_available <= fifo_space_available + 1;
	2'b11: fifo_space_available <= fifo_space_available - M_AXI_ARLEN;
	// Verilator lint_on  WIDTH
	default: begin end
	endcase
	// }}}

	// write_realignment
	// {{{
	always @(*)
	if (OPT_UNALIGNED)
	begin
		// Verilator lint_off WIDTH
		// write_remaining
		write_realignment[ADDRLSB+1:0]
			= r_len[ADDRLSB-1:0]+r_dst_addr[ADDRLSB-1:0]
				+ (1<<ADDRLSB)-1;

		// Raw length
		write_realignment[2*ADDRLSB+2:ADDRLSB+2]
			= r_len[ADDRLSB-1:0] + (1<<ADDRLSB)-1;
		// Verilator lint_on  WIDTH
	end else
		write_realignment = 0;
	// }}}

	// extra_realignment_write
	// {{{
	always @(posedge i_clk)
	if (!OPT_UNALIGNED)
		extra_realignment_write <= 1'b0;
	else if (!r_busy)
	begin
		if ({ 1'b0, write_realignment[2*ADDRLSB+2] }
			!= write_realignment[ADDRLSB+1:ADDRLSB])
			extra_realignment_write <= 1'b1;
		else
			extra_realignment_write <= 1'b0;
	end else if (M_AXI_WVALID && M_AXI_WREADY && fifo_empty)
		extra_realignment_write <= 1'b0;
	// }}}

	// last_read_beat
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
		last_read_beat <= 1'b0;
	else
		last_read_beat <= M_AXI_RVALID && M_AXI_RREADY
				&& (read_beats_remaining_w == 1);
	// }}}

	// next_fifo_data_available
	// {{{
	always @(*)
	begin
		next_fifo_data_available = fifo_data_available;
		// Verilator lint_off WIDTH
		if (phantom_write)
			next_fifo_data_available = next_fifo_data_available
				- (M_AXI_AWLEN + (r_write_fifo && !fifo_full ? 0:1));
		else if (r_write_fifo && !fifo_full)
			next_fifo_data_available = next_fifo_data_available + 1;

		if (extra_realignment_write && last_read_beat)
			next_fifo_data_available = next_fifo_data_available + 1;
		// Verilator lint_on  WIDTH
	end
	// }}}

	// fifo_data_available
	// {{{
	initial	fifo_data_available = 0;
	always @(posedge i_clk)
	if (!r_busy || r_done)
		fifo_data_available <= 0;
	else
		fifo_data_available <= next_fifo_data_available;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI write processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write data from the FIFO to the AXI bus
	//

	// write_address
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
		write_address <= { 1'b0, r_dst_addr };
	else if (phantom_write)
	begin
		// Verilator lint_off WIDTH
		write_address <= write_address + ((M_AXI_AWLEN+1)<< M_AXI_AWSIZE);
		// Verilator lint_on WIDTH
		write_address[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// writes_remaining_w, multiple_write_bursts_remaining
	// {{{
	// Verilator lint_off WIDTH
	always @(*)
		w_writes_remaining_w = writes_remaining_w - (M_AXI_AWLEN+1);

	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		writes_remaining_w <= writelen_b[LGLEN:ADDRLSB];
		multiple_write_bursts_remaining <= |writelen_b[LGLEN:(ADDRLSB+LGMAXBURST)];
	end else if (phantom_write)
	begin
		writes_remaining_w <= w_writes_remaining_w;
		multiple_write_bursts_remaining
			<= |w_writes_remaining_w[LGLENW:LGMAXBURST];
	end
	// Verilator lint_on WIDTH
	// }}}

	// write_beats_remaining
	// {{{
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		write_beats_remaining <= writelen_b[LGLEN:ADDRLSB];
	end else if (M_AXI_WVALID && M_AXI_WREADY)
		write_beats_remaining <= write_beats_remaining - 1;
	// }}}

	// write_requests_remaining
	// {{{
	// Verilator lint_off WIDTH
	initial	write_requests_remaining = 0;
	always @(posedge i_clk)
	if (i_reset)
		write_requests_remaining <= 1'b0;
	else if (!r_busy)
		write_requests_remaining <= w_start;
	else if (phantom_write)
		write_requests_remaining <= (writes_remaining_w != (M_AXI_AWLEN+1));
	// Verilator lint_on WIDTH
	// }}}

	// write_bursts_outstanding
	// {{{
	initial	write_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		write_bursts_outstanding <= 0;
	end else case({phantom_write, M_AXI_BVALID && M_AXI_BREADY })
	2'b01: write_bursts_outstanding <= write_bursts_outstanding - 1;
	2'b10: write_bursts_outstanding <= write_bursts_outstanding + 1;
	default: begin end
	endcase
	// }}}

	// last_write_ack
	// {{{
	// Verilator lint_off  WIDTH
	always @(posedge i_clk)
	if (!r_busy)
		last_write_ack <= 0;
	else if (writes_remaining_w > ((phantom_write) ? (M_AXI_AWLEN+1) : 0))
		last_write_ack <= 0;
	else
		last_write_ack <= (write_bursts_outstanding
			== (phantom_write ? 0:1) + (M_AXI_BVALID ? 1:0));
	// Verilator lint_on  WIDTH
	// }}}

	// r_done
	// {{{
	always @(posedge i_clk)
	if (!r_busy || M_AXI_ARVALID || M_AXI_AWVALID)
		r_done <= 0;
	else if (read_bursts_outstanding > 0)
		r_done <= 0;
	else if (write_bursts_outstanding > (M_AXI_BVALID ? 1:0))
		r_done <= 0;
	else if (r_abort || r_err)
		r_done <= 1;
	else if (writes_remaining_w > 0)
		r_done <= 0;
	else
		r_done <= 1;
	// }}}

	// writelen_b
	// {{{
	always @(*)
	if (OPT_UNALIGNED)
		writelen_b = { 1'b0, r_len } + { {(LGLEN+1-ADDRLSB){1'b0}},
					r_dst_addr[ADDRLSB-1:0] }
			+ { {(LGLEN+1-ADDRLSB){1'b0}}, {(ADDRLSB){1'b1}} };
			// was + (1<<ADDRLSB)-1;
	else begin
		writelen_b = { 1'b0, r_len };
		writelen_b[ADDRLSB-1:0] = 0;
	end
	// }}}

	// initial_write_distance_to_boundary_w
	// {{{
	always @(*)
	begin
		initial_write_distance_to_boundary_w
			= - { 1'b0, write_address[ADDRLSB +: LGMAXBURST] };
		initial_write_distance_to_boundary_w[LGMAXBURST] = 1'b0;
	end
	// }}}

	// first_write_burst, first_write_len_w
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
	begin
		first_write_burst <= 1'b1;
		if (|writelen_b[LGLEN:ADDRLSB+LGMAXBURST])
			first_write_len_w <= MAXBURST;
		else
			first_write_len_w <= { 1'b0,
				writelen_b[ADDRLSB +: LGMAXBURST] };
	end else begin
		if (phantom_write)
			first_write_burst <= 1'b0;

		if (first_write_burst
			&& write_address[ADDRLSB +: LGMAXBURST] != 0
			&& first_write_len_w
				> initial_write_distance_to_boundary_w)
			first_write_len_w<=initial_write_distance_to_boundary_w;
	end
	// }}}

	// write_burst_length
	// {{{
	// Verilator lint_off WIDTH
	always @(*)
	if (first_write_burst)
		write_burst_length = first_write_len_w;
	else begin
		write_burst_length = MAXBURST;

		if (!multiple_write_bursts_remaining
			&& (write_burst_length[ADDRLSB +: LGMAXBURST]
				> writes_remaining_w[ADDRLSB +: LGMAXBURST]))
			write_burst_length = writes_remaining_w;
	end
	// Verilator lint_on WIDTH
	// }}}

	// write_count
	// {{{
	initial	write_count = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		write_count <= 0;
	else if (w_write_start)
	begin
		write_count <= 0;
		write_count[LGMAXBURST:0] <= write_burst_length[LGMAXBURST:0];
	end else if (M_AXI_WVALID && M_AXI_WREADY)
		write_count <= write_count - 1;
	// }}}

	// M_AXI_WLAST
	// {{{
	initial	M_AXI_WLAST = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
	begin
		M_AXI_WLAST <= 0;
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		M_AXI_WLAST <= 1;
		if (write_count > 2)
			M_AXI_WLAST <= 0;
		if (w_write_start)
`ifdef	AXI3
			M_AXI_WLAST <= (write_burst_length[3:0] == 1);
`else
			M_AXI_WLAST <= (write_burst_length[7:0] == 1);
`endif
	end
	// }}}

	// w_write_start
	// {{{
	always @(*)
		last_write_burst = (write_burst_length == writes_remaining_w);

	always @(*)
	begin
		// Verilator lint_off WIDTH
		if (!last_write_burst && OPT_UNALIGNED)
			w_write_start = (fifo_data_available > 1)
				&&(fifo_data_available > write_burst_length);
		else
			w_write_start = (fifo_data_available >= write_burst_length);
		// Verilator lint_on WIDTH
		if (!write_requests_remaining)
			w_write_start = 0;
		if (!OPT_WRAPMEM && write_address[C_AXI_ADDR_WIDTH])
			w_write_start = 0;
		if (phantom_write)
			w_write_start = 0;
		if (M_AXI_AWVALID && !M_AXI_AWREADY)
			w_write_start = 0;
		if (M_AXI_WVALID && (!M_AXI_WLAST || !M_AXI_WREADY))
			w_write_start = 0;
		if (i_reset || r_err || r_abort || !r_busy)
			w_write_start = 0;
	end
	// }}}

	// M_AXI_AWVALID, phantom_write
	// {{{
	initial	M_AXI_AWVALID = 0;
	initial	phantom_write = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		M_AXI_AWVALID <= 0;
		phantom_write <= 0;
	end else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		M_AXI_AWVALID <= w_write_start;
		phantom_write <= w_write_start;
	end else
		phantom_write <= 0;
	// }}}

	// M_AXI_WVALID
	// {{{
	initial	M_AXI_WVALID = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		M_AXI_WVALID <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		M_AXI_WVALID <= 0;
		if (M_AXI_WVALID && !M_AXI_WLAST)
			M_AXI_WVALID <= 1;
		if (w_write_start)
			M_AXI_WVALID <= 1;
	end
	// }}}

	// M_AXI_AWLEN
	// {{{
	initial	M_AXI_AWLEN = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		M_AXI_AWLEN <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		M_AXI_AWLEN <= 0;
		if (w_write_start)
`ifdef	AXI3
			M_AXI_AWLEN <= write_burst_length[3:0]-1;
`else
			M_AXI_AWLEN <= write_burst_length[7:0]-1;
`endif
	end
	// }}}

	// M_AXI_AWADDR
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
		M_AXI_AWADDR <= r_dst_addr;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		M_AXI_AWADDR <= write_address[C_AXI_ADDR_WIDTH-1:0];
	// }}}

	always @(*)
	begin
		M_AXI_AWID    = AXI_WRITE_ID;
		M_AXI_AWBURST = AXI_INCR;
		M_AXI_AWSIZE  = ADDRLSB[2:0];
		M_AXI_AWLOCK  = 1'b0;
		M_AXI_AWCACHE = 4'b0011;
		M_AXI_AWPROT  = r_prot;
		M_AXI_AWQOS   = r_qos;
		//
`ifdef	AXI3
		M_AXI_WID     = AXI_WRITE_ID;
`endif
		M_AXI_BREADY = !r_done;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Clock gating
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_CLKGATE)
	begin : CLK_GATING
		// {{{
		reg	r_clk_active;
		reg	gaten /* verilator clock_enable */;

		// clk_active
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_clk_active <= 1'b1;
		else begin
			r_clk_active <= 1'b0;

			if (r_busy)
				r_clk_active <= 1'b1;
			if (awskd_valid || wskd_valid || arskd_valid)
				r_clk_active <= 1'b1;
			if (S_AXIL_BVALID || S_AXIL_RVALID)
				r_clk_active <= 1'b1;
		end

		assign	clk_active = r_clk_active;
		// }}}
		// Gate the clock here locally
		// {{{
		always @(negedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			gaten <= 1'b1;
		else
			gaten <= r_clk_active;

		assign	gated_clk = S_AXI_ACLK && gaten;

		assign	clk_active = r_clk_active;
		// }}}
		// }}}
	end else begin : NO_CLK_GATING
		// {{{
		// Always active
		assign	clk_active = 1'b1;
		assign	gated_clk = S_AXI_ACLK;
		// }}}
	end endgenerate
	// }}}
	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	// Verilator coverage_off
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_BID,
			M_AXI_RID, M_AXI_BRESP[0], M_AXI_RRESP[0],
			S_AXIL_AWADDR[AXILLSB-1:0], S_AXIL_ARADDR[AXILLSB-1:0],
			fifo_full, fifo_fill, fifo_empty,
`ifdef	AXI3
			readlen_w[LGLENW:4],
`else
			readlen_w[LGLENW:8],
`endif
			writelen_b[ADDRLSB-1:0], readlen_b[ADDRLSB-1:0],
			read_distance_to_boundary_b
			};

	generate if (C_AXI_ADDR_WIDTH < 2*C_AXIL_DATA_WIDTH)
	begin : NEW_UNUSED
		wire	genunused;

		assign genunused = &{ 1'b0,
			new_widesrc[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH],
			new_widedst[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH] };
	end endgenerate

	// Verilator coverage_on
	// Verilator lint_on UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// The following formal properties are only a subset of those used
	// to verify the full core.  Do not be surprised to find syntax errors
	// here, or registers that are not defined.  These are correct in the
	// full version.
	//
	////////////////////////////////////////////////////////////////////////
	//
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	//
	// ...
	//

	reg	[C_AXI_ADDR_WIDTH:0]	f_next_wraddr, f_next_rdaddr;

	reg	[C_AXI_ADDR_WIDTH:0]	f_src_addr, f_dst_addr,
				f_read_address, f_write_address,
				f_read_check_addr, f_write_beat_addr,
				f_read_beat_addr;
	reg	[LGLEN:0]	f_length, f_rdlength, f_wrlength,
				f_writes_complete, f_reads_complete;



	////////////////////////////////////////////////////////////////////////
	//
	// The control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxil_slave #(
		.C_AXI_DATA_WIDTH(C_AXIL_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXIL_ADDR_WIDTH)
		//
		// ...
		//
		)
	faxil(
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXIL_AWVALID),
		.i_axi_awready(S_AXIL_AWREADY),
		.i_axi_awaddr(S_AXIL_AWADDR),
		.i_axi_awprot(S_AXIL_AWPROT),
		//
		.i_axi_wvalid(S_AXIL_WVALID),
		.i_axi_wready(S_AXIL_WREADY),
		.i_axi_wdata( S_AXIL_WDATA),
		.i_axi_wstrb( S_AXIL_WSTRB),
		//
		.i_axi_bvalid(S_AXIL_BVALID),
		.i_axi_bready(S_AXIL_BREADY),
		.i_axi_bresp( S_AXIL_BRESP),
		//
		.i_axi_arvalid(S_AXIL_ARVALID),
		.i_axi_arready(S_AXIL_ARREADY),
		.i_axi_araddr( S_AXIL_ARADDR),
		.i_axi_arprot( S_AXIL_ARPROT),
		//
		.i_axi_rvalid(S_AXIL_RVALID),
		.i_axi_rready(S_AXIL_RREADY),
		.i_axi_rdata( S_AXIL_RDATA),
		.i_axi_rresp( S_AXIL_RRESP)
		//
		// ...
		//
		);

	//
	// ...
	//

	//
	// Verify the AXI-lite result registers
	//
	always @(*)
	if (!r_busy)
		assert((r_done && (r_err || r_abort))
				|| (zero_len == (r_len == 0)));
	else
		assert(zero_len == (r_len == 0 && writes_remaining_w == 0));

	always @(*)
	if (!i_reset && !OPT_UNALIGNED)
		assert(r_src_addr[ADDRLSB-1:0] == 0);

	always @(*)
	if (!i_reset && !OPT_UNALIGNED)
		assert(r_dst_addr[ADDRLSB-1:0] == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The main AXI data interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxi_master #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_MAXBURST(MAXBURST)
		//
		// ...
		//
		)
	faxi(
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(M_AXI_AWVALID),
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awid(   M_AXI_AWID),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awlen(  M_AXI_AWLEN),
		.i_axi_awsize( M_AXI_AWSIZE),
		.i_axi_awburst(M_AXI_AWBURST),
		.i_axi_awlock( M_AXI_AWLOCK),
		.i_axi_awcache(M_AXI_AWCACHE),
		.i_axi_awprot( M_AXI_AWPROT),
		.i_axi_awqos(  M_AXI_AWQOS),
		//
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		//
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(   M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		//
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_arid(   M_AXI_ARID),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arlen(  M_AXI_ARLEN),
		.i_axi_arsize( M_AXI_ARSIZE),
		.i_axi_arburst(M_AXI_ARBURST),
		.i_axi_arlock( M_AXI_ARLOCK),
		.i_axi_arcache(M_AXI_ARCACHE),
		.i_axi_arprot( M_AXI_ARPROT),
		.i_axi_arqos(  M_AXI_ARQOS),
		//
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rid(   M_AXI_RID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rlast( M_AXI_RLAST),
		.i_axi_rresp( M_AXI_RRESP)
		//
		// ...
		//
		);

	always @(*)
	begin
		//
		// ...
		//
		if (r_done)
		begin
			//
			// ...
			//
			assert(!M_AXI_AWVALID);
			assert(!M_AXI_WVALID);
			assert(!M_AXI_ARVALID);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal assertions (Induction)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (w_start)
	begin
		f_src_addr <= { 1'b0, r_src_addr };
		f_dst_addr <= { 1'b0, r_dst_addr };
		f_length   <= r_len;
	end else if (r_busy)
	begin
		assert(f_length != 0);
		assert(f_length[LGLEN] == 0);

		assert(f_src_addr[C_AXI_ADDR_WIDTH] == 1'b0);
		assert(f_dst_addr[C_AXI_ADDR_WIDTH] == 1'b0);
	end

	always @(*)
	begin
		f_rdlength = f_length + f_src_addr[ADDRLSB-1:0]
				+ (1<<ADDRLSB)-1;
		f_rdlength[ADDRLSB-1:0] = 0;

		f_wrlength = f_length + f_dst_addr[ADDRLSB-1:0]
				+ (1<<ADDRLSB)-1;
		f_wrlength[ADDRLSB-1:0] = 0;

		f_raw_length = f_length + (1<<ADDRLSB)-1;
		f_raw_length[ADDRLSB-1:0] = 0;

		// One past the last address we'll actually read
		f_last_src_addr = f_src_addr + f_length + (1<<ADDRLSB)-1;
		f_last_src_addr[ADDRLSB-1:0] = 0;
		f_last_src_beat = f_src_addr + f_length -1;
		f_last_src_beat[ADDRLSB-1:0] = 0;

		f_last_dst_addr = f_dst_addr + f_length + (1<<ADDRLSB)-1;
		f_last_dst_addr[ADDRLSB-1:0] = 0;

		f_rd_arfirst = ({ 1'b0, M_AXI_ARADDR } == f_src_addr);
		f_rd_arlast  = (M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			+ (M_AXI_ARLEN+1)
			== f_last_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]);
		f_rd_ckfirst = (faxi_rd_ckaddr == f_src_addr);
		f_rd_cklast  = (faxi_rd_ckaddr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				+ faxi_rd_cklen == f_last_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]);

		// f_extra_realignment_read
		// true if we need to write a partial word to the FIFO/buffer
		// *after* all of our reads are complete.  This is a final
		// flush sort of thing.
		if (OPT_UNALIGNED && f_src_addr[ADDRLSB-1:0] != 0)
		begin
			// In general, if we are 1) unaligned, and 2) the
			// length is greater than a word, and 3) there's a
			// fraction of a word remaining, then we need to flush
			// a last word into the FIFO.
			f_extra_realignment_read
				= (((1<<ADDRLSB)-f_src_addr[ADDRLSB-1:0])
					>= f_length[ADDRLSB-1:0]) ? 1:0;
			if (f_length[ADDRLSB-1:0] == 0)
				f_extra_realignment_read = 0;
		end else
			f_extra_realignment_read = 1'b0;

		//
		// f_extra_realignment_preread
		// will be true anytime we need to read a first word before
		// writing anything to the buffer.
		if (OPT_UNALIGNED && f_src_addr[ADDRLSB-1:0] != 0)
			f_extra_realignment_preread = 1'b1;
		else
			f_extra_realignment_preread = 1'b0;

		//
		// f_extra_realignment_write
		// true if following the last read from the FIFO there's a
		// partial word that will need to be flushed through the
		// system.
		if (OPT_UNALIGNED && f_raw_length[LGLEN:ADDRLSB]
						!= f_wrlength[LGLEN:ADDRLSB])
			f_extra_realignment_write = 1'b1;
		else
			f_extra_realignment_write = 1'b0;

		f_extra_write_in_fifo = (f_extra_realignment_write)
			&& (read_beats_remaining_w == 0)&&(!last_read_beat);
	end

	always @(*)
	if (r_busy && !OPT_UNALIGNED)
	begin
		assert(f_src_addr[ADDRLSB-1:0] == 0);
		assert(f_dst_addr[ADDRLSB-1:0] == 0);
		assert(f_length[ADDRLSB-1:0] == 0);
	end

	always @(*)
	if (r_busy)
	begin
		if (!f_extra_realignment_write)
			assert(!extra_realignment_write);
		else if (f_writes_complete >= f_wrlength[LGLEN:ADDRLSB]-1)
			assert(!extra_realignment_write);
		else
			assert(extra_realignment_write);

		if ((f_writes_complete > 0 || M_AXI_WVALID)
					&& extra_realignment_write)
			assert(r_partial_outvalid);
	end

	always @(*)
	if (r_busy)
	begin
		if (extra_realignment_read)
			assert(f_extra_realignment_read);
		else if (read_beats_remaining_w > 0)
		assert(f_extra_realignment_read == extra_realignment_read);
	end

	//
	// ...
	//

	always @(*)
	if (fifo_full)
		assert(no_read_bursts_outstanding);

	always @(*)
	if (r_busy)
		assert(!r_int);

	////////////////////////////////////////////////////////////////////////
	//
	// Write checks
	//

	//
	// ...
	//

	always @(*)
	begin
		f_write_address = 0;
		f_write_address[C_AXI_ADDR_WIDTH:ADDRLSB]
		= f_dst_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
			+ (f_wrlength[LGLEN:ADDRLSB] - writes_remaining_w);
	end

	always @(*)
	begin
		f_next_wraddr = { 1'b0, M_AXI_AWADDR }
					+ ((M_AXI_AWLEN+1)<<M_AXI_AWSIZE);
		f_next_wraddr[ADDRLSB-1:0] = 0;
	end

	always @(*)
	if (M_AXI_AWVALID)
	begin
		assert(M_AXI_WVALID);
		assert(M_AXI_AWLEN < (1<<LGMAXBURST));

		if (M_AXI_AWLEN != (1<<LGMAXBURST)-1)
		begin
			assert((M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				== f_dst_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB])
				||(phantom_write)
				||(writes_remaining_w == 0));
		end else begin
			assert(M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			== f_write_beat_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]);
		end

		if (M_AXI_AWADDR[ADDRLSB-1:0] != 0)
			assert({ 1'b0, M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:0] }
					== f_dst_addr);
		else if (M_AXI_AWADDR != f_dst_addr)
			assert(M_AXI_AWADDR[0 +: LGMAXBURST+ADDRLSB] == 0);
	end

	always @(*)
	if (!OPT_UNALIGNED)
	begin
		assert(r_len[ADDRLSB-1:0] == 0);
		assert(r_src_addr[ADDRLSB-1:0] == 0);
		assert(r_dst_addr[ADDRLSB-1:0] == 0);
	end

	always @(*)
	if (r_busy)
	begin
		assert(writes_remaining_w  <= f_wrlength[LGLEN:ADDRLSB]);
		assert(f_writes_complete   <= f_wrlength[LGLEN:ADDRLSB]);
		assert(fifo_fill           <= f_wrlength[LGLEN:ADDRLSB]);

		assert(write_address[C_AXI_ADDR_WIDTH:ADDRLSB]
			== f_write_address[C_AXI_ADDR_WIDTH:ADDRLSB]);

		if (M_AXI_AWADDR != f_dst_addr && writes_remaining_w != 0)
			assert(M_AXI_AWADDR[LGMAXBURST+ADDRLSB-1:0] == 0);
		else if (!OPT_UNALIGNED)
			assert(M_AXI_AWADDR[ADDRLSB-1:0] == 0);

		if((writes_remaining_w!= f_wrlength[LGLEN:ADDRLSB])
			&&(writes_remaining_w != 0))
			assert(write_address[LGMAXBURST+ADDRLSB-1:0] == 0);

		if ((write_address[C_AXI_ADDR_WIDTH:ADDRLSB]
				!= f_dst_addr[C_AXI_ADDR_WIDTH:ADDRLSB])
			&&(writes_remaining_w > 0))
			assert(write_address[LGMAXBURST+ADDRLSB-1:0] == 0);

		if (writes_remaining_w != f_wrlength[LGLEN:ADDRLSB]
				&& writes_remaining_w != 0)
			assert((write_burst_length == (1<<LGMAXBURST))
				||(write_burst_length == writes_remaining_w));

		assert(write_requests_remaining == (writes_remaining_w != 0));
	end

	//
	// ...
	//

	always @(*)
	if (M_AXI_AWVALID && !phantom_write)
	begin
		assert(write_count == (M_AXI_AWLEN+1));
		//
		// ...
		//
	end

	always @(*)
	if (r_busy && last_write_ack)
	begin
		assert(reads_remaining_w == 0);
		assert(!M_AXI_ARVALID);
		assert(writes_remaining_w == 0);
	end

	always @(*)
	if (r_busy && !r_abort && !r_err)
		assert(write_address[C_AXI_ADDR_WIDTH:ADDRLSB]
				== f_dst_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
			|| (write_address[LGMAXBURST-1:0] == 0)
			|| (writes_remaining_w == 0));

	always @(*)
	if (phantom_write)
		assert(writes_remaining_w >= (M_AXI_AWLEN+1));
	else if (M_AXI_AWVALID)
		assert(write_address[C_AXI_ADDR_WIDTH-1:0]
					== f_next_wraddr[C_AXI_ADDR_WIDTH-1:0]);

	//
	// ...
	//

	always @(*)
	if (M_AXI_WVALID)
	begin
		if (OPT_UNALIGNED)
			assert(r_partial_outvalid);
		else
			assert(!fifo_empty || r_abort || r_err);
		//
		// ...
		//
	end

	always @(*)
	begin
		f_write_beat_addr = 0;
		f_write_beat_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
			= f_dst_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
			+ (f_wrlength[LGLEN:ADDRLSB]-write_beats_remaining);

		//
		// ...
		//
	end

	always @(*)
	if (r_busy)
	begin
		//
		// ...
		//

		if (write_beats_remaining == 0)
			assert(!M_AXI_WVALID);
	end

	always @(*)
	if (writes_remaining_w < f_wrlength[LGLEN:ADDRLSB])
	begin
		if (writes_remaining_w == 0)
			assert(fifo_data_available == 0);
		// else ...
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Read checks
	//
	always @(*)
	begin
		f_reads_complete = f_rdlength[LGLEN:ADDRLSB]
				- reads_remaining_w - // ...
		//
		// ...
		//
	end

	always @(*)
	begin
		if (reads_remaining_w == f_rdlength[LGLEN:ADDRLSB])
			f_read_address = f_src_addr;
		else begin
			f_read_address = 0;
			f_read_address[C_AXI_ADDR_WIDTH:ADDRLSB]
			= f_src_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				+ (f_rdlength[LGLEN:ADDRLSB] - reads_remaining_w);
		end

		f_araddr = f_read_address;
		if (M_AXI_ARVALID && !phantom_read)
			f_araddr[C_AXI_ADDR_WIDTH:ADDRLSB]
				= f_araddr[C_AXI_ADDR_WIDTH:ADDRLSB]
						- (M_AXI_ARLEN+1);
		if (f_araddr[C_AXI_ADDR_WIDTH:ADDRLSB]
					== f_src_addr[C_AXI_ADDR_WIDTH:ADDRLSB])
			f_araddr[ADDRLSB-1:0] = f_src_addr[ADDRLSB-1:0];

		//
		// Match the read check address to our source address
		//
		f_read_check_addr = 0;
		f_read_check_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			= f_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			+ f_reads_complete + // ...


		//
		// Match the RVALID address to our source address
		//
		f_read_beat_addr = 0;
		if (f_reads_complete == 0)
			f_read_beat_addr = f_src_addr;
		else
			f_read_beat_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				= f_src_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				+ f_reads_complete;

		f_end_of_read_burst = M_AXI_ARADDR;
		f_end_of_read_burst[ADDRLSB-1:0] = 0;
		f_end_of_read_burst[C_AXI_ADDR_WIDTH:ADDRLSB]
			= f_end_of_read_burst[C_AXI_ADDR_WIDTH:ADDRLSB]
			+ (M_AXI_ARLEN + 1);

		//
		// ...
		//
	end

	always @(*)
	begin
		f_next_rdaddr = { 1'b0, M_AXI_ARADDR } + ((M_AXI_ARLEN+1)<<M_AXI_ARSIZE);
		f_next_rdaddr[ADDRLSB-1:0] = 0;
	end

	/////////
	//
	// Constrain the read address
	//

	always @(*)
	if (r_busy)
	begin
		if (!f_rd_arfirst)
		begin
			assert(reads_remaining_w < f_rdlength[LGLEN:ADDRLSB]);

			// All bursts following the first one must be aligned
			if (M_AXI_ARVALID || reads_remaining_w > 0)
				assert(M_AXI_ARADDR[0 +: LGMAXBURST + ADDRLSB] == 0);
		end else if (phantom_read)
			assert(reads_remaining_w == f_rdlength[LGLEN:ADDRLSB]);
		else if (M_AXI_ARVALID)
			assert(reads_remaining_w == f_rdlength[LGLEN:ADDRLSB]
				- (M_AXI_ARLEN+1));

		// All but the first burst should be aligned
		if (!OPT_UNALIGNED || M_AXI_ARADDR != f_src_addr)
			assert(M_AXI_ARADDR[ADDRLSB-1:0] == 0);

		if (phantom_read)
			assert(M_AXI_ARADDR == read_address[C_AXI_ADDR_WIDTH-1:0]);
		else if (M_AXI_ARVALID)
			assert(read_address[C_AXI_ADDR_WIDTH-1:0] == f_next_rdaddr[C_AXI_ADDR_WIDTH-1:0]);
	end // else ...

	//
	// ...
	//

	// Constrain read_address--our pointer to the next bursts address
	always @(*)
	if (r_busy)
	begin
		assert((read_address == f_src_addr)
			|| (read_address[LGMAXBURST+ADDRLSB-1:0] == 0)
			|| (reads_remaining_w == 0));


		assert(read_address == f_read_address);
		if (!OPT_UNALIGNED)
			assert(read_address[ADDRLSB-1:0] == 0);

		if ((reads_remaining_w != f_rdlength[LGLEN:ADDRLSB])
			&&(reads_remaining_w > 0))
			assert(read_address[LGMAXBURST+ADDRLSB-1:0] == 0);

		if ((read_address[C_AXI_ADDR_WIDTH:ADDRLSB]
				!= f_src_addr[C_AXI_ADDR_WIDTH:ADDRLSB])
			&&(reads_remaining_w > 0))
			assert(read_address[LGMAXBURST+ADDRLSB-1:0] == 0);
	end


	/////////
	//
	// Constrain the read length
	//
	always @(*)
	if (M_AXI_ARVALID)
	begin
		assert(M_AXI_ARLEN < (1<<LGMAXBURST));
		if (M_AXI_ARLEN != (1<<LGMAXBURST)-1)
		begin
			assert((M_AXI_ARADDR == f_src_addr)
				||(phantom_read)
				||(reads_remaining_w == 0));
		end

		assert(f_end_of_read_burst_last[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB]
			== M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB]);
	end

	always @(*)
	if (M_AXI_ARVALID && reads_remaining_w > (M_AXI_ARLEN+1))
		assert(f_end_of_read_burst[ADDRLSB+LGMAXBURST-1:0]==0);


	/////////
	//
	// Constrain RLAST
	//

	always @(*)
	if (M_AXI_RVALID)
	begin
		if (M_AXI_RLAST)
		begin
			if (f_read_beat_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				!= f_last_src_beat[C_AXI_ADDR_WIDTH:ADDRLSB])
				assert(&f_read_beat_addr[ADDRLSB+LGMAXBURST-1:ADDRLSB]);
		end else
			assert(f_read_beat_addr[ADDRLSB+LGMAXBURST-1:ADDRLSB]
			!= {(LGMAXBURST){1'b1}});
	end

	always @(*)
	if (f_read_beat_addr == f_last_src_beat)
		assert(!M_AXI_RVALID || M_AXI_RLAST);
	else
		assert(!M_AXI_RVALID
			|| M_AXI_RLAST == (&f_read_beat_addr[LGMAXBURST+ADDRLSB-1:ADDRLSB]));


	/////////
	//
	//
	//


	always @(*)
		assert(no_read_bursts_outstanding == (read_bursts_outstanding == 0));

	always @(*)
	if (r_busy && !r_err)
		assert(f_read_beat_addr[C_AXI_ADDR_WIDTH-1:0] == r_src_addr);

	always @(*)
	if (r_busy)
	begin
		// Some quick checks to make sure the subsequent checks
		// don't overflow anything
		assert(reads_remaining_w   <= f_rdlength[LGLEN:ADDRLSB]);
		assert(f_reads_complete    <= f_rdlength[LGLEN:ADDRLSB]);
		// ...
		assert(fifo_fill           <= f_raw_length[LGLEN:ADDRLSB]);
		assert(fifo_space_available<= (1<<LGFIFO));
		assert(fifo_space_available<= (1<<LGFIFO) - fifo_fill);
		// ...


		if (reads_remaining_w != f_rdlength[LGLEN:ADDRLSB]
				&& reads_remaining_w != 0)
			assert((readlen_w == (1<<LGMAXBURST))
				||(readlen_w == reads_remaining_w));

		//
		// Read-length checks
		assert(readlen_w <= (1<<LGMAXBURST));
		if (reads_remaining_w > 0)
			assert(readlen_w != 0);
		if (readlen_w != (1<<LGMAXBURST))
			assert(reads_remaining_w == readlen_w
				||(read_address == f_src_addr));
	end

	//
	// ...
	//

	////////////////////////////////////////
	//
	// Errors or aborts -- do we properly end gracefully
	//
	// Make certain we don't deadlock here, but also that we wait
	// for the last burst return before we clear
	//

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && r_busy && $past(r_busy))
	begin
		// Not allowed to set r_done while anything remains outstanding
		if (!no_read_bursts_outstanding)
			assert(!r_done);
		if (write_bursts_outstanding > 0)
			assert(!r_done);

		//
		// If no returns are outstanding, and following an error, then
		// r_done should be set
		if ($past(r_busy && (r_err || r_abort))
		    &&($past(!M_AXI_ARVALID && read_bursts_outstanding==0))
		    &&($past(!M_AXI_AWVALID && write_bursts_outstanding==0)))
			assert(r_done);

		if ($past(r_err || r_abort))
		begin
			//
			// Just double check that we aren't starting anything
			// new following either an abort or an error
			//
			assert(!$rose(M_AXI_ARVALID));
			assert(!$rose(M_AXI_AWVALID));

			if ($past(!M_AXI_WVALID || M_AXI_WREADY))
				assert(M_AXI_WSTRB == 0);
		end
	end

	//
	// ...
	//

	////////////////////////////////////////

	//
	// ...
	//

	always @(*)
	if (r_busy)
	begin
		if (readlen_w == 0)
			assert(reads_remaining_w == 0);
		else begin
			assert(reads_remaining_w > 0);
			if (!w_start_read)
			begin
				assert(readlen_w <= reads_remaining_w);
				assert(readlen_w <= (1<<LGMAXBURST));
			end
		end
	end

	always @(*)
	if (M_AXI_BVALID)
		assert(M_AXI_BREADY);

	always @(*)
	if (M_AXI_RVALID)
		assert(M_AXI_RREADY);

	generate if (OPT_UNALIGNED)
	begin : REALIGNMENT_CHECKS

		//
		// ...
		//

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checks
	//

	//
	// ...
	//

	always @(*)
	if (phantom_read)
		assert(M_AXI_ARVALID);

	always @(*)
	if (phantom_write)
		assert(M_AXI_AWVALID);

	////////////////////////////////////////////////////////////////////////
	//
	// Combined
	//

	always @(*)
	if (r_busy)
	begin
		//
		// ...
		//

		assert(writes_remaining_w + write_bursts_outstanding
			<= f_wrlength[LGLEN:ADDRLSB]);

		//
		// ...
		//
		if (write_count > 0)
			assert(M_AXI_WVALID);
		//
		// ...
		//
	end

	always @(*)
	if (r_busy)
		assert(last_write_ack == ((write_bursts_outstanding <= 1)
			&&(writes_remaining_w == 0)));

	////////////////////////////////////////////////////////////////////////
	//
	// Initial (only) constraints
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assert(!S_AXIL_BVALID);
		assert(!S_AXIL_RVALID);

		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(!M_AXI_ARVALID);

		assert(write_bursts_outstanding == 0);
		assert(write_requests_remaining == 0);

		assert(!phantom_read);
		assert(!phantom_write);
		assert(!r_busy);
		assert(read_bursts_outstanding == 0);
		assert(no_read_bursts_outstanding);

		assert(r_len == 0);
		assert(zero_len);

		assert(write_count == 0);
		assert(!M_AXI_WLAST);
		assert(M_AXI_AWLEN == 0);
		assert(!r_write_fifo);
		assert(r_src_addr == 0);
		assert(r_dst_addr == 0);
	end

	always @(*)
		assert(ADDRLSB + LGMAXBURST <= 12);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract checking
	// {{{
	// Given an arbitrary address within the source address range, and an
	// arbitrary piece of data at that source address, prove that said
	// piece of data will get properly written to the destination address
	// range
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// We'll pick the byte read from const_addr_src, and then written to
	// const_addr_dst.
	//
	generate if (OPT_UNALIGNED)
	begin : F_UNALIGNED_SAMPLE_CHECK
		(* anyconst *) reg	[C_AXI_ADDR_WIDTH-1:0]	f_const_posn;
		reg	[C_AXI_ADDR_WIDTH:0]	f_const_addr_src,
						f_const_addr_dst;
		reg	[8-1:0]			f_const_byte;
		reg	[C_AXI_ADDR_WIDTH:0]	f_write_fifo_addr,
						f_read_fifo_addr,
						f_partial_out_addr;
		reg	[C_AXI_DATA_WIDTH-1:0]	f_shifted_read, f_shifted_write;
		reg	[C_AXI_DATA_WIDTH/8-1:0] f_shifted_wstrb;
		reg	[C_AXI_DATA_WIDTH-1:0]	f_shifted_to_fifo,
						f_shifted_partial_to_fifo,
						f_shifted_partial_from_fifo;
		reg	[C_AXI_DATA_WIDTH-1:0]	f_shifted_from_fifo,
						f_shifted_from_partial_out;
		reg	[ADDRLSB-1:0]		subshift;


		always @(*)
		begin
			assume(f_const_posn < f_length);

			f_const_addr_src = f_src_addr + f_const_posn;
			f_const_addr_dst = f_dst_addr + f_const_posn;

			f_shifted_read =(M_AXI_RDATA >> (8*f_const_addr_src[ADDRLSB-1:0]));
			f_shifted_write=(M_AXI_WDATA >> (8*f_const_addr_dst[ADDRLSB-1:0]));
			f_shifted_wstrb=(M_AXI_WSTRB >> (f_const_addr_dst[ADDRLSB-1:0]));
		end

		////////////////////////////////////////////////////////////////
		//
		// Step 1: Assume a known input
		//	Actually, we'll copy it when it comes in
		//
		always @(posedge S_AXI_ACLK)
		if (M_AXI_RVALID
			&& f_read_beat_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				== f_const_addr_src[C_AXI_ADDR_WIDTH:ADDRLSB])
		begin
			// Record our byte to be read
			f_const_byte <= f_shifted_read[7:0];
		end

		////////////////////////////////////////////////////////////////
		//
		// Step 2: Assert that value gets written on the way out
		//
		always @(*)
		if (M_AXI_WVALID
			&& f_write_beat_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				== f_const_addr_dst[C_AXI_ADDR_WIDTH:ADDRLSB])
		begin
			// Assert that we have the right byte in the end
			if (!r_err && !r_abort)
			begin
				// Although it only really matters if we are
				// actually writing it to the bus
				assert(f_shifted_wstrb[0]);
				assert(f_shifted_write[7:0] == f_const_byte);
			end else
				assert(f_shifted_wstrb[0] || M_AXI_WSTRB==0);
		end


		////////////////////////////////////////////////////////////////
		//
		// Assert the write side of the realignment FIFO
		//
		always @(*)
		begin
			//
			// ...
			//

			subshift = f_const_posn[ADDRLSB-1:0];
		end

		always @(*)
			f_shifted_to_fifo = REALIGNMENT_FIFO.r_realigned_incoming
				>> (8*subshift);

		always @(*)
			f_shifted_partial_to_fifo = REALIGNMENT_FIFO.r_partial_inword
				>> (8*subshift);

		//
		// ...
		//

		always @(*)
		if (S_AXI_ARESETN && r_write_fifo
			&& f_write_fifo_addr <= f_const_addr_src
			&& f_write_fifo_addr + (1<<ADDRLSB) > f_const_addr_src)
		begin
			// Assert that our special byte gets written to the FIFO
			assert(f_const_byte == f_shifted_to_fifo[7:0]);
		end

		////////////////////////////////////////////////////////////////
		//
		// Assert the read side of the realignment FIFO
		//
		always @(*)
		begin
			f_read_fifo_addr =f_dst_addr;
			f_read_fifo_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
				= f_dst_addr[C_AXI_ADDR_WIDTH:ADDRLSB]
					+ (r_partial_outvalid ? 1:0)
					+ f_writes_complete;

			f_partial_out_addr = f_read_fifo_addr;
			f_partial_out_addr[ADDRLSB-1:0] = 0;
		end

		always @(*)
			f_shifted_from_fifo = REALIGNMENT_FIFO.fifo_data
							>> (8*subshift);

		always @(*)
			f_shifted_from_partial_out
				= REALIGNMENT_FIFO.r_partial_outword
						>> (8*f_const_addr_dst[ADDRLSB-1:0]);


		always @(*)
		if (!fifo_empty && f_read_fifo_addr <= f_const_addr_dst
			&& f_read_fifo_addr + (1<<ADDRLSB) > f_const_addr_dst)
		begin
			// Assume that our special byte gets read from the FIFO
			// That way we don't have to verify every element of the
			// FIFO.  We'll instead rely upon the FIFO working from
			// here.
			assume(f_const_byte == f_shifted_from_fifo[7:0]);
		end

		//
		// ...
		//

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	f_cvr_rd_bursts, f_cvr_wr_bursts;
	reg		f_cvr_complete;

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		f_cvr_wr_bursts <= 0;
	else if (w_start)
		f_cvr_wr_bursts <= 0;
	else if (M_AXI_AWVALID && M_AXI_AWREADY && !f_cvr_wr_bursts[3])
		f_cvr_wr_bursts <= f_cvr_wr_bursts + 1;

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		f_cvr_rd_bursts <= 0;
	else if (w_start)
		f_cvr_rd_bursts <= 0;
	else if (M_AXI_ARVALID && M_AXI_ARREADY && !f_cvr_rd_bursts[3])
		f_cvr_rd_bursts <= f_cvr_rd_bursts + 1;

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy))
		cover(!r_busy && !r_err && !r_abort && f_cvr_wr_bursts[0]
			&& f_cvr_rd_bursts[0]);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy))
		cover(r_done && !r_err && !r_abort && f_cvr_wr_bursts[0]
			&& f_cvr_rd_bursts[0]);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy))
		cover(!r_busy && !r_err && !r_abort && &f_cvr_wr_bursts[1]
			&& f_cvr_rd_bursts[1]);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy))
		cover(!r_busy && !r_err && !r_abort && (&f_cvr_wr_bursts[1:0])
			&& (&f_cvr_rd_bursts[1:0]));

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy))
		cover(!r_busy && !r_err && !r_abort && f_cvr_wr_bursts[2]
			&& f_cvr_rd_bursts[2]);

	always @(*)
		cover(f_past_valid && S_AXI_ARESETN && r_busy && r_err);

	always @(*)
		cover(f_past_valid && S_AXI_ARESETN && r_busy
			&& M_AXI_RVALID && M_AXI_RRESP[1]);

	always @(*)
		cover(f_past_valid && S_AXI_ARESETN && r_busy
			&& M_AXI_RVALID && M_AXI_BRESP[1]);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy && r_err))
		cover(!r_busy && r_err);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy && r_abort))
		cover(!r_busy && r_abort);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && r_busy && !r_abort && !r_err)
		cover(reads_remaining_w == 0);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && r_busy && !r_abort && !r_err)
		cover(reads_remaining_w == 0 && fifo_empty);

	generate if (OPT_UNALIGNED)
	begin : COVER_MISALIGNED_COPYING

		reg	[2:0]	cvr_opt_checks;
		integer		ik;

		always @(*)
		begin
			cvr_opt_checks[0] = (f_src_addr[ADDRLSB-1:0] == 0);
			cvr_opt_checks[1] = (f_dst_addr[ADDRLSB-1:0] == 0);
			cvr_opt_checks[2] = (f_length[  ADDRLSB-1:0] == 0);
		end

		always @(posedge S_AXI_ACLK)
		if (f_past_valid && S_AXI_ARESETN && o_int)
		begin
			for(ik=0; ik<8; ik=ik+1)
			begin
				cover(cvr_opt_checks == ik[2:0]
					&& !r_busy && r_err && !r_abort
					&& f_cvr_wr_bursts[0]
					&& f_cvr_rd_bursts[0]);

				cover(cvr_opt_checks == ik[2:0]
					&& !r_busy && !r_err && r_abort
					&& f_cvr_wr_bursts[0]
					&& f_cvr_rd_bursts[0]);

				cover(cvr_opt_checks == ik[2:0]
					&& !r_busy && !r_err && !r_abort
					&& f_cvr_wr_bursts[0]
					&& f_cvr_rd_bursts[0]);

				cover(cvr_opt_checks == ik[2:0]
					&& !r_busy && !r_err && !r_abort
					&& f_cvr_wr_bursts[2]
					&& f_cvr_rd_bursts[2]);
			end
		end

		always @(posedge S_AXI_ACLK)
		if (f_past_valid && S_AXI_ARESETN && o_int)
		begin
			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& f_extra_realignment_read
				&& f_extra_realignment_write);

			//
			// Will never happen--since f_extra_realignment_read
			// can only be true if f_extra_realignment_preread
			// is also true
			//
			// cover(!r_busy && !r_err && !r_abort
				// && !f_extra_realignment_preread
				// && f_extra_realignment_read
				// && f_extra_realignment_write);

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& f_extra_realignment_write);

			cover(!r_busy && !r_err && !r_abort
				&& !f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& f_extra_realignment_write);

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& f_extra_realignment_read
				&& !f_extra_realignment_write);

			// !preread && read will never happen

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& !f_extra_realignment_write);

			cover(!r_busy && !r_err && !r_abort
				&& !f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& !f_extra_realignment_write);

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& f_extra_realignment_read
				&& f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);

			// !preread && read will never happen

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);

			cover(!r_busy && !r_err && !r_abort
				&& !f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& f_extra_realignment_read
				&& !f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);


			// !preread && read will never happen

			cover(!r_busy && !r_err && !r_abort
				&& f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& !f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);

			cover(!r_busy && !r_err && !r_abort
				&& !f_extra_realignment_preread
				&& !f_extra_realignment_read
				&& !f_extra_realignment_write
				&& f_length[LGLEN-1:ADDRLSB] > 2);
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions (i.e. constraints)
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// None (currently)
`endif
// }}}
endmodule
