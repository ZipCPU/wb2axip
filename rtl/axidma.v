////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axidma.v
//
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
//		1b	Interrupt Set
//		1b	Start
//	1. Source address
//		(Last value read address)
//	2. Destination address
//		(Next value to write address)
//	3. Length
//		(Total number minus successful writes)
//
// Performance goals:
//	100% throughput
//	Stay off the bus until you can drive it hard
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2020, Gisselquist Technology, LLC
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
// `define			AXI3
//
module	axidma #(
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		//
		// These two "parameters" really aren't things that can be
		// changed externally.
		localparam	C_AXIL_ADDR_WIDTH = 4,
		localparam	C_AXIL_DATA_WIDTH = 32,
		//
		// OPT_UNALIGNED turns on support for unaligned addresses,
		// whether source, destination, or length parameters.
		//
		// This support is not offered in this version of the core.
		localparam [0:0]	OPT_UNALIGNED = 1'b0,
		//
`ifdef	AXI3
		parameter	LGMAXBURST=4,	// 16 beats max
`else
		parameter	LGMAXBURST=8,	// 256 beats
`endif
		localparam	MAXBURST=(1<<LGMAXBURST),
		parameter	LGFIFO = LGMAXBURST+1,	// 512 element FIFO
		parameter	LGLEN = C_AXI_ADDR_WIDTH,
		//
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_READ_ID = 0,
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_WRITE_ID = 0,
		parameter	[7:0]			ABORT_KEY  = 8'h6d,
		//
		localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3,
		localparam	AXILLSB= $clog2(C_AXIL_DATA_WIDTH)-3,
		localparam	LGLENW= LGLEN-ADDRLSB
	) (
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// The AXI4-lite control interface
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
		output	reg	[1:0]			S_AXIL_BRESP,
		//
		input	wire				S_AXIL_ARVALID,
		output	wire				S_AXIL_ARREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_ARADDR,
		input	wire 	[2:0]			S_AXIL_ARPROT,
		//
		output	reg				S_AXIL_RVALID,
		input	wire				S_AXIL_RREADY,
		output	reg [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_RDATA,
		output	reg	[1:0]			S_AXIL_RRESP,
		//
		//
		// The AXI Master (DMA) interface
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
		output	reg	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	reg	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
`ifdef	AXI3
		output	reg	[3:0]			M_AXI_ARLEN,
`else
		output	reg	[7:0]			M_AXI_ARLEN,
`endif
		output	reg	[2:0]			M_AXI_ARSIZE,
		output	reg	[1:0]			M_AXI_ARBURST,
		output	reg				M_AXI_ARLOCK,
		output	reg	[3:0]			M_AXI_ARCACHE,
		output	reg	[2:0]			M_AXI_ARPROT,
		output	reg	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	reg				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP,
		//
		output	reg				o_int);

	localparam	[1:0]	CTRL_ADDR = 2'b00,
				SRC_ADDR = 2'b01,
				DST_ADDR = 2'b10,
				LEN_ADDR = 2'b11;
	localparam		CTRL_START_BIT = 0,
				CTRL_BUSY_BIT  = 0,
				CTRL_INT_BIT   = 1,
				CTRL_INTEN_BIT = 2,
				CTRL_ABORT_BIT = 3,
				CTRL_ERR_BIT   = 4;
	localparam	[1:0]	AXI_INCR = 2'b01, AXI_OKAY = 2'b00;

	wire	i_clk   = S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	reg	axil_write_ready, axil_read_ready;

	reg	r_busy, r_err, r_abort, w_start, r_int, r_int_enable,
				r_done, last_write_ack, zero_len;
	reg	[3:0]		r_qos;
	reg	[2:0]		r_prot;
	reg	[LGLEN-1:0]	r_len;	// Length of transfer in octets
	reg	[C_AXI_ADDR_WIDTH-1:0]	r_src_addr, r_dst_addr;

	reg			fifo_reset;
	wire	[LGFIFO:0]	fifo_fill;
	reg	[LGFIFO:0]	fifo_space_available;
	reg	[LGFIFO:0]	fifo_writes_available;
	wire			fifo_full, fifo_empty;
	reg	[8:0]		write_count;
	//
	reg				phantom_read, w_start_read,
					no_read_bursts_outstanding;
	reg	[LGLEN:0]		readlen_b;
	reg	[LGLENW:0]		readlen_w, initial_readlen_w;
	reg	[C_AXI_ADDR_WIDTH-1:0]	read_address;
	reg	[LGLENW:0]		reads_remaining_w,
					read_bursts_outstanding;
	reg	[C_AXI_ADDR_WIDTH-1:0]	read_distance_to_boundary_b;
	//
	reg				phantom_write, w_write_start;
	reg	[C_AXI_ADDR_WIDTH-1:0]	write_address;
	reg	[LGLENW:0]		writes_remaining_w,
					write_bursts_outstanding;
	reg	[LGLENW:0]		write_burst_length;
	reg				write_requests_remaining;
	reg	[C_AXI_ADDR_WIDTH-1:0]	write_distance_to_boundary_b;
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


	////////////////////////////////////////////////////////////////////////
	//
	// AXI-Lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH + C_AXIL_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WSTRB, S_AXIL_WDATA }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_strb, wskd_data }));

	always  @(*)
	begin
		axil_write_ready = !S_AXIL_BVALID || S_AXIL_BREADY;;
		if (!awskd_valid || !wskd_valid)
			axil_write_ready = 0;
	end

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		S_AXIL_BVALID <= 1'b0;
	else if (!S_AXIL_BVALID || S_AXIL_BREADY)
		S_AXIL_BVALID <=  axil_write_ready;

	always @(*)
		S_AXIL_BRESP = AXI_OKAY;

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

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		r_err <= 1'b0;
	else if (!r_busy && axil_write_ready)
		r_err <= (r_err) && (!wskd_strb[0] || !wskd_data[CTRL_ERR_BIT]);
	else if (r_busy)
		r_err <= (r_err || (M_AXI_RVALID && M_AXI_RRESP[1])
				|| (M_AXI_BVALID && M_AXI_BRESP[1]));

	always @(posedge S_AXI_ACLK)
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

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_int_enable || !r_busy)
		o_int <= 0;
	else if (r_done)
		o_int <= 1'b1;
	else
		o_int <= (last_write_ack && M_AXI_BVALID && M_AXI_BREADY);

	always @(posedge S_AXI_ACLK)
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
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		r_abort <= 1'b0;
	// else if (!r_busy || (last_write_ack && M_AXI_BVALID && M_AXI_BREADY))
	//	r_abort <= 1'b0;
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
	end else if (!r_abort) // && r_busy
		r_abort <= (axil_write_ready && awskd_addr == CTRL_ADDR)
			&&(wskd_strb[3] && wskd_data[31:24] == ABORT_KEY);

	always @(posedge S_AXI_ACLK)
	if (i_reset)
	begin
		r_len <= 0;
		zero_len <= 1;
		r_prot <= 0;
		r_qos  <= 0;
		r_src_addr <= 0;
		r_dst_addr <= 0;
		r_int_enable <= 0;
	end else if (!r_busy && axil_write_ready)
	begin
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
		SRC_ADDR: begin
			if (wskd_strb[0])
				r_src_addr[7:0] <= wskd_data[((C_AXI_ADDR_WIDTH <= 8) ? C_AXI_ADDR_WIDTH : 8)-1:0];
			if ((C_AXI_ADDR_WIDTH >=  8) && (wskd_strb[1]))
				r_src_addr[15:8] <= wskd_data[((C_AXI_ADDR_WIDTH <= 16) ? C_AXI_ADDR_WIDTH : 16)-1:8];
			if ((C_AXI_ADDR_WIDTH >= 16) && (wskd_strb[2]))
				r_src_addr[23:16] <= wskd_data[((C_AXI_ADDR_WIDTH <= 24) ? C_AXI_ADDR_WIDTH : 24)-1:16];
			if ((C_AXI_ADDR_WIDTH >= 24) && (wskd_strb[3]))
				r_src_addr[C_AXI_ADDR_WIDTH-1:24] <= wskd_data[C_AXI_ADDR_WIDTH-1:24];
			if (!OPT_UNALIGNED)
				r_src_addr[ADDRLSB-1:0] <= 0;
			end
		DST_ADDR: begin
			r_dst_addr <= wskd_data[C_AXI_ADDR_WIDTH-1:0];
			if (!OPT_UNALIGNED)
				r_dst_addr[ADDRLSB-1:0] <= 0;
			end
		LEN_ADDR: begin
			r_len <= wskd_data[LGLEN-1:0];
			if (OPT_UNALIGNED)
				zero_len <= (wskd_data[LGLEN-1:0] == 0);
			else begin
				zero_len <= (wskd_data[LGLEN-1:ADDRLSB] == 0);
				r_len[ADDRLSB-1:0] <= 0;
			end end
		// default:
		endcase
	end else if (r_busy)
	begin
		// r_src_addr <= 0;
		r_dst_addr <= write_address;
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
	end

	always @(*)
		S_AXIL_BRESP = 2'b00;


	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite control read interface
	//
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
	end

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		S_AXIL_RVALID <= 1'b0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
		S_AXIL_RVALID <= axil_read_ready;

	always @(posedge S_AXI_ACLK)
	if (!i_reset)
		S_AXIL_RDATA <= 0;
	else if (!S_AXIL_RVALID || |S_AXIL_RREADY)
	begin
		S_AXIL_RDATA <= 0;
		case(arskd_addr)
		CTRL_ADDR: begin
			S_AXIL_RDATA[CTRL_ABORT_BIT] <= r_abort;
			S_AXIL_RDATA[CTRL_ERR_BIT]   <= r_err;
			S_AXIL_RDATA[CTRL_BUSY_BIT]  <= r_busy;
			S_AXIL_RDATA[CTRL_INTEN_BIT] <= r_int_enable;
			S_AXIL_RDATA[CTRL_INT_BIT]   <= r_int;
			end
		SRC_ADDR:
			S_AXIL_RDATA[C_AXI_ADDR_WIDTH-1:0] <= r_src_addr;
		DST_ADDR:
			S_AXIL_RDATA[C_AXI_ADDR_WIDTH-1:0] <= r_dst_addr;
		LEN_ADDR:
			S_AXIL_RDATA[LGLEN-1:0] <= r_len;
		endcase

		if (!axil_read_ready)
			S_AXIL_RDATA <= 0;
	end

	always @(*)
		S_AXIL_RRESP = AXI_OKAY;

	////////////////////////////////////////////////////////////////////////
	//
	// AXI read processing
	//
	// Read data into our FIFO
	//
	////////////////////////////////////////////////////////////////////////
	//
	//


	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		read_address <= r_src_addr;
	else if (phantom_read)
	begin
	// Verilator lint_off WIDTH
		read_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			<= read_address[C_AXI_ADDR_WIDTH-1:ADDRLSB] +(M_AXI_ARLEN+1);
	// Verilator lint_on WIDTH
		read_address[ADDRLSB-1:0] <= 0;
	end

	// Verilator lint_off WIDTH
	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		reads_remaining_w <= readlen_b[LGLEN:ADDRLSB];
	else if (phantom_read)
		reads_remaining_w <= reads_remaining_w - (M_AXI_ARLEN+1);
	// Verilator lint_on WIDTH

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
	begin
		read_bursts_outstanding <= 0;
	end else case({phantom_read,M_AXI_RVALID&& M_AXI_RREADY && M_AXI_RLAST})
	2'b01: read_bursts_outstanding <= read_bursts_outstanding - 1;
	2'b10: read_bursts_outstanding <= read_bursts_outstanding + 1;
	default: begin end
	endcase

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
	begin
		no_read_bursts_outstanding <= 1;
	end else case({phantom_read,M_AXI_RVALID&& M_AXI_RREADY && M_AXI_RLAST})
	2'b01: no_read_bursts_outstanding <= (read_bursts_outstanding == 1);
	2'b10: no_read_bursts_outstanding <= 0;
	default: begin end
	endcase

	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		M_AXI_ARADDR <= r_src_addr;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		M_AXI_ARADDR <= read_address;

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

	always @(*)
	begin
		read_distance_to_boundary_b = 0;
		read_distance_to_boundary_b[ADDRLSB +: LGMAXBURST]
					= -r_src_addr[ADDRLSB +: LGMAXBURST];
	end

	always @(*)
	begin
		// initial_readlen_w = (1<<LGMAXBURST);
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

	// Verilator lint_off WIDTH
	always @(posedge S_AXI_ACLK)
	if (!r_busy)
	begin
		readlen_w <= initial_readlen_w;
	end else if (phantom_read)
	begin
		readlen_w <= reads_remaining_w - (M_AXI_ARLEN+1);
		if (reads_remaining_w - (M_AXI_ARLEN+1) > (1<<LGMAXBURST))
			readlen_w <= (1<<LGMAXBURST);
	end
	// Verilator lint_on WIDTH

	always @(*)
	begin
		w_start_read = r_busy && (reads_remaining_w > 0);
		if (phantom_read)
			w_start_read = 0;
		if (fifo_space_available < (1<<LGMAXBURST))
			w_start_read = 0;
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			w_start_read = 0;
		if (r_err || r_abort)
			w_start_read = 0;
	end

	always @(posedge S_AXI_ACLK)
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

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
		M_AXI_ARLEN <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
`ifdef	AXI3
		M_AXI_ARLEN <= readlen_w[3:0] - 4'h1;
`else
		M_AXI_ARLEN <= readlen_w[7:0] - 8'h1;
`endif

	always @(*)
	begin
		M_AXI_ARID    = AXI_READ_ID;
		M_AXI_ARBURST = AXI_INCR;
		M_AXI_ARSIZE  = ADDRLSB[2:0];
		M_AXI_ARLOCK  = 1'b0;
		M_AXI_ARCACHE = 4'h0;
		M_AXI_ARPROT  = r_prot;
		M_AXI_ARQOS   = r_qos;
		//
		M_AXI_RREADY = !no_read_bursts_outstanding;
	end

	////////////////////////////////////////////////////////////////////////
	//
	// The intermediate FIFO
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		fifo_reset = i_reset || !r_busy || r_done;

	generate if (OPT_UNALIGNED)
	begin : REALIGNMENT_FIFO

		////////////////////////////////////////////////////////////////
		//
		// Write strobe logic for the unaligned case
		//
		////////////////////////////////////////////////////////////////
		//
		//
		// The realignment logic has been removed from this version
		//
		// Please contact Gisselquist Technology, LLC, if you would
		// like access to the realignment code and/or the full
		// set of formal properties.
		//
	end else begin : ALIGNED_FIFO

		always @(*)
			r_first_wstrb = -1;

		always @(*)
			r_last_wstrb = -1;

		always @(*)
			r_partial_in_valid = 1;

		always @(*)
			r_partial_outvalid = !fifo_empty;

		always @(posedge S_AXI_ACLK)
		if (fifo_reset)
			fifo_space_available <= (1<<LGFIFO);
		else case({ phantom_read, M_AXI_WVALID && M_AXI_WREADY })
		// Verilator lint_off WIDTH
		2'b10: fifo_space_available <= fifo_space_available - (M_AXI_ARLEN+1);
		2'b01: fifo_space_available <= fifo_space_available + 1;
		2'b11: fifo_space_available <= fifo_space_available - M_AXI_ARLEN;
		// Verilator lint_on WIDTH
		default: begin end
		endcase

		always @(*)
			r_write_fifo = M_AXI_RVALID;

		always @(*)
			r_read_fifo = M_AXI_WVALID && M_AXI_WREADY;

		sfifo #(.BW(C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b1))
		middata(i_clk, fifo_reset,
				r_write_fifo, M_AXI_RDATA, fifo_full, fifo_fill,
				r_read_fifo,  M_AXI_WDATA, fifo_empty);


		initial	fifo_writes_available = 0;
		always @(posedge S_AXI_ACLK)
		if (fifo_reset)
			fifo_writes_available <= 0;
		else case({ phantom_write, M_AXI_RVALID })
		// Verilator lint_off WIDTH
		2'b10: fifo_writes_available <= fifo_writes_available - (M_AXI_AWLEN+1);
		2'b01: fifo_writes_available <= fifo_writes_available + 1;
		2'b11: fifo_writes_available <= fifo_writes_available - (M_AXI_AWLEN);
		// Verilator lint_on WIDTH
		default: begin end
		endcase

		initial	M_AXI_WSTRB = -1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || !r_busy)
			M_AXI_WSTRB <= -1;
		else if (!M_AXI_WVALID || M_AXI_WREADY)
			M_AXI_WSTRB <= (r_err || r_abort) ? 0 : -1;

	end endgenerate


	////////////////////////////////////////////////////////////////////////
	//
	// AXI write processing
	//
	// Write data from the FIFO to the AXI bus
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		write_address <= r_dst_addr;
	else if (phantom_write)
	begin
		// Verilator lint_off WIDTH
		write_address <= write_address + ((M_AXI_AWLEN+1)<< M_AXI_AWSIZE);
		// Verilator lint_on WIDTH
		write_address[ADDRLSB-1:0] <= 0;
	end

	// Verilator lint_off WIDTH
	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
	begin
		writes_remaining_w <= writelen_b[LGLEN:ADDRLSB];
	end else if (phantom_write)
		writes_remaining_w <= writes_remaining_w - (M_AXI_AWLEN+1);

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
	begin
		write_beats_remaining <= writelen_b[LGLEN:ADDRLSB];
	end else if (M_AXI_WVALID && M_AXI_WREADY)
		write_beats_remaining <= write_beats_remaining - 1;

	always @(posedge S_AXI_ACLK)
	if (i_reset)
		write_requests_remaining <= 1'b0;
	else if (!r_busy)
		write_requests_remaining <= w_start;
	else if (phantom_write)
		write_requests_remaining <= (writes_remaining_w != (M_AXI_AWLEN+1));
	// Verilator lint_on WIDTH

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
	begin
		write_bursts_outstanding <= 0;
	end else case({phantom_write, M_AXI_BVALID && M_AXI_BREADY })
	2'b01: write_bursts_outstanding <= write_bursts_outstanding - 1;
	2'b10: write_bursts_outstanding <= write_bursts_outstanding + 1;
	default: begin end
	endcase

	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		last_write_ack <= 0;
	else if (writes_remaining_w > ((phantom_write) ? (M_AXI_AWLEN+1) : 0))
		last_write_ack <= 0;
	else
		last_write_ack <= (write_bursts_outstanding
			== (phantom_write ? 0:1) + (M_AXI_BVALID ? 1:0));

	always @(posedge S_AXI_ACLK)
	if (!r_busy || M_AXI_ARVALID || M_AXI_AWVALID)
		r_done <= 0;
	else if (read_bursts_outstanding > (M_AXI_RVALID && M_AXI_RLAST ? 1:0))
		r_done <= 0;
	else if (write_bursts_outstanding > (M_AXI_BVALID ? 1:0))
		r_done <= 0;
	else if (r_abort || r_err)
		r_done <= 1;
	else if (writes_remaining_w > 0)
		r_done <= 0;
	else
		r_done <= 1;

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

	always @(*)
	begin
		write_distance_to_boundary_b = 0;
		write_distance_to_boundary_b[ADDRLSB +: LGMAXBURST]
					= -write_address[ADDRLSB +: LGMAXBURST];
	end

	// Verilator lint_off WIDTH
	always @(*)
	begin
		write_burst_length = (1<<LGMAXBURST);
		if ((write_address[ADDRLSB +: LGMAXBURST] != 0)
			&& (write_distance_to_boundary_b[ADDRLSB +: LGMAXBURST] != 0))
			write_burst_length = write_distance_to_boundary_b[LGLEN-1:ADDRLSB];
		if (write_burst_length > writes_remaining_w)
			write_burst_length = writes_remaining_w;
	end
	// Verilator lint_on WIDTH

	always @(posedge S_AXI_ACLK)
	if (i_reset || !r_busy)
		write_count <= 0;
	else if (w_write_start)
		write_count <= write_burst_length[LGMAXBURST:0];
	else if (M_AXI_WVALID && M_AXI_WREADY)
		write_count <= write_count - 1;

	always @(posedge S_AXI_ACLK)
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

	reg	last_write_burst;

	always @(*)
		last_write_burst = (write_burst_length == writes_remaining_w);

	always @(*)
	begin
		// Verilator lint_off WIDTH
		if (!last_write_burst && OPT_UNALIGNED)
			w_write_start = (fifo_writes_available > 1)
				&&(fifo_writes_available > write_burst_length);
		else
			w_write_start = (fifo_writes_available >= write_burst_length);
		if (write_burst_length == 0)
			w_write_start = 0;
		// Verilator lint_on WIDTH
		if (!write_requests_remaining)
			w_write_start = 0;
		if (phantom_write)
			w_write_start = 0;
		if (M_AXI_WVALID && (!M_AXI_WLAST || !M_AXI_WREADY))
			w_write_start = 0;
		if (i_reset || r_err || r_abort || !r_busy)
			w_write_start = 0;
	end

	always @(posedge S_AXI_ACLK)
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

	always @(posedge S_AXI_ACLK)
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

	always @(posedge S_AXI_ACLK)
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

	always @(posedge S_AXI_ACLK)
	if (!r_busy)
		M_AXI_AWADDR <= r_dst_addr;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		M_AXI_AWADDR <= write_address;


	always @(*)
	begin
		M_AXI_AWID    = AXI_WRITE_ID;
		M_AXI_AWBURST = AXI_INCR;
		M_AXI_AWSIZE  = ADDRLSB[2:0];
		M_AXI_AWLOCK  = 1'b0;
		M_AXI_AWCACHE = 4'h0;
		M_AXI_AWPROT  = r_prot;
		M_AXI_AWQOS   = r_qos;
		//
`ifdef	AXI3
		M_AXI_WID     = AXI_WRITE_ID;
`endif
		M_AXI_BREADY = !r_done;
	end

	// Keep Verilator happy
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_BID,
			M_AXI_RID, M_AXI_BRESP[0], M_AXI_RRESP[0],
			S_AXIL_AWADDR[AXILLSB-1:0], S_AXIL_ARADDR[AXILLSB-1:0],
			write_distance_to_boundary_b[ADDRLSB-1:0],
			fifo_full, fifo_fill, fifo_empty,
`ifdef	AXI3
			readlen_w[LGLENW:4],
`else
			readlen_w[LGLENW:8],
`endif
			writelen_b[ADDRLSB-1:0], readlen_b[ADDRLSB-1:0] };
	// Verilator lint_on UNUSED

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
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

	reg	[C_AXI_ADDR_WIDTH-1:0]	f_next_wraddr, f_next_rdaddr;

	reg	[C_AXI_ADDR_WIDTH-1:0]	f_src_addr, f_dst_addr,
				f_read_address, f_write_address,
				f_read_check_addr, f_write_beat_addr,
				f_read_beat_addr;
	reg	[LGLEN:0]	f_length, f_rdlength, f_wrlength,
				f_writes_complete, f_reads_complete;



	////////////////////////////////////////////////////////////////////////
	//
	// The control interface
	//
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


	////////////////////////////////////////////////////////////////////////
	//
	// The main AXI data interface
	//
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

	////////////////////////////////////////////////////////////////////////
	//
	// Internal assertions (Induction)
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (w_start)
	begin
		f_src_addr <= r_src_addr;
		f_dst_addr <= r_dst_addr;
		f_length   <= r_len;
	end else if (r_busy)
	begin
		assert(f_length != 0);
		assert(f_length[LGLEN] == 0);
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

		f_rd_arfirst = (M_AXI_ARADDR == f_src_addr);
		f_rd_arlast  = (M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			+ (M_AXI_ARLEN+1)
			== f_last_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]);
		//
		// ...
		//
	end

	always @(*)
	if (r_busy && !OPT_UNALIGNED)
	begin
		assert(f_src_addr[ADDRLSB-1:0] == 0);
		assert(f_dst_addr[ADDRLSB-1:0] == 0);
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
		f_write_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
		= f_dst_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			+ (f_wrlength[LGLEN:ADDRLSB] - writes_remaining_w);
	end

	always @(*)
	begin
		f_next_wraddr = M_AXI_AWADDR + ((M_AXI_AWLEN+1)<<M_AXI_AWSIZE);
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
		end
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
		assert(writes_remaining_w   <= f_wrlength[LGLEN:ADDRLSB]);
		assert(f_writes_complete    <= f_wrlength[LGLEN:ADDRLSB]);
		assert(fifo_fill            <= f_wrlength[LGLEN:ADDRLSB]);
		assert(fifo_writes_available<= fifo_fill);

		assert(write_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			== f_write_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]);

		if (M_AXI_AWADDR != f_dst_addr && writes_remaining_w != 0)
			assert(M_AXI_AWADDR[LGMAXBURST+ADDRLSB-1:0] == 0);
		else if (!OPT_UNALIGNED)
			assert(M_AXI_AWADDR[ADDRLSB-1:0] == 0);

		if((writes_remaining_w!= f_wrlength[LGLEN:ADDRLSB])
			&&(writes_remaining_w != 0))
			assert(write_address[LGMAXBURST+ADDRLSB-1:0] == 0);

		if ((write_address[C_AXI_ADDR_WIDTH-1:ADDRLSB] != f_dst_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB])
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
		assert(write_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				== f_dst_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			|| (write_address[LGMAXBURST-1:0] == 0)
			|| (writes_remaining_w == 0));

	always @(*)
	if (phantom_write)
		assert(writes_remaining_w >= (M_AXI_AWLEN+1));
	else if (M_AXI_AWVALID)
		assert(write_address == f_next_wraddr);

	//
	// ...
	//

	always @(*)
	if (M_AXI_WVALID)
	begin
		if (OPT_UNALIGNED)
			assert(r_partial_outvalid || r_abort || r_err);
		else
			assert(!fifo_empty || r_abort || r_err);
		//
		// ...
		//
	end

	always @(*)
	begin
		f_write_beat_addr = 0;
		f_write_beat_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			= f_dst_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
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
			assert(fifo_writes_available == 0);
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
			f_read_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			= f_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				+ (f_rdlength[LGLEN:ADDRLSB] - reads_remaining_w);
		end

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
			f_read_beat_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				= f_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				+ f_reads_complete;

		f_end_of_read_burst = M_AXI_ARADDR;
		f_end_of_read_burst[ADDRLSB-1:0] = 0;
		f_end_of_read_burst[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			= f_end_of_read_burst[C_AXI_ADDR_WIDTH-1:ADDRLSB]
			+ (M_AXI_ARLEN + 1);

		//
		// ...
		//
	end

	always @(*)
	begin
		f_next_rdaddr = M_AXI_ARADDR + ((M_AXI_ARLEN+1)<<M_AXI_ARSIZE);
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
			assert(M_AXI_ARADDR == read_address);
		else if (M_AXI_ARVALID)
			assert(read_address == f_next_rdaddr);
	end // else ...

	//
	// ...
	//

	// Constrain read_address--our pointer to the next bursts address
	always @(*)
	if (r_busy) //  && !r_abort && !r_err)
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

		if ((read_address[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				!= f_src_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB])
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
			if (f_read_beat_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB] != f_last_src_beat[C_AXI_ADDR_WIDTH-1:ADDRLSB])
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
		assert(f_read_beat_addr == r_src_addr);

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

	always @(posedge  S_AXI_ACLK)
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

	////////////////////////////////////////

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


	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checks
	//
	always @(*)
	if (!r_busy)
		assert(fifo_writes_available == 0);
	// else ...

	always @(*)
	if (!fifo_reset)
	begin
		if (!r_busy)
			assert(fifo_space_available == (1<<LGFIFO));
		// else ...
	end

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

		assert(reads_remaining_w <= writes_remaining_w);

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
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
	begin
		assume(!S_AXIL_BVALID);
		assume(!S_AXIL_RVALID);

		assume(!M_AXI_AWVALID);
		assume(!M_AXI_WVALID);
		assume(!M_AXI_ARVALID);

		assume(write_bursts_outstanding == 0);

		assume(!phantom_read);
		assume(!phantom_write);
		assume(!r_busy);
		assume(read_bursts_outstanding == 0);
		assume(no_read_bursts_outstanding);

		assume(r_len == 0);
		assume(zero_len);
	end

	always @(*)
		assert(ADDRLSB + LGMAXBURST <= 12);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
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

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy && r_err))
		cover(!r_busy && r_abort);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && r_busy && r_abort))
		cover(!r_busy && r_err);

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

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions (i.e. constraints)
	//

	// None (currently)
`endif
endmodule
