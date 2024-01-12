////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axil2axis
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Demonstrates a simple AXI-Lite interface to drive an AXI-Stream
//		channel.  This can then be used to debug DSP processing.
//
// Registers:	This AXI-lite to AXI-Stream core supports four word-sized
//		addresses.  Byte enables are ignored.
//
//   2'b00, ADDR_SINK
//		Writes to this register will send data to the stream master,
//		with TLAST clear.  Data goes first through a FIFO.  If the
//		FIFO is full, the write will stall.  If it stalls OPT_TIMEOUT
//		cycles, the write will fail and return a bus error.
//
//		Reads from this register will return data from the stream slave,
//		but without consuming it.  Values read here may still be read
//		from the ADDR_SOURCE register later.
//
//   2'b01, ADDR_SOURCE
//		Writes to this register will send data downstream to the stream
//		master as well, but this time with TLAST set.
//
//		Reads from this register will accept a value from the stream
//		slave interface.  The read value contains TDATA.  TLAST is
//		ignored in this read.  If you want access to TLAST, you can get
//		it from the ADDR_FIFO register.
//
//		If there is no data to be read, the read will not and does not
//		stall.  It will instead return a bus error.
//
//   2'b10, ADDR_STATS
//		Since we can, we'll handle some statistics  here.  The top half
//		word contains two counters: a 4-bit counter of TLAST's issued
//		from the stream master, and a 12-bit counter of TDATA values
//		issued.  Neither counter includes data still contained in the
//		FIFO.  If the OPT_SOURCE option is clear, these values will
//		always be zero.
//
//		The second (bottom, or least-significant) halfword contains the
//		same regarding the stream slave.  If OPT_SINK is set, these
//		counters count values read from the core.  If OPT_SINK is clear,
//		so that the stream sink is not truly implemented, then TREADY
//		will be held high and the counter will just count values coming
//		into the core never going into the FIFO.
//
//   2'b11, ADDR_FIFO
//		Working with the core can be a challenge.  You want to make
//		certain that writing to the core  doesn't hang the design, and
//		that reading from the core doesn't cause a bus error.
//
//		Bits 31:16 contain the number of items in the write FIFO, and
//		bits 14:0 contain the number of items in the read FIFO.
//
//		Bit 15 contains whether or not the next item to be read is
//		the last item in a packet, i.e. with TLAST set.
//		
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
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
`default_nettype none
// }}}
module	axil2axis #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXI_ADDR_WIDTH = 4,
		localparam	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXIS_DATA_WIDTH = 16,
		//
		// OPT_SOURCE enables the AXI stream master logic.  If not
		// enabled, M_AXI_TVALID will be held at zero, and the stream
		// master logic may be ignored.
		parameter [0:0] OPT_SOURCE = 1'b1,
		//
		// OPT_SINK enables the AXI stream slave logic.  If not enabled,
		// reads will always return zero, and S_AXIS_TREADY will be
		// held high.
		parameter [0:0] OPT_SINK = 1'b1,
		//
		// If OPT_SIGN_EXTEND is set, values received will be sign
		// extended to fill the full data width on read.  Otherwise
		// the most significant of any unused bits will remain clear.
		parameter [0:0] OPT_SIGN_EXTEND = 1'b0,
		//
		// Data written to this core will be placed into a FIFO before
		// entering the AXI stream master.  LGFIFO is the log, based
		// two, of the number of words in this FIFO.  Similarly, data
		// consumed by AXI stream slave contained in this core will go
		// first into a read FIFO.  Reads from the core will then return
		// data from this FIFO, or a bus error if none is available.
		parameter 	LGFIFO = 5,
		//
		// OPT_TIMEOUT, if non-zero, will allow writes to the stream
		// master, or reads from the stream slave, to stall the core
		// for OPT_TIMEOUT cycles for the stream to be ready.  If the
		// stream isn't ready at this time (i.e. if the write FIFO is
		// still full, or the read FIFO still empty), the result will
		// be returned as a bus error.  Likewise, if OPT_TIMEOUT==0,
		// the core will always return a bus error if ever the write
		// FIFO is full or the read FIFO empty.
		parameter	OPT_TIMEOUT = 5,
		//
		// OPT_LOWPOWER sets outputs to zero if not valid.  This applies
		// to the AXI-lite bus, however, and not the AXI stream FIFOs,
		// since those don't have LOWPOWER support (currently).
		parameter [0:0]	OPT_LOWPOWER = 0
		//
		// This design currently ignores WSTRB, beyond checking that it
		// is not zero.  I see no easy way to add it.  (I'll leave that
		// to you to implement, if you wish.)
		// parameter [0:0]	OPT_WSTRB = 0,
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		// AXI-lite signals
		// {{{
		input	wire					S_AXI_AWVALID,
		output	wire					S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		output	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		output	wire	[1:0]				S_AXI_BRESP,
		//
		input	wire					S_AXI_ARVALID,
		output	wire					S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		//
		output	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_RDATA,
		output	wire	[1:0]				S_AXI_RRESP,
		// }}}
		// AXI stream slave (sink) signals
		// {{{
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire	[C_AXIS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		input	wire				S_AXIS_TLAST,
		// }}}
		// AXI stream master (source) signals
		// {{{
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]	M_AXIS_TDATA,
		output	reg				M_AXIS_TLAST
		// }}}
		// }}}
	);

	localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3;
	localparam	[1:0]	ADDR_SINK = 2'b00,	// Read from stream
				ADDR_SOURCE = 2'b01, // Write, also sets TLAST
				ADDR_STATS  = 2'b10,
				ADDR_FIFO   = 2'b11;
	localparam	SW = C_AXIS_DATA_WIDTH;

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire	i_reset = !S_AXI_ARESETN;

	wire				axil_write_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	awskd_addr;
	//
	wire	[C_AXI_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid, axil_berr;
	//
	wire				axil_read_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	arskd_addr;
	reg	[C_AXI_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	wire			awskd_valid, wskd_valid;
	wire			wfifo_full, wfifo_write, wfifo_empty;
	wire	[LGFIFO:0]	wfifo_fill;
	reg			write_timeout;

	wire			read_timeout;
	reg			axil_rerr;
	reg	[3:0]		read_bursts_completed;
	reg	[11:0]		reads_completed;

	wire	[3:0]	write_bursts_completed;
	wire	[11:0]	writes_completed;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	//
	// {{{
	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
		.i_data(S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
		.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXI_BVALID || S_AXI_BREADY)
			&& ((awskd_addr[1] != ADDR_SOURCE[1])
				|| (!wfifo_full || write_timeout));

	//
	// Write timeout generation
	//
	// {{{
	generate if ((OPT_TIMEOUT > 1) && OPT_SOURCE)
	begin : GEN_WRITE_TIMEOUT
		reg				r_write_timeout;
		reg [$clog2(OPT_TIMEOUT)-1:0] write_timer;

		initial	write_timer = OPT_TIMEOUT-1;
		initial	r_write_timeout = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			write_timer <= OPT_TIMEOUT-1;
			r_write_timeout<= 1'b0;
		end else if (!awskd_valid || !wfifo_full || !wskd_valid
				|| (awskd_addr[1] != ADDR_SOURCE[1])
				|| (S_AXI_BVALID && !S_AXI_BREADY))
		begin
			write_timer <= OPT_TIMEOUT-1;
			r_write_timeout<= 1'b0;
		end else begin
			if (write_timer > 0)
				write_timer <= write_timer - 1;
			r_write_timeout <= (write_timer <= 1);
		end

		assign	write_timeout = r_write_timeout;
`ifdef	FORMAL
		always @(*)
			assert(write_timer <= OPT_TIMEOUT-1);
		always @(*)
			assert(write_timeout == (write_timer == 0));
`endif
	end else begin : NO_WRITE_TIMEOUT

		assign	write_timeout = 1'b1;

	end endgenerate
	// }}}
	

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXI_BREADY)
		axil_bvalid <= 0;

	assign	S_AXI_BVALID = axil_bvalid;

	initial	axil_berr = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && i_reset)
		axil_berr <= 0;
	else if (axil_write_ready)
		axil_berr <= (wfifo_full)&&(awskd_addr[1]==ADDR_SOURCE[1]);
	else if (OPT_LOWPOWER && S_AXI_BREADY)
		axil_berr <= 1'b0;

	assign	S_AXI_BRESP = { axil_berr, 1'b0 };
	// }}}

	//
	// AXI-stream source (Write) FIFO
	//
	// {{{
	assign	wfifo_write = axil_write_ready && awskd_addr[1]==ADDR_SOURCE[1]
			&& wskd_strb != 0 && !wfifo_full;

	generate if (OPT_SOURCE)
	begin : GEN_SOURCE_FIFO

		sfifo #(.BW(SW+1), .LGFLEN(LGFIFO))
		source(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(wfifo_write),
			.i_data({awskd_addr[0]==ADDR_SOURCE[0],
					wskd_data[SW-1:0]}),
			.o_full(wfifo_full), .o_fill(wfifo_fill),
			.i_rd(M_AXIS_TREADY),
				.o_data({ M_AXIS_TLAST, M_AXIS_TDATA }),
				.o_empty(wfifo_empty));

		assign	M_AXIS_TVALID = !wfifo_empty;

	end else begin : NO_SOURCE_FIFO

		assign	M_AXIS_TVALID = 1'b0;
		assign	M_AXIS_TDATA  = 0;
		assign	M_AXIS_TLAST  = 0;

		assign	wfifo_full = 1'b0;
		assign	wfifo_fill = 0;

	end endgenerate
	// }}}

	//
	// AXI-stream consumer/sink (Read) FIFO
	//
	// {{{
	wire			rfifo_empty, rfifo_full, rfifo_last, read_rfifo;
	wire	[LGFIFO:0]	rfifo_fill;
	wire	[SW-1:0]	rfifo_data;

	generate if (OPT_SINK)
	begin : GEN_SINK_FIFO

		sfifo #(.BW(SW+1), .LGFLEN(LGFIFO))
		sink(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(S_AXIS_TVALID && S_AXIS_TREADY),
			.i_data({S_AXIS_TLAST, S_AXIS_TDATA}),
			.o_full(rfifo_full), .o_fill(rfifo_fill),
			.i_rd(read_rfifo),
				.o_data({ rfifo_last, rfifo_data }),
				.o_empty(rfifo_empty));

		assign	S_AXIS_TREADY = !rfifo_full;
		assign	read_rfifo =(axil_read_ready && arskd_addr== ADDR_SINK)
				&& !rfifo_empty;

	end else begin : NO_SINK

		assign	S_AXIS_TREADY = 1'b1;

		assign rfifo_empty = 1'b1;
		assign rfifo_data  = 0;
		assign rfifo_last  = 1'b1;
		assign rfifo_fill  = 0;

	end endgenerate
	// }}}

	//
	// Read timeout generation
	//
	// {{{
	generate if (OPT_SINK && OPT_TIMEOUT > 1)
	begin : GEN_READ_TIMEOUT
		reg [$clog2(OPT_TIMEOUT)-1:0]	read_timer;
		reg				r_read_timeout;

		initial	read_timer = OPT_TIMEOUT-1;
		initial	r_read_timeout = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			read_timer <= OPT_TIMEOUT-1;
			r_read_timeout<= 1'b0;
		end else if (!arskd_valid || (S_AXI_RVALID && !S_AXI_RREADY)
				||!rfifo_empty
				||(arskd_addr[1] != ADDR_SINK[1]))
		begin
			read_timer <= OPT_TIMEOUT-1;
			r_read_timeout<= 1'b0;
		end else begin
			if (read_timer > 0)
				read_timer <= read_timer - 1;
			r_read_timeout <= (read_timer <= 1);
		end

		assign	read_timeout = r_read_timeout;

`ifdef	FORMAL
		always @(*)
			assert(read_timer <= OPT_TIMEOUT-1);
		always @(*)
			assert(read_timeout == (read_timer == 0));
`endif
	end else begin : NO_READ_TIMEOUT

		assign	read_timeout = 1'b1;

	end endgenerate
	// }}}

	//
	// Read signaling
	//
	// {{{
	wire	arskd_valid;

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
		.i_data(S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	assign	axil_read_ready = arskd_valid
			&& (!S_AXI_RVALID || S_AXI_RREADY)
			&& ((arskd_addr[1] != ADDR_SINK[1])
				|| (!rfifo_empty || read_timeout));

	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (S_AXI_RREADY)
		axil_read_valid <= 1'b0;

	assign	S_AXI_RVALID = axil_read_valid;

	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		axil_rerr <= 1'b0;
	else if (axil_read_ready)
		axil_rerr <= rfifo_empty && (arskd_addr[1] == ADDR_SINK[1]);
	else if (OPT_LOWPOWER && S_AXI_RREADY)
		axil_rerr <= 1'b0;

	assign	S_AXI_RRESP = { axil_rerr, 1'b0 };
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Read data counting : reads_completed and read_bursts_completed
	// {{{
	initial	reads_completed = 0;
	initial	read_bursts_completed = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		reads_completed <= 0;
		read_bursts_completed <= 0;
		// }}}
	end else if (!OPT_SINK)
	begin
		// {{{
		reads_completed <= reads_completed + (S_AXIS_TVALID ? 1:0);
		read_bursts_completed <= read_bursts_completed
				+ ((S_AXIS_TVALID && S_AXIS_TLAST) ? 1:0);
		// }}}
	end else if (read_rfifo && !rfifo_empty)
	begin
		// {{{
		reads_completed <= reads_completed + 1;
		read_bursts_completed <= read_bursts_completed + (rfifo_last ? 1:0);
		// }}}
	end
	// }}}

	//
	// Write data counting
	// {{{
	generate if (OPT_SOURCE)
	begin : GEN_WRITES_COMPLETED
		// {{{
		reg	[3:0]	r_write_bursts_completed;
		reg	[11:0]	r_writes_completed;

		initial	r_writes_completed = 0;
		initial	r_write_bursts_completed = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			r_writes_completed <= 0;
			r_write_bursts_completed <= 0;
		end else if (M_AXIS_TVALID && M_AXIS_TREADY)
		begin
			r_writes_completed <= writes_completed + 1;
			r_write_bursts_completed <= write_bursts_completed
					+ (M_AXIS_TLAST ? 1:0);
		end

		assign	writes_completed = r_writes_completed;
		assign	write_bursts_completed = r_write_bursts_completed;
		// }}}
	end else begin : NO_COMPLETION_COUNTERS // No AXI-stream source logic
		// {{{
		assign	writes_completed = 0;
		assign	write_bursts_completed = 0;
		// }}}
	end endgenerate
	// }}}

	//
	// Read data register
	// {{{
	initial	axil_read_data = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		axil_read_data <= 0;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		axil_read_data <= 0;
		casez(arskd_addr)
		{ ADDR_SINK[1], 1'b? }:	begin
			if (OPT_SIGN_EXTEND && rfifo_data[SW-1])
				axil_read_data <= -1;
			axil_read_data[SW-1:0] <= rfifo_data;
			end
		ADDR_STATS: begin
			axil_read_data[31:28] <= write_bursts_completed;
			axil_read_data[27:16] <= writes_completed;
			axil_read_data[15:12] <= read_bursts_completed;
			axil_read_data[11:0]  <= reads_completed;
			end
		ADDR_FIFO:	begin
			// FIFO information
			axil_read_data[16 +: LGFIFO+1] <= wfifo_fill;
			axil_read_data[15] <= rfifo_last;
			axil_read_data[LGFIFO:0] <= rfifo_fill;
			end
		endcase

		if (OPT_LOWPOWER && !axil_read_ready)
			axil_read_data <= 0;
	end

	assign	S_AXI_RDATA  = axil_read_data;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
			S_AXI_ARADDR[ADDRLSB-1:0],
			S_AXI_AWADDR[ADDRLSB-1:0],
			wskd_data[C_AXI_DATA_WIDTH-1:SW] };
	// Verilator lint_on  UNUSED
	// }}}
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Register definitions
	// {{{
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(OPT_TIMEOUT + 2),
		.F_AXI_MAXDELAY(OPT_TIMEOUT + 2),
		.F_AXI_MAXRSTALL(2),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awprot( S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arprot( S_AXI_ARPROT),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rresp( S_AXI_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	always @(*)
	begin
		assert(faxil_awr_outstanding== (S_AXI_BVALID ? 1:0)
			+(S_AXI_AWREADY ? 0:1));

		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0)
			+(S_AXI_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(S_AXI_ARREADY ? 0:1));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Verifying the packet counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[11:0]	f_reads, f_writes;
	reg	[3:0]	f_read_pkts, f_write_pkts;

	//
	// Mirror the read counter
	//
	initial	f_reads      = 0;
	initial	f_read_pkts  = 0;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		f_reads <= 0;
		f_read_pkts <= 0;
	end else if (OPT_SINK && (axil_read_ready
			&& arskd_addr == ADDR_SINK && !rfifo_empty))
	begin
		f_reads <= f_reads + 1;
		f_read_pkts <= f_read_pkts + (rfifo_last ? 1:0);
	end else if (!OPT_SINK && S_AXIS_TVALID)
	begin
		f_reads <= f_reads + 1;
		f_read_pkts <= f_read_pkts + (S_AXIS_TLAST ? 1:0);
	end

	always @(*)
		assert(f_reads == reads_completed);
	always @(*)
		assert(f_read_pkts == read_bursts_completed);

	always @(*)
	if (!OPT_SINK)
		assert(S_AXIS_TREADY);

	//
	// Mirror the write counter
	//
	initial	f_writes     = 0;
	initial	f_write_pkts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		f_writes <= 0;
		f_write_pkts <= 0;
	end else if (OPT_SOURCE && M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		f_writes <= f_writes + 1;
		f_write_pkts <= f_write_pkts + (M_AXIS_TLAST ? 1:0);
	end

	always @(*)
	if (!OPT_SOURCE)
	begin
		assert(f_writes == 0);
		assert(f_write_pkts == 0);
	end

	always @(*)
	begin
		assert(f_writes == writes_completed);
		assert(f_write_pkts == write_bursts_completed);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Verify the read result
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && axil_read_ready))
	begin
		assert(S_AXI_RVALID);
		case($past(arskd_addr))
		ADDR_SINK: begin
			assert(S_AXI_RDATA[SW-1:0] == $past(rfifo_data));
			if (SW < C_AXI_DATA_WIDTH)
			begin
				if (OPT_SIGN_EXTEND && $past(rfifo_data[SW-1]))
					assert(&S_AXI_RDATA[C_AXI_DATA_WIDTH-1:SW]);
				else
					assert(S_AXI_RDATA[C_AXI_DATA_WIDTH-1:SW] == 0);
			end end
		// 1: assert(S_AXI_RDATA == $past(r1));
		ADDR_STATS: begin
			assert(S_AXI_RRESP == 2'b00);
			assert(S_AXI_RDATA[31:28]
					== $past(write_bursts_completed));
			assert(S_AXI_RDATA[27:16] == $past(writes_completed));

			assert(S_AXI_RDATA[15:12]
					== $past(read_bursts_completed));
			assert(S_AXI_RDATA[11:0] == $past(reads_completed));
			end
		ADDR_FIFO: begin
			assert(S_AXI_RRESP == 2'b00);
			if (LGFIFO < 16)
				assert(S_AXI_RDATA[31:16+LGFIFO+1] == 0);
			assert(S_AXI_RDATA[16+: LGFIFO+1]==$past(wfifo_fill));
			assert(S_AXI_RDATA[15] == $past(rfifo_last));
			if (LGFIFO < 15)
				assert(S_AXI_RDATA[14:LGFIFO+1] == 0);
			assert(S_AXI_RDATA[ 0+: LGFIFO+1]==$past(rfifo_fill));
			end
		default: begin end
		endcase
	end

	//
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXI_RVALID)
		assert(S_AXI_RDATA == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-stream interfaces
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Slave/consumer properties
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
	begin
		assume(!S_AXIS_TVALID);
	end else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
		assume($stable(S_AXIS_TLAST));
	end

	// Master/producer/source properties
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
	begin
		assert(!M_AXIS_TVALID);
	end else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		cover(S_AXI_ARESETN && writes_completed == 16);

	always @(*)
		cover(S_AXI_ARESETN && reads_completed == 16);

	always @(*)
		cover(S_AXI_ARESETN && writes_completed == 16
				&& reads_completed == 16);

	always @(*)
		cover(S_AXI_BVALID && S_AXI_BRESP != 2'b00);

	always @(*)
		cover(S_AXI_RVALID && S_AXI_RRESP != 2'b00);

	// }}}
	// }}}
`endif
endmodule
