////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axiperf
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Measure the performance of a high speed AXI interface.  The
//		following monitor requires connecting to both an AXI-lite slave
//	interface, as well as a second AXI interface as a monitor.  The AXI
//	monitor interface is read only, and (ideally) shouldn't be corrupted by
//	the inclusion of the AXI-lite interface on the same bus.
//
//	The core works by counting clock cycles in a fashion that should
//	supposedly make it easy to calculate 1) throughput, and 2) lag.
//	Moreover, the counters are arranged such that after the fact, the
//	various contributors to throughput can be measured and evaluted: was
//	the slave the holdup?  Or was it the master?
//
//	To use the core, connect it and build your design.  Then write a '3'
//	to register 15 (address 60).  Once the bus returns to idle, the core
//	will begin capturing data and statistics.  When done, write a '0' to
//	the same register.  This will create a stop request.  Once the bus
//	comes to a stop, the core will stop accumulating values into its
//	statistics.  Those statistics can then be read out from the AXI-lite
//	bus and analyzed.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
// }}}
//
`default_nettype none
//
module	axiperf #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXIL_ADDR_WIDTH = 7,
		localparam	C_AXIL_DATA_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 4,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter	LGCNT = 32,
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		input	wire					S_AXIL_AWVALID,
		output	wire					S_AXIL_AWREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_AWADDR,
		input	wire	[2:0]				S_AXIL_AWPROT,
		//
		input	wire					S_AXIL_WVALID,
		output	wire					S_AXIL_WREADY,
		input	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_WDATA,
		input	wire	[C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	wire					S_AXIL_BVALID,
		input	wire					S_AXIL_BREADY,
		output	wire	[1:0]				S_AXIL_BRESP,
		//
		input	wire					S_AXIL_ARVALID,
		output	wire					S_AXIL_ARREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_ARADDR,
		input	wire	[2:0]				S_AXIL_ARPROT,
		//
		output	wire					S_AXIL_RVALID,
		input	wire					S_AXIL_RREADY,
		output	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_RDATA,
		output	wire	[1:0]				S_AXIL_RRESP,
		//
		//
		// The AXI Monitor interface
		//
		input	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		input	wire	[7:0]			M_AXI_AWLEN,
		input	wire	[2:0]			M_AXI_AWSIZE,
		input	wire	[1:0]			M_AXI_AWBURST,
		input	wire				M_AXI_AWLOCK,
		input	wire	[3:0]			M_AXI_AWCACHE,
		input	wire	[2:0]			M_AXI_AWPROT,
		input	wire	[3:0]			M_AXI_AWQOS,
		//
		//
		input	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		input	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		input	wire				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		input	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		//
		//
		input	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		input	wire	[7:0]			M_AXI_ARLEN,
		input	wire	[2:0]			M_AXI_ARSIZE,
		input	wire	[1:0]			M_AXI_ARBURST,
		input	wire				M_AXI_ARLOCK,
		input	wire	[3:0]			M_AXI_ARCACHE,
		input	wire	[2:0]			M_AXI_ARPROT,
		input	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		input	wire				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP
		//
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	wire	i_reset = !S_AXI_ARESETN;

	wire				axil_write_ready;
	wire	[C_AXIL_ADDR_WIDTH-ADDRLSB-1:0]	awskd_addr;
	//
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				axil_read_ready;
	wire	[C_AXIL_ADDR_WIDTH-ADDRLSB-1:0]	arskd_addr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// Write signaling
	//
	// {{{

	wire	awskd_valid, wskd_valid;

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXIL_ADDR_WIDTH-ADDRLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:ADDRLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXIL_BVALID || S_AXIL_BREADY);

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXIL_BREADY)
		axil_bvalid <= 0;

	assign	S_AXIL_BVALID = axil_bvalid;
	assign	S_AXIL_BRESP = 2'b00;
	// }}}

	//
	// Read signaling
	//
	// {{{

	wire	arskd_valid;

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXIL_ADDR_WIDTH-ADDRLSB))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:ADDRLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	assign	axil_read_ready = arskd_valid
			&& (!axil_read_valid || S_AXIL_RREADY);

	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (S_AXIL_RREADY)
		axil_read_valid <= 1'b0;

	assign	S_AXIL_RVALID = axil_read_valid;
	assign	S_AXIL_RDATA  = axil_read_data;
	assign	S_AXIL_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg		idle_bus, triggered, stop_request,
			clear_request, start_request;
	reg	[LGCNT-1:0]	active_time;
	reg	[7:0]	wr_max_burst_size;
	reg	[LGCNT-1:0]	wr_awburst_count, wr_wburst_count, wr_beat_count;
	reg	[LGCNT-1:0]	wr_aw_byte_count, wr_w_byte_count;
	reg	[7:0]	wr_aw_outstanding, wr_w_outstanding,
			wr_aw_max_outstanding, wr_w_max_outstanding,
			wr_max_outstanding;
	reg		wr_aw_zero_outstanding, wr_w_zero_outstanding,
			wr_in_progress;
	reg	[LGCNT-1:0]	wr_idle_cycles,
			wr_b_lag_count, wr_b_stall_count,
			wr_slow_data, wr_stall,
			wr_addr_lag, wr_data_lag,
			wr_beat,
			wr_aw_burst, wr_addr_stall,
			wr_aww_stall, wr_aww_slow, wr_aww_nodata, wr_aww_beat;
	reg[C_AXI_DATA_WIDTH/8:0]	wstrb_count;

	reg [LGCNT-1:0]	rd_idle_cycles, rd_lag_counter, rd_slow_link,
			rd_burst_count, rd_byte_count, rd_beat_count,
			rd_ar_stalls, rd_r_stalls;
	reg	[7:0]	rd_outstanding_bursts, rd_max_burst_size,
			rd_max_outstanding_bursts;
	reg [7:0]	rd_outstanding_bursts_id [0:(1<<C_AXI_ID_WIDTH)-1];
	reg [(1<<C_AXI_ID_WIDTH)-1:0]	rd_nonzero_outstanding_id,
			rd_bursts_in_flight;
	reg [C_AXI_ID_WIDTH:0]	rd_total_in_flight, rd_responding,
			rd_max_responding_bursts;
	reg		rd_responding_d;

	integer		ik;
	genvar		gk;

	always @(posedge S_AXI_ACLK)
	begin
		if (axil_write_ready)
		begin
			clear_request <= 1'b0;
			if (!clear_request && idle_bus)
			begin
				start_request <= 0;
				stop_request <= 0;
			end
			case(awskd_addr)
			5'h1f:	if (wskd_strb[0]) begin
				// Start, stop, clear, reset
				//
				clear_request <=  wskd_data[1] && !wskd_data[0];
				stop_request  <= !wskd_data[0];
				start_request <=  wskd_data[0] && (!stop_request);
				end
			default: begin end
			endcase
		end

		if (!S_AXI_ARESETN)
		begin
			clear_request <= 1'b0;
			stop_request <= 1'b0;
			start_request <= 1'b0;
		end
	end

	initial	axil_read_data = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		axil_read_data <= 0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		axil_read_data <= 0;
		case(arskd_addr)
		5'h00: axil_read_data[LGCNT-1:0] <= active_time;
		5'h01: axil_read_data <= { wr_max_outstanding,
					rd_max_outstanding_bursts,
					wr_max_burst_size,
					rd_max_burst_size };
		5'h02: axil_read_data[LGCNT-1:0] <= wr_idle_cycles;
		5'h03: axil_read_data[LGCNT-1:0] <= wr_awburst_count;
		5'h04: axil_read_data[LGCNT-1:0] <= wr_beat_count;
		5'h05: axil_read_data[LGCNT-1:0] <= wr_aw_byte_count;
		5'h06: axil_read_data[LGCNT-1:0] <= wr_w_byte_count;
		5'h07: axil_read_data[LGCNT-1:0] <= wr_slow_data;
		5'h08: axil_read_data[LGCNT-1:0] <= wr_stall;
		5'h09: axil_read_data[LGCNT-1:0] <= wr_addr_lag;
		5'h0a: axil_read_data[LGCNT-1:0] <= wr_data_lag;
		5'h0b: axil_read_data[LGCNT-1:0] <= wr_beat;
		5'h0c: axil_read_data[LGCNT-1:0] <= wr_aw_burst;
		5'h0d: axil_read_data[LGCNT-1:0] <= wr_addr_stall;
		5'h0e: axil_read_data[LGCNT-1:0] <= wr_aww_stall;
		5'h0f: axil_read_data[LGCNT-1:0] <= wr_aww_slow;
		5'h10: axil_read_data[LGCNT-1:0] <= wr_aww_nodata;
		5'h11: axil_read_data[LGCNT-1:0] <= wr_aww_beat;
		5'h12: axil_read_data[LGCNT-1:0] <= wr_b_lag_count;
		5'h13: axil_read_data[LGCNT-1:0] <= wr_b_stall_count;
		//
		5'h16: axil_read_data[LGCNT-1:0] <= rd_idle_cycles;
		5'h17: axil_read_data	<= {
				{(C_AXIL_DATA_WIDTH-C_AXI_ID_WIDTH-1){1'b0}},
				rd_max_responding_bursts };
		5'h18: axil_read_data[LGCNT-1:0] <= rd_burst_count;
		5'h19: axil_read_data[LGCNT-1:0] <= rd_beat_count;
		5'h1a: axil_read_data[LGCNT-1:0] <= rd_byte_count;
		5'h1b: axil_read_data[LGCNT-1:0] <= rd_ar_stalls;
		5'h1c: axil_read_data[LGCNT-1:0] <= rd_r_stalls;
		5'h1d: axil_read_data[LGCNT-1:0] <= rd_lag_counter;
		5'h1e: axil_read_data[LGCNT-1:0] <= rd_slow_link;
		5'h1f: axil_read_data <= {
				// pending_idle,
				// pending_first_burst,
				// cleared,
				28'h0, 1'b0,
				triggered,
				clear_request,
				start_request
				};
		default: begin end
		endcase

		if (OPT_LOWPOWER && !axil_read_ready)
			axil_read_data <= 0;
	end

	function [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXI_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXI_DATA_WIDTH-1:0]		new_data;
		input	[C_AXI_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXI_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// AXI performance counters
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		triggered <= 0;
	else if (start_request)
	begin
		if (idle_bus)
			triggered <= 1'b1;
	end else if (stop_request && idle_bus)
		triggered <= 0;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		active_time <= 0;
	else if (triggered)
		active_time <= active_time + 1;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		idle_bus <= 1;
	else if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
		idle_bus <= 0;
	else if ((wr_aw_outstanding
			==((M_AXI_BVALID && M_AXI_BREADY) ? 1:0))
		&& (wr_w_outstanding == ((M_AXI_BVALID && M_AXI_BREADY) ? 1:0))
		&& (rd_outstanding_bursts
			==((M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST)? 1:0)))
		idle_bus <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Write statistics
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{


	initial	wr_max_burst_size = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_max_burst_size <= 0;
	else if (triggered)
	begin
		if (M_AXI_AWVALID && M_AXI_AWLEN > wr_max_burst_size)
			wr_max_burst_size <= M_AXI_AWLEN;
	end

	initial	wr_awburst_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_awburst_count <= 0;
	else if (triggered && M_AXI_AWVALID && M_AXI_AWREADY)
		wr_awburst_count <= wr_awburst_count + 1;

	initial	wr_wburst_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_wburst_count <= 0;
	else if (triggered && M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST)
		wr_wburst_count <= wr_wburst_count + 1;

	initial	wr_beat_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_beat_count <= 0;
	else if (triggered && M_AXI_WVALID && M_AXI_WREADY)
		wr_beat_count <= wr_beat_count + 1;

	always @(*)
	begin
		wstrb_count = 0;
		for(ik=0; ik<C_AXI_DATA_WIDTH/8; ik=ik+1)
		if (M_AXI_WSTRB[ik])
			wstrb_count = wstrb_count + 1;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_aw_byte_count <= 0;
	else if (triggered && M_AXI_AWVALID && M_AXI_AWREADY)
	begin
		wr_aw_byte_count <= wr_aw_byte_count
			+ (({ 24'b0, M_AXI_AWLEN}+32'h1) << M_AXI_AWSIZE);
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_w_byte_count <= 0;
	else if (triggered && M_AXI_WVALID && M_AXI_WREADY)
	begin
		wr_w_byte_count <= wr_w_byte_count
			+ { {(32-C_AXI_DATA_WIDTH/8-1){1'b0}}, wstrb_count };
	end

	initial	wr_aw_outstanding = 0;
	initial	wr_aw_zero_outstanding = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		wr_aw_outstanding <= 0;
		wr_aw_zero_outstanding <= 1;
	end else case ({ M_AXI_AWVALID && M_AXI_AWREADY,
				M_AXI_BVALID && M_AXI_BREADY })
	2'b10: begin
		wr_aw_outstanding <= wr_aw_outstanding + 1;
		wr_aw_zero_outstanding <= 0;
		end
	2'b01: begin
		wr_aw_outstanding <= wr_aw_outstanding - 1;
		wr_aw_zero_outstanding <= (wr_aw_outstanding <= 1);
		end
	default: begin end
	endcase

	initial	wr_aw_max_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_aw_max_outstanding <= 0;
	else if (triggered && (wr_aw_max_outstanding > wr_aw_outstanding))
		wr_aw_max_outstanding <= wr_aw_outstanding;

	initial	wr_w_outstanding = 0;
	initial	wr_w_zero_outstanding = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		wr_w_outstanding <= 0;
		wr_w_zero_outstanding <= 1;
	end else case ({ M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST,
				M_AXI_BVALID && M_AXI_BREADY })
	2'b10: begin
		wr_w_outstanding <= wr_w_outstanding + 1;
		wr_w_zero_outstanding <= 0;
		end
	2'b01: begin
		wr_w_outstanding <= wr_w_outstanding - 1;
		wr_w_zero_outstanding <= (wr_w_outstanding <= 1);
		end
	default: begin end
	endcase

	initial	wr_w_max_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_w_max_outstanding <= 0;
	else if (triggered)
	begin
		if (wr_w_max_outstanding > wr_w_outstanding)
			wr_w_max_outstanding <= wr_w_outstanding;
	end

//	always @(posedge S_AXI_ACLK)
//	if (!S_AXI_ARESETN || clear_request)
//		wr_max_addr_outstanding <= 0;
//	else if (wr_aw_outstanding - wr_max_outstanding
//				> wr_max_addr_outstanding)
//		wr_max_addr_outstanding
//			<= wr_aw_max_outstanding - wr_w_max_outstanding;	

	initial	wr_max_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		wr_max_outstanding <= 0;
	else if (wr_aw_max_outstanding > wr_w_max_outstanding
						+ (wr_in_progress ? 1:0))
		wr_max_outstanding <= wr_aw_max_outstanding;
	else
		wr_max_outstanding <= wr_w_max_outstanding
						+ (wr_in_progress ? 1:0);

	initial	wr_in_progress = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		wr_in_progress <= 0;
	else case ({ M_AXI_WVALID, M_AXI_WLAST })
	2'b10: wr_in_progress <= 1;
	2'b11: wr_in_progress <= 0;
	default: begin end
	endcase

	initial	wr_data_lag      = 0;
	initial	wr_idle_cycles   = 0;
	initial	wr_b_lag_count   = 0;
	initial	wr_b_stall_count = 0;
	initial	wr_slow_data     = 0;
	initial	wr_stall         = 0;
	initial	wr_data_lag      = 0;
	initial	wr_beat          = 0;
	initial	wr_aw_burst      = 0;
	initial	wr_addr_stall    = 0;
	initial	wr_addr_lag      = 0;
	initial	wr_aww_stall     = 0;
	initial	wr_aww_slow      = 0;
	initial	wr_aww_nodata    = 0;
	initial	wr_aww_beat      = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
	begin
		wr_data_lag      <= 0;
		wr_idle_cycles   <= 0;
		wr_b_lag_count   <= 0;
		wr_b_stall_count <= 0;
		wr_slow_data     <= 0;
		wr_stall         <= 0;
		wr_data_lag      <= 0;
		wr_beat          <= 0;
		wr_aw_burst      <= 0;
		wr_addr_stall    <= 0;
		wr_addr_lag      <= 0;
		wr_aww_stall     <= 0;
		wr_aww_slow      <= 0;
		wr_aww_nodata    <= 0;
		wr_aww_beat      <= 0;
	end else if (triggered)
	casez({ !wr_aw_zero_outstanding, !wr_w_zero_outstanding,
		wr_in_progress,
		M_AXI_AWVALID, M_AXI_AWREADY,
		M_AXI_WVALID,  M_AXI_WREADY,
		M_AXI_BVALID,  M_AXI_BREADY })
	9'b0000?0???: wr_idle_cycles   <= wr_idle_cycles   + 1;
	9'b11?????0?: wr_b_lag_count   <= wr_b_lag_count   + 1;
	9'b11?????10: wr_b_stall_count <= wr_b_stall_count + 1;
	9'b11?????11: begin end // BURST count
	9'b101??0???: wr_slow_data <= wr_slow_data  + 1;
	9'b10???10??: wr_stall     <= wr_stall      + 1;
	9'b100??0???: wr_data_lag  <= wr_data_lag   + 1;
	9'b100??11??: wr_beat      <= wr_beat       + 1;
	9'b01?0?????: wr_addr_lag  <= wr_addr_lag   + 1;
	9'b01?11????: wr_aw_burst  <= wr_aw_burst   + 1;
	9'b0??10????: wr_addr_stall<= wr_addr_stall + 1;
	9'b0000?1???: wr_addr_lag  <= wr_addr_lag   + 1;
	9'b0010?????: wr_addr_lag  <= wr_addr_lag   + 1;
	9'b00?1110??: wr_aww_stall <= wr_aww_stall  + 1;
	9'b001110???: wr_aww_slow  <= wr_aww_slow   + 1;
	9'b000110???: wr_aww_nodata<= wr_aww_nodata + 1;
	9'b00?1111??: wr_aww_beat  <= wr_aww_beat   + 1;
	default: begin end
	endcase

	//
	//	AW_O W_O WIP AWV AWR WV WR BV BR
	//	0    0	 0   0       0		IDLE-CYCLE
	//	1    1	            	   0	B-LAG
	//	1    1	            	   1  0	B-STALL
	//	1    1	            	   1  1	(BURSTS COMPLETED)
	//	1    0	 1           0  	W-SLOW
	//	1    0	             1  0	W-STALL
	//	1    0   0           0          DATA-LAG
	//	1    0	             1  1	W-BEAT
	//	0    1       0                  ADDR-LAG
	//	0    1	     1   1       	AW-BURST
	//	0    ?	     1   0       	AW-STALL
	//	0    0   0   0       1          ADDR-LAG
	//	0    0   1   0       1          ADDR-LAG
	//
	//	0    0	     1   1   1  0	W-STALL
	//	0    0	 1   1   1   0  	W-SLOW
	//	0    0   1   0                  ADDR-LAG
	//	0    0   0   1   1   0          DATA-LAG
	//	0    0   0   0       1          ADDR-LAG
	//
	//
	//
	//	      	     1   1       	AW-BURST
	//	      	             1  1	W-BEAT
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read statistics
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_max_burst_size <= 0;
	else if (triggered)
	begin
		if (M_AXI_ARVALID && M_AXI_ARLEN > rd_max_burst_size)
			rd_max_burst_size <= M_AXI_ARLEN;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_burst_count <= 0;
	else if (triggered && M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST)
		rd_burst_count <= rd_burst_count + 1;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_byte_count <= 0;
	else if (triggered && (M_AXI_ARVALID && M_AXI_ARREADY))
		rd_byte_count <= rd_byte_count
			+ (({ 24'h0, M_AXI_ARLEN} + 32'h1)<< M_AXI_ARSIZE);

	initial	rd_beat_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_beat_count <= 0;
	else if (triggered && (M_AXI_RVALID && M_AXI_RREADY))
		rd_beat_count <= rd_beat_count+ 1;


	initial	rd_outstanding_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rd_outstanding_bursts <= 0;
	else case ({ M_AXI_ARVALID && M_AXI_ARREADY,
				M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST})
	2'b10: rd_outstanding_bursts <= rd_outstanding_bursts + 1;
	2'b01: rd_outstanding_bursts <= rd_outstanding_bursts - 1;
	default: begin end
	endcase

	generate for(gk=0; gk < (1<<C_AXI_ID_WIDTH); gk=gk+1)
	begin : PER_ID_READ_STATISTICS

		initial	rd_outstanding_bursts_id[gk]  = 0;	
		initial	rd_nonzero_outstanding_id[gk] = 0;	
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rd_outstanding_bursts_id[gk]  <= 0;
			rd_nonzero_outstanding_id[gk] <= 0;
		end else case(
			{ M_AXI_ARVALID && M_AXI_ARREADY && (M_AXI_ARID == gk),
				M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST
					&& (M_AXI_RID == gk) })
		2'b10: begin
			rd_outstanding_bursts_id[gk]
					<= rd_outstanding_bursts_id[gk] + 1;
			rd_nonzero_outstanding_id[gk] <= 1'b1;
			end
		2'b01: begin
			rd_outstanding_bursts_id[gk]
					<= rd_outstanding_bursts_id[gk] - 1;
			rd_nonzero_outstanding_id[gk]
					<= (rd_outstanding_bursts_id[gk] > 1);
			end
		default: begin end
		endcase

		initial	rd_bursts_in_flight = 0;	
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			rd_bursts_in_flight[gk] <= 0;
		else case({ M_AXI_RVALID && (M_AXI_RID == gk), M_AXI_RLAST })
		2'b10: rd_bursts_in_flight[gk] <= 1'b1;
		2'b11: rd_bursts_in_flight[gk] <= 1'b0;
		default: begin end
		endcase

	end endgenerate

	always @(*)
	begin
		rd_total_in_flight = 0;
		for(ik=0; ik<(1<<C_AXI_ID_WIDTH); ik=ik+1)
		if (rd_bursts_in_flight[ik])
			rd_total_in_flight = rd_total_in_flight + 1;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
	begin
		rd_responding <= 0;
		rd_responding_d <= 0;
	end else if (triggered)
	begin
		rd_responding <= rd_total_in_flight;
		rd_responding_d <= 1;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_max_responding_bursts <= 0;
	else if (rd_responding_d)
	begin
		if (rd_responding > rd_max_responding_bursts)
			rd_max_responding_bursts <= rd_responding;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_max_outstanding_bursts <= 0;
	else if (triggered)
	begin
		if (rd_outstanding_bursts > rd_max_outstanding_bursts)
			rd_max_outstanding_bursts <= rd_outstanding_bursts;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
		rd_ar_stalls <= 0;
	else if (triggered)
	begin
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			rd_ar_stalls <= rd_ar_stalls + 1;
	
		if (M_AXI_RVALID && !M_AXI_RREADY)
			rd_r_stalls <= rd_r_stalls + 1;
	end

	initial	rd_idle_cycles = 0;
	initial	rd_lag_counter = 0;
	initial	rd_slow_link   = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || clear_request)
	begin
		rd_idle_cycles <= 0;
		rd_lag_counter <= 0;
		rd_slow_link   <= 0;
	end else if (triggered)
	begin
		if (!M_AXI_RVALID)
		begin
			if (rd_bursts_in_flight != 0)
				rd_slow_link <= rd_slow_link + 1;
			else if (rd_nonzero_outstanding_id != 0)
				rd_lag_counter <= rd_lag_counter + 1;
			else if (!M_AXI_ARVALID)
				rd_idle_cycles <= rd_idle_cycles + 1;
		end // else if (M_AXI_RREADDY) rd_beat_count <= rd_beat_count+1;
	end


	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT,
			S_AXIL_ARADDR[ADDRLSB-1:0],
			S_AXIL_AWADDR[ADDRLSB-1:0],
			wskd_data, wskd_strb,
			M_AXI_AWBURST, M_AXI_AWLOCK, M_AXI_AWCACHE, M_AXI_AWQOS,
			M_AXI_AWID, M_AXI_AWADDR, M_AXI_ARADDR,
			M_AXI_AWPROT, M_AXI_ARPROT,
			M_AXI_BID, M_AXI_BRESP,
			M_AXI_ARBURST, M_AXI_ARLOCK, M_AXI_ARCACHE, M_AXI_ARQOS,
			M_AXI_WDATA, M_AXI_RDATA,
			M_AXI_RRESP
			};
	// Verilator lint_on  UNUSED
	// }}}
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties used in verfiying this core
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXIL_AWVALID),
		.i_axi_awready(S_AXIL_AWREADY),
		.i_axi_awaddr( S_AXIL_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot( S_AXIL_AWPROT),
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
		.i_axi_arcache(4'h0),
		.i_axi_arprot( S_AXIL_ARPROT),
		//
		.i_axi_rvalid(S_AXIL_RVALID),
		.i_axi_rready(S_AXIL_RREADY),
		.i_axi_rdata( S_AXIL_RDATA),
		.i_axi_rresp( S_AXIL_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	always @(*)
	begin
		assert(faxil_awr_outstanding== (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXIL_RVALID ? 1:0)
			+(S_AXIL_ARREADY ? 0:1));
	end

	//
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXIL_RVALID)
		assert(S_AXIL_RDATA == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// While there are already cover properties in the formal property
	// set above, you'll probably still want to cover something
	// application specific here

	// }}}
	// }}}
`endif
endmodule
