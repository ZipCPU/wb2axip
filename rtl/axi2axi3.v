////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi2axi3.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Bridge from an AXI4 slave to an AXI3 master
//
//	The goal here is to not lose bus resolution, capacity or capability,
//	while bridging from AXI4 to AXI3.  The biggest problem with such
//	a bridge is that we'll need to break large requests (AxLEN>15) up
//	into smaller packets.  After that, everything should work as normal
//	with only minor modifications for AxCACHE.
//
// Opportunity:
//	The cost of this core is very much determined by the number of ID's
//	supported.  It should be possible, with little extra cost or effort,
//	to reduce the ID space herein.  This should be a topic for future
//	exploration.
//
// Status:
//	This core is an unverified first draft.  It has past neither formal
//	nor simulation testing.  Therefore, it is almost certain to have bugs
//	within it.  Use it at your own risk.
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
`default_nettype none
// }}}
//
module	axi2axi3 #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32
		// }}}
	) (
		// {{{
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		// The AXI4 incoming/slave interface
		input	reg				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	reg	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	reg	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	reg	[7:0]			S_AXI_AWLEN,
		input	reg	[2:0]			S_AXI_AWSIZE,
		input	reg	[1:0]			S_AXI_AWBURST,
		input	reg				S_AXI_AWLOCK,
		input	reg	[3:0]			S_AXI_AWCACHE,
		input	reg	[2:0]			S_AXI_AWPROT,
		input	reg	[3:0]			S_AXI_AWQOS,
		//
		//
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire [C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		input	wire				S_AXI_WLAST,
		//
		//
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_BID,
		output	wire	[1:0]			S_AXI_BRESP,
		//
		//
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[7:0]			S_AXI_ARLEN,
		input	wire	[2:0]			S_AXI_ARSIZE,
		input	wire	[1:0]			S_AXI_ARBURST,
		input	wire				S_AXI_ARLOCK,
		input	wire	[3:0]			S_AXI_ARCACHE,
		input	wire	[2:0]			S_AXI_ARPROT,
		input	wire	[3:0]			S_AXI_ARQOS,
		//
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_RID,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire				S_AXI_RLAST,
		output	wire	[1:0]			S_AXI_RRESP,
		//
		//
		// The AXI3 Master (outgoing) interface
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[3:0]			M_AXI_AWLEN,
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
		output	wire	[1:0]			M_AXI_AWLOCK,
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_WID,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		//
		//
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[3:0]			M_AXI_ARLEN,
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
		output	wire	[1:0]			M_AXI_ARLOCK,
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
	);

	//
	localparam		ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3;
	localparam	[0:0]	OPT_LOWPOWER = 1'b0;
	localparam		LGWFIFO = 4;
	localparam		NID = (1<<C_AXI_ID_WIDTH);
	parameter		LGFIFO = 8;

	genvar	ID;

	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// WRITE SIDE
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////
	//
	// Write address channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[7:0]			r_awlen;
	reg	[3:0]			next_wlen;
	wire				awskd_valid;
	reg				awskd_ready;
	wire	[C_AXI_ID_WIDTH-1:0]	awskd_id;
	wire	[C_AXI_ADDR_WIDTH-1:0]	awskd_addr;
	wire	[7:0]			awskd_len;
	wire	[2:0]			awskd_size;
	wire	[1:0]			awskd_burst;
	wire				awskd_lock;
	wire	[3:0]			awskd_cache;
	wire	[2:0]			awskd_prot;
	wire	[3:0]			awskd_qos;
	reg				axi_awvalid;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_awid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	reg	[3:0]			axi_awlen;
	reg	[2:0]			axi_awsize;
	reg	[1:0]			axi_awburst;
	reg	[1:0]			axi_awlock;
	reg	[3:0]			axi_awcache;
	reg	[2:0]			axi_awprot;
	reg	[3:0]			axi_awqos;

	skidbuffer #(
		.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH + 8 + 3 + 2 + 1+4+3+4),
		.OPT_OUTREG(1'b0)
	) awskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWADDR,  S_AXI_AWLEN,
				S_AXI_AWSIZE, S_AXI_AWBURST, S_AXI_AWLOCK,
				S_AXI_AWCACHE,  S_AXI_AWPROT,  S_AXI_AWQOS }),
		.o_valid(awskd_valid), .i_ready(awskd_ready),
			.o_data({ awskd_id,  awskd_addr,  awskd_len,
				awskd_size,  awskd_burst, awskd_lock,
				awskd_cache, awskd_prot,  awskd_qos })
	);

	always @(*)
	begin
		awskd_ready = 1;
		if (r_awlen > 0)
			awskd_ready = 0;
		if (M_AXI_AWVALID && M_AXI_AWREADY)
			awskd_ready = 0;
		if (|wfifo_fill[LGWFIFO:LGWFIFO-1])
			awskd_ready = 0;
	end

	initial	axi_awvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_awvalid <= 0;
	else if (awskd_valid || r_awlen > 0)
		axi_awvalid <= 1;
	else if (M_AXI_AWREADY)
		axi_awvalid <= 0;

	initial	r_awlen = 0;
	initial	axi_awlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		r_awlen <= 0;
		axi_awlen <= 0;
	end else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		if (r_awlen > 15)
		begin
			axi_awlen <= 4'd15;
			r_awlen <= r_awlen - 8'd16;
		end else if (r_awlen > 0)
		begin
			axi_awlen[3:0] <= r_awlen[3:0] - 1;
			r_awlen <= 0;
		end else if (awskd_valid)
		begin
			if (awskd_len > 15)
			begin
				r_awlen <= awskd_len + 1'b1 - 8'd16;
				axi_awlen <= 4'd15;
			end else begin
				r_awlen <= 0;
				axi_awlen <= awskd_len[3:0];
			end
		end else begin
			r_awlen <= 0;
			axi_awlen <= 0;
		end
	end


	always @(posedge S_AXI_ACLK)
	if (awskd_valid && awskd_ready)
		axi_awaddr <= awskd_addr;
	else if (M_AXI_AWVALID && M_AXI_AWREADY)
	begin
		// Verilator lint_off WIDTH
		axi_awaddr <= axi_awaddr + ((M_AXI_AWLEN + 1) << M_AXI_AWSIZE);
		// Verilator lint_on  WIDTH

		case(M_AXI_AWSIZE)
		3'b000: begin end
		3'b001: axi_awaddr[  0] <= 0;
		3'b010: axi_awaddr[1:0] <= 0;
		3'b011: axi_awaddr[2:0] <= 0;
		3'b100: axi_awaddr[3:0] <= 0;
		3'b101: axi_awaddr[4:0] <= 0;
		3'b110: axi_awaddr[5:0] <= 0;
		3'b111: axi_awaddr[6:0] <= 0;
		endcase
	end


	initial	M_AXI_AWSIZE = ADDRLSB[2:0];
	always @(posedge S_AXI_ACLK)
	begin
		if (awskd_valid && awskd_ready)
		begin
			axi_awid     <= awskd_id;
			axi_awsize   <= awskd_size;
			axi_awburst  <= awskd_burst;
			axi_awlock[0]<=awskd_lock;
			axi_awcache  <= awskd_cache;
			axi_awprot   <= awskd_prot;
			axi_awqos    <= awskd_qos;
		end

		if (C_AXI_DATA_WIDTH < 16)
			axi_awsize <= 3'b000;
		else if (C_AXI_DATA_WIDTH < 32)
			axi_awsize[2:1] <= 2'b00;
		else if (C_AXI_DATA_WIDTH < 128)
			axi_awsize[2] <= 1'b0;

		axi_awlock[1] <= 1'b0;
	end

	assign	M_AXI_AWVALID = axi_awvalid;
	assign	M_AXI_AWID    = axi_awid;
	assign	M_AXI_AWADDR  = axi_awaddr;
	assign	M_AXI_AWLEN   = axi_awlen;
	assign	M_AXI_AWSIZE  = axi_awsize;
	assign	M_AXI_AWBURST = axi_awburst;
	assign	M_AXI_AWLOCK  = axi_awlock;
	assign	M_AXI_AWCACHE = axi_awcache;
	assign	M_AXI_AWPROT  = axi_awprot;
	assign	M_AXI_AWQOS   = axi_awqos;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write data channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire				wskd_valid;
	reg				wskd_ready, write_idle;
	wire	[C_AXI_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wskd_strb;
	wire 				wskd_last;
	reg	[4:0]			r_wlen;
	wire	[C_AXI_ID_WIDTH-1:0]	wfifo_id,   raw_wfifo_id;
	wire	[3:0]			wfifo_wlen, raw_wfifo_wlen;
	reg				next_wlast, r_wlast;
	wire				raw_wfifo_last;
	wire				wfifo_empty, wfifo_full;
	wire	[LGWFIFO:0]		wfifo_fill;
	reg				axi_wvalid;
	reg	[C_AXI_DATA_WIDTH-1:0]	axi_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	axi_wstrb;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_wid;
	reg				axi_wlast;

	skidbuffer #(
		.DW(C_AXI_DATA_WIDTH + (C_AXI_DATA_WIDTH/8) + 1),
		.OPT_OUTREG(1'b0)
	) wskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB,  S_AXI_WLAST }),
		.o_valid(wskd_valid), .i_ready(wskd_ready),
			.o_data({ wskd_data,  wskd_strb,  wskd_last })
	);

	always @(*)
		wskd_ready = !M_AXI_WVALID || M_AXI_WREADY;

	initial	axi_wvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_wvalid <= 0;
	else if (wskd_valid)
		axi_wvalid <= 1;
	else if (M_AXI_WREADY)
		axi_wvalid <= 0;

	initial	write_idle = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		write_idle <= 1;
	else if (M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST && !wskd_valid)
		write_idle <= 1;
	else if (wskd_valid && wskd_ready)
		write_idle <= 0;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
	begin
		axi_wdata <= 0;
		axi_wstrb <= 0;
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		axi_wdata <= wskd_data;
		axi_wstrb <= wskd_strb;

		if (OPT_LOWPOWER && !wskd_valid)
		begin
			axi_wdata <= 0;
			axi_wstrb <= 0;
		end
	end

	always @(*)
	begin
		if (r_awlen[7:4] != 0)
			next_wlen = 4'd15;
		else if (r_awlen[3:0] != 0)
			next_wlen = r_awlen[3:0];
		else if (awskd_len[7:4] != 0)
			next_wlen = 4'd15;
		else
			next_wlen = awskd_len[3:0];

		if (r_awlen != 0)
			next_wlast = (r_awlen[7:4] == 0);
		else
			next_wlast = (awskd_len[7:4] == 0);
	end

	sfifo #(.BW(C_AXI_ID_WIDTH+4+1), .LGFLEN(LGWFIFO))
	wfifo(S_AXI_ACLK, !S_AXI_ARESETN,
		(!M_AXI_AWVALID || M_AXI_AWREADY)&&(awskd_valid||(r_awlen > 0))
			&& !write_idle,
		// The length of the next burst
		{ ((r_awlen != 0) ? M_AXI_AWID : awskd_id),
						next_wlen, next_wlast },
		wfifo_full, wfifo_fill,
		//
		(!M_AXI_WVALID || M_AXI_WREADY),
		{ raw_wfifo_id, raw_wfifo_wlen, raw_wfifo_last },
		wfifo_empty);

	assign	wfifo_id   = (wfifo_empty) ? awskd_id  : raw_wfifo_id;
	assign	wfifo_wlen = (wfifo_empty) ? next_wlen : raw_wfifo_wlen;

	initial	r_wlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
		r_wlen <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (r_wlen > 1)
			r_wlen <= r_wlen - 1;
		else if (!wfifo_empty)
			r_wlen <= raw_wfifo_wlen + 1;
		else if (awskd_valid && awskd_ready)
			r_wlen <= next_wlen + 1;
	end

	initial	r_wlast = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
		r_wlast <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (r_wlen > 0)
			r_wlast <= (r_wlen <= 1);
		else
			r_wlast <= raw_wfifo_last;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
	begin
		axi_wid   <= 0;
		axi_wlast <= 0;
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		axi_wid   <= wfifo_id;
		axi_wlast <= r_wlast;

		if (OPT_LOWPOWER && !wskd_valid)
		begin
			axi_wid   <= 0;
			axi_wlast <= 0;
		end
	end

	assign	M_AXI_WVALID = axi_wvalid;
	assign	M_AXI_WDATA  = axi_wdata;
	assign	M_AXI_WSTRB  = axi_wstrb;
	assign	M_AXI_WID    = axi_wid;
	assign	M_AXI_WLAST  = axi_wlast;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write return channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire				bskd_valid;
	reg				bskd_ready;
	wire	[C_AXI_ID_WIDTH-1:0]	bskd_id;
	wire	[1:0]			bskd_resp;
	reg	[1:0]			bburst_err	[0:NID-1];
	reg	[NID-1:0]		wbfifo_valid;
	reg	[NID-1:0]		wbfifo_last;
	reg				axi_bvalid;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_bid;
	reg	[1:0]			axi_bresp;

	skidbuffer #(.DW(C_AXI_ID_WIDTH + 2), .OPT_OUTREG(1'b0)
	) bskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(M_AXI_BVALID), .o_ready(M_AXI_BREADY),
			.i_data({ M_AXI_BID, M_AXI_BRESP }),
		.o_valid(bskd_valid), .i_ready(bskd_ready),
			.o_data({ bskd_id, bskd_resp })
	);

	generate for(ID=0; ID < NID; ID = ID + 1)
	begin : WRITE_BURST_TRACKING
		wire			wbfifo_empty, wbfifo_full;
		wire	[LGFIFO:0]	wbfifo_fill;

		initial	wbfifo_valid[ID] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			wbfifo_valid[ID] <= 0;
		else if (!wbfifo_valid[ID] && !wbfifo_empty)
			wbfifo_valid[ID] <= 1;
		else if (bskd_valid && bskd_ready && bskd_id==ID)
			wbfifo_valid[ID] <= !wbfifo_empty;

		sfifo #(.BW(1), .LGFLEN(LGFIFO))
		wbfifo(S_AXI_ACLK, !S_AXI_ARESETN,
			(M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST)
				&& (M_AXI_WID == ID),
			(r_wlen == 0) ? 1'b1 : 1'b0,
			wbfifo_full, wbfifo_fill,
			//
			(!wbfifo_valid[ID] || (M_AXI_BVALID && M_AXI_BREADY
					&& M_AXI_BID == ID)),
			wbfifo_last[ID], wbfifo_empty
		);

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, wbfifo_full, wbfifo_fill };
		// Verilator lint_on  UNUSED

	end endgenerate

	always @(*)
		bskd_ready = (!S_AXI_BVALID || S_AXI_BREADY);

	initial	axi_bvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_bvalid <= 1'b0;
	else if (bskd_valid && bskd_ready)
		axi_bvalid <= wbfifo_last[bskd_id];
	else if (M_AXI_BREADY)
		axi_bvalid <= 1'b0;

	generate for(ID=0; ID < NID; ID = ID + 1)
	begin : WRITE_ERR_BY_ID

		initial	bburst_err[ID] = 2'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bburst_err[ID] <= 2'b0;
		else if (S_AXI_BVALID && S_AXI_BREADY && S_AXI_BID == ID
				&& wbfifo_last[ID])
			bburst_err[ID] <= 2'b0;
		else if (bskd_valid && bskd_id == ID)
			bburst_err[ID] <= bburst_err[ID] | bskd_resp;

	end endgenerate

	initial	axi_bid   = 0;
	initial	axi_bresp = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
	begin
		axi_bid   <= 0;
		axi_bresp <= 0;
	end else if (!S_AXI_BVALID || S_AXI_BREADY)
	begin
		axi_bid   <= bskd_id;
		axi_bresp <= bskd_resp | bburst_err[bskd_id];

		if (OPT_LOWPOWER && !bskd_valid)
		begin
			axi_bid   <= 0;
			axi_bresp <= 0;
		end
	end

	assign	S_AXI_BVALID = axi_bvalid;
	assign	S_AXI_BID    = axi_bid;
	assign	S_AXI_BRESP  = axi_bresp;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// READ SIDE
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////
	//
	// Read address channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[7:0]			r_arlen;
	wire				arskd_valid;
	reg				arskd_ready;
	wire	[C_AXI_ID_WIDTH-1:0]	arskd_id;
	wire	[C_AXI_ADDR_WIDTH-1:0]	arskd_addr;
	wire	[7:0]			arskd_len;
	wire	[2:0]			arskd_size;
	wire	[1:0]			arskd_burst;
	wire				arskd_lock;
	wire	[3:0]			arskd_cache;
	wire	[2:0]			arskd_prot;
	wire	[3:0]			arskd_qos;
	reg				axi_arvalid;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_arid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_araddr;
	reg	[3:0]			axi_arlen;
	reg	[2:0]			axi_arsize;
	reg	[1:0]			axi_arburst;
	reg	[1:0]			axi_arlock;
	reg	[3:0]			axi_arcache;
	reg	[2:0]			axi_arprot;
	reg	[3:0]			axi_arqos;

	skidbuffer #(
		.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH + 8 + 3 + 2 + 1+4+3+4),
		.OPT_OUTREG(1'b0)
	) arskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data({ S_AXI_ARID, S_AXI_ARADDR,  S_AXI_ARLEN,
				S_AXI_ARSIZE, S_AXI_ARBURST, S_AXI_ARLOCK,
				S_AXI_ARCACHE,  S_AXI_ARPROT,  S_AXI_ARQOS }),
		.o_valid(arskd_valid), .i_ready(arskd_ready),
			.o_data({ arskd_id,  arskd_addr,  arskd_len,
				arskd_size,  arskd_burst, arskd_lock,
				arskd_cache, arskd_prot,  arskd_qos })
	);

	always @(*)
	begin
		arskd_ready = 1;
		if (r_arlen > 0)
			arskd_ready = 0;
		if (M_AXI_ARVALID && M_AXI_ARREADY)
			arskd_ready = 0;
	end

	initial	axi_arvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_arvalid <= 1'b0;
	else if (r_arlen > 0)
		axi_arvalid <= 1'b1;
	else if (arskd_ready)
		axi_arvalid <= 1'b1;
	else if (M_AXI_ARREADY)
		axi_arvalid <= 1'b0;

	initial	r_arlen = 0;
	initial	M_AXI_ARLEN = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		r_arlen   <= 0;
		axi_arlen <= 0;
	end else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		if (r_arlen[7:4] != 0)
		begin
			axi_arlen <= 4'd15;
			r_arlen <= r_arlen - 16;
		end else if (r_arlen[3:0] != 0)
		begin
			axi_arlen <= r_arlen[3:0] - 1;
			r_arlen <= 0;
		end else if (arskd_valid)
		begin
			if (arskd_len[7:4] != 0)
			begin
				r_arlen <= arskd_len + 1 - 16;
				axi_arlen <= 4'd15;
			end else begin
				r_arlen <= 0;
				axi_arlen <= arskd_len[3:0];
			end
		end else begin
			r_arlen <= 0;
			axi_arlen <= 0;
		end
	end


	always @(posedge S_AXI_ACLK)
	if (arskd_valid && arskd_ready)
		axi_araddr <= arskd_addr;
	else if (M_AXI_ARVALID && M_AXI_ARREADY)
	begin
		// Verilator lint_off WIDTH
		axi_araddr <= axi_araddr + ((M_AXI_ARLEN + 1) << M_AXI_ARSIZE);
		// Verilator lint_on  WIDTH

		case(M_AXI_AWSIZE)
		3'b000: begin end
		3'b001: axi_araddr[  0] <= 0;
		3'b010: axi_araddr[1:0] <= 0;
		3'b011: axi_araddr[2:0] <= 0;
		3'b100: axi_araddr[3:0] <= 0;
		3'b101: axi_araddr[4:0] <= 0;
		3'b110: axi_araddr[5:0] <= 0;
		3'b111: axi_araddr[6:0] <= 0;
		endcase
	end

	initial	axi_arsize = ADDRLSB[2:0];
	always @(posedge S_AXI_ACLK)
	begin
		if (arskd_valid && arskd_ready)
		begin
			axi_arid      <= arskd_id;
			axi_arsize    <= arskd_size;
			axi_arburst   <= arskd_burst;
			axi_arlock[0] <= arskd_lock;
			axi_arcache   <= arskd_cache;
			axi_arprot    <= arskd_prot;
			axi_arqos     <= arskd_qos;
		end

		// Propagate constants, to help the optimizer out out a touch
		axi_arlock[1] <= 1'b0;

		if (C_AXI_DATA_WIDTH < 16)
			axi_arsize <= 3'b000;
		else if (C_AXI_DATA_WIDTH < 32)
			axi_arsize[2:1] <= 2'b00;
		else if (C_AXI_DATA_WIDTH < 128)
			axi_arsize[2] <= 1'b0;
	end

	generate for(ID=0; ID < NID; ID = ID + 1)
	begin : READ_BURST_TRACKING
		wire			rbfifo_empty, rbfifo_full;
		wire	[LGFIFO:0]	rbfifo_fill;

		initial	rbfifo_valid[ID] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			rbfifo_valid[ID] <= 0;
		else if (!rbfifo_valid[ID] && !rbfifo_empty)
			rbfifo_valid[ID] <= 1;
		else if (rskd_valid && rskd_ready && rskd_last && rskd_id==ID)
			rbfifo_valid[ID] <= !rbfifo_empty;

		sfifo #(.BW(1), .LGFLEN(LGFIFO))
		rbfifo(S_AXI_ACLK, !S_AXI_ARESETN,
			(!M_AXI_ARVALID || M_AXI_ARREADY)
				&& (((r_arlen>0)&&(M_AXI_ARID==ID))
					|| (arskd_valid && arskd_id == ID)),
			((arskd_valid && arskd_ready && arskd_len <= 15)
				||(r_arlen <= 15)) ? 1'b1 : 1'b0,
			rbfifo_full, rbfifo_fill,
			//
			(!rbfifo_valid[ID] || (M_AXI_RVALID && M_AXI_RREADY
					&& M_AXI_RID == ID && M_AXI_RLAST)),
			rid_last[ID], rbfifo_empty
		);

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, rbfifo_full, rbfifo_fill };
		// Verilator lint_on  UNUSED
	end endgenerate

	assign	M_AXI_ARVALID= axi_arvalid;
	assign	M_AXI_ARID   = axi_arid;
	assign	M_AXI_ARADDR = axi_araddr;
	assign	M_AXI_ARLEN  = axi_arlen;
	assign	M_AXI_ARSIZE = axi_arsize;
	assign	M_AXI_ARBURST= axi_arburst;
	assign	M_AXI_ARLOCK = axi_arlock;
	assign	M_AXI_ARCACHE= axi_arcache;
	assign	M_AXI_ARPROT = axi_arprot;
	assign	M_AXI_ARQOS  = axi_arqos;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read data channel
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire				rskd_valid;
	reg				rskd_ready;
	wire	[C_AXI_ID_WIDTH-1:0]	rskd_id;
	wire	[C_AXI_DATA_WIDTH-1:0]	rskd_data;
	wire				rskd_last;
	wire	[1:0]			rskd_resp;
	reg	[1:0]			rburst_err	[0:NID-1];
	reg	[NID-1:0]		rbfifo_valid;
	reg	[NID-1:0]		rid_last;
	reg				axi_rvalid;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_rid;
	reg	[C_AXI_DATA_WIDTH-1:0]	axi_rdata;
	reg				axi_rlast;
	reg	[1:0]			axi_rresp;

	skidbuffer #(
		.DW(C_AXI_DATA_WIDTH + C_AXI_ID_WIDTH + 3),
		.OPT_OUTREG(1'b0)
	) rskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(M_AXI_RVALID), .o_ready(M_AXI_RREADY),
			.i_data({ M_AXI_RID, M_AXI_RDATA,  M_AXI_RLAST,
				M_AXI_RRESP }),
		.o_valid(rskd_valid), .i_ready(rskd_ready),
			.o_data({ rskd_id,  rskd_data,  rskd_last, rskd_resp })
	);

	always @(*)
		rskd_ready = !S_AXI_RVALID || S_AXI_RREADY;

	initial	axi_rvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_rvalid <= 1'b0;
	else if (rskd_valid && rskd_ready)
		axi_rvalid <= 1'b1;
	else if (S_AXI_RREADY)
		axi_rvalid <= 1'b0;

	generate for(ID=0; ID < NID; ID = ID + 1)
	begin : READ_ERR_BY_ID

		initial	rburst_err[ID] = 2'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			rburst_err[ID] <= 2'b0;
		else if (S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST
				&& S_AXI_RID == ID)
			rburst_err[ID] <= 2'b0;
		else if (rskd_valid && rskd_id == ID)
			rburst_err[ID] <= rburst_err[ID] | rskd_resp;

	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		axi_rid   <= rskd_id;
		axi_rdata <= rskd_data;
		axi_rresp <= rskd_resp | rburst_err[rskd_id];
		axi_rlast <= rid_last[rskd_id] && rskd_last;
	end

	assign	S_AXI_RVALID= axi_rvalid;
	assign	S_AXI_RID   = axi_rid;
	assign	S_AXI_RDATA = axi_rdata;
	assign	S_AXI_RRESP = axi_rresp;
	assign	S_AXI_RLAST = axi_rlast;
	// }}}
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, wfifo_fill[LGWFIFO-2:0], wskd_last,
			wfifo_wlen, wfifo_full };
	// Verilator lint_on UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
//
// This design has not been formally verified.
//
`endif
endmodule
