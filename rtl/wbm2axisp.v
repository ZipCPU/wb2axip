////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbm2axisp.v (Wishbone master to AXI slave, pipelined)
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	The B4 Wishbone SPEC allows transactions at a speed as fast as
//		one per clock.  The AXI bus allows transactions at a speed of
//	one read and one write transaction per clock.  These capabilities work
//	by allowing requests to take place prior to responses, such that the
//	requests might go out at once per clock and take several clocks, and
//	the responses may start coming back several clocks later.  In other
//	words, both protocols allow multiple transactions to be "in flight" at
//	the same time.  Current wishbone to AXI converters, however, handle only
//	one transaction at a time: initiating the transaction, and then waiting
//	for the transaction to complete before initiating the next.
//
//	The purpose of this core is to maintain the speed of both buses, while
//	transiting from the Wishbone (as master) to the AXI bus (as slave) and
//	back again.
//
//	Since the AXI bus allows transactions to be reordered, whereas the
//	wishbone does not, this core can be configured to reorder return
//	transactions as well.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2020, Gisselquist Technology, LLC
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
//
module wbm2axisp #(
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	=  28,	// AXI Address width (log wordsize)
	parameter C_AXI_ID_WIDTH	=   1,
	parameter DW			=  32,	// Wishbone data width
	parameter AW			=  26,	// Wishbone address width (log wordsize)
	parameter [C_AXI_ID_WIDTH-1:0] AXI_READ_ID = 1'b1,
	parameter [C_AXI_ID_WIDTH-1:0] AXI_WRITE_ID = 1'b0,
	parameter LGFIFO		=   6
	) (
	(* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME M_AXI_ACLK, ASSOCIATED_BUSIF M_AXI" *)
	// , ASSOCIATED_RESET S_AXI_ARESETN, FREQ_HZ 80000000, PHASE 0.000" *)
	(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 M_AXI_ACLK CLK" *)     input	wire			i_clk,	// System clock
	input	wire			i_reset,// Reset signal,drives AXI rst

	// AXI write address channel signals
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWVALID" *)   output	reg			o_axi_awvalid,	// Write address valid
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREADY" *)   input	wire			i_axi_awready, // Slave is ready to accept
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWID" *)      output	wire	[C_AXI_ID_WIDTH-1:0]	o_axi_awid,	// Write ID
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWADDR" *)    output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_awaddr,	// Write address
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLEN" *)     output	wire	[7:0]		o_axi_awlen,	// Write Burst Length
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWSIZE" *)    output	wire	[2:0]		o_axi_awsize,	// Write Burst size
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWBURST" *)   output	wire	[1:0]		o_axi_awburst,	// Write Burst type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLOCK" *)    output	wire	[0:0]		o_axi_awlock,	// Write lock type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWCACHE" *)   output	wire	[3:0]		o_axi_awcache,	// Write Cache type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWPROT" *)    output	wire	[2:0]		o_axi_awprot,	// Write Protection type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWQOS" *)     output	wire	[3:0]		o_axi_awqos,	// Write Quality of Svc

// AXI write data channel signals
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WVALID" *)    output	reg			o_axi_wvalid,	// Write valid
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WREADY" *)    input	wire			i_axi_wready,  // Write data ready
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WDATA" *)     output	reg	[C_AXI_DATA_WIDTH-1:0]	o_axi_wdata,	// Write data
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WSTRB" *)     output	reg	[C_AXI_DATA_WIDTH/8-1:0] o_axi_wstrb,	// Write strobes
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WLAST" *)     output	wire			o_axi_wlast,	// Last write transaction

// AXI write response channel signals
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BVALID" *)    input	wire			i_axi_bvalid,  // Write reponse valid
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BREADY" *)    output	wire			o_axi_bready,  // Response ready
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BID" *)       input wire [C_AXI_ID_WIDTH-1:0]	i_axi_bid,	// Response ID
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BRESP" *)     input	wire [1:0]		i_axi_bresp,	// Write response

// AXI read address channel signals
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARVALID" *)   output	reg			o_axi_arvalid,	// Read address valid
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREADY" *)   input	wire			i_axi_arready,	// Read address ready
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARID" *)      output	wire	[C_AXI_ID_WIDTH-1:0]	o_axi_arid,	// Read ID
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARADDR" *)    output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_araddr,	// Read address
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLEN" *)     output	wire	[7:0]		o_axi_arlen,	// Read Burst Length
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARSIZE" *)    output	wire	[2:0]		o_axi_arsize,	// Read Burst size
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARBURST" *)   output	wire	[1:0]		o_axi_arburst,	// Read Burst type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLOCK" *)    output	wire	[0:0]		o_axi_arlock,	// Read lock type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARCACHE" *)   output	wire	[3:0]		o_axi_arcache,	// Read Cache type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARPROT" *)    output	wire	[2:0]		o_axi_arprot,	// Read Protection type
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARQOS" *)     output	wire	[3:0]		o_axi_arqos,	// Read Protection type

// AXI read data channel signals
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RVALID" *)    input	wire			i_axi_rvalid,  // Read reponse valid
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RREADY" *)    output	wire			o_axi_rready,  // Read Response ready
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RID" *)       input wire [C_AXI_ID_WIDTH-1:0]	i_axi_rid,     // Response ID
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RDATA" *)     input wire [C_AXI_DATA_WIDTH-1:0] i_axi_rdata,    // Read data
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RRESP" *)     input	wire	[1:0]		i_axi_rresp,   // Read response
	(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RLAST" *)     input	wire			i_axi_rlast,    // Read last

	// We'll share the clock and the reset
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS CYC" *)      input	wire			i_wb_cyc,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS STB" *)      input	wire			i_wb_stb,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS WE" *)       input	wire			i_wb_we,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS ADR" *)      input	wire	[(AW-1):0]	i_wb_addr,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS DAT_MOSI" *) input	wire	[(DW-1):0]	i_wb_data,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS SEL" *)      input	wire	[(DW/8-1):0]	i_wb_sel,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS STALL" *)    output	reg			o_wb_stall,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS ACK" *)      output	reg			o_wb_ack,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS DAT_MISO" *) output	reg	[(DW-1):0]	o_wb_data,
	(* X_INTERFACE_INFO = "opencores.org:bus:wishbone4:4.0 WBS ERR" *)      output	reg			o_wb_err
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	LG_AXI_DW	= $clog2(C_AXI_DATA_WIDTH);
	localparam	LG_WB_DW	= $clog2(DW);
	localparam	FIFOLN = (1<<LGFIFO);
	localparam	SUBW = LG_AXI_DW-LG_WB_DW;


//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

// Things we're not changing ...
	localparam	DWSIZE = $clog2(DW)-3;
	assign o_axi_awid    = AXI_WRITE_ID;
	assign o_axi_awlen   = 8'h0;	// Burst length is one
	assign o_axi_awsize  = DWSIZE[2:0];
	assign o_axi_wlast   = 1;
	assign o_axi_awburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_awlock  = 1'b0;	// Normal signaling
	assign o_axi_arlock  = 1'b0;	// Normal signaling
	assign o_axi_awcache = 4'h2;	// Normal: no cache, no buffer
	//
	assign o_axi_arid    = AXI_READ_ID;
	assign o_axi_arlen   = 8'h0;	// Burst length is one
	assign o_axi_arsize  = DWSIZE[2:0];
	assign o_axi_arburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_arcache = 4'h2;	// Normal: no cache, no buffer
	assign o_axi_awprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_arprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_awqos   = 4'h0;	// Lowest quality of service (unused)
	assign o_axi_arqos   = 4'h0;	// Lowest quality of service (unused)

	// wire	[(C_AXI_DATA_WIDTH>DW ? $clog2(C_AXI_DATA_WIDTH/DW):0)+$clog2(DW)-4:0]	axi_lsbs;
	wire	[$clog2(DW)-4:0]	axi_lsbs;
	assign	axi_lsbs = 0;

	reg			direction, full, empty, flushing, nearfull;
	reg	[LGFIFO:0]	npending;
	//
	reg			r_stb, r_we, m_valid, m_we, m_ready;
	reg	[AW-1:0]	r_addr, m_addr;
	reg	[DW-1:0]	r_data, m_data;
	reg	[DW/8-1:0]	r_sel,  m_sel;

// Command logic
	initial	direction = 0;
	always @(posedge i_clk)
	if (empty && m_ready)
		direction <= m_we;

	initial	npending = 0;
	initial	empty    = 1;
	initial	full     = 0;
	initial	nearfull = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		npending <= 0;
		empty    <= 1;
		full     <= 0;
		nearfull <= 0;
	end else case ({m_valid && m_ready, i_axi_bvalid||i_axi_rvalid})
	2'b10: begin
		npending <= npending + 1;
		empty <= 0;
		nearfull <= &(npending[LGFIFO-1:1]);
		full <= &(npending[LGFIFO-1:0]);
		end
	2'b01: begin
		nearfull <= full;
		npending <= npending - 1;
		empty <= (npending == 1);
		full <= 0;
		end
	default: begin end
	endcase

	initial	flushing = 0;
	always @(posedge i_clk)
	if (i_reset)
		flushing <= 0;
	else if ((i_axi_rvalid && i_axi_rresp[1])
		||(i_axi_bvalid && i_axi_bresp[1])
		||(!i_wb_cyc && !empty))
		flushing <= 1'b1;
	else if (empty)
		flushing <= 1'b0;

	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone input skidbuffer
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	r_stb = 0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		r_stb <= 0;
	else if (m_ready)
		r_stb <= 1'b0;
	else if (!o_wb_stall)
		// Double buffer a transaction
		r_stb <= i_wb_stb;

	always @(posedge i_clk)
	if (!o_wb_stall)
	begin
		// Double buffer a transaction
		r_we  <= i_wb_we;
		r_addr<= i_wb_addr;
		r_data<= i_wb_data;
		r_sel <= i_wb_sel;
	end

	always @(*)
		o_wb_stall = r_stb;

	always @(*)
	begin
		m_valid = (i_wb_stb || r_stb) && i_wb_cyc;
		m_we    = r_stb ? r_we   : i_wb_we;
		m_addr  = r_stb ? r_addr : i_wb_addr;
		m_data  = r_stb ? r_data : i_wb_data;
		m_sel   = r_stb ? r_sel  : i_wb_sel;

		if (flushing || nearfull || ((m_we != direction)&&(!empty)))
			m_ready = 1'b0;
		else if (m_we)
			m_ready = (!o_axi_awvalid || i_axi_awready)
				&&(!o_axi_wvalid || i_axi_wready);
		else
			m_ready = (!o_axi_arvalid || i_axi_arready);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// AXI Signaling
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Send write transactions
	initial	o_axi_awvalid = 0;
	initial	o_axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_axi_awvalid <= 0;
		o_axi_wvalid  <= 0;
	end else if (m_valid && m_we && m_ready)
	begin
		o_axi_awvalid <= 1;
		o_axi_wvalid  <= 1;
	end else begin
		if (i_axi_awready)
			o_axi_awvalid <= 0;
		if (i_axi_wready)
			o_axi_wvalid <= 0;
	end

	always @(posedge i_clk)
	if (!o_axi_wvalid || i_axi_wready)
		o_axi_wdata   <= {(C_AXI_DATA_WIDTH/DW){m_data}};

	// Send read transactions
	initial	o_axi_arvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_arvalid <= 0;
	else if (m_valid && !m_we && m_ready)
		o_axi_arvalid <= 1;
	else if (i_axi_arready)
	begin
		o_axi_arvalid <= 0;
	end

	generate if (DW == 8)
	begin

		always @(posedge i_clk)
		if (!o_axi_awvalid || i_axi_awready)
			o_axi_awaddr  <= m_addr;

		always @(posedge i_clk)
		if (!o_axi_arvalid || i_axi_arready)
			o_axi_araddr  <= m_addr;

	end else begin
		always @(posedge i_clk)
		if (!o_axi_awvalid || i_axi_awready)
			o_axi_awaddr  <= { m_addr, axi_lsbs };

		always @(posedge i_clk)
		if (!o_axi_arvalid || i_axi_arready)
			o_axi_araddr  <= { m_addr, axi_lsbs };

	end endgenerate


	generate if (DW == C_AXI_DATA_WIDTH)
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready)
			o_axi_wstrb   <= m_sel;

	end else if (DW*2 == C_AXI_DATA_WIDTH)
	// {{{
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready)
		begin
			if (m_addr[0])
				o_axi_wstrb   <= { m_sel, {(DW/8){1'b0}} };
			else
				o_axi_wstrb   <= { {(DW/8){1'b0}}, m_sel };
		end

	end else if (DW*4 == C_AXI_DATA_WIDTH)
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready) case(~m_addr[1:0])
		2'b00: o_axi_wstrb   <= { m_sel, {(3*DW/8){1'b0}} };
		2'b01: o_axi_wstrb   <= { {(  DW/8){1'b0}}, m_sel, {(2*DW/8){1'b0}} };
		2'b10: o_axi_wstrb   <= { {(2*DW/8){1'b0}}, m_sel, {(  DW/8){1'b0}} };
		2'b11: o_axi_wstrb   <= { {(3*DW/8){1'b0}}, m_sel };
		endcase

	end else if (DW*8 == C_AXI_DATA_WIDTH)
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready) case(~m_addr[2:0])
		3'b000: o_axi_wstrb   <= { m_sel, {(7*DW/8){1'b0}} };
		3'b001: o_axi_wstrb   <= { {(  DW/8){1'b0}}, m_sel, {(6*DW/8){1'b0}} };
		3'b010: o_axi_wstrb   <= { {(2*DW/8){1'b0}}, m_sel, {(5*DW/8){1'b0}} };
		3'b011: o_axi_wstrb   <= { {(3*DW/8){1'b0}}, m_sel, {(4*DW/8){1'b0}} };
		3'b100: o_axi_wstrb   <= { {(4*DW/8){1'b0}}, m_sel, {(3*DW/8){1'b0}} };
		3'b101: o_axi_wstrb   <= { {(5*DW/8){1'b0}}, m_sel, {(2*DW/8){1'b0}} };
		3'b110: o_axi_wstrb   <= { {(6*DW/8){1'b0}}, m_sel, {(  DW/8){1'b0}} };
		3'b111: o_axi_wstrb   <= { {(7*DW/8){1'b0}}, m_sel };
		endcase

	end else if (DW*16 == C_AXI_DATA_WIDTH)
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready) case(~m_addr[3:0])
		4'b0000: o_axi_wstrb   <= { m_sel, {(15*DW/8){1'b0}} };
		4'b0001: o_axi_wstrb   <= { {(   DW/8){1'b0}}, m_sel, {(14*DW/8){1'b0}} };
		4'b0010: o_axi_wstrb   <= { {( 2*DW/8){1'b0}}, m_sel, {(13*DW/8){1'b0}} };
		4'b0011: o_axi_wstrb   <= { {( 3*DW/8){1'b0}}, m_sel, {(12*DW/8){1'b0}} };
		4'b0100: o_axi_wstrb   <= { {( 4*DW/8){1'b0}}, m_sel, {(11*DW/8){1'b0}} };
		4'b0101: o_axi_wstrb   <= { {( 5*DW/8){1'b0}}, m_sel, {(10*DW/8){1'b0}} };
		4'b0110: o_axi_wstrb   <= { {( 6*DW/8){1'b0}}, m_sel, {( 9*DW/8){1'b0}} };
		4'b0111: o_axi_wstrb   <= { {( 7*DW/8){1'b0}}, m_sel, {( 8*DW/8){1'b0}} };
		4'b1000: o_axi_wstrb   <= { {( 8*DW/8){1'b0}}, m_sel, {( 7*DW/8){1'b0}} };
		4'b1001: o_axi_wstrb   <= { {( 9*DW/8){1'b0}}, m_sel, {( 6*DW/8){1'b0}} };
		4'b1010: o_axi_wstrb   <= { {(10*DW/8){1'b0}}, m_sel, {( 5*DW/8){1'b0}} };
		4'b1011: o_axi_wstrb   <= { {(11*DW/8){1'b0}}, m_sel, {( 4*DW/8){1'b0}} };
		4'b1100: o_axi_wstrb   <= { {(12*DW/8){1'b0}}, m_sel, {( 3*DW/8){1'b0}} };
		4'b1101: o_axi_wstrb   <= { {(13*DW/8){1'b0}}, m_sel, {( 2*DW/8){1'b0}} };
		4'b1110: o_axi_wstrb   <= { {(14*DW/8){1'b0}}, m_sel, {(   DW/8){1'b0}} };
		4'b1111: o_axi_wstrb   <= { {(15*DW/8){1'b0}}, m_sel };
		endcase

	end else if (DW*32 == C_AXI_DATA_WIDTH)
	begin

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready) case(~m_addr[4:0])
		5'b00000: o_axi_wstrb   <= { m_sel, {(31*DW/8){1'b0}} };
		5'b00001: o_axi_wstrb   <= { {(   DW/8){1'b0}}, m_sel, {(30*DW/8){1'b0}} };
		5'b00010: o_axi_wstrb   <= { {( 2*DW/8){1'b0}}, m_sel, {(29*DW/8){1'b0}} };
		5'b00011: o_axi_wstrb   <= { {( 3*DW/8){1'b0}}, m_sel, {(28*DW/8){1'b0}} };
		5'b00100: o_axi_wstrb   <= { {( 4*DW/8){1'b0}}, m_sel, {(27*DW/8){1'b0}} };
		5'b00101: o_axi_wstrb   <= { {( 5*DW/8){1'b0}}, m_sel, {(26*DW/8){1'b0}} };
		5'b00110: o_axi_wstrb   <= { {( 6*DW/8){1'b0}}, m_sel, {(25*DW/8){1'b0}} };
		5'b00111: o_axi_wstrb   <= { {( 7*DW/8){1'b0}}, m_sel, {(24*DW/8){1'b0}} };
		5'b01000: o_axi_wstrb   <= { {( 8*DW/8){1'b0}}, m_sel, {(23*DW/8){1'b0}} };
		5'b01001: o_axi_wstrb   <= { {( 9*DW/8){1'b0}}, m_sel, {(22*DW/8){1'b0}} };
		5'b01010: o_axi_wstrb   <= { {(10*DW/8){1'b0}}, m_sel, {(21*DW/8){1'b0}} };
		5'b01011: o_axi_wstrb   <= { {(11*DW/8){1'b0}}, m_sel, {(20*DW/8){1'b0}} };
		5'b01100: o_axi_wstrb   <= { {(12*DW/8){1'b0}}, m_sel, {(19*DW/8){1'b0}} };
		5'b01101: o_axi_wstrb   <= { {(13*DW/8){1'b0}}, m_sel, {(18*DW/8){1'b0}} };
		5'b01110: o_axi_wstrb   <= { {(14*DW/8){1'b0}}, m_sel, {(17*DW/8){1'b0}} };
		5'b01111: o_axi_wstrb   <= { {(15*DW/8){1'b0}}, m_sel, {(16*DW/8){1'b0}} };
		5'b10000: o_axi_wstrb   <= { {(16*DW/8){1'b0}}, m_sel, {(15*DW/8){1'b0}} };
		5'b10001: o_axi_wstrb   <= { {(17*DW/8){1'b0}}, m_sel, {(14*DW/8){1'b0}} };
		5'b10010: o_axi_wstrb   <= { {(18*DW/8){1'b0}}, m_sel, {(13*DW/8){1'b0}} };
		5'b10011: o_axi_wstrb   <= { {(19*DW/8){1'b0}}, m_sel, {(12*DW/8){1'b0}} };
		5'b10100: o_axi_wstrb   <= { {(20*DW/8){1'b0}}, m_sel, {(11*DW/8){1'b0}} };
		5'b10101: o_axi_wstrb   <= { {(21*DW/8){1'b0}}, m_sel, {(10*DW/8){1'b0}} };
		5'b10110: o_axi_wstrb   <= { {(22*DW/8){1'b0}}, m_sel, {( 9*DW/8){1'b0}} };
		5'b10111: o_axi_wstrb   <= { {(23*DW/8){1'b0}}, m_sel, {( 8*DW/8){1'b0}} };
		5'b11000: o_axi_wstrb   <= { {(24*DW/8){1'b0}}, m_sel, {( 7*DW/8){1'b0}} };
		5'b11001: o_axi_wstrb   <= { {(25*DW/8){1'b0}}, m_sel, {( 6*DW/8){1'b0}} };
		5'b11010: o_axi_wstrb   <= { {(26*DW/8){1'b0}}, m_sel, {( 5*DW/8){1'b0}} };
		5'b11011: o_axi_wstrb   <= { {(27*DW/8){1'b0}}, m_sel, {( 4*DW/8){1'b0}} };
		5'b11100: o_axi_wstrb   <= { {(28*DW/8){1'b0}}, m_sel, {( 3*DW/8){1'b0}} };
		5'b11101: o_axi_wstrb   <= { {(29*DW/8){1'b0}}, m_sel, {( 2*DW/8){1'b0}} };
		5'b11110: o_axi_wstrb   <= { {(30*DW/8){1'b0}}, m_sel, {(   DW/8){1'b0}} };
		5'b11111: o_axi_wstrb   <= { {(31*DW/8){1'b0}}, m_sel };
		endcase
	// }}}
	end endgenerate

	generate if (DW == C_AXI_DATA_WIDTH)
	begin : NO_READ_DATA_SELECT_NECESSARY

		always @(*)
			o_wb_data = i_axi_rdata;

		always @(*)
			o_wb_ack = !flushing&&((i_axi_rvalid && !i_axi_rresp[1])
				||(i_axi_bvalid && !i_axi_bresp[1]));

		always @(*)
			o_wb_err = !flushing&&((i_axi_rvalid && i_axi_rresp[1])
				||(i_axi_bvalid && i_axi_bresp[1]));

	end else begin : READ_FIFO_DATA_SELECT
	// {{{

		reg	[SUBW-1:0]	addr_fifo	[0:(1<<LGFIFO)-1];
		reg	[SUBW-1:0]	fifo_value;
		reg	[LGFIFO:0]	wr_addr, rd_addr;

		initial	o_wb_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc)
			o_wb_ack <= 0;
		else
			o_wb_ack <= !flushing
				&&((i_axi_rvalid && !i_axi_rresp[1])
				||(i_axi_bvalid && !i_axi_bresp[1]));

		initial	o_wb_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc)
			o_wb_err <= 0;
		else
			o_wb_err <= (!flushing)&&((i_axi_rvalid && i_axi_rresp[1])
				||(i_axi_bvalid && i_axi_bresp[1]));


		initial	wr_addr = 0;
		always @(posedge i_clk)
		if (i_reset)
			wr_addr <= 0;
		else if (m_valid && m_ready)
			wr_addr <= wr_addr + 1;

		always @(posedge i_clk)
		if (m_valid && m_ready)
			addr_fifo[wr_addr[LGFIFO-1:0]] <= i_wb_addr[SUBW-1:0];

		initial	rd_addr = 0;
		always @(posedge i_clk)
		if (i_reset)
			rd_addr <= 0;
		else if (i_axi_bvalid || i_axi_rvalid)
			rd_addr <= rd_addr + 1;

		always @(*)
			fifo_value = addr_fifo[rd_addr[LGFIFO-1:0]];

		wire	[C_AXI_DATA_WIDTH-1:0]	return_data;
		assign	return_data = i_axi_rdata >> (rd_addr * DW);
		always @(*)
			o_wb_data = return_data[DW-1:0];

`ifdef	FORMAL
		always @(*)
			assert(wr_addr - rd_addr == npending);

		always @(*)
			assert(empty == (wr_addr == rd_addr));


		//
		// ...
		//
`endif
	// }}}
	end endgenerate

	// Read data channel / response logic
	assign	o_axi_rready = 1'b1;
	assign	o_axi_bready = 1'b1;

	// Make verilator's -Wall happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, full, i_axi_bid, i_axi_bresp[0], i_axi_rid, i_axi_rresp[0], i_axi_rlast, m_data, m_sel };
	generate if (C_AXI_DATA_WIDTH > DW)
	begin
		wire	[C_AXI_DATA_WIDTH-1:DW] unused_data;
		assign	unused_data = i_axi_rdata[C_AXI_DATA_WIDTH-1:DW];
	end endgenerate
	// verilator lint_on  UNUSED

/////////////////////////////////////////////////////////////////////////
//
//
//
// Formal methods section
//
// Below are a scattering of the formal properties used.  They are not the
// complete set of properties.  Those are maintained elsewhere.
//
/////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	//
	// ...
	//

	// Parameters
	initial	assert(	  (C_AXI_DATA_WIDTH / DW ==32)
			||(C_AXI_DATA_WIDTH / DW ==16)
			||(C_AXI_DATA_WIDTH / DW == 8)
			||(C_AXI_DATA_WIDTH / DW == 4)
			||(C_AXI_DATA_WIDTH / DW == 2)
			||(C_AXI_DATA_WIDTH      == DW));
	//
	initial	assert( C_AXI_ADDR_WIDTH == AW + (LG_WB_DW-3));


	//////////////////////////////////////////////
	//
	//
	// Assumptions about the WISHBONE inputs
	//
	//
	//////////////////////////////////////////////
	//
	// ...

	fwb_slave #(.DW(DW),.AW(AW),
			.F_MAX_STALL(0),
			.F_MAX_ACK_DELAY(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS(0))
		f_wb(i_clk, i_reset, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr,
					i_wb_data, i_wb_sel,
				o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

	//////////////////////////////////////////////
	//
	//
	// Assumptions about the AXI inputs
	//
	//
	//////////////////////////////////////////////


	faxi_master #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH))
		f_axi(.i_clk(i_clk), .i_axi_reset_n(!i_reset),
			// {{{
			// Write address channel
			.i_axi_awready(i_axi_awready),
			.i_axi_awid(   o_axi_awid),
			.i_axi_awaddr( o_axi_awaddr),
			.i_axi_awlen(  o_axi_awlen),
			.i_axi_awsize( o_axi_awsize),
			.i_axi_awburst(o_axi_awburst),
			.i_axi_awlock( o_axi_awlock),
			.i_axi_awcache(o_axi_awcache),
			.i_axi_awprot( o_axi_awprot),
			.i_axi_awqos(  o_axi_awqos),
			.i_axi_awvalid(o_axi_awvalid),
			// Write data channel
			.i_axi_wready( i_axi_wready),
			.i_axi_wdata(  o_axi_wdata),
			.i_axi_wstrb(  o_axi_wstrb),
			.i_axi_wlast(  o_axi_wlast),
			.i_axi_wvalid( o_axi_wvalid),
			// Write response channel
			.i_axi_bid(    i_axi_bid),
			.i_axi_bresp(  i_axi_bresp),
			.i_axi_bvalid( i_axi_bvalid),
			.i_axi_bready( o_axi_bready),
			// Read address channel
			.i_axi_arready(i_axi_arready),
			.i_axi_arid(   o_axi_arid),
			.i_axi_araddr( o_axi_araddr),
			.i_axi_arlen(  o_axi_arlen),
			.i_axi_arsize( o_axi_arsize),
			.i_axi_arburst(o_axi_arburst),
			.i_axi_arlock( o_axi_arlock),
			.i_axi_arcache(o_axi_arcache),
			.i_axi_arprot( o_axi_arprot),
			.i_axi_arqos(  o_axi_arqos),
			.i_axi_arvalid(o_axi_arvalid),
			// Read data channel
			.i_axi_rid(    i_axi_rid),
			.i_axi_rresp(  i_axi_rresp),
			.i_axi_rvalid( i_axi_rvalid),
			.i_axi_rdata(  i_axi_rdata),
			.i_axi_rlast(  i_axi_rlast),
			.i_axi_rready( o_axi_rready),
			// Counts
			.f_axi_awr_nbursts(f_axi_awr_nbursts),
			.f_axi_wr_pending(f_axi_wr_pending),
			.f_axi_rd_nbursts(f_axi_rd_nbursts),
			.f_axi_rd_outstanding(f_axi_rd_outstanding)
			//
			// ...
			//
			// }}}
		);

	always @(*)
	if (!flushing && i_wb_cyc)
		assert(f_wb_outstanding == npending + (r_stb ? 1:0)
			+ ( ((C_AXI_DATA_WIDTH != DW)
				&& (o_wb_ack|o_wb_err))? 1:0));

	always @(*)
	if (f_axi_awr_nbursts > 0)
	begin
		assert(direction);
		assert(f_axi_rd_nbursts == 0);
		assert(f_axi_awr_nbursts + (o_axi_awvalid ? 1:0) == npending);
		assert(f_axi_wr_pending == (o_axi_wvalid&&!o_axi_awvalid ? 1:0));

		//
		// ...
		//
	end
	always @(*)
	if (o_axi_awvalid)
		assert(o_axi_wvalid);

	// Some quick read checks
	always @(*)
	if (f_axi_rd_nbursts > 0)
	begin
		assert(!direction);
		assert(f_axi_rd_nbursts+(o_axi_arvalid ? 1:0)
				== npending);
		assert(f_axi_awr_nbursts == 0);

		//
		// ...
		//
	end

	always @(*)
	if (direction)
	begin
		assert(npending == (o_axi_awvalid ? 1:0) + f_axi_awr_nbursts);
		assert(!o_axi_arvalid);
		assert(f_axi_rd_nbursts == 0);
		assert(!i_axi_rvalid);
	end else begin
		assert(npending == (o_axi_arvalid ? 1:0) + f_axi_rd_nbursts);
		assert(!o_axi_awvalid);
		assert(!o_axi_wvalid);
		assert(f_axi_awr_nbursts == 0);
	end

	//////////////////////////////////////////////
	//
	//
	// Pending counter properties
	//
	//
	//////////////////////////////////////////////

	always @(*)
	begin
		assert(npending <= { 1'b1, {(LGFIFO){1'b0}} });
		assert(empty == (npending == 0));
		assert(full == (npending == {1'b1, {(LGFIFO){1'b0}}}));
		assert(nearfull == (npending >= {1'b0, {(LGFIFO){1'b1}}}));
		if (full)
			assert(o_wb_stall);
	end

	//////////////////////////////////////////////
	//
	//
	// Assertions about the AXI4 ouputs
	//
	//
	//////////////////////////////////////////////

	// Write response channel
	always @(posedge i_clk)
		// We keep bready high, so the other condition doesn't
		// need to be checked
		assert(o_axi_bready);

	// AXI read data channel signals
	always @(posedge i_clk)
		// We keep o_axi_rready high, so the other condition's
		// don't need to be checked here
		assert(o_axi_rready);

	//
	// AXI write address channel
	//
	//
	always @(*)
	begin
		if (o_axi_awvalid || o_axi_wvalid || f_axi_awr_nbursts>0)
			assert(direction);
		//
		// ...
		//
	end
	//
	// AXI read address channel
	//
	always @(*)
	begin
		if (o_axi_arvalid || i_axi_rvalid || f_axi_rd_nbursts > 0)
			assert(!direction);
		//
		// ...
		//
	end

	//
	// AXI write response channel
	//


	//
	// AXI read data channel signals
	//

	//
	// Bus contract
	//

	(* anyconst *) reg [C_AXI_ADDR_WIDTH-1:0]	f_const_addr;
	reg		[C_AXI_DATA_WIDTH-1:0]		f_data;

	////////////////////////////////////////////////////////////////////////
	//
	// Assume a basic bus response to the given data and address
	//
	//
	integer	iN;

	initial	f_data = 0;
	always @(posedge i_clk)
	if (o_axi_wvalid && i_axi_wready && o_axi_awaddr == f_const_addr)
	begin
		for(iN=0; iN<C_AXI_DATA_WIDTH/8; iN=iN+1)
		begin
			if (o_axi_wstrb[iN])
				f_data[8*iN +: 8] <= o_axi_wdata[8*iN +: 8];
		end
	end

	always @(*)
	if (i_axi_rvalid && o_axi_rready && f_axi_rd_ckvalid
			&& (f_axi_rd_ckaddr == f_const_addr))
		assume(i_axi_rdata == f_data);

	////////////////////////////////////////////////////////////////////////
	//
	// Prove that a write to this address will change this value
	//
	//
	(* anyconst *)	reg	[DW-1:0]	f_wb_data;
	(* anyconst *)	reg	[DW/8-1:0]	f_wb_strb;
			reg	[AW-1:0]	f_wb_addr;
			reg	[C_AXI_DATA_WIDTH-1:0]		f_axi_data;
			reg	[C_AXI_DATA_WIDTH/8-1:0]	f_axi_strb;

	//
	// ...
	//

	always @(*)
		f_wb_addr = f_const_addr[C_AXI_ADDR_WIDTH-1:DWSIZE];
	generate if (DW > 8)
	begin
		always @(*)
			assume(f_const_addr[$clog2(DW)-4:0] == 0);
	end endgenerate
	always @(*)
		f_axi_data = {(C_AXI_DATA_WIDTH/DW){f_wb_data}};

	//
	// ...
	//

	always @(*)
	begin
		f_valid_wb_response = 1;
		for(iN=0; iN<DW/8; iN=iN+1)
		begin
			if (f_wb_strb[iN] && (o_wb_data[iN*8 +: 8] != f_wb_data[iN*8 +: 8]))
				f_valid_wb_response = 0;
		end
	end


	always @(*)
	begin
		f_valid_axi_data = 1;
		for(iN=0; iN<C_AXI_DATA_WIDTH/8; iN=iN+1)
		begin
			if (f_axi_strb[iN] && (f_axi_data[iN*8 +: 8] != f_data[iN*8 +: 8]))
				f_valid_axi_data = 0;
		end
	end

	always @(*)
	begin
		f_valid_axi_response = 1;
		for(iN=0; iN<C_AXI_DATA_WIDTH/8; iN=iN+1)
		begin
			if (f_axi_strb[iN] && (i_axi_rdata[iN*8 +: 8] != f_data[iN*8 +: 8]))
				f_valid_axi_response = 0;
		end
	end

	//
	// ...
	//

	generate if (DW == C_AXI_DATA_WIDTH)
	begin

		always @(*)
			f_axi_strb = f_wb_strb;

	end else if (DW*2 == C_AXI_DATA_WIDTH)
	begin

		always @(*)
		begin
			if (f_wb_addr[0])
				f_axi_strb   <= { f_wb_strb, {(DW/8){1'b0}} };
			else
				f_axi_strb   <= { {(DW/8){1'b0}}, f_wb_strb };
		end

	end else if (DW*4 == C_AXI_DATA_WIDTH)
	begin

		always @(*)
		begin
		case(~f_wb_addr[1:0])
		2'b00: f_axi_strb   = { f_wb_strb, {(3*DW/8){1'b0}} };
		2'b01: f_axi_strb   = { {(  DW/8){1'b0}}, f_wb_strb, {(2*DW/8){1'b0}} };
		2'b10: f_axi_strb   = { {(2*DW/8){1'b0}}, f_wb_strb, {(  DW/8){1'b0}} };
		2'b11: f_axi_strb   = { {(3*DW/8){1'b0}}, f_wb_strb };
		endcase
		end

	end else if // ...
	//
	// ...
	//

	end endgenerate


	generate if (DW > 8)
	begin

		always @(*)
		if (o_axi_awvalid)
			assert(o_axi_awaddr[$clog2(DW)-4:0] == 0);
		always @(*)
		if (o_axi_arvalid)
			assert(o_axi_araddr[$clog2(DW)-4:0] == 0);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[F_LGDEPTH-1:0]	r_hit_reads, r_hit_writes,
				r_check_fault, check_fault;

	initial	r_hit_reads = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_hit_writes <= 0;
	else if (f_axi_awr_nbursts > 3)
		r_hit_writes <= 1;

	initial	r_hit_reads = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_hit_reads <= 0;
	else if (f_axi_rd_nbursts > 3)
		r_hit_reads <= 1;

	always @(*)
	begin
		check_fault = 0;
		if (!i_wb_cyc && o_axi_awvalid)
			check_fault = 1;
		if (!i_wb_cyc && o_axi_wvalid)
			check_fault = 1;
		if (!i_wb_cyc && f_axi_awr_nbursts > 0)
			check_fault = 1;
		if (!i_wb_cyc && i_axi_bvalid)
			check_fault = 1;
		//
		if (!i_wb_cyc && o_axi_arvalid)
			check_fault = 1;
		if (!i_wb_cyc && f_axi_rd_outstanding > 0)
			check_fault = 1;
		if (!i_wb_cyc && i_axi_rvalid)
			check_fault = 1;
		if (!i_wb_cyc && (o_wb_ack | o_wb_err))
			check_fault = 1;

		if (flushing)
			check_fault = 1;
	end

	initial	r_check_fault = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_check_fault <= 0;
	else if (check_fault)
		r_check_fault <= 1;

	always @(*)
		cover(r_hit_writes && r_hit_reads && f_axi_rd_nbursts == 0
			&& f_axi_awr_nbursts == 0
			&& !o_axi_awvalid && !o_axi_arvalid && !o_axi_wvalid
			&& !i_axi_bvalid && !i_axi_rvalid
			&& !o_wb_ack && !o_wb_stall && !i_wb_stb
			&& !check_fault && !r_check_fault);

	//
	// ...
	//
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
