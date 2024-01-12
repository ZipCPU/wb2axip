////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi32axi.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Bridge from an AXI3 slave to an AXI4 master
//
//	The goal here is to support as high a bus speed as possible, maintain
//	burst support (if possible) and (more important) allow bus requests
//	coming from the ARM within either the Zynq or one of Intel's SOC chips
//	to speak with an AutoFPGA based design.
//
//	Note that if you aren't using AutoFPGA, then you probably don't need
//	this core--the vendor tools should be able to handle this conversion
//	quietly and automatically for you.
//
// Notes:
//	AxCACHE is remapped as per the AXI4 specification, since the values
//	aren't truly equivalent.  This forces a single clock delay in the Ax*
//	channels and (likely) the W* channel as well as a system level
//	consequence.
//
//	AXI3 locking is not supported under AXI4.  As per the AXI4 spec,
//	AxLOCK is converteted from AXI3 to AXI4 by just dropping the high
//	order bit.
//
//	The WID input is ignored.  Whether or not this input can be ignored
//	is based upon how the ARM is implemented internally.  After a bit
//	of research into both Zynq's and Intel SOCs, this appears to be the
//	appropriate answer here.
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
`default_nettype none
// }}}
module	axi32axi #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	OPT_REORDER_METHOD = 0,
		parameter [0:0]	OPT_TRANSFORM_AXCACHE = 1,
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter [0:0]	OPT_LOW_LATENCY = 0,
		parameter	WID_LGAWFIFO = 3,
		parameter	WID_LGWFIFO = 3
		//
		// }}}
	) (
		// {{{
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		// The AXI3 incoming/slave interface
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[3:0]			S_AXI_AWLEN,
		input	wire	[2:0]			S_AXI_AWSIZE,
		input	wire	[1:0]			S_AXI_AWBURST,
		input	wire	[1:0]			S_AXI_AWLOCK,
		input	wire	[3:0]			S_AXI_AWCACHE,
		input	wire	[2:0]			S_AXI_AWPROT,
		input	wire	[3:0]			S_AXI_AWQOS,
		//
		//
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_WID,
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
		input	wire	[3:0]			S_AXI_ARLEN,
		input	wire	[2:0]			S_AXI_ARSIZE,
		input	wire	[1:0]			S_AXI_ARBURST,
		input	wire	[1:0]			S_AXI_ARLOCK,
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
		// The AXI4 Master (outgoing) interface
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[7:0]			M_AXI_AWLEN,
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
		output	wire				M_AXI_AWLOCK,
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
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
		output	wire	[7:0]			M_AXI_ARLEN,
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
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
	);

	// Register/net declarations
	// {{{
	// localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3;
	localparam	IW=C_AXI_ID_WIDTH;
	reg	[3:0]	axi4_awcache, axi4_arcache;
	reg		axi4_awlock, axi4_arlock;
	wire		awskd_ready;
	wire		wid_reorder_awready;
	wire [IW-1:0]	reordered_wid;
	// }}}

	// Write cache remapping
	// {{{
	always @(*)
	case(S_AXI_AWCACHE)
	4'b1010: axi4_awcache = 4'b1110;
	4'b1011: axi4_awcache = 4'b1111;
	default: axi4_awcache = S_AXI_AWCACHE;
	endcase
	// }}}

	// AWLOCK
	// {{{
	always @(*)
		axi4_awlock = S_AXI_AWLOCK[0];
	// }}}

	// AW Skid buffer
	// {{{
	generate if (OPT_TRANSFORM_AXCACHE)
	begin : GEN_AWCACHE
		// {{{
		skidbuffer #(
			.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH
					+ 4 + 3 + 2 + 1+4+3+4),
			.OPT_OUTREG(1'b1)
		) awskid (
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_AWVALID && wid_reorder_awready),
				.o_ready(awskd_ready),
				.i_data({ S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
					S_AXI_AWSIZE, S_AXI_AWBURST,axi4_awlock,
					axi4_awcache, S_AXI_AWPROT, S_AXI_AWQOS
					}),
			.o_valid(M_AXI_AWVALID), .i_ready(M_AXI_AWREADY),
				.o_data({ M_AXI_AWID, M_AXI_AWADDR,
							 M_AXI_AWLEN[3:0],
					M_AXI_AWSIZE,M_AXI_AWBURST,M_AXI_AWLOCK,
					M_AXI_AWCACHE,M_AXI_AWPROT, M_AXI_AWQOS
					})
		);

		assign	M_AXI_AWLEN[7:4] = 4'h0;
		assign	S_AXI_AWREADY = awskd_ready && wid_reorder_awready;
		// }}}
	end else begin : IGN_AWCACHE
		// {{{
		assign	M_AXI_AWVALID = S_AXI_AWVALID && wid_reorder_awready;
		assign	S_AXI_AWREADY = M_AXI_AWREADY;
		assign	M_AXI_AWID    = S_AXI_AWID;
		assign	M_AXI_AWADDR  = S_AXI_AWADDR;
		assign	M_AXI_AWLEN   = { 4'h0, S_AXI_AWLEN };
		assign	M_AXI_AWSIZE  = S_AXI_AWSIZE;
		assign	M_AXI_AWBURST = S_AXI_AWBURST;
		assign	M_AXI_AWLOCK  = axi4_awlock;
		assign	M_AXI_AWCACHE = axi4_awcache;
		assign	M_AXI_AWPROT  = S_AXI_AWPROT;
		assign	M_AXI_AWQOS   = S_AXI_AWQOS;

		assign	awskd_ready = 1;
		// }}}
	end endgenerate
	// }}}

	// Handle write channel de-interleaving
	// {{{
	axi3reorder #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_METHOD(OPT_REORDER_METHOD),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_LOW_LATENCY(OPT_LOW_LATENCY),
		.LGAWFIFO(WID_LGAWFIFO),
		.LGWFIFO(WID_LGWFIFO)
		// }}}
	) widreorder (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		// Incoming Write address ID
		.S_AXI3_AWVALID(S_AXI_AWVALID && S_AXI_AWREADY),
			.S_AXI3_AWREADY(wid_reorder_awready),
			.S_AXI3_AWID(S_AXI_AWID),
		// Incoming Write data info
		.S_AXI3_WVALID(S_AXI_WVALID),
			.S_AXI3_WREADY(S_AXI_WREADY),
			.S_AXI3_WID(S_AXI_WID),
			.S_AXI3_WDATA(S_AXI_WDATA),
			.S_AXI3_WSTRB(S_AXI_WSTRB),
			.S_AXI3_WLAST(S_AXI_WLAST),
		// Outgoing write data channel
		.M_AXI_WVALID(M_AXI_WVALID),
			.M_AXI_WREADY(M_AXI_WREADY),
			.M_AXI_WID(reordered_wid),
			.M_AXI_WDATA(M_AXI_WDATA),
			.M_AXI_WSTRB(M_AXI_WSTRB),
			.M_AXI_WLAST(M_AXI_WLAST)
		// }}}
	);
	// }}}

	// Forward the B* channel return
	// {{{
	assign	S_AXI_BVALID = M_AXI_BVALID;
	assign	M_AXI_BREADY = S_AXI_BREADY;
	assign	S_AXI_BID    = M_AXI_BID;
	assign	S_AXI_BRESP  = M_AXI_BRESP;
	// }}}

	// Read cache remapping
	// {{{
	always @(*)
	case(S_AXI_ARCACHE)
	4'b0110: axi4_arcache = 4'b1110;
	4'b0111: axi4_arcache = 4'b1111;
	default: axi4_arcache = S_AXI_ARCACHE;
	endcase
	// }}}

	// ARLOCK
	// {{{
	always @(*)
		axi4_arlock = S_AXI_ARLOCK[0];
	// }}}

	// AR Skid buffer
	// {{{
	generate if (OPT_TRANSFORM_AXCACHE)
	begin : GEN_ARCACHE
		// {{{
		skidbuffer #(
			.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH
					+ 4 + 3 + 2 + 1+4+3+4),
			.OPT_OUTREG(1'b1)
		) arskid (
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
				.i_data({ S_AXI_ARID, S_AXI_ARADDR,  S_AXI_ARLEN,
					S_AXI_ARSIZE, S_AXI_ARBURST, axi4_arlock,
					axi4_arcache,  S_AXI_ARPROT,  S_AXI_ARQOS }),
			.o_valid(M_AXI_ARVALID), .i_ready(M_AXI_ARREADY),
				.o_data({ M_AXI_ARID,  M_AXI_ARADDR,  M_AXI_ARLEN[3:0],
					M_AXI_ARSIZE,  M_AXI_ARBURST, M_AXI_ARLOCK,
					M_AXI_ARCACHE, M_AXI_ARPROT,  M_AXI_ARQOS })
		);

		assign	M_AXI_ARLEN[7:4] = 4'h0;
		// }}}
	end else begin : IGN_ARCACHE
		// {{{
		assign	M_AXI_ARVALID = S_AXI_ARVALID;
		assign	S_AXI_ARREADY = M_AXI_ARREADY;
		assign	M_AXI_ARID    = S_AXI_ARID;
		assign	M_AXI_ARADDR  = S_AXI_ARADDR;
		assign	M_AXI_ARLEN   = { 4'h0, S_AXI_ARLEN };
		assign	M_AXI_ARSIZE  = S_AXI_ARSIZE;
		assign	M_AXI_ARBURST = S_AXI_ARBURST;
		assign	M_AXI_ARLOCK  = axi4_arlock;
		assign	M_AXI_ARCACHE = axi4_arcache;
		assign	M_AXI_ARPROT  = S_AXI_ARPROT;
		assign	M_AXI_ARQOS   = S_AXI_ARQOS;
		// }}}
	end endgenerate
	// }}}

	// Forward the R* channel return
	// {{{
	assign	S_AXI_RVALID = M_AXI_RVALID;
	assign	M_AXI_RREADY = S_AXI_RREADY;
	assign	S_AXI_RID    = M_AXI_RID;
	assign	S_AXI_RDATA  = M_AXI_RDATA;
	assign	S_AXI_RLAST  = M_AXI_RLAST;
	assign	S_AXI_RRESP  = M_AXI_RRESP;
	// }}}

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWLOCK[1], S_AXI_ARLOCK[1],
			reordered_wid };
	// Verilator lint_on UNUSED

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
