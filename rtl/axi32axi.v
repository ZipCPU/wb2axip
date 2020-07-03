////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi32axi.v
//
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
`default_nettype none
//
//
module	axi32axi #(
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		//
		localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3
	) (
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		// The AXI3 incoming/slave interface
		input	reg				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	reg	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	reg	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	reg	[3:0]			S_AXI_AWLEN,
		input	reg	[2:0]			S_AXI_AWSIZE,
		input	reg	[1:0]			S_AXI_AWBURST,
		input	reg	[1:0]			S_AXI_AWLOCK,
		input	reg	[3:0]			S_AXI_AWCACHE,
		input	reg	[2:0]			S_AXI_AWPROT,
		input	reg	[3:0]			S_AXI_AWQOS,
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
	);

	reg	[3:0]	axi4_awcache, axi4_arcache;
	reg		axi4_awlock, axi4_arlock;

	always @(*)
	case(S_AXI_AWCACHE)
	4'b1010: axi4_awcache = 4'b1110;
	4'b1011: axi4_awcache = 4'b1111;
	default: axi4_awcache = S_AXI_AWCACHE;
	endcase

	always @(*)
		axi4_awlock = S_AXI_AWLOCK[0];

	skidbuffer #(
		.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH + 4 + 3 + 2 + 1+4+3+4),
		.OPT_OUTREG(1'b1)
	) awskid (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWADDR,  S_AXI_AWLEN,
				S_AXI_AWSIZE, S_AXI_AWBURST, axi4_awlock,
				axi4_awcache,  S_AXI_AWPROT,  S_AXI_AWQOS }),
		.o_valid(M_AXI_AWVALID), .i_ready(M_AXI_AWREADY),
			.o_data({ M_AXI_AWID,  M_AXI_AWADDR,  M_AXI_AWLEN[3:0],
				M_AXI_AWSIZE,  M_AXI_AWBURST, M_AXI_AWLOCK,
				M_AXI_AWCACHE, M_AXI_AWPROT,  M_AXI_AWQOS })
	);


	assign	S_AXI_BVALID = M_AXI_BVALID;
	assign	M_AXI_BREADY = S_AXI_BREADY;
	assign	S_AXI_BID    = M_AXI_BID;
	assign	S_AXI_BRESP  = M_AXI_BRESP;

	always @(*)
	case(S_AXI_ARCACHE)
	4'b0110: axi4_arcache = 4'b1110;
	4'b0111: axi4_arcache = 4'b1111;
	default: axi4_arcache = S_AXI_ARCACHE;
	endcase

	always @(*)
		axi4_arlock = S_AXI_ARLOCK[0];

	skidbuffer #(
		.DW(C_AXI_ADDR_WIDTH + C_AXI_ID_WIDTH + 4 + 3 + 2 + 1+4+3+4),
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

	assign	S_AXI_RVALID = M_AXI_RVALID;
	assign	M_AXI_RREADY = S_AXI_RREADY;
	assign	S_AXI_RID    = M_AXI_RID;
	assign	S_AXI_RDATA  = M_AXI_RDATA;
	assign	S_AXI_RLAST  = M_AXI_RLAST;
	assign	S_AXI_RRESP  = M_AXI_RRESP;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_WID, S_AXI_AWLOCK[1], S_AXI_ARLOCK[1] };
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
