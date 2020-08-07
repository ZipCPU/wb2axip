////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	easyaxil
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A formal miter core to compare the easyaxil core to a similar
//		(but mutated) core.
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
module	easyaxil_tb #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXI_ADDR_WIDTH = 4,
		localparam	C_AXI_DATA_WIDTH = 32,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
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
		input	wire	[7:0]				mutation_index
	);

	easyaxil // #(.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		// .OPT_SKIDBUFFER(OPT_SKIDBUFFER),
		// .OPT_LOWPOWER(OPT_LOWPOWER)
		// )
	gold (
		.S_AXI_ACLK(   S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXI_AWVALID(S_AXI_AWVALID),
		.S_AXI_AWREADY(S_AXI_AWREADY),
		.S_AXI_AWADDR( S_AXI_AWADDR),
		.S_AXI_AWPROT( S_AXI_AWPROT),
		//
		.S_AXI_WVALID( S_AXI_WVALID),
		.S_AXI_WREADY( S_AXI_WREADY),
		.S_AXI_WDATA(  S_AXI_WDATA),
		.S_AXI_WSTRB(  S_AXI_WSTRB),
		//
		.S_AXI_BVALID( S_AXI_BVALID),
		.S_AXI_BREADY( S_AXI_BREADY),
		.S_AXI_BRESP(  S_AXI_BRESP),
		//
		.S_AXI_ARVALID(S_AXI_ARVALID),
		.S_AXI_ARREADY(S_AXI_ARREADY),
		.S_AXI_ARADDR( S_AXI_ARADDR),
		.S_AXI_ARPROT( S_AXI_ARPROT),
		//
		.S_AXI_RVALID(S_AXI_RVALID),
		.S_AXI_RREADY(S_AXI_RREADY),
		.S_AXI_RDATA( S_AXI_RDATA),
		.S_AXI_RRESP( S_AXI_RRESP),
		.mutsel(0)
	);

	wire	uut_AWREADY, uut_WREADY, uut_BVALID, uut_ARREADY, uut_RVALID;
	wire	[1:0]	uut_BRESP, uut_RRESP;
	wire	[31:0]	uut_RDATA;

	easyaxil // #(
		// .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		// .OPT_SKIDBUFFER(OPT_SKIDBUFFER),
		// .OPT_LOWPOWER(OPT_LOWPOWER)
		// )
	uut (
		.S_AXI_ACLK(   S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXI_AWVALID(S_AXI_AWVALID),
		.S_AXI_AWREADY(uut_AWREADY),
		.S_AXI_AWADDR( S_AXI_AWADDR),
		.S_AXI_AWPROT( S_AXI_AWPROT),
		//
		.S_AXI_WVALID( S_AXI_WVALID),
		.S_AXI_WREADY( uut_WREADY),
		.S_AXI_WDATA(  S_AXI_WDATA),
		.S_AXI_WSTRB(  S_AXI_WSTRB),
		//
		.S_AXI_BVALID( uut_BVALID),
		.S_AXI_BREADY( S_AXI_BREADY),
		.S_AXI_BRESP(  uut_BRESP),
		//
		.S_AXI_ARVALID(S_AXI_ARVALID),
		.S_AXI_ARREADY(uut_ARREADY),
		.S_AXI_ARADDR( S_AXI_ARADDR),
		.S_AXI_ARPROT( S_AXI_ARPROT),
		//
		.S_AXI_RVALID(uut_RVALID),
		.S_AXI_RREADY(S_AXI_RREADY),
		.S_AXI_RDATA( uut_RDATA),
		.S_AXI_RRESP( uut_RRESP),
		.mutsel(mutation_index)
	);

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
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awcache(4'h0),
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
		.i_axi_arcache(4'h0),
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
	if (S_AXI_ARESETN)
	begin
		if (S_AXI_AWVALID)
			assert(S_AXI_AWREADY == uut_AWREADY);

		if (S_AXI_WVALID)
			assert(S_AXI_WREADY == uut_WREADY);

		if (S_AXI_ARVALID)
			assert(S_AXI_ARREADY == uut_ARREADY);

		assert(S_AXI_BVALID == uut_BVALID);
		assert(S_AXI_RVALID == uut_RVALID);

		if (S_AXI_BVALID)
			assert( S_AXI_BRESP == uut_BRESP );

		if (S_AXI_RVALID)
			assert({ S_AXI_RRESP, S_AXI_RDATA }
				== { uut_RRESP, uut_RDATA });
	end

	// }}}
	// }}}
`endif
endmodule
