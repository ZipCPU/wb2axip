////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axim2wbsp.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	So ... this converter works in the other direction from
//		wbm2axisp.  This converter takes AXI commands, and organizes
//	them into pipelined wishbone commands.
//
//	This particular core treats AXI as two separate buses: one for writes,
//	and the other for reads.  This particular core combines the two channels
//	into one.  The designer should be aware that the two AXI buses turned
//	Wishbone buses can be kept separate as separate inputs to a WB crosssbar
//	for better performance in some circumstances.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2016-2024, Gisselquist Technology, LLC
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
// }}}
module axim2wbsp #(
		// {{{
		parameter C_AXI_ID_WIDTH = 2, // The AXI id width used for R&W
                                             // This is an int between 1-16
		parameter  C_AXI_DATA_WIDTH  = 32,// Width of the AXI R&W data
		parameter  C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
		localparam AXI_LSBS		= $clog2(C_AXI_DATA_WIDTH)-3,
		localparam DW			= C_AXI_DATA_WIDTH,
		localparam AW			= C_AXI_ADDR_WIDTH - AXI_LSBS,
		parameter  LGFIFO		= 5,
		parameter [0:0]	OPT_SWAP_ENDIANNESS = 1'b0,
		parameter [0:0]	OPT_READONLY	= 1'b0,
		parameter [0:0]	OPT_WRITEONLY	= 1'b0
		// }}}
	) (
		// {{{
		//
		input	wire			S_AXI_ACLK,	// System clock
		input	wire			S_AXI_ARESETN,

		// AXI write address channel signals
		// {{{
		input	wire			S_AXI_AWVALID,
		output	wire			S_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[7:0]		S_AXI_AWLEN,
		input	wire	[2:0]		S_AXI_AWSIZE,
		input	wire	[1:0]		S_AXI_AWBURST,
		input	wire	[0:0]		S_AXI_AWLOCK,
		input	wire	[3:0]		S_AXI_AWCACHE,
		input	wire	[2:0]		S_AXI_AWPROT,
		input	wire	[3:0]		S_AXI_AWQOS,
		// }}}
		// AXI write data channel signals
		// {{{
		input	wire			S_AXI_WVALID,
		output	wire			S_AXI_WREADY, 
		input	wire [C_AXI_DATA_WIDTH-1:0]   S_AXI_WDATA,
		input	wire [C_AXI_DATA_WIDTH/8-1:0] S_AXI_WSTRB,
		input	wire			S_AXI_WLAST,
		// }}}
		// AXI write response channel signals
		// {{{
		output	wire 			S_AXI_BVALID, 
		input	wire			S_AXI_BREADY,
		output	wire [C_AXI_ID_WIDTH-1:0] S_AXI_BID,
		output	wire [1:0]		S_AXI_BRESP,
		// }}}
		// AXI read address channel signals
		// {{{
		input	wire			S_AXI_ARVALID,
		output	wire			S_AXI_ARREADY,
		input	wire [C_AXI_ID_WIDTH-1:0]   S_AXI_ARID,
		input	wire [C_AXI_ADDR_WIDTH-1:0] S_AXI_ARADDR,
		input	wire	[7:0]		S_AXI_ARLEN,
		input	wire	[2:0]		S_AXI_ARSIZE,
		input	wire	[1:0]		S_AXI_ARBURST,
		input	wire	[0:0]		S_AXI_ARLOCK,
		input	wire	[3:0]		S_AXI_ARCACHE,
		input	wire	[2:0]		S_AXI_ARPROT,
		input	wire	[3:0]		S_AXI_ARQOS,
		// }}}
		// AXI read data channel signals
		// {{{
		output	wire			S_AXI_RVALID,  // Rd rslt valid
		input	wire			S_AXI_RREADY,  // Rd rslt ready
		output	wire [C_AXI_ID_WIDTH-1:0]   S_AXI_RID, // Response ID
		output	wire [C_AXI_DATA_WIDTH-1:0] S_AXI_RDATA,// Read data
		output	wire			S_AXI_RLAST,   // Read last
		output	wire [1:0]		S_AXI_RRESP,   // Read response
		// }}}
		// We'll share the clock and the reset
		// {{{
		output	wire				o_reset,
		output	wire				o_wb_cyc,
		output	wire				o_wb_stb,
		output	wire				o_wb_we,
		output	wire [(AW-1):0]			o_wb_addr,
		output	wire [(C_AXI_DATA_WIDTH-1):0]	o_wb_data,
		output	wire [(C_AXI_DATA_WIDTH/8-1):0]	o_wb_sel,
		input	wire				i_wb_stall,
		input	wire				i_wb_ack,
		input	wire [(C_AXI_DATA_WIDTH-1):0]	i_wb_data,
		input	wire				i_wb_err
		// }}}
		// }}}
	);
	//
	//
	//


	wire	[(AW-1):0]			w_wb_addr, r_wb_addr;
	wire	[(C_AXI_DATA_WIDTH-1):0]	w_wb_data;
	wire	[(C_AXI_DATA_WIDTH/8-1):0]	w_wb_sel, r_wb_sel;
	wire	r_wb_err, r_wb_cyc, r_wb_stb, r_wb_stall, r_wb_ack;
	wire	w_wb_err, w_wb_cyc, w_wb_stb, w_wb_stall, w_wb_ack;
	wire	r_wb_we, w_wb_we;

	assign	r_wb_we = 1'b0;
	assign	w_wb_we = 1'b1;

	generate if (!OPT_READONLY)
	begin : AXI_WR
		// {{{
		aximwr2wbsp #(
			// {{{
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.OPT_SWAP_ENDIANNESS(OPT_SWAP_ENDIANNESS),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_write_decoder(
		// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			//
			.S_AXI_AWVALID(S_AXI_AWVALID),
			.S_AXI_AWREADY(S_AXI_AWREADY),
			.S_AXI_AWID(   S_AXI_AWID),
			.S_AXI_AWADDR( S_AXI_AWADDR),
			.S_AXI_AWLEN(  S_AXI_AWLEN),
			.S_AXI_AWSIZE( S_AXI_AWSIZE),
			.S_AXI_AWBURST(S_AXI_AWBURST),
			.S_AXI_AWLOCK( S_AXI_AWLOCK),
			.S_AXI_AWCACHE(S_AXI_AWCACHE),
			.S_AXI_AWPROT( S_AXI_AWPROT),
			.S_AXI_AWQOS(  S_AXI_AWQOS),
			//
			.S_AXI_WVALID( S_AXI_WVALID),
			.S_AXI_WREADY( S_AXI_WREADY),
			.S_AXI_WDATA(  S_AXI_WDATA),
			.S_AXI_WSTRB(  S_AXI_WSTRB),
			.S_AXI_WLAST(  S_AXI_WLAST),
			//
			.S_AXI_BVALID(S_AXI_BVALID),
			.S_AXI_BREADY(S_AXI_BREADY),
			.S_AXI_BID(   S_AXI_BID),
			.S_AXI_BRESP( S_AXI_BRESP),
			//
			.o_wb_cyc(  w_wb_cyc),
			.o_wb_stb(  w_wb_stb),
			.o_wb_addr( w_wb_addr),
			.o_wb_data( w_wb_data),
			.o_wb_sel(  w_wb_sel),
			.i_wb_ack(  w_wb_ack),
			.i_wb_stall(w_wb_stall),
			.i_wb_err(  w_wb_err)
		// }}}
		);
		// }}}
	end else begin : NO_WRITE_CHANNEL
		// {{{
		assign	w_wb_cyc  = 0;
		assign	w_wb_stb  = 0;
		assign	w_wb_addr = 0;
		assign	w_wb_data = 0;
		assign	w_wb_sel  = 0;
		assign	S_AXI_AWREADY = 0;
		assign	S_AXI_WREADY  = 0;
		assign	S_AXI_BVALID  = 0;
		assign	S_AXI_BRESP   = 2'b11;
		assign	S_AXI_BID     = 0;
		// }}}
	end endgenerate

	generate if (!OPT_WRITEONLY)
	begin : AXI_RD
		// {{{
		aximrd2wbsp #(
			// {{{
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.OPT_SWAP_ENDIANNESS(OPT_SWAP_ENDIANNESS),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_read_decoder(
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			//
			.S_AXI_ARVALID(S_AXI_ARVALID),
			.S_AXI_ARREADY(S_AXI_ARREADY),
			.S_AXI_ARID(   S_AXI_ARID),
			.S_AXI_ARADDR( S_AXI_ARADDR),
			.S_AXI_ARLEN(  S_AXI_ARLEN),
			.S_AXI_ARSIZE( S_AXI_ARSIZE),
			.S_AXI_ARBURST(S_AXI_ARBURST),
			.S_AXI_ARLOCK( S_AXI_ARLOCK),
			.S_AXI_ARCACHE(S_AXI_ARCACHE),
			.S_AXI_ARPROT( S_AXI_ARPROT),
			.S_AXI_ARQOS(  S_AXI_ARQOS),
			//
			.S_AXI_RVALID(S_AXI_RVALID),
			.S_AXI_RREADY(S_AXI_RREADY),
			.S_AXI_RID(   S_AXI_RID),
			.S_AXI_RDATA( S_AXI_RDATA),
			.S_AXI_RLAST( S_AXI_RLAST),
			.S_AXI_RRESP( S_AXI_RRESP),
			//
			.o_wb_cyc(  r_wb_cyc),
			.o_wb_stb(  r_wb_stb),
			.o_wb_addr( r_wb_addr),
			.o_wb_sel(  r_wb_sel),
			.i_wb_ack(  r_wb_ack),
			.i_wb_stall(r_wb_stall),
			.i_wb_data( i_wb_data),
			.i_wb_err(  r_wb_err)
			// }}}
		);
		// }}}
	end else begin : NO_READ_CHANNEL
		// {{{
		assign	r_wb_cyc  = 0;
		assign	r_wb_stb  = 0;
		assign	r_wb_addr = 0;
		//
		assign S_AXI_ARREADY = 0;
		assign S_AXI_RVALID  = 0;
		assign S_AXI_RID     = 0;
		assign S_AXI_RDATA   = 0;
		assign S_AXI_RLAST   = 0;
		assign S_AXI_RRESP   = 0;
		// }}}
	end endgenerate

	generate if (OPT_READONLY)
	begin : ARB_RD
		// {{{
		assign	o_wb_cyc  = r_wb_cyc;
		assign	o_wb_stb  = r_wb_stb;
		assign	o_wb_we   = r_wb_we;
		assign	o_wb_addr = r_wb_addr;
		assign	o_wb_data = 0;
		assign	o_wb_sel  = r_wb_sel;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_stall= i_wb_stall;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_err  = i_wb_err;
		// }}}
	end else if (OPT_WRITEONLY)
	begin : ARB_WR
		// {{{
		assign	o_wb_cyc  = w_wb_cyc;
		assign	o_wb_stb  = w_wb_stb;
		assign	o_wb_we   = w_wb_we;
		assign	o_wb_addr = w_wb_addr;
		assign	o_wb_data = w_wb_data;
		assign	o_wb_sel  = w_wb_sel;
		assign	w_wb_ack  = i_wb_ack;
		assign	w_wb_stall= i_wb_stall;
		assign	w_wb_ack  = i_wb_ack;
		assign	w_wb_err  = i_wb_err;
		// }}}
	end else begin : ARB_WB
		// {{{
		wbarbiter	#(.DW(DW), .AW(AW))
		readorwrite(S_AXI_ACLK, o_reset,
			r_wb_cyc, r_wb_stb, r_wb_we, r_wb_addr, w_wb_data, r_wb_sel,
				r_wb_ack, r_wb_stall, r_wb_err,
			w_wb_cyc, w_wb_stb, w_wb_we, w_wb_addr, w_wb_data, w_wb_sel,
				w_wb_ack, w_wb_stall, w_wb_err,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_err
			);
		// }}}
	end endgenerate

	assign	o_reset = (S_AXI_ARESETN == 1'b0);

`ifdef	FORMAL
`endif
endmodule
