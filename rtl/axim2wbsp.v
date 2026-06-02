////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/axim2wbsp.v
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
// Copyright (C) 2016-2025, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
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

	localparam	LCL_LOCK = OPT_LOCK && !OPT_WRITEONLY && !OPT_READONLY;
	wire	[(AW-1):0]			w_wb_addr, r_wb_addr;
	wire	[(C_AXI_DATA_WIDTH-1):0]	w_wb_data;
	wire	[(C_AXI_DATA_WIDTH/8-1):0]	w_wb_sel, r_wb_sel;
	wire	r_wb_err, r_wb_cyc, r_wb_stb, r_wb_stall, r_wb_ack;
	wire	w_wb_err, w_wb_cyc, w_wb_stb, w_wb_stall, w_wb_ack;
	wire	r_wb_we, w_wb_we;

	assign	r_wb_we = 1'b0;
	assign	w_wb_we = 1'b1;

	wire			skid_awvalid, skid_awready;
	wire	[C_AXI_ID_WIDTH-1:0]	skid_awid;
	wire	[C_AXI_ADDR_WIDTH-1:0]	skid_awaddr;
	wire	[7:0]		skid_awlen;
	wire	[2:0]		skid_awsize;
	wire	[1:0]		skid_awburst;
	wire			skid_awlock;
	wire	[3:0]		skid_awcache;
	wire	[2:0]		skid_awprot;
	wire	[3:0]		skid_awqos;

	wire			skid_wvalid, skid_wready, skid_wlast;
	wire	[C_AXI_DATA_WIDTH-1:0]	skid_wdata;
	wire [C_AXI_DATA_WIDTH/8-1:0]	skid_wstrb;

	wire			skid_arvalid, skid_arready;
	wire	[C_AXI_ID_WIDTH-1:0]	skid_arid;
	wire	[C_AXI_ADDR_WIDTH-1:0]	skid_araddr;
	wire	[7:0]		skid_arlen;
	wire	[2:0]		skid_arsize;
	wire	[1:0]		skid_arburst;
	wire			skid_arlock;
	wire	[3:0]		skid_arcache;
	wire	[2:0]		skid_arprot;
	wire	[3:0]		skid_arqos;

	wire	exread_hold, exwrite_hold, write_busy, exwrite_access;


	generate if (!OPT_READONLY)
	begin : AXI_WR
		// {{{

		if (LCL_LOCK)
		begin : GEN_SKIDS
			// {{{
			wire	tmp_awvalid, tmp_awready;

			skidbuffer #(
				.OPT_OUTREG(0),
				.DW(C_AXI_ID_WIDTH+C_AXI_ADDR_WIDTH+8+5+1+4+3+4)
			) u_awskid (
				// {{{
				.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
				.i_valid(S_AXI_AWVALID),.o_ready(S_AXI_AWREADY),
				.i_data({
					S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
					S_AXI_AWSIZE, S_AXI_AWBURST,
					S_AXI_AWLOCK, S_AXI_AWCACHE,
					S_AXI_AWPROT, S_AXI_AWQOS
					}),
				.o_valid(tmp_awvalid), .i_ready(tmp_awready),
				.o_data({
					skid_awid, skid_awaddr, skid_awlen,
					skid_awsize, skid_awburst,
					skid_awlock, skid_awcache,
					skid_awprot, skid_awqos
					})
				// }}}
			);

			skidbuffer #(
				.OPT_OUTREG(0),
				.DW(1+C_AXI_DATA_WIDTH/8+C_AXI_DATA_WIDTH)
			) u_wskid (
				// {{{
				.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
				.i_valid(S_AXI_WVALID),.o_ready(S_AXI_WREADY),
				.i_data({
					S_AXI_WLAST, S_AXI_WSTRB, S_AXI_WDATA
					}),
				.o_valid(skid_wvalid), .i_ready(skid_wready),
				.o_data({
					skid_wlast, skid_wstrb, skid_wdata
					})
				// }}}
			);

			assign	skid_awvalid  = tmp_awvalid && !exwrite_hold;
			assign	tmp_awready   = skid_awready&& !exwrite_hold;
			// }}}
		end else begin : NO_SKIDS
			// {{{
			assign	skid_awvalid  = S_AXI_AWVALID && !exwrite_hold;
			assign	S_AXI_AWREADY = skid_awready  && !exwrite_hold;
			assign	skid_awid     = S_AXI_AWID;
			assign	skid_awaddr   = S_AXI_AWADDR;
			assign	skid_awlen    = S_AXI_AWLEN;
			assign	skid_awsize   = S_AXI_AWSIZE;
			assign	skid_awburst  = S_AXI_AWBURST;
			assign	skid_awlock   = S_AXI_AWLOCK;
			assign	skid_awcache  = S_AXI_AWCACHE;
			assign	skid_awprot   = S_AXI_AWPROT;
			assign	skid_awqos    = S_AXI_AWQOS;

			assign	skid_wvalid  = S_AXI_WVALID;
			assign	S_AXI_WREADY = skid_wready;
			assign	skid_wdata   = S_AXI_WDATA;
			assign	skid_wstrb   = S_AXI_WSTRB;
			assign	skid_wlast   = S_AXI_WLAST;
			// }}}
		end

		aximwr2wbsp #(
			// {{{
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.OPT_SWAP_ENDIANNESS(OPT_SWAP_ENDIANNESS),
			.OPT_LOCK(LCL_LOCK),
			.OPT_FAST_RETURN(OPT_FAST_RETURN),
			.OPT_SKIDBUFFER(!LCL_LOCK),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_write_decoder(
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			//
			.S_AXI_AWVALID(skid_awvalid),
			.S_AXI_AWREADY(skid_awready),
			.S_AXI_AWID(   skid_awid),
			.S_AXI_AWADDR( skid_awaddr),
			.S_AXI_AWLEN(  skid_awlen),
			.S_AXI_AWSIZE( skid_awsize),
			.S_AXI_AWBURST(skid_awburst),
			.S_AXI_AWLOCK( skid_awlock),
			.S_AXI_AWCACHE(skid_awcache),
			.S_AXI_AWPROT( skid_awprot),
			.S_AXI_AWQOS(  skid_awqos),
			.S_EXACCESS(   exwrite_access),
			//
			.S_AXI_WVALID( skid_wvalid),
			.S_AXI_WREADY( skid_wready),
			.S_AXI_WDATA(  skid_wdata),
			.S_AXI_WSTRB(  skid_wstrb),
			.S_AXI_WLAST(  skid_wlast),
			//
			.S_AXI_BVALID(S_AXI_BVALID),
			.S_AXI_BREADY(S_AXI_BREADY),
			.S_AXI_BID(   S_AXI_BID),
			.S_AXI_BRESP( S_AXI_BRESP),
			.S_BUSY(      write_busy),
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

		assign	skid_awvalid  = 1'b0;
		assign	skid_awready  = 1'b0;
		assign	skid_awid     = {(C_AXI_ID_WIDTH){1'b0}};
		assign	skid_awaddr   = {(C_AXI_ADDR_WIDTH){1'b0}};
		assign	skid_awlen    = 8'h0;
		assign	skid_awsize   = 3'h0;
		assign	skid_awburst  = 2'h0;
		assign	skid_awlock   = 1'b0;
		assign	skid_awcache  = 4'h0;
		assign	skid_awprot   = 3'h0;
		assign	skid_awqos    = 4'h0;

		assign	skid_wvalid  = 1'b0;
		assign	skid_wready  = 1'b0;
		assign	skid_wdata   = {(C_AXI_DATA_WIDTH){1'b0}};
		assign	skid_wstrb   = {(C_AXI_DATA_WIDTH/8){1'b0}};
		assign	skid_wlast   = 1'b0;

		assign	write_busy   = 1'b0;

		assign	w_wb_stall = 1'b0;
		assign	w_wb_ack   = 1'b0;
		assign	w_wb_err   = 1'b0;

		// Verilator lint_off UNUSED

		wire	unused_writes;
		assign	unused_writes = &{ 1'b0,
			S_AXI_AWVALID, S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
			S_AXI_AWSIZE, S_AXI_AWBURST, S_AXI_AWLOCK,
			S_AXI_AWCACHE, S_AXI_AWPROT, S_AXI_AWQOS,
			S_AXI_WVALID, S_AXI_WDATA, S_AXI_WSTRB, S_AXI_WLAST,
			S_AXI_BREADY,
			skid_awvalid, skid_awid, skid_awaddr, skid_awlen,
			skid_awsize, skid_awburst, skid_awlock,
			skid_awcache, skid_awprot, skid_awqos,
			skid_awready,
			skid_wvalid, skid_wdata, skid_wstrb, skid_wlast,
			skid_wready,
			w_wb_cyc, w_wb_stb, w_wb_we, w_wb_addr, w_wb_data,
			w_wb_sel, w_wb_stall, w_wb_ack, w_wb_err,
			exwrite_hold, exwrite_access
			};
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	generate if (!OPT_WRITEONLY)
	begin : AXI_RD
		// {{{
		if (LCL_LOCK)
		begin : GEN_ARSKID
			// {{{
			wire	tmp_arvalid, tmp_arready;

			skidbuffer #(
				.OPT_OUTREG(1'b0),
				.DW(C_AXI_ID_WIDTH+C_AXI_ADDR_WIDTH+8+5+12)
			) u_arskid (
				.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
				.i_valid(S_AXI_ARVALID),.o_ready(S_AXI_ARREADY),
				.i_data({
					S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN,
					S_AXI_ARSIZE, S_AXI_ARBURST,
					S_AXI_ARLOCK, S_AXI_ARCACHE,
					S_AXI_ARPROT, S_AXI_ARQOS
					}),
				.o_valid(tmp_arvalid),.i_ready(tmp_arready),
				.o_data({
					skid_arid, skid_araddr, skid_arlen,
					skid_arsize, skid_arburst,
					skid_arlock, skid_arcache,
					skid_arprot, skid_arqos
					})
			);

			assign	skid_arvalid = tmp_arvalid && !exread_hold;
			assign	tmp_arready = skid_arready && !exread_hold;
			// }}}
		end else begin : NO_ARSKID
			// {{{
			assign	skid_arvalid  = S_AXI_ARVALID && !exread_hold;
			assign	S_AXI_ARREADY = skid_arready && !exread_hold;
			assign	skid_arid     = S_AXI_ARID;
			assign	skid_araddr   = S_AXI_ARADDR;
			assign	skid_arlen    = S_AXI_ARLEN;
			assign	skid_arsize   = S_AXI_ARSIZE;
			assign	skid_arburst  = S_AXI_ARBURST;
			assign	skid_arlock   = S_AXI_ARLOCK;
			assign	skid_arcache  = S_AXI_ARCACHE;
			assign	skid_arprot   = S_AXI_ARPROT;
			assign	skid_arqos    = S_AXI_ARQOS;
			// }}}
		end

		aximrd2wbsp #(
			// {{{
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.OPT_SWAP_ENDIANNESS(OPT_SWAP_ENDIANNESS),
			.OPT_LOCK(LCL_LOCK),
			.OPT_FAST_RETURN(OPT_FAST_RETURN),
			.OPT_SKIDBUFFER(!LCL_LOCK),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_read_decoder(
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			//
			.S_AXI_ARVALID(skid_arvalid),
			.S_AXI_ARREADY(skid_arready),
			.S_AXI_ARID(   skid_arid),
			.S_AXI_ARADDR( skid_araddr),
			.S_AXI_ARLEN(  skid_arlen),
			.S_AXI_ARSIZE( skid_arsize),
			.S_AXI_ARBURST(skid_arburst),
			.S_AXI_ARLOCK( skid_arlock),
			.S_AXI_ARCACHE(skid_arcache),
			.S_AXI_ARPROT( skid_arprot),
			.S_AXI_ARQOS(  skid_arqos),
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
		assign	r_wb_sel  = 0;
		//
		assign S_AXI_ARREADY = 0;
		assign S_AXI_RVALID  = 0;
		assign S_AXI_RID     = 0;
		assign S_AXI_RDATA   = 0;
		assign S_AXI_RLAST   = 0;
		assign S_AXI_RRESP   = 0;
		//
		assign	skid_arvalid  = 1'b0;
		assign	skid_arready  = 1'b0;
		assign	skid_arid     = {(C_AXI_ID_WIDTH){1'b0}};
		assign	skid_araddr   = {(C_AXI_ADDR_WIDTH){1'b0}};
		assign	skid_arlen    = 8'h0;
		assign	skid_arsize   = 3'h0;
		assign	skid_arburst  = 2'h0;
		assign	skid_arlock   = 1'b0;
		assign	skid_arcache  = 4'h0;
		assign	skid_arprot   = 3'h0;
		assign	skid_arqos    = 4'h0;

		// Verilator lint_off UNUSED
		wire	unused_read = &{ 1'b0,
				S_AXI_ARVALID, S_AXI_ARID, S_AXI_ARADDR,
				S_AXI_ARLEN, S_AXI_ARBURST, S_AXI_ARSIZE,
				S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT,
				S_AXI_ARQOS,
				skid_arvalid, skid_arid, skid_araddr,
				skid_arlen,  skid_arburst, skid_arsize,
				skid_arlock, skid_arcache, skid_arprot,
				skid_arqos,
				skid_arready, S_AXI_RREADY,
				r_wb_cyc, r_wb_stb, r_wb_we, r_wb_addr,
				r_wb_sel, i_wb_data, r_wb_ack, r_wb_err,
				r_wb_stall,
				exread_hold
				};
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	generate if (LCL_LOCK)
	begin : GEN_EXACCESS
		// {{{
		// Local declarations
		// {{{
		localparam	[1:0]	AXI_FIX = 2'b00, AXI_INCR = 2'b01;
					// AXI_WRAP = 2'b10;
		reg	[C_AXI_ADDR_WIDTH-1:0]	skid_awmin, skid_awmax,
						ex_amin, ex_amax, ex_addr,
						aw_wrap_mask, ar_wrap_mask;
		reg	[C_AXI_ID_WIDTH-1:0]	ex_id;
		reg	[7:0]			ex_len;
		reg	[2:0]			ex_size;
		reg	[1:0]			ex_burst;
		reg	[LGFIFO:0]	reads_active, r_exread_pending;
		reg			r_exread_active, ex_valid,
					r_exwrite_access;
		wire			exread_active;
		// }}}

		assign	exwrite_hold = exread_active
					|| (skid_arvalid && skid_arlock);
		assign	exread_hold = reads_active[LGFIFO]
					|| (skid_arlock && write_busy);

		// reads_active: Count the number of active reads
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			reads_active <= 0;
		else case({ skid_arvalid && skid_arready,
					S_AXI_RVALID && S_AXI_RREADY })
		2'b00: begin end
		2'b01: reads_active <= reads_active - 1;
		// Verilator lint_off WIDTH
		2'b10: reads_active <= reads_active +(skid_arlen+1);
		2'b11: reads_active <= reads_active + skid_arlen;
		// Verilator lint_on  WIDTH
		endcase
		// }}}

		// exread_pending, exread_active
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			r_exread_pending <= 0;
			r_exread_active  <= 1'b0;
		end else if (skid_arvalid && skid_arready && skid_arlock)
		begin
			// Verilator lint_off WIDTH
			r_exread_pending <= reads_active + skid_arlen + 1;
			// Verilator lint_on  WIDTH
			r_exread_active  <= 1;
		end else if (S_AXI_RVALID && S_AXI_RREADY && r_exread_active)
		begin
			r_exread_pending <= r_exread_pending - 1;
			r_exread_active  <= (r_exread_pending > 1);
		end

		assign	exread_active = r_exread_active;
		// }}}

		// Address manipulation: aw_wrap_mask, skid_awmax/min
		// {{{
		always @(*)
		begin
			// Verilator lint_off WIDTH
			aw_wrap_mask = ((skid_awlen[3:0]+1) << skid_awsize)-1;
			ar_wrap_mask = ((skid_arlen[3:0]+1) << skid_arsize)-1;
			// Verilator lint_on  WIDTH

			if (skid_awburst == AXI_FIX)
			begin
				skid_awmax = skid_awaddr;
				case(skid_awsize)
				3'h0: begin end
				3'h1: skid_awmax[  0] = -1;
				3'h2: skid_awmax[1:0] = -1;
				3'h3: skid_awmax[2:0] = -1;
				3'h4: skid_awmax[3:0] = -1;
				3'h5: skid_awmax[4:0] = -1;
				3'h6: skid_awmax[5:0] = -1;
				3'h7: skid_awmax[6:0] = -1;
				endcase
				skid_awmin = skid_awaddr;
			end else if (skid_awburst == AXI_INCR)
			begin
				// Verilator lint_off WIDTH
				skid_awmax = (skid_awaddr
					+((skid_awlen+1) << skid_awsize)-1
							>= ex_amin);
				// Verilator lint_on  WIDTH
				skid_awmin = skid_awaddr;
			end else // if (skid_awburst == AXI_WRAP)
			begin
				skid_awmin = skid_awaddr & ~aw_wrap_mask;
				skid_awmax = skid_awaddr |  aw_wrap_mask;
			end
		end
		// }}}

		// ex_valid
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			ex_valid <= 1'b0;
		else if (skid_arvalid && skid_arready && skid_arlock)
			ex_valid <= 1'b1;
		else if (skid_awvalid && skid_awready)
		begin
			if ((skid_awmin <= ex_amax)
					&& (skid_awmax >= ex_amin))
				ex_valid <= 0;
		end
		// }}}

		// Ex access transaction details: ex_*
		// {{{
		always @(posedge S_AXI_ACLK)
		if (skid_arvalid && skid_arready && skid_arlock)
		begin
			ex_id    <= skid_arid;
			ex_addr  <= skid_araddr;
			ex_len   <= skid_arlen;
			ex_burst <= skid_arburst;
			ex_size  <= skid_arsize;

			if (skid_arburst == 2'b00)
			begin
				ex_amax <= ex_addr;
				ex_amin <= ex_addr;

				case(skid_arsize)
				3'h0: begin end
				3'h1: { ex_amax[0], ex_amin[0] } <= 2'b00;
				3'h2: { ex_amax[1:0], ex_amin[1:0]} <= 4'h0;
				3'h3: { ex_amax[2:0], ex_amin[2:0]} <= 6'h0;
				3'h4: { ex_amax[3:0], ex_amin[3:0]} <= 8'h0;
				3'h5: { ex_amax[4:0], ex_amin[4:0]} <= 10'h0;
				3'h6: { ex_amax[5:0], ex_amin[5:0]} <= 12'h0;
				3'h7: { ex_amax[6:0], ex_amin[6:0]} <= 14'h0;
				endcase
			end else if (skid_arburst == 2'b01)
			begin /// INCR
				// Verilator lint_off WIDTH
				ex_amax  <= skid_araddr
					+ ((skid_arlen+1) << skid_arsize)-1;
				// Verilator lint_on  WIDTH
				ex_amin  <= skid_araddr;
			end else begin // WRAP
				ex_amin <= skid_araddr & ~ar_wrap_mask;
				ex_amax <= skid_araddr |  ar_wrap_mask;
			end
		end
		// }}}

		// exwrite_access: Is this a valid exclusive access write?
		// {{{
		always @(*)
		begin
			r_exwrite_access = ex_valid
				&& skid_awid    == ex_id
				&& skid_awaddr  == ex_addr
				&& skid_awlen   == ex_len
				&& skid_awburst == ex_burst
				&& skid_awsize  == ex_size;
		end

		assign	exwrite_access = r_exwrite_access;
		// }}}
		// }}}
	end else begin : NO_LOCK
		// {{{
		assign	exwrite_hold   = 1'b0;
		assign	exread_hold    = 1'b0;

		assign	exwrite_access = 1'b0;

		// Verililator lint_off UNUSED
		wire	unused_lock;
		assign	unused_lock = &{ 1'b0, write_busy };
		// Verililator lint_on  UNUSED
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

		assign	r_wb_ack  = 1'b0;
		assign	r_wb_stall= 1'b0;
		assign	r_wb_ack  = 1'b0;
		assign	r_wb_err  = 1'b0;
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
