////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/axiupsz.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2026, Gisselquist Technology, LLC
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
module axiupsz #(
		// {{{
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter	C_AXI_ID_WIDTH	= 1,
		parameter	C_S_AXI_DATA_WIDTH	= 32,
		parameter	C_M_AXI_DATA_WIDTH	= 64,
		parameter	C_AXI_ADDR_WIDTH	= 16,
		localparam	IW	= C_AXI_ID_WIDTH,
		localparam	AW	= C_AXI_ADDR_WIDTH,
		localparam	SDW	= C_S_AXI_DATA_WIDTH,
		localparam	MDW	= C_M_AXI_DATA_WIDTH
		// }}}
	) (
		// {{{
		input	wire			S_CLK,
		input	wire			S_ARESETN,
		//
		// The input side, operating at a width of SDW.
		// {{{
		//
		//	Write address
		input	wire			S_AWVALID,
		output	reg			S_AWREADY,
		input	wire [IW-1 : 0]		S_AWID,
		input	wire [AW-1 : 0]		S_AWADDR,
		input	wire [7 : 0]		S_AWLEN,
		input	wire [2 : 0]		S_AWSIZE,
		input	wire [1 : 0]		S_AWBURST,
		input	wire			S_AWLOCK,
		input	wire [3 : 0]		S_AWCACHE,
		input	wire [2 : 0]		S_AWPROT,
		input	wire [3 : 0]		S_AWQOS,
		//	Write data
		input	wire			S_WVALID,
		output	reg			S_WREADY,
		input	wire [SDW-1 : 0]	S_WDATA,
		input	wire [(SDW/8)-1 : 0]	S_WSTRB,
		input	wire			S_WLAST,
		//	Write return
		output	wire			S_BVALID,
		input	wire			S_BREADY,
		output	wire [IW-1 : 0]		S_BID,
		output	wire [1 : 0]		S_BRESP,
		//	Read address
		input	wire			S_ARVALID,
		output	reg			S_ARREADY,
		input	wire [IW-1 : 0]		S_ARID,
		input	wire [AW-1 : 0]		S_ARADDR,
		input	wire [7 : 0]		S_ARLEN,
		input	wire [2 : 0]		S_ARSIZE,
		input	wire [1 : 0]		S_ARBURST,
		input	wire			S_ARLOCK,
		input	wire [3 : 0]		S_ARCACHE,
		input	wire [2 : 0]		S_ARPROT,
		input	wire [3 : 0]		S_ARQOS,
		//	Read data
		output	reg			S_RVALID,
		input	wire			S_RREADY,
		output	reg [IW-1 : 0]		S_RID,
		output	reg [SDW-1 : 0]		S_RDATA,
		output	reg [1 : 0]		S_RRESP,
		output	reg			S_RLAST,
		// }}}
		//
		// The output side, operating at a width of MDW, MDW > SDW
		// {{{
		//	Write address
		// {{{
		output	reg			M_AWVALID,
		input	wire			M_AWREADY,
		output	reg [IW-1 : 0]		M_AWID,
		output	reg [AW-1 : 0]		M_AWADDR,
		output	reg [7 : 0]		M_AWLEN,
		output	reg [2 : 0]		M_AWSIZE,
		output	reg [1 : 0]		M_AWBURST,
		output	reg			M_AWLOCK,
		output	reg [3 : 0]		M_AWCACHE,
		output	reg [2 : 0]		M_AWPROT,
		output	reg [3 : 0]		M_AWQOS,
		//	Write data
		output	reg			M_WVALID,
		input	wire			M_WREADY,
		output	reg [MDW-1 : 0]		M_WDATA,
		output	reg [(MDW/8)-1 : 0]	M_WSTRB,
		output	reg			M_WLAST,
		//	Write return
		input	wire			M_BVALID,
		output	wire			M_BREADY,
		input	wire [IW-1 : 0]		M_BID,
		input	wire [1 : 0]		M_BRESP,
		// }}}
		//	Read address
		// {{{
		output	reg			M_ARVALID,
		input	wire			M_ARREADY,
		output	reg [IW-1 : 0]		M_ARID,
		output	reg [AW-1 : 0]		M_ARADDR,
		output	reg [7 : 0]		M_ARLEN,
		output	reg [2 : 0]		M_ARSIZE,
		output	reg [1 : 0]		M_ARBURST,
		output	reg			M_ARLOCK,
		output	reg [3 : 0]		M_ARCACHE,
		output	reg [2 : 0]		M_ARPROT,
		output	reg [3 : 0]		M_ARQOS,
		//	Read data
		input	wire			M_RVALID,
		output	wire			M_RREADY,
		input	wire [IW-1 : 0]		M_RID,
		input	wire [MDW-1 : 0]	M_RDATA,
		input	wire [1 : 0]		M_RRESP,
		input	wire			M_RLAST
		// }}}
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	MLSB = $clog2(MDW/8), SLSB = $clog2(SDW/8);

	// AW Skidbuffer
	// {{{
	wire			skd_awvalid, skd_awready;
	wire	[IW-1:0]	skd_awid;
	wire	[AW-1:0]	skd_awaddr;
	wire	[7:0]		skd_awlen;
	wire	[1:0]		skd_awburst;
	wire	[2:0]		skd_awsize;
	wire			skd_awlock;
	wire	[3:0]		skd_awcache;
	wire	[2:0]		skd_awprot;
	wire	[3:0]		skd_awqos;
	// }}}

	// W Skidbuffer
	// {{{
	wire			skd_wvalid, skd_wready;
	wire	[SDW-1:0]	skd_wdata;
	wire	[SDW/8-1:0]	skd_wstrb;
	wire			skd_wlast;
	// }}}

	// Next write address
	// {{{
	reg			aw_active;
	reg	[AW-1:0]	waddr;
	reg	[7:0]		wlen;
	reg	[2:0]		wsize;
	reg	[1:0]		wburst;
	wire	[AW-1:0]	next_waddr, this_awaddr;
	// }}}

	// AR Skidbuffer
	// {{{
	wire			skd_arvalid, skd_arready;
	wire	[IW-1:0]	skd_arid;
	wire	[AW-1:0]	skd_araddr;
	wire	[7:0]		skd_arlen;
	wire	[1:0]		skd_arburst;
	wire	[2:0]		skd_arsize;
	wire			skd_arlock;
	wire	[3:0]		skd_arcache;
	wire	[2:0]		skd_arprot;
	wire	[3:0]		skd_arqos;
	// }}}

	reg	[IW-1:0]	arid;
	// AR/R FIFO
	// {{{
	wire		rfifo_read, rfifo_full, rfifo_empty;
	wire	[2:0]	rfifo_size;
	wire	[1:0]	rfifo_burst;
	wire	[7:0]	rfifo_len;
	wire [AW-1:0]	rfifo_addr;
	wire	[5:0]	ign_rfifo_fill;
	// }}}

	// R Skidbuffer
	// {{{
	wire			skd_rvalid, skd_rready;
	wire	[MDW-1:0]	skd_rdata;
	wire			skd_rlast;
	wire	[1:0]		skd_rresp;
	// }}}

	// Next read address
	// {{{
	reg			ar_active;
	wire			next_ar_active;

	reg	[AW-1:0]	raddr;
	reg	[7:0]		rlen;
	reg	[2:0]		rsize;
	reg	[1:0]		rburst;
	wire	[AW-1:0]	next_raddr;
	// }}}

	// }}}

	// Write Addresses
	// {{{
	skidbuffer #(
		// {{{
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1'b1),
`endif
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_OUTREG(1'b0), .DW(IW+AW+8+3+2+1+4+3+4)
		// }}}
	) u_awskid (
		// {{{
		.i_clk(S_CLK), .i_reset(!S_ARESETN),
		//
		.i_valid(S_AWVALID), .o_ready(S_AWREADY),
		.i_data({ S_AWID, S_AWADDR, S_AWLEN,
			S_AWSIZE, S_AWBURST, S_AWLOCK,
			S_AWCACHE, S_AWPROT, S_AWQOS }),
		//
		.o_valid(skd_awvalid), .i_ready(skd_awready),
		.o_data({
			skd_awid, skd_awaddr, skd_awlen,
			skd_awsize, skd_awburst, skd_awlock,
			skd_awcache, skd_awprot, skd_awqos })
		// }}}
	);

	initial	M_AWVALID = 1'b0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		M_AWVALID <= 1'b0;
	else if (!M_AWVALID || M_AWREADY)
		M_AWVALID <= skd_awvalid && skd_awready;

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
	begin
		M_AWID    <= {(IW){1'b0}};
		M_AWADDR  <= {(AW){1'b0}};
		M_AWLEN   <= {(8){1'b0}};
		M_AWSIZE  <= 3'h0;
		M_AWBURST <= 2'h0;
		M_AWLOCK  <= 1'b0;
		M_AWCACHE <= 4'h0;
		M_AWPROT  <= 3'h0;
		M_AWQOS   <= 4'h0;
	end else if (!M_AWVALID || M_AWREADY)
	begin
		M_AWID    <= skd_awid;
		M_AWADDR  <= skd_awaddr;
		M_AWLEN   <= skd_awlen;
		M_AWSIZE  <= skd_awsize;
		M_AWBURST <= skd_awburst;
		M_AWLOCK  <= skd_awlock;
		M_AWCACHE <= skd_awcache;
		M_AWPROT  <= skd_awprot;
		M_AWQOS   <= skd_awqos;

		if (OPT_LOWPOWER && !skd_awvalid)
		begin
			M_AWID    <= {(IW){1'b0}};
			M_AWADDR  <= {(AW){1'b0}};
			M_AWLEN   <= {(8){1'b0}};
			M_AWSIZE  <= 3'h0;
			M_AWBURST <= 2'h0;
			M_AWLOCK  <= 1'b0;
			M_AWCACHE <= 4'h0;
			M_AWPROT  <= 3'h0;
			M_AWQOS   <= 4'h0;
		end
	end

	always @(posedge S_CLK)
	if (!S_ARESETN)
		aw_active <= 1'b0;
	else if (skd_wvalid && skd_wready && skd_wlast)
	begin
		if (!aw_active)
			aw_active <= 1'b0;
		else if (!skd_awvalid || !skd_awready)
			aw_active <= 1'b0;
	end else if (skd_awvalid && skd_awready)
		aw_active <= 1'b1;

	assign	skd_awready = (!M_AWVALID || M_AWREADY) && skd_awvalid
		&& (!aw_active
			|| ((!M_WVALID || M_WREADY)&& skd_wvalid && skd_wlast));
	// }}}

	// Write Data
	// {{{
	skidbuffer #(
		// {{{
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1'b1),
`endif
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_OUTREG(1'b0), .DW(1+SDW/8+SDW)
		// }}}
	) u_wskid (
		// {{{
		.i_clk(S_CLK), .i_reset(!S_ARESETN),
		//
		.i_valid(S_WVALID), .o_ready(S_WREADY),
		.i_data({ S_WLAST, S_WSTRB, S_WDATA }),
		//
		.o_valid(skd_wvalid), .i_ready(skd_wready),
		.o_data({
			skd_wlast, skd_wstrb, skd_wdata })
		// }}}
	);

	initial	M_WVALID = 0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		M_WVALID <= 0;
	else if (!M_WVALID || M_WREADY)
		M_WVALID <= skd_wvalid && skd_wready;

	axi_addr #(
		.AW(AW), .DW(SDW)
	) next_write_address (
		.i_last_addr(	skd_awready ? skd_awaddr  : waddr),
		.i_size(	skd_awready ? skd_awsize  : wsize),
		.i_burst(	skd_awready ? skd_awburst : wburst),
		.i_len(		skd_awready ? skd_awlen : wlen),
		.o_next_addr(next_waddr)
	);

	always @(posedge S_CLK)
	if (!S_ARESETN)
	begin
		waddr <= 0;
		wlen  <= 0;
		wsize <= 3'h0;
		wburst<= 2'h0;
	end else if (skd_awvalid && skd_awready)
	begin
		waddr <= next_waddr;
		wlen  <= skd_awlen;
		wsize <= skd_awsize;
		wburst<= skd_awburst;

		if (!skd_wvalid || !skd_wready || aw_active)
			waddr <= skd_awaddr;
	end else if (skd_wvalid && skd_wready)
		waddr <= next_waddr;

	assign	this_awaddr = aw_active ? waddr : skd_awaddr;

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
	begin
		M_WLAST <= 0;
		M_WSTRB <= 0;
		M_WDATA <= 0;
	end else if (!M_WVALID || M_WREADY)
	begin
		M_WLAST <= skd_wlast;
		// Verilator lint_off WIDTH
		M_WDATA <= skd_wdata << (this_awaddr[MLSB-1:SLSB]* SDW);
		M_WSTRB <= skd_wstrb << (this_awaddr[MLSB-1:SLSB]*(SDW/8));
		// Verilator lint_on  WIDTH

		if (OPT_LOWPOWER && !skd_wvalid)
		begin
			M_WLAST <= 0;
			M_WSTRB <= 0;
			M_WDATA <= 0;
		end
	end

	assign	skd_wready = (!M_WVALID || M_WREADY) && (aw_active
			|| (skd_awvalid && skd_awready));
	// }}}

	// Write response channel--pass through
	// {{{
	assign	S_BVALID = M_BVALID;
	assign	M_BREADY = S_BREADY;
	assign	S_BID    = M_BID;
	assign	S_BRESP  = M_BRESP;
	// }}}

	// Read Addresses
	// {{{
	skidbuffer #(
		// {{{
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1'b1),
`endif
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_OUTREG(1'b0), .DW(IW+AW+8+3+2+1+4+3+4)
		// }}}
	) u_arskid (
		// {{{
		.i_clk(S_CLK), .i_reset(!S_ARESETN),
		//
		.i_valid(S_ARVALID), .o_ready(S_ARREADY),
		.i_data({ S_ARID, S_ARADDR, S_ARLEN,
			S_ARSIZE, S_ARBURST, S_ARLOCK,
			S_ARCACHE, S_ARPROT, S_ARQOS }),
		//
		.o_valid(skd_arvalid), .i_ready(skd_arready),
		.o_data({
			skd_arid, skd_araddr, skd_arlen,
			skd_arsize, skd_arburst, skd_arlock,
			skd_arcache, skd_arprot, skd_arqos })
		// }}}
	);

	initial	M_ARVALID = 1'b0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		M_ARVALID <= 1'b0;
	else if (!M_ARVALID || M_ARREADY)
		M_ARVALID <= skd_arvalid && skd_arready;

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
	begin
		M_ARID    <= {(IW){1'b0}};
		M_ARADDR  <= {(AW){1'b0}};
		M_ARLEN   <= {(8){1'b0}};
		M_ARSIZE  <= 3'h0;
		M_ARBURST <= 2'h0;
		M_ARLOCK  <= 1'b0;
		M_ARCACHE <= 4'h0;
		M_ARPROT  <= 3'h0;
		M_ARQOS   <= 4'h0;
	end else if (!M_ARVALID || M_ARREADY)
	begin
		M_ARID    <= skd_arid;
		M_ARADDR  <= skd_araddr;
		M_ARLEN   <= skd_arlen;
		M_ARSIZE  <= skd_arsize;
		M_ARBURST <= skd_arburst;
		M_ARLOCK  <= skd_arlock;
		M_ARCACHE <= skd_arcache;
		M_ARPROT  <= skd_arprot;
		M_ARQOS   <= skd_arqos;

		if (OPT_LOWPOWER && !skd_arvalid)
		begin
			M_ARID    <= {(IW){1'b0}};
			M_ARADDR  <= {(AW){1'b0}};
			M_ARLEN   <= {(8){1'b0}};
			M_ARSIZE  <= 3'h0;
			M_ARBURST <= 2'h0;
			M_ARLOCK  <= 1'b0;
			M_ARCACHE <= 4'h0;
			M_ARPROT  <= 3'h0;
			M_ARQOS   <= 4'h0;
		end
	end

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
		arid <= 0;
	else if (skd_arvalid && skd_arready)
		arid <= skd_arid;

	assign	skd_arready = (!M_ARVALID || M_ARREADY) && skd_arvalid
			&& (arid == skd_arid || (!ar_active && rfifo_empty)) && !rfifo_full;
	// }}}

	// Read returns
	// {{{
`ifdef	FORMAL
	wire	[5:0]	f_rfifo_first_addr, f_rfifo_second_addr,
			f_rfifo_distance_to_first, f_rfifo_distance_to_second;
	wire		f_rfifo_first_in_fifo, f_rfifo_second_in_fifo;
	wire	[AW+8+2+3-1:0]	f_rfifo_first_data, f_rfifo_second_data;
`endif
	sfifo #(
		.BW(AW+8+2+3), .LGFLEN(5)
	) u_arfifo (
		.i_clk(S_CLK), .i_reset(!S_ARESETN),
		.i_wr(skd_arvalid && skd_arready),
		.i_data({ skd_arsize, skd_arburst, skd_arlen, skd_araddr }),
			.o_full(rfifo_full),
			.o_fill(ign_rfifo_fill),
		.i_rd(rfifo_read),
		.o_data({ rfifo_size, rfifo_burst, rfifo_len, rfifo_addr }),
			.o_empty(rfifo_empty)
`ifdef	FORMAL
		, .f_first_addr(f_rfifo_first_addr),
		.f_second_addr(f_rfifo_second_addr),
		.f_first_data(f_rfifo_first_data),
		.f_second_data(f_rfifo_second_data),
		.f_first_in_fifo(f_rfifo_first_in_fifo),
		.f_second_in_fifo(f_rfifo_second_in_fifo),
		.f_distance_to_first(f_rfifo_distance_to_first),
		.f_distance_to_second(f_rfifo_distance_to_second)
`endif
	);

	axi_addr #(
		.AW(AW), .DW(SDW)
	) next_read_address (
		.i_last_addr(	raddr),
		.i_size(	rsize),
		.i_burst(	rburst),
		.i_len(		rlen),
		.o_next_addr(next_raddr)
	);


	skidbuffer #(
		// {{{
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1'b1),
`endif
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_OUTREG(1'b0), .DW(MDW+2+1)
		// }}}
	) u_rskid (
		// {{{
		.i_clk(S_CLK), .i_reset(!S_ARESETN),
		//
		.i_valid(M_RVALID), .o_ready(M_RREADY),
		.i_data({ M_RRESP, M_RLAST, M_RDATA }),
		//
		.o_valid(skd_rvalid), .i_ready(skd_rready),
		.o_data({ skd_rresp, skd_rlast, skd_rdata })
		// }}}
	);

	always @(posedge S_CLK)
	if (!S_ARESETN)
		ar_active <= 0;
	else if (rfifo_read)
		ar_active <= 1'b1;
	else if (skd_rvalid && skd_rready)
		ar_active <= !skd_rlast;

	assign	next_ar_active = ar_active && (!skd_rvalid || !skd_rready
					|| !skd_rlast);

	always @(posedge S_CLK)
	if (!S_ARESETN)
	begin
		raddr  <= 0;
		rsize <= 0;
		rburst <= 0;
		rlen <= 0;
	end else if (rfifo_read)
	begin
		raddr  <= rfifo_addr;
		rlen   <= rfifo_len;
		rsize  <= rfifo_size;
		rburst <= rfifo_burst;
	end else if (skd_rvalid && skd_rready)
		raddr <= next_raddr;

	assign	rfifo_read = (!ar_active
				|| (skd_rvalid && (!S_RVALID || S_RREADY) && skd_rlast))&& !rfifo_empty;
			// skd_rvalid && skd_rready
			//		&& (!ar_active || skd_rlast);

	initial	S_RVALID = 1'b0;
	always @(posedge S_CLK)
	if (!S_ARESETN)
		S_RVALID <= 0;
	else if (!S_RVALID || S_RREADY)
		S_RVALID <= skd_rvalid;

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
		S_RID <= 0;
	else if (skd_rvalid && (!S_RVALID || S_RREADY))
		S_RID <= arid;

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
		{ S_RRESP, S_RLAST } <= 0;
	else if (!S_RVALID || S_RREADY)
	begin
		{ S_RRESP, S_RLAST } <= { skd_rresp, skd_rlast };
		if (OPT_LOWPOWER && (!skd_rvalid || !skd_rready))
			{ S_RRESP, S_RLAST } <= 3'h0;
	end

	always @(posedge S_CLK)
	if (!S_ARESETN && OPT_LOWPOWER)
		S_RDATA <= 0;
	else if (!S_RVALID || S_RREADY)
	begin
		// Verilator lint_off WIDTH
		if (ar_active)
			S_RDATA <= skd_rdata >> (SDW * raddr[MLSB-1:SLSB]);
		else
			S_RDATA <= skd_rdata >> (SDW * rfifo_addr[MLSB-1:SLSB]);
		// Verilator lint_on  WIDTH
		if (OPT_LOWPOWER && (!skd_rvalid || !skd_rready))
			S_RDATA <= {(SDW){1'b0}};
	end

	assign	skd_rready = !S_RVALID || S_RREADY;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_RID, ign_rfifo_fill };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Local (formal) declarations
	// {{{
	localparam	F_LGDEPTH = 20;
	reg		f_past_valid;
	reg	[8:0]	f_rlen;
	wire	[F_LGDEPTH-1:0]	fm_awr_nbursts, fs_awr_nbursts;
	wire	[9-1:0]		fm_wr_pending, fs_wr_pending;
	wire	[F_LGDEPTH-1:0]	fm_rd_nbursts, fs_rd_nbursts;
	wire	[F_LGDEPTH-1:0]	fm_rd_outstanding, fs_rd_outstanding;
	wire	[IW-1:0]	fm_wr_checkid, fs_wr_checkid;
	wire			fm_wr_ckvalid, fs_wr_ckvalid;
	wire	[F_LGDEPTH-1:0]	fm_wrid_nbursts, fs_wrid_nbursts;
	wire	[AW-1:0]	fm_wr_addr, fs_wr_addr;
	reg	[AW-1:0]	f_raddr;
	wire	[7:0]		fm_wr_incr, fs_wr_incr;
	wire	[1:0]		fm_wr_burst, fs_wr_burst;
	wire	[2:0]		fm_wr_size, fs_wr_size;
	wire	[7:0]		fm_wr_len, fs_wr_len;
	wire			fm_wr_lockd, fs_wr_lockd;

	wire	[IW-1:0]	fm_rd_checkid, fs_rd_checkid;
	wire			fm_rd_ckvalid, fs_rd_ckvalid;
	wire	[8:0]		fm_rd_cklen, fs_rd_cklen;
	wire	[AW-1:0]	fm_rd_ckaddr, fs_rd_ckaddr;
	wire	[7:0]		fm_rd_ckincr, fs_rd_ckincr;
	wire	[1:0]		fm_rd_ckburst, fs_rd_ckburst;
	wire	[2:0]		fm_rd_cksize, fs_rd_cksize;
	wire	[7:0]		fm_rd_ckarlen, fs_rd_ckarlen;
	wire			fm_rd_cklockd, fs_rd_cklockd;

	wire	[F_LGDEPTH-1:0]	fm_rdid_nbursts, fs_rdid_nbursts;
	wire	[F_LGDEPTH-1:0]	fm_rdid_outstanding, fs_rdid_outstanding;
	wire	[F_LGDEPTH-1:0]	fm_rdid_ckign_nbursts, fs_rdid_ckign_nbursts;
	wire	[F_LGDEPTH-1:0]	fm_rdid_ckign_outstanding, fs_rdid_ckign_outstanding;
	wire	[1:0]		fm_ex_state, fs_ex_state;
	wire			fm_ex_checklock, fs_ex_checklock;
	wire	[F_LGDEPTH-1:0]	fm_rdid_bursts_to_lock, fs_rdid_bursts_to_lock;
	wire	[F_LGDEPTH-1:0]	fm_wrid_bursts_to_exwrite, fs_wrid_bursts_to_exwrite;
	reg	[AW-1:0]	f_waddr;
	wire	[AW-1:0]	f_wnext, f_rnext;
	reg	[7:0]		f_wlen;
	reg	[2:0]		f_wsize;
	reg	[1:0]		f_wburst;
	// }}}

	initial	f_past_valid = 0;
	always @(posedge S_CLK)
		f_past_valid <= 1;

	faxi_master #(
		// {{{
		.F_LGDEPTH(F_LGDEPTH), .F_AXI_MAXRSTALL(0),
		.C_AXI_ID_WIDTH(IW), .C_AXI_DATA_WIDTH(MDW),
		.C_AXI_ADDR_WIDTH(AW),
		.OPT_EXCLUSIVE(1'b0)
		// }}}
	) faxim (
		// {{{
		.i_clk(S_CLK), .i_axi_reset_n(S_ARESETN),
		//
		.i_axi_awvalid(M_AWVALID),
		.i_axi_awready(M_AWREADY),
		.i_axi_awid(M_AWID),
		.i_axi_awaddr(M_AWADDR),
		.i_axi_awlen(M_AWLEN),
		.i_axi_awburst(M_AWBURST),
		.i_axi_awsize(M_AWSIZE),
		.i_axi_awlock(M_AWLOCK),
		.i_axi_awcache(M_AWCACHE),
		.i_axi_awprot(M_AWPROT),
		.i_axi_awqos(M_AWQOS),
		//
		.i_axi_wvalid(M_WVALID),
		.i_axi_wready(M_WREADY),
		.i_axi_wdata(M_WDATA),
		.i_axi_wstrb(M_WSTRB),
		.i_axi_wlast(M_WLAST),
		//
		.i_axi_bvalid(M_BVALID),
		.i_axi_bready(M_BREADY),
		.i_axi_bid(M_BID),
		.i_axi_bresp(M_BRESP),
		//
		.i_axi_arvalid(M_ARVALID),
		.i_axi_arready(M_ARREADY),
		.i_axi_arid(M_ARID),
		.i_axi_araddr(M_ARADDR),
		.i_axi_arlen(M_ARLEN),
		.i_axi_arburst(M_ARBURST),
		.i_axi_arsize(M_ARSIZE),
		.i_axi_arlock(M_ARLOCK),
		.i_axi_arcache(M_ARCACHE),
		.i_axi_arprot(M_ARPROT),
		.i_axi_arqos(M_ARQOS),
		//
		.i_axi_rvalid(M_RVALID),
		.i_axi_rready(M_RREADY),
		.i_axi_rid(M_RID),
		.i_axi_rdata(M_RDATA),
		.i_axi_rresp(M_RRESP),
		.i_axi_rlast(M_RLAST),
		//
		.f_axi_awr_nbursts(fm_awr_nbursts),
		.f_axi_wr_pending(fm_wr_pending),
		.f_axi_rd_nbursts(fm_rd_nbursts),
		.f_axi_rd_outstanding(fm_rd_outstanding),
		//
		.f_axi_wr_checkid(fm_wr_checkid),
		.f_axi_wr_ckvalid(fm_wr_ckvalid),
		.f_axi_wrid_nbursts(fm_wrid_nbursts),
		.f_axi_wr_addr(fm_wr_addr),
		.f_axi_wr_incr(fm_wr_incr),
		.f_axi_wr_burst(fm_wr_burst),
		.f_axi_wr_size(fm_wr_size),
		.f_axi_wr_len(fm_wr_len),
		.f_axi_wr_lockd(fm_wr_lockd),
		//
		.f_axi_rd_checkid(fm_rd_checkid),
		.f_axi_rd_ckvalid(fm_rd_ckvalid),
		.f_axi_rd_cklen(fm_rd_cklen),
		.f_axi_rd_ckaddr(fm_rd_ckaddr),
		.f_axi_rd_ckincr(fm_rd_ckincr),
		.f_axi_rd_ckburst(fm_rd_ckburst),
		.f_axi_rd_cksize(fm_rd_cksize),
		.f_axi_rd_ckarlen(fm_rd_ckarlen),
		.f_axi_rd_cklockd(fm_rd_cklockd),
		//
		.f_axi_rdid_nbursts(fm_rdid_nbursts),
		.f_axi_rdid_outstanding(fm_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(fm_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(fm_rdid_ckign_outstanding),
		//
		.f_axi_ex_state(fm_ex_state),
		.f_axi_ex_checklock(fm_ex_checklock),
		.f_axi_rdid_bursts_to_lock(fm_rdid_bursts_to_lock),
		.f_axi_wrid_bursts_to_exwrite(fm_wrid_bursts_to_exwrite),
		.i_active_lock(1'b0),
		.i_exlock_addr(0),
		.i_exlock_len(1'b0),
		.i_exlock_burst(2'b00),
		.i_exlock_size(3'h0),
		//
		.f_axi_exreq_addr(),
		.f_axi_exreq_len(),
		.f_axi_exreq_burst(),
		.f_axi_exreq_size(),
		.f_axi_exreq_return()
		// }}}
	);

	faxi_slave #(
		// {{{
		.F_LGDEPTH(F_LGDEPTH), .F_AXI_MAXDELAY(0), .F_AXI_MAXSTALL(0),
		.C_AXI_ID_WIDTH(IW), .C_AXI_DATA_WIDTH(SDW),
		.C_AXI_ADDR_WIDTH(AW),
		.OPT_EXCLUSIVE(1'b0)
		// }}}
	) faxis (
		// {{{
		.i_clk(S_CLK), .i_axi_reset_n(S_ARESETN),
		//
		.i_axi_awvalid(S_AWVALID),
		.i_axi_awready(S_AWREADY),
		.i_axi_awid(S_AWID),
		.i_axi_awaddr(S_AWADDR),
		.i_axi_awlen(S_AWLEN),
		.i_axi_awburst(S_AWBURST),
		.i_axi_awsize(S_AWSIZE),
		.i_axi_awlock(S_AWLOCK),
		.i_axi_awcache(S_AWCACHE),
		.i_axi_awprot(S_AWPROT),
		.i_axi_awqos(S_AWQOS),
		//
		.i_axi_wvalid(S_WVALID),
		.i_axi_wready(S_WREADY),
		.i_axi_wdata(S_WDATA),
		.i_axi_wstrb(S_WSTRB),
		.i_axi_wlast(S_WLAST),
		//
		.i_axi_bvalid(S_BVALID),
		.i_axi_bready(S_BREADY),
		.i_axi_bid(S_BID),
		.i_axi_bresp(S_BRESP),
		//
		.i_axi_arvalid(S_ARVALID),
		.i_axi_arready(S_ARREADY),
		.i_axi_arid(S_ARID),
		.i_axi_araddr(S_ARADDR),
		.i_axi_arlen(S_ARLEN),
		.i_axi_arburst(S_ARBURST),
		.i_axi_arsize(S_ARSIZE),
		.i_axi_arlock(S_ARLOCK),
		.i_axi_arcache(S_ARCACHE),
		.i_axi_arprot(S_ARPROT),
		.i_axi_arqos(S_ARQOS),
		//
		.i_axi_rvalid(S_RVALID),
		.i_axi_rready(S_RREADY),
		.i_axi_rid(S_RID),
		.i_axi_rdata(S_RDATA),
		.i_axi_rresp(S_RRESP),
		.i_axi_rlast(S_RLAST),
		//
		.f_axi_awr_nbursts(fs_awr_nbursts),
		.f_axi_wr_pending(fs_wr_pending),
		.f_axi_rd_nbursts(fs_rd_nbursts),
		.f_axi_rd_outstanding(fs_rd_outstanding),
		//
		.f_axi_wr_checkid(fs_wr_checkid),
		.f_axi_wr_ckvalid(fs_wr_ckvalid),
		.f_axi_wrid_nbursts(fs_wrid_nbursts),
		.f_axi_wr_addr(fs_wr_addr),
		.f_axi_wr_incr(fs_wr_incr),
		.f_axi_wr_burst(fs_wr_burst),
		.f_axi_wr_size(fs_wr_size),
		.f_axi_wr_len(fs_wr_len),
		.f_axi_wr_lockd(fs_wr_lockd),
		//
		.f_axi_rd_checkid(fs_rd_checkid),
		.f_axi_rd_ckvalid(fs_rd_ckvalid),
		.f_axi_rd_cklen(fs_rd_cklen),
		.f_axi_rd_ckaddr(fs_rd_ckaddr),
		.f_axi_rd_ckincr(fs_rd_ckincr),
		.f_axi_rd_ckburst(fs_rd_ckburst),
		.f_axi_rd_cksize(fs_rd_cksize),
		.f_axi_rd_ckarlen(fs_rd_ckarlen),
		.f_axi_rd_cklockd(fs_rd_cklockd),
		//
		.f_axi_rdid_nbursts(fs_rdid_nbursts),
		.f_axi_rdid_outstanding(fs_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(fs_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(fs_rdid_ckign_outstanding),
		//
		.f_axi_ex_state(fs_ex_state),
		.f_axi_ex_checklock(fs_ex_checklock),
		.f_axi_rdid_bursts_to_lock(fs_rdid_bursts_to_lock),
		.f_axi_wrid_bursts_to_exwrite(fs_wrid_bursts_to_exwrite),
		.i_active_lock(1'b0),
		.i_exlock_addr(0),
		.i_exlock_len(1'b0),
		.i_exlock_burst(2'b00),
		.i_exlock_size(3'h0),
		//
		.f_axi_exreq_addr(),
		.f_axi_exreq_len(),
		.f_axi_exreq_burst(),
		.f_axi_exreq_size(),
		.f_axi_exreq_return()
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Induction write properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(*)
		assume(fm_wr_checkid == fs_wr_checkid);

	always @(posedge S_CLK)
	if (!M_WVALID || M_WREADY)
	begin
		// if (!skd_awready)
		if (skd_awvalid && skd_awready && !aw_active)
		begin
			f_waddr  <= skd_awaddr;
			f_wsize  <= skd_awsize;
			f_wburst <= skd_awburst;
			f_wlen   <= skd_awlen;
		end else begin
			f_waddr  <= waddr;
			f_wsize  <= wsize;
			f_wburst <= wburst;
			f_wlen   <= wlen;
		end
	end

	faxi_addr #(
		.AW(AW)
	) f_next_waddr (
		.i_last_addr(	M_AWVALID ? M_AWADDR  : f_waddr),
		.i_size(	M_AWVALID ? M_AWSIZE  : f_wsize),
		.i_burst(	M_AWVALID ? M_AWBURST : f_wburst),
		.i_len(		M_AWVALID ? M_AWLEN   : f_wlen),
		.o_incr(),
		.o_next_addr(f_wnext)
	);

	always @(*)
	if (f_past_valid && fs_wr_pending > 0)
	begin
		assert(waddr == fs_wr_addr);
		assert(wsize == fs_wr_size);
		assert(wburst== fs_wr_burst);
		assert(wlen  == fs_wr_len);
	end

	always @(posedge S_CLK)
	if (f_past_valid && M_AWVALID)
	begin
		if (fm_wr_pending == 0)
		begin
			assert(f_waddr == M_AWADDR);
			if (M_WVALID && !M_WLAST)
			begin
				assert(waddr  == f_wnext);
				assert(wsize  == f_wsize);
				assert(wburst == f_wburst);
				assert(wlen   == f_wlen);
			end
		end
		assert((M_WVALID && fm_wr_pending==0
				&&(M_WLAST || waddr == f_wnext))
			|| waddr  == M_AWADDR);
		assert(wburst == M_AWBURST);
		assert(wsize  == M_AWSIZE);
		assert(wlen   == M_AWLEN);

		if (!aw_active)
		begin
			// assert(f_waddr == ... don't care
			assert(f_wburst == wburst);
			assert(f_wsize  == wsize);
			assert(f_wlen == wlen);
		end
	end

	always @(posedge S_CLK)
	if (f_past_valid && fm_wr_pending > 0 && !M_AWVALID)
	begin
		assert(f_waddr  == fm_wr_addr);
		assert(f_wburst == fm_wr_burst);
		assert(f_wsize  == fm_wr_size);
		assert(f_wlen == fm_wr_len);
		if (!M_AWVALID && (!M_WVALID || !M_WLAST))
		begin
			assert(M_WVALID ? (f_wnext  == waddr)
					: (f_waddr == fm_wr_addr));
			assert(f_wburst == wburst);
			assert(f_wsize  == wsize);
			assert(f_wlen   == wlen);
		end
		if (!M_AWVALID && (!M_WVALID || M_WLAST))
		begin
			assert(f_wburst == wburst);
			assert(f_wsize  == wsize);
			assert(f_wlen   == wlen);
		end
	end

	always @(*)
	if (f_past_valid)
	begin
		assert(aw_active == (fs_wr_pending != 0));
		if (fs_wr_pending == 0)
		begin
			assert(fm_wr_pending == 0 || (M_WVALID && M_WLAST));
		end

		if (fm_wr_pending <= ((M_WVALID && M_WLAST) ? 1:0))
		begin
			assert(fs_wr_pending == 0 || (M_WVALID && M_WLAST)
				||(M_AWVALID &&(M_AWLEN + 1 == fs_wr_pending + (M_WVALID ? 1:0))));
		end

		if (fm_wr_pending > 1)
		begin
			assert(fs_wr_pending + (M_WVALID ? 1:0)
					== fm_wr_pending);
		end

		assert(fm_awr_nbursts
			+ (M_AWVALID ? 1:0)
			// + (S_BVALID ? 1:0)
			== fs_awr_nbursts);

		assert(fm_wrid_nbursts
			+ ((M_AWVALID && M_AWID == fm_wr_checkid) ? 1:0)
			// + ((S_BVALID && S_BID == fm_wr_checkid) ? 1:0)
			== fs_wrid_nbursts);

		if (!aw_active)
		begin
			assert(fm_wr_pending == 0
				|| (!M_AWVALID && M_WVALID && fm_wr_pending == 1));
			assert(!M_AWVALID || (M_WVALID && M_WLAST));
		end else if (fs_wr_pending == 1)
		begin
			assert(fm_wr_pending == 1
				|| (!M_AWVALID && M_WVALID && fm_wr_pending == 2)
				|| (M_AWVALID && M_AWLEN==(M_WVALID ? 8'h1:8'h0) && fm_wr_pending == 0));
			if (!M_AWVALID)
				assert(!M_WVALID || !M_WLAST);
		end if (fs_wr_pending + (M_WVALID ? 1:0) != fm_wr_pending)
		begin
			// assert(!M_WVALID || M_WLAST);
			if (!M_WVALID || !M_WLAST)
			begin
				assert(M_AWVALID && M_AWLEN + 1 == fs_wr_pending + (M_WVALID ? 1:0));
				assert(fs_wr_ckvalid == (M_AWID == fs_wr_checkid));
			end
		end

		if (M_AWVALID && aw_active)
		begin
			assert(fs_wr_ckvalid == (M_AWID == fs_wr_checkid));
		end else if (aw_active)
			assert(fm_wr_ckvalid == fs_wr_ckvalid);
	end

	// Handle CkVALID
	always @(*)
	if (f_past_valid && fs_wr_ckvalid && M_AWVALID)
		assert(M_AWID == fs_wr_checkid);

	always @(*)
	if (f_past_valid && fs_wr_ckvalid != fm_wr_ckvalid)
	begin
		if (!aw_active)
			assert(!fs_wr_ckvalid);
		if (M_AWVALID && aw_active)
		begin
			assert(fs_wr_ckvalid == (M_AWID == fs_wr_checkid));
		end else if (!aw_active)
			assert(M_WVALID && M_WLAST);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction read properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	f_assume_fifo, fs_check_first, fs_check_second,
		fm_check_first, fm_check_second,
		fs_check_active, fm_check_active;
	wire	fs_last_burst, fs_last_burstid;
	wire	[AW-1:0]	f1rd_addr,  f2rd_addr;
	wire	[7:0]		f1rd_len,   f2rd_len;
	wire	[1:0]		f1rd_burst, f2rd_burst;
	wire	[2:0]		f1rd_size,  f2rd_size;
	wire	[F_LGDEPTH-1:0]	fmx_rdoutstanding, fmn_rdoutstanding,
				fmx_rdnext, fmn_rdnext;


	always @(posedge S_CLK)
	if (!S_ARESETN)
		f_rlen <= 0;
	else if (rfifo_read)
		f_rlen <= rfifo_len + 1;
	else if (skd_rvalid && skd_rready)
		f_rlen <= f_rlen - 1;

	always @(posedge S_CLK)
	if (!S_RVALID || S_RREADY)
		f_raddr <= raddr;

	always @(*)
	if (f_rlen > 1)
	begin
		assume(!M_RVALID || !M_RLAST);
	end else if (f_rlen <= 1)
		assume(!M_RVALID || M_RLAST);

	faxi_addr #(
		.AW(AW)
	) f_next_raddr (
		.i_last_addr(	fs_rd_ckaddr),
		.i_size(	fs_rd_cksize),
		.i_burst(	fs_rd_ckburst),
		.i_len(		fs_rd_ckarlen),
		.o_incr(),
		.o_next_addr(f_rnext)
	);


	always @(posedge S_CLK)
	if (f_past_valid && S_ARESETN)
	begin
		assert(fs_rd_nbursts == ign_rfifo_fill + ar_active
			+ ((S_RVALID && S_RLAST) ? 1:0));
		if (arid == fs_rd_checkid)
		begin
			assert(fs_rd_nbursts == fs_rdid_nbursts
				+ ((S_RVALID && S_RLAST
					&& S_RID != fs_rd_checkid) ? 1:0));
		end else begin
			assert(fs_rdid_nbursts == ((S_RVALID && S_RLAST
				&& S_RID == fs_rd_checkid) ? 1:0));
		end

		assert(fs_rd_nbursts == fm_rd_nbursts
			+ ((S_RVALID && S_RLAST) ? 1:0) + (M_ARVALID ? 1:0));
		assert(fs_rdid_nbursts == fm_rdid_nbursts
			+ ((S_RVALID && S_RLAST && S_RID == fs_rd_checkid) ? 1:0)
			+ ((M_ARVALID && M_ARID == fs_rd_checkid) ? 1:0));


		assert(fs_rd_outstanding == fm_rd_outstanding
				+ (M_ARVALID ? (M_ARLEN+1) : 0)
				+ (S_RVALID ? 1:0));
	end

	always @(*)
	if (f_past_valid && fs_rd_ckvalid && S_RID == fs_rd_checkid)
	begin
		if (fs_rdid_ckign_nbursts == 0)
		begin
			if (S_RVALID)
			begin
				assert(f_raddr == fs_rd_ckaddr);
			end

			if (ar_active && (!S_RVALID || !S_RLAST))
			begin
				assert(fs_rd_ckburst == rburst);
				assert(fs_rd_cksize  == rsize);
				assert(fs_rd_cklen == f_rlen + (S_RVALID ? 1:0));
			end
		end
	end

	assign	fs_last_burst = S_RVALID && S_RLAST;
	assign	fs_last_burstid = fs_last_burst && S_RID == fs_rd_checkid;
	assign	f1rd_addr = f_rfifo_first_data[AW-1:0];
	assign	f1rd_len  = f_rfifo_first_data[AW +: 8];
	assign	{ f1rd_size, f1rd_burst } = f_rfifo_first_data[AW + 8 +: 5];
	assign	f2rd_addr = f_rfifo_second_data[AW-1:0];
	assign	f2rd_len  = f_rfifo_second_data[AW +: 8];
	assign	{ f2rd_size, f2rd_burst } = f_rfifo_second_data[AW + 8 +: 5];

	always @(*)
	begin
		fs_check_first = fs_rd_ckvalid && f_rfifo_first_in_fifo
			&& (f_rfifo_distance_to_first + (fs_last_burstid ? 1:0)
				+ (ar_active ? 1:0)
				== fs_rdid_ckign_nbursts);

		fs_check_second = fs_rd_ckvalid && f_rfifo_second_in_fifo
			&& (f_rfifo_distance_to_second + (fs_last_burstid ? 1:0)
				+ (ar_active ? 1:0)
				== fs_rdid_ckign_nbursts);

		fm_check_first = fm_rd_ckvalid && f_rfifo_first_in_fifo
			&& (f_rfifo_distance_to_first + (ar_active ? 1:0)
				== fm_rdid_ckign_nbursts);

		fm_check_second = fm_rd_ckvalid && f_rfifo_second_in_fifo
			&& (f_rfifo_distance_to_second + (ar_active ? 1:0)
				== fm_rdid_ckign_nbursts);

		f_assume_fifo = ((!fs_check_first && !fm_check_first)
					|| f_rfifo_distance_to_first > 0)
			&& ((!fs_check_second && !fm_check_second)
					 || f_rfifo_distance_to_second > 0);

		fs_check_active = ar_active && fs_rd_ckvalid
			&& fs_rdid_ckign_nbursts == (fs_last_burstid ? 1 : 0);
		fm_check_active = ar_active && fm_rd_ckvalid
					&& fm_rdid_ckign_nbursts == 0;
	end

	always @(*)
	if (f_past_valid)
	begin
		if (fm_rd_ckvalid)
		begin
			assert(arid == fs_rd_checkid);
		end

		if (fs_rd_ckvalid)
		begin
			assert(arid == fs_rd_checkid || fs_last_burstid);
		end

		if (fs_check_active)
		begin
			if (!S_RVALID)
			begin
				assert(fs_rd_ckaddr  == raddr);
				assert(fs_rd_cklen   == f_rlen);
			end else if (!S_RLAST)
			begin
				assert(raddr == f_rnext);
				assert(fs_rd_cklen   == f_rlen + 1);
			end
			assert(fs_rd_cksize  == rsize);
			assert(fs_rd_ckburst == rburst);
			assert(fs_rd_ckarlen == rlen);
		end

		if (fm_check_active)
		begin
			assert(fm_rd_ckaddr  == raddr);
			assert(fm_rd_cksize  == rsize);
			assert(fm_rd_ckburst == rburst);
			assert(fm_rd_ckarlen == rlen);
			assert(fm_rd_cklen   == f_rlen);
		end

		if (rfifo_read && f_assume_fifo)
		begin
			assume(rfifo_size <= $clog2(SDW/8));
			assume(rfifo_burst != 2'b11);

			assume(fmn_rdnext <= fs_rd_outstanding
				+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN+1) : 0)
				+ ((S_RVALID && S_RREADY) ? 1 : 0));
			assume(fmx_rdnext >= fs_rd_outstanding
				+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN+1) : 0)
				+ ((S_RVALID && S_RREADY) ? 1 : 0));
			// assume(fmn_rdnext <= fm_rd_outstanding
			//	+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN+1) : 0)
			//	+ ((S_RVALID && S_RREADY) ? 1 : 0));
			// assume(fmx_rdnext >= fm_rd_outstanding
			//	+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN+1) : 0)
			//	+ ((S_RVALID && S_RREADY) ? 1 : 0));
		end

		if (fs_rd_ckvalid && (fs_rdid_ckign_nbursts
				>= (ar_active ? 1:0)
					+ (fs_last_burstid ? 1:0))
			&&(fs_rdid_ckign_nbursts
				< fm_rd_nbursts+((S_RVALID && S_RLAST) ? 1:0)));
		begin
			if (fm_rd_nbursts > 0)
				assume(fm_rd_ckvalid);
		end if (!fs_rd_ckvalid)
			assume(!fm_rd_ckvalid);

		if (fm_rd_ckvalid)
			// ||(fm_rd_ckvalid && fm_rdid_ckign_nbursts > 1)
			// ) // ||(fs_rd_ckvalid && fs_rdid_ckign_nbursts
			//	> 
		begin
			assert(fm_rd_ckvalid == fs_rd_ckvalid);
			if (fm_rd_cklen == fs_rd_cklen)
				assert(fm_rd_ckaddr  == fs_rd_ckaddr);
			assert(fm_rd_cksize  == fs_rd_cksize);
			assert(fm_rd_ckburst == fs_rd_ckburst);
			assert(fm_rd_ckarlen == fs_rd_ckarlen);
			assume(fm_rdid_ckign_nbursts
				+ ((S_RVALID && S_RLAST) ? 1:0)
				== fs_rdid_ckign_nbursts);
			assert(fm_rdid_ckign_outstanding
				+ ((S_RVALID && S_RLAST) ? 1 : 0)
				== fs_rdid_ckign_outstanding);		// !!!
		end

		if (rfifo_read && f_assume_fifo && fs_rd_ckvalid
			&& (fs_rdid_ckign_nbursts == (fs_last_burstid ? 1:0)))
		begin
			assume(rfifo_addr  == fs_rd_ckaddr);
			assume(rfifo_len   == fs_rd_ckarlen);
			assume(rfifo_size  == fs_rd_cksize);
			assume(rfifo_burst == fs_rd_ckburst);
			assume(rfifo_size == fs_rd_cksize);
		end

		if (rfifo_read && f_assume_fifo && fm_rd_ckvalid
					&& fm_rdid_ckign_nbursts == 0);
		begin
			assume(rfifo_addr  == fm_rd_ckaddr);
			assume(rfifo_len   == fm_rd_ckarlen);
			assume(rfifo_size  == fm_rd_cksize);
			assume(rfifo_burst == fm_rd_ckburst);
			assume(rfifo_size  == fm_rd_cksize);
		end

		if (fs_check_first)
		begin
			assert(fs_rd_ckaddr  == f1rd_addr);
			assert(fs_rd_cksize  == f1rd_size);
			assert(fs_rd_ckburst == f1rd_burst);
			assert(fs_rd_ckarlen == f1rd_len);
		end

		if (fs_check_second)
		begin
			assert(fs_rd_ckaddr  == f2rd_addr);
			assert(fs_rd_cksize  == f2rd_size);
			assert(fs_rd_ckburst == f2rd_burst);
			assert(fs_rd_ckarlen == f2rd_len);
		end

		if (fm_check_first)
		begin
			assert(fm_rd_ckaddr  == f1rd_addr);
			assert(fm_rd_cksize  == f1rd_size);
			assert(fm_rd_ckburst == f1rd_burst);
			assert(fm_rd_ckarlen == f1rd_len);
		end

		if (fm_check_second)
		begin
			assert(fm_rd_ckaddr  == f2rd_addr);
			assert(fm_rd_cksize  == f2rd_size);
			assert(fm_rd_ckburst == f2rd_burst);
			assert(fm_rd_ckarlen == f2rd_len);
		end

		if (f_rfifo_first_in_fifo)
		begin
			assert(f1rd_size <= $clog2(SDW/8));
			assert(f1rd_burst != 2'b11);
		end

		if (f_rfifo_second_in_fifo)
		begin
			assert(f2rd_size <= $clog2(SDW/8));
			assert(f2rd_burst != 2'b11);
		end
	end

	assign	fmn_rdoutstanding = ign_rfifo_fill
			+ (ar_active ? f_rlen : 0)
			+ (S_RVALID ? 1:0)
			+((fs_rd_ckvalid && !fs_check_first && !fs_check_second
					&& !fs_check_active
					&& fs_rdid_ckign_nbursts>0)
				? fs_rd_ckarlen : 0)
			+ (f_rfifo_first_in_fifo ? f1rd_len : 0)
			+ (f_rfifo_second_in_fifo ? f2rd_len : 0);

	assign	fmx_rdoutstanding = { ign_rfifo_fill, 8'h00 }
			+ (ar_active ? f_rlen : 0)
			+ (S_RVALID ? 1:0)
			+((fs_rd_ckvalid && !fs_check_first && !fs_check_second
					&& !fs_check_active
					&& fs_rdid_ckign_nbursts>0)
				? (fs_rd_ckarlen - 255) : 0)
			+ (f_rfifo_first_in_fifo ? (f1rd_len-255) : 0)
			+ (f_rfifo_second_in_fifo ? (f2rd_len-255) : 0);

	assign	fmn_rdnext = fmn_rdoutstanding
			+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN + 1) : 0)
			- ((S_RVALID && S_RREADY) ? 1:0)
			+ (rfifo_read ? rfifo_len : 0);

	assign	fmx_rdnext = fmx_rdoutstanding
			+ ((S_ARVALID && S_ARREADY) ? (S_ARLEN + 1) : 0)
			- ((S_RVALID && S_RREADY) ? 1:0)
			+ (rfifo_read ? rfifo_len : 0);
	always @(*)
	if (f_past_valid)
	begin
		assert(fs_rd_outstanding >= fmn_rdoutstanding);
		assert(fs_rd_outstanding <= fmx_rdoutstanding);
		//
		assert(fm_rd_outstanding + (M_ARVALID ? (M_ARLEN+1) : 0)
				+ (S_RVALID ? 1:0)
			>= fmn_rdoutstanding);
		assert(fm_rd_outstanding + (M_ARVALID ? (M_ARLEN+1) : 0)
				+ (S_RVALID ? 1:0)
			<= fmx_rdoutstanding);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	(* anyconst *)	reg	[AW-1:0]	fc_addr;
	reg	[7:0]	fc_wbyte_s, fc_wbyte_m, fc_rbyte;
	wire	[7:0]	fc_mwbyte, fc_swbyte;
	wire		fc_mwstrb, fc_swstrb;

	initial	fc_wbyte_s = 0;
	initial	fc_wbyte_m = 0;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		fc_wbyte_s <= 8'h00;
	else if (S_WVALID && S_WREADY && fs_wr_addr[AW-1:SLSB] == fc_addr[AW-1:SLSB])
	begin
		if (fc_swstrb)
			fc_wbyte_s <= fc_swbyte;
	end

	assign	fc_swbyte = S_WDATA >> (fc_addr[SLSB-1:0]*8);
	assign	fc_swstrb = S_WSTRB >> (fc_addr[SLSB-1:0]);
	assign	fc_mwbyte = M_WDATA >> (fc_addr[MLSB-1:0]*8);
	assign	fc_mwstrb = M_WSTRB >> (fc_addr[MLSB-1:0]);

	always @(posedge S_CLK)
	if (!S_ARESETN)
		fc_wbyte_m <= 8'h00;
	else if (M_WVALID && M_WREADY
			&& fm_wr_addr[AW-1:MLSB] == fc_addr[AW-1:MLSB])
	begin
		if (fc_mwstrb)
			fc_wbyte_m <= fc_mwbyte;
	end

	always @(*)
	if (S_ARESETN && fc_wbyte_s != fc_wbyte_m)
	begin
		assert(M_WVALID);
		assert(fc_mwstrb);
		assert(fc_mwbyte == fc_wbyte_s);
		assert(fm_wr_addr[AW-1:MLSB] == fc_addr[AW-1:MLSB]);
	end else if (S_ARESETN && M_WVALID && fm_wr_addr[AW-1:MLSB]
						== fc_addr[AW-1:MLSB])
	begin
		assert(!fc_mwstrb || fc_mwbyte == fc_wbyte_m);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	(* anyconst *)	reg	fcvr_data;
	integer		ik;
	reg	[3:0]	cvr_wrburst, cvr_rdburst,
			cvr_write, cvr_read;
	reg		cvr_rdburst_valid, cvr_wrburst_valid;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_write <= 0;
	else if (!cvr_write[3] && M_WVALID && M_WREADY && M_WLAST)
		cvr_write <= cvr_write + 1;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_read <= 0;
	else if (!cvr_read[3] && S_RVALID && S_RREADY && S_RLAST)
		cvr_read <= cvr_read + 1;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_wrburst_valid <= 1;
	else if (S_AWVALID && (S_AWLEN < 8'h1 || S_AWBURST == 2'b00 || S_AWSIZE != 3'b010))
		cvr_wrburst_valid <= 0;
	else if (S_WVALID && S_WSTRB != 0)
		cvr_wrburst_valid <= 0;
	else if (M_BVALID && M_BRESP[1])
		cvr_wrburst_valid <= 0;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_wrburst <= 0;
	else if (!cvr_wrburst_valid)
		cvr_wrburst <= 0;
	else if (!cvr_wrburst[3] && M_WVALID && M_WREADY && M_WLAST)
		cvr_wrburst <= cvr_wrburst + 1;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_rdburst_valid <= 1;
	else if (S_ARVALID && (S_ARLEN < 8'h1 || S_ARBURST == 2'b00 || S_ARSIZE != 3'b010))
		cvr_rdburst_valid <= 0;
	else if (M_RVALID && M_RRESP[1])
		cvr_rdburst_valid <= 0;

	always @(posedge S_CLK)
	if (!S_ARESETN)
		cvr_rdburst <= 0;
	else if (!cvr_rdburst_valid)
		cvr_rdburst <= 0;
	else if (!cvr_rdburst[3] && S_RVALID && S_RREADY && S_RLAST)
		cvr_rdburst <= cvr_rdburst + 1;

	always @(posedge S_CLK)
	if (S_WVALID && fcvr_data)
	begin
		assume(S_WDATA[7:0] != 0);
		for(ik=1; ik<SDW/8; ik=ik+1)
			assume(S_WDATA[ik*8 +: 8] == S_WDATA[7:0] + ik);
		assume(S_WLAST == (S_WDATA[3:0] == 0));
	end

	always @(posedge S_CLK)
	if (S_WVALID && $past(S_WVALID && S_WREADY) && fcvr_data)
		assume($changed(S_WDATA));

	always @(posedge S_CLK)
	if (M_RVALID && fcvr_data)
	begin
		assume(M_RDATA[SDW-1:0] == 0
			|| M_RDATA[MDW-1:MDW-SDW] == 0);
	end

	always @(posedge S_CLK)
	if (S_RVALID && fcvr_data)
	begin
		assume(S_RDATA[7:0] != 0);
		for(ik=1; ik<SDW/8; ik=ik+1)
			assume(S_RDATA[ik*8 +: 8] == S_RDATA[7:0] + ik);
	end

	always @(posedge S_CLK)
	if (S_RVALID && $past(S_RVALID && S_RREADY) && fcvr_data)
		assume($changed(S_RDATA));

	always @(posedge S_CLK)
	if (S_ARESETN)
	begin
		cover(M_WVALID && M_WSTRB[0]);		// S4
		cover(M_WVALID && M_WSTRB[MDW/8-1]);	// S4
		cover(S_RVALID && S_RDATA[7:0] != 0);	// S6
		cover(S_RVALID && S_RDATA[SDW-1:SDW-8] != 0);	// S6
		cover(S_RVALID && $past(M_RVALID && M_RREADY
					&& M_RDATA[7:0] != 0)
				&& S_RDATA[7:0] != $past(M_RDATA[7:0])); // S6
		cover(S_RVALID && $past(M_RVALID && M_RREADY
					&& M_RDATA[SDW-1:0] == 0)
				&& S_RDATA[SDW-1:SDW-8] != 0);	// S6

		if (!S_BVALID && !M_WVALID && !M_AWVALID && fs_awr_nbursts == 0 && fcvr_data)
		begin
			cover(cvr_write == 1);		// S6
			cover(cvr_write == 2);		// S7
			cover(cvr_write == 3);		// S8
			//
			cover(cvr_wrburst == 1);	// S7
			cover(cvr_wrburst == 2);	// S9
			cover(cvr_wrburst == 3);	// S11
		end

		if (!S_RVALID && fs_rd_nbursts == 0 && fcvr_data)
		begin
			cover(cvr_read == 1);		// S7
			cover(cvr_read == 2);		// S8
			cover(cvr_read == 3);		// S9

			cover(cvr_rdburst == 1);	// S8
			cover(cvr_rdburst == 2);	// S10
			cover(cvr_rdburst == 3);	// S12
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	localparam [0:0]	F_OPT_WRITE_ONLY = 1'b0,
				F_OPT_READ_ONLY  = 1'b0;

	always @(*)
		assume(fm_rd_checkid == fs_rd_checkid);


	always @(*)
	if (F_OPT_WRITE_ONLY && f_past_valid)
	begin
		assume(!S_ARVALID);
		assert(!M_ARVALID);
		assert(!M_RVALID);
		assert(!S_RVALID);
		assert(fm_rd_nbursts == 0);
		assert(fs_rd_nbursts == 0);
		assert(fm_rd_outstanding == 0);
		assert(fs_rd_outstanding == 0);
	end

	always @(*)
	if (F_OPT_READ_ONLY && f_past_valid)
	begin
		assume(!S_AWVALID);
		assume(!S_WVALID);
		assert(!S_BVALID);
		assert(!M_AWVALID);
		assert(!M_WVALID);
		assert(fs_awr_nbursts == 0);
		assert(fm_awr_nbursts == 0);
		assert(fs_wr_pending == 0);
		assert(fm_wr_pending == 0);
	end

	always @(*)
	if (fs_awr_nbursts[F_LGDEPTH-1])
	begin
		assume(!S_AWVALID);
		assert(fs_awr_nbursts[F_LGDEPTH-2:0] == 0);
	end
	// }}}
`endif	// FORMAL
// }}}
endmodule
