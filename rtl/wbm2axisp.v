////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbm2axisp.v (Wishbone master to AXI slave, pipelined)
// {{{
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
module wbm2axisp #(
	// {{{
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	=  28,	// AXI Address width (log wordsize)
	parameter C_AXI_ID_WIDTH	=   1,
	parameter DW			=  32,	// Wishbone data width
	parameter AW			=  26,	// Wishbone address width (log wordsize)
	parameter [C_AXI_ID_WIDTH-1:0] AXI_WRITE_ID = 1'b0,
	parameter [C_AXI_ID_WIDTH-1:0] AXI_READ_ID  = 1'b1,
	//
	// OPT_LITTLE_ENDIAN controls which word has the greatest address
	// when the bus size is adjusted.  If OPT_LITTLE_ENDIAN is true,
	// the biggest address is in the most significant word(s), otherwise
	// the least significant word(s).  This parameter is ignored if
	// C_AXI_DATA_WIDTH == DW.
	parameter [0:0]			OPT_LITTLE_ENDIAN = 1'b1,
	parameter LGFIFO		=   6
	// }}}
	) (
	// {{{
	input	wire			i_clk,	// System clock
	input	wire			i_reset,// Reset signal,drives AXI rst

	// AXI write address channel signals
	output	reg			o_axi_awvalid,	// Write address valid
	input	wire			i_axi_awready, // Slave is ready to accept
	output	wire	[C_AXI_ID_WIDTH-1:0]	o_axi_awid,	// Write ID
	output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_awaddr,	// Write address
	output	wire	[7:0]		o_axi_awlen,	// Write Burst Length
	output	wire	[2:0]		o_axi_awsize,	// Write Burst size
	output	wire	[1:0]		o_axi_awburst,	// Write Burst type
	output	wire	[0:0]		o_axi_awlock,	// Write lock type
	output	wire	[3:0]		o_axi_awcache,	// Write Cache type
	output	wire	[2:0]		o_axi_awprot,	// Write Protection type
	output	wire	[3:0]		o_axi_awqos,	// Write Quality of Svc

// AXI write data channel signals
	output	reg			o_axi_wvalid,	// Write valid
	input	wire			i_axi_wready,  // Write data ready
	output	reg	[C_AXI_DATA_WIDTH-1:0]	o_axi_wdata,	// Write data
	output	reg	[C_AXI_DATA_WIDTH/8-1:0] o_axi_wstrb,	// Write strobes
	output	wire			o_axi_wlast,	// Last write transaction

// AXI write response channel signals
	input	wire			i_axi_bvalid,  // Write reponse valid
	output	wire			o_axi_bready,  // Response ready
	input wire [C_AXI_ID_WIDTH-1:0]	i_axi_bid,	// Response ID
	input	wire [1:0]		i_axi_bresp,	// Write response

// AXI read address channel signals
	output	reg			o_axi_arvalid,	// Read address valid
	input	wire			i_axi_arready,	// Read address ready
	output	wire	[C_AXI_ID_WIDTH-1:0]	o_axi_arid,	// Read ID
	output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_araddr,	// Read address
	output	wire	[7:0]		o_axi_arlen,	// Read Burst Length
	output	wire	[2:0]		o_axi_arsize,	// Read Burst size
	output	wire	[1:0]		o_axi_arburst,	// Read Burst type
	output	wire	[0:0]		o_axi_arlock,	// Read lock type
	output	wire	[3:0]		o_axi_arcache,	// Read Cache type
	output	wire	[2:0]		o_axi_arprot,	// Read Protection type
	output	wire	[3:0]		o_axi_arqos,	// Read Protection type

// AXI read data channel signals
	input	wire			i_axi_rvalid,  // Read reponse valid
	output	wire			o_axi_rready,  // Read Response ready
	input wire [C_AXI_ID_WIDTH-1:0]	i_axi_rid,     // Response ID
	input wire [C_AXI_DATA_WIDTH-1:0] i_axi_rdata,    // Read data
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rlast,    // Read last

	// We'll share the clock and the reset
	input	wire			i_wb_cyc,
	input	wire			i_wb_stb,
	input	wire			i_wb_we,
	input	wire	[(AW-1):0]	i_wb_addr,
	input	wire	[(DW-1):0]	i_wb_data,
	input	wire	[(DW/8-1):0]	i_wb_sel,
	output	reg			o_wb_stall,
	output	reg			o_wb_ack,
	output	reg	[(DW-1):0]	o_wb_data,
	output	reg			o_wb_err
	// }}}
);
	////////////////////////////////////////////////////////////////////////
	//
	// Localparameter declarations, initial parameter consistency check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	LG_AXI_DW	= $clog2(C_AXI_DATA_WIDTH);
	localparam	LG_WB_DW	= $clog2(DW);
	// localparam	FIFOLN = (1<<LGFIFO);
	localparam	SUBW = LG_AXI_DW-LG_WB_DW;

	// The various address widths must be properly related.  We'll insist
	// upon that relationship here.
	initial begin
		// This design can't (currently) handle WB widths wider than
		// the AXI width it is driving.  It can only handle widths
		// mismatches in the other direction
		if (C_AXI_DATA_WIDTH < DW)
			$stop;
		if (DW == 8 && AW != C_AXI_ADDR_WIDTH)
			$stop;

		// There must be a definitive relationship between the address
		// widths of the AXI and WB, and that width is dependent upon
		// the WB data width
		if (C_AXI_ADDR_WIDTH != AW + $clog2(DW)-3)
			$stop;
		if (	  (C_AXI_DATA_WIDTH / DW !=32)
			&&(C_AXI_DATA_WIDTH / DW !=16)
			&&(C_AXI_DATA_WIDTH / DW != 8)
			&&(C_AXI_DATA_WIDTH / DW != 4)
			&&(C_AXI_DATA_WIDTH / DW != 2)
			&&(C_AXI_DATA_WIDTH      != DW))
			$stop;
	end
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Internal register and wire declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Things we're not changing ...
	localparam	DWSIZE = $clog2(DW)-3;
	assign o_axi_awid    = AXI_WRITE_ID;
	assign o_axi_awlen   = 8'h0;	// Burst length is one
	assign o_axi_awsize  = DWSIZE[2:0];
	assign o_axi_wlast   = 1;
	assign o_axi_awburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_awlock  = 1'b0;	// Normal signaling
	assign o_axi_arlock  = 1'b0;	// Normal signaling
	assign o_axi_awcache = 4'h3;	// Normal: no cache, modifiable
	//
	assign o_axi_arid    = AXI_READ_ID;
	assign o_axi_arlen   = 8'h0;	// Burst length is one
	assign o_axi_arsize  = DWSIZE[2:0];
	assign o_axi_arburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_arcache = 4'h3;	// Normal: no cache, modifiable
	assign o_axi_awprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_arprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_awqos   = 4'h0;	// Lowest quality of service (unused)
	assign o_axi_arqos   = 4'h0;	// Lowest quality of service (unused)

	reg			direction, full, empty, flushing, nearfull;
	reg	[LGFIFO:0]	npending;
	//
	wire			skid_ready, m_valid, m_we;
	reg			m_ready;
	wire	[AW-1:0]	m_addr;
	wire	[DW-1:0]	m_data;
	wire	[DW/8-1:0]	m_sel;

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Overarching command logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	direction = 0;
	always @(posedge i_clk)
	if (empty)
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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone input skidbuffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		// {{{
		.DW(1+AW+DW+(DW/8)),
		.OPT_OUTREG(1'b0)
		// }}}
	) skid (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || !i_wb_cyc),
		.i_valid(i_wb_stb), .o_ready(skid_ready),
			.i_data({ i_wb_we, i_wb_addr, i_wb_data, i_wb_sel }),
		.o_valid(m_valid), .i_ready(m_ready),
			.o_data({ m_we, m_addr, m_data, m_sel })
		// }}}
	);

	always @(*)
		o_wb_stall = !skid_ready;

	always @(*)
	begin
		m_ready = 1;

		if (flushing || nearfull || ((m_we != direction)&&(!empty)))
			m_ready = 1'b0;
		if (o_axi_awvalid && !i_axi_awready)
			m_ready = 1'b0;
		if (o_axi_wvalid && !i_axi_wready)
			m_ready = 1'b0;
		if (o_axi_arvalid && !i_axi_arready)
			m_ready = 1'b0;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI Signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write transactions
	//

	// awvalid, wvalid
	// {{{
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
	// }}}

	// wdata
	// {{{
	always @(posedge i_clk)
	if (!o_axi_wvalid || i_axi_wready)
		o_axi_wdata   <= {(C_AXI_DATA_WIDTH/DW){m_data}};
	// }}}

	// wstrb
	// {{{
	generate if (DW == C_AXI_DATA_WIDTH)
	begin : NO_WSTRB_ADJUSTMENT
		// {{{
		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready)
			o_axi_wstrb   <= m_sel;
		// }}}
	end else if (OPT_LITTLE_ENDIAN)
	begin : LITTLE_ENDIAN_WSTRB
		// {{{
		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready)
			// Verilator lint_off WIDTH
			o_axi_wstrb   <= m_sel << ((DW/8) * m_addr[SUBW-1:0]);
			// Verilator lint_on  WIDTH
		// }}}
	end else begin : BIG_ENDIAN_WSTRB
		// {{{
		reg	[SUBW-1:0]	neg_addr;

		always @(*)
			neg_addr = ~m_addr[SUBW-1:0];

		always @(posedge i_clk)
		if (!o_axi_wvalid || i_axi_wready)
			// Verilator lint_off WIDTH
			o_axi_wstrb   <= m_sel << ((DW/8)* neg_addr);
			// Verilator lint_on  WIDTH
		// }}}
	end endgenerate
	// }}}

	//
	// Read transactions
	//

	// arvalid
	// {{{
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
	// }}}

	// awaddr, araddr
	// {{{
	generate if (OPT_LITTLE_ENDIAN || DW == C_AXI_DATA_WIDTH)
	begin : GEN_ADDR_LSBS
		// {{{
		always @(posedge i_clk)
		if (!o_axi_awvalid || i_axi_awready)
			o_axi_awaddr  <= { m_addr, {($clog2(DW)-3){1'b0}} };

		always @(posedge i_clk)
		if (!o_axi_arvalid || i_axi_arready)
			o_axi_araddr  <= { m_addr, {($clog2(DW)-3){1'b0}} };
		// }}}
	end else begin : OPT_BIG_ENDIAN
		// {{{
		reg	[SUBW-1:0]	neg_addr;

		always @(*)
			neg_addr = ~m_addr[SUBW-1:0];

		always @(posedge i_clk)
		if (!o_axi_awvalid || i_axi_awready)
		begin
			o_axi_awaddr <= 0;
			o_axi_awaddr <= m_addr << ($clog2(DW)-3);
			o_axi_awaddr[$clog2(DW)-3 +: SUBW] <= neg_addr;
		end

		always @(posedge i_clk)
		if (!o_axi_arvalid || i_axi_arready)
		begin
			o_axi_araddr <= 0;
			o_axi_araddr <= m_addr << ($clog2(DW)-3);
			o_axi_araddr[$clog2(DW)-3 +: SUBW] <= neg_addr;
		end
		// }}}
	end endgenerate
	// }}}

	// rdata, and returned o_wb_data, o_wb_ack, o_wb_err
	// {{{
	generate if (DW == C_AXI_DATA_WIDTH)
	begin : NO_READ_DATA_SELECT_NECESSARY
		// {{{
		always @(*)
			o_wb_data = i_axi_rdata;

		always @(*)
			o_wb_ack = !flushing&&((i_axi_rvalid && !i_axi_rresp[1])
				||(i_axi_bvalid && !i_axi_bresp[1]));

		always @(*)
			o_wb_err = !flushing&&((i_axi_rvalid && i_axi_rresp[1])
				||(i_axi_bvalid && i_axi_bresp[1]));
		// }}}
	end else begin : READ_FIFO_DATA_SELECT
	// {{{

		reg	[SUBW-1:0]	addr_fifo	[0:(1<<LGFIFO)-1];
		reg	[SUBW-1:0]	fifo_value;
		reg	[LGFIFO:0]	wr_addr, rd_addr;
		wire	[C_AXI_DATA_WIDTH-1:0]	return_data;

		initial	o_wb_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || flushing)
			o_wb_ack <= 0;
		else
			o_wb_ack <= ((i_axi_rvalid && !i_axi_rresp[1])
				||(i_axi_bvalid && !i_axi_bresp[1]));

		initial	o_wb_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || flushing)
			o_wb_err <= 0;
		else
			o_wb_err <= ((i_axi_rvalid && i_axi_rresp[1])
				||(i_axi_bvalid && i_axi_bresp[1]));


		initial	wr_addr = 0;
		always @(posedge i_clk)
		if (i_reset)
			wr_addr <= 0;
		else if (m_valid && m_ready)
			wr_addr <= wr_addr + 1;

		always @(posedge i_clk)
		if (m_valid && m_ready)
			addr_fifo[wr_addr[LGFIFO-1:0]] <= m_addr[SUBW-1:0];

		initial	rd_addr = 0;
		always @(posedge i_clk)
		if (i_reset)
			rd_addr <= 0;
		else if (i_axi_bvalid || i_axi_rvalid)
			rd_addr <= rd_addr + 1;

		always @(*)
			fifo_value = addr_fifo[rd_addr[LGFIFO-1:0]];

		if (OPT_LITTLE_ENDIAN)
		begin : LITTLE_ENDIAN_RDATA

			assign	return_data = i_axi_rdata >> (fifo_value * DW);

		end else begin : BIG_ENDIAN_RDATA

			reg	[SUBW-1:0]	neg_fifo_value;

			always @(*)
				neg_fifo_value = ~fifo_value;

			assign	return_data = i_axi_rdata
						>> (neg_fifo_value * DW);

		end

		always @(posedge i_clk)
			o_wb_data <= return_data[DW-1:0];

		// Make Verilator happy here
		// verilator lint_off UNUSED
		if (C_AXI_DATA_WIDTH > DW)
		begin : UNUSED_DATA
			wire	unused_data;
			assign	unused_data = &{ 1'b0,
					return_data[C_AXI_DATA_WIDTH-1:DW] };
		end
		// verilator lint_on  UNUSED
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
	// }}}

	// Read data channel / response logic
	assign	o_axi_rready = 1'b1;
	assign	o_axi_bready = 1'b1;
	// }}}

	// Make verilator's -Wall happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, full, i_axi_bid, i_axi_bresp[0], i_axi_rid, i_axi_rresp[0], i_axi_rlast, m_data, m_sel };
	generate if (C_AXI_DATA_WIDTH > DW)
	begin : GEN_UNUSED_DW
		wire	[C_AXI_DATA_WIDTH-1:DW] unused_data;
		assign	unused_data = i_axi_rdata[C_AXI_DATA_WIDTH-1:DW];
	end endgenerate
	// verilator lint_on  UNUSED
	// }}}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
//
// Formal methods section
// {{{
// Below are a scattering of the formal properties used.  They are not the
// complete set of properties.  Those are maintained elsewhere.
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
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


	initial begin
		assert(C_AXI_DATA_WIDTH >= DW);
		assert((DW == 8) == (AW == C_AXI_ADDR_WIDTH));
		assert(C_AXI_ADDR_WIDTH == AW + $clog2(DW)-3);
	end
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Setup / f_past_valid
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about the WISHBONE inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	fwb_slave #(.DW(DW),.AW(AW),
			.F_MAX_STALL(0),
			.F_MAX_ACK_DELAY(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS(0))
		f_wb(i_clk, i_reset, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr,
					i_wb_data, i_wb_sel,
				o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about the AXI inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH)
		// ...
		// }}}
	) f_axi(.i_clk(i_clk), .i_axi_reset_n(!i_reset),
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
	else if (flushing && i_wb_cyc && !o_wb_err)
		assert(f_wb_outstanding == (r_stb ? 1:0));

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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pending counter properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assert(npending <= { 1'b1, {(LGFIFO){1'b0}} });
		assert(empty == (npending == 0));
		assert(full == (npending == {1'b1, {(LGFIFO){1'b0}} }));
		assert(nearfull == (npending >= {1'b0, {(LGFIFO){1'b1}} }));
		if (full)
			assert(!m_ready);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the AXI4 ouputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Prove that a write to this address will change this value
	//

	// Some extra register declarations
	// {{{
	(* anyconst *) reg [C_AXI_ADDR_WIDTH-1:0]	f_const_addr;
	reg		[C_AXI_DATA_WIDTH-1:0]		f_data;
	// }}}

	//
	// Assume a basic bus response to the given data and address
	//
	integer	iN;

	// f_data
	// {{{
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
	// }}}

	// Assume RDATA == f_data if appropriate
	// {{{
	always @(*)
	if (i_axi_rvalid && o_axi_rready && f_axi_rd_ckvalid
			&& (f_axi_rd_ckaddr == f_const_addr))
		assume(i_axi_rdata == f_data);
	// }}}

	// f_wb_addr -- A WB address designed to match f_const_addr (AXI addr)
	// {{{
	always @(*)
	begin
		f_wb_addr = f_const_addr[C_AXI_ADDR_WIDTH-1:DWSIZE];
		if (!OPT_LITTLE_ENDIAN && SUBW > 0)
			f_wb_addr[0 +: SUBW] = ~f_wb_addr[0 +: SUBW];
	end
	// }}}

	// Assume the address is Wishbone word aligned
	// {{{
	generate if (DW > 8)
	begin
		always @(*)
			assume(f_const_addr[$clog2(DW)-4:0] == 0);
	end endgenerate
	// }}}

	// f_axi_data -- Replicate f_wb_data across the whole word
	// {{{
	always @(*)
		f_axi_data = {(C_AXI_DATA_WIDTH/DW){f_wb_data}};
	// }}}

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
	// }}}

	// f_valid_axi_data
	// {{{
	always @(*)
	begin
		f_valid_axi_data = 1;
		for(iN=0; iN<C_AXI_DATA_WIDTH/8; iN=iN+1)
		begin
			if (f_axi_strb[iN] && (f_axi_data[iN*8 +: 8] != f_data[iN*8 +: 8]))
				f_valid_axi_data = 0;
		end
	end
	// }}}

	// f_valid_axi_response
	// {{{
	always @(*)
	begin
		f_valid_axi_response = 1;
		for(iN=0; iN<C_AXI_DATA_WIDTH/8; iN=iN+1)
		begin
			if (f_axi_strb[iN] && (i_axi_rdata[iN*8 +: 8] != f_data[iN*8 +: 8]))
				f_valid_axi_response = 0;
		end
	end
	// }}}

	//
	// ...
	//

	generate if (DW == C_AXI_DATA_WIDTH)
	begin

		always @(*)
			f_axi_strb = f_wb_strb;

	end else if (OPT_LITTLE_ENDIAN)
	begin

		always @(*)
			f_axi_strb   <= f_wb_strb << ( (DW/8) *
				f_wb_addr[SUBW-1:0]);

	end else // if (!OPT_LITTLE_ENDIAN)
	begin
		reg	[SUBW-1:0]	f_neg_addr;

		always @(*)
			f_neg_addr = ~f_wb_addr[SUBW-1:0];

		always @(*)
			f_axi_strb   <= f_wb_strb << ( (DW/8) * f_neg_addr );

	end endgenerate
	// }}}


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Ad-hoc assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (DW > 8)
	begin
		always @(*)
		if (o_axi_awvalid)
			assert(o_axi_awaddr[$clog2(DW)-4:0] == 0);

		always @(*)
		if (o_axi_arvalid)
			assert(o_axi_araddr[$clog2(DW)-4:0] == 0);

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[F_LGDEPTH-1:0]	r_hit_reads, r_hit_writes,
				r_check_fault, check_fault,
				cvr_nreads, cvr_nwrites;
	reg			cvr_flushed, cvr_read2write, cvr_write2read;

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

	initial	cvr_flushed = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_flushed <= 1'b0;
	else if (flushing)
		cvr_flushed <= 1'b1;

	always @(*)
	begin
		cover(!i_reset && cvr_flushed && !flushing);
		cover(!i_reset && cvr_flushed && !flushing && !o_wb_stall);
	end

	//
	// Let's cover our ability to turn around, from reads to writes or from
	// writes to reads.
	//
	// Note that without the RMW option above, switching direction requires
	// dropping i_wb_cyc.  Let's just make certain here, that if we do so,
	// we don't drop it until after all of the returns come back.
	//
	initial	cvr_read2write = 0;
	always @(posedge i_clk)
	if (i_reset || (!i_wb_cyc && f_wb_nreqs != f_wb_nacks))
		cvr_read2write <= 0;
	else if (!direction && !empty && m_we)
		cvr_read2write <= 1;

	initial	cvr_write2read = 0;
	always @(posedge i_clk)
	if (i_reset || (!i_wb_cyc && f_wb_nreqs != f_wb_nacks))
		cvr_write2read <= 0;
	else if (direction && !empty && !m_we)
		cvr_write2read <= 1;

	always @(*)
	begin
		cover(cvr_read2write &&  direction && o_wb_ack && f_wb_outstanding == 1);
		cover(cvr_write2read && !direction && o_wb_ack && f_wb_outstanding == 1);
	end

	reg	[2:0]	cvr_ack_after_abort;

	initial	cvr_ack_after_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_ack_after_abort <= 0;
	else begin
		if (!i_wb_cyc)
			cvr_ack_after_abort[2:0] <= (empty) ? 0 : 3'b01;
		if (cvr_ack_after_abort[0] && i_wb_cyc && r_stb && flushing)
			cvr_ack_after_abort[1] <= 1;
		if (o_wb_ack && &cvr_ack_after_abort[1:0])
			cvr_ack_after_abort[2] <= 1;
	end

	always @(*)
		cover(&cvr_ack_after_abort[1:0]);
	always @(*)
		cover(!flushing && (&cvr_ack_after_abort[1:0]));
	always @(*)
		cover(&cvr_ack_after_abort[2:0]);
	always @(*)
		cover(!i_wb_cyc && &cvr_ack_after_abort[2:0]);

	initial	cvr_nwrites = 0;
	always @(posedge i_clk)
	if (i_reset || flushing || !i_wb_cyc || !i_wb_we || o_wb_err)
		cvr_nwrites <= 0;
	else if (i_axi_bvalid && o_axi_bready)
		cvr_nwrites <= cvr_nwrites + 1;

	initial	cvr_nreads = 0;
	always @(posedge i_clk)
	if (i_reset || flushing || !i_wb_cyc || i_wb_we || o_wb_err)
		cvr_nreads <= 0;
	else if (i_axi_rvalid && o_axi_rready)
		cvr_nreads <= cvr_nreads + 1;

	always @(*)
		cover(cvr_nwrites == 3 && !o_wb_ack && !o_wb_err && !i_wb_cyc);

	always @(*)
		cover(cvr_nreads == 3 && !o_wb_ack && !o_wb_err && !i_wb_cyc);

	//
	// Generate a cover that doesn't include an abort
	// {{{
	(* anyconst *) reg f_never_abort;

	always @(*)
	if (f_never_abort && f_wb_nacks != f_wb_nreqs)
		assume(!i_reset && i_wb_cyc && !o_wb_err);

	always @(posedge i_clk)
	if (f_never_abort && $past(o_wb_ack) && o_wb_ack)
		assume($changed(o_wb_data));

	always @(*)
		cover(cvr_nreads == 3 && !o_wb_ack && !o_wb_err && !i_wb_cyc
			&& f_never_abort);
	// }}}

	// }}}
`endif // FORMAL
// }}}
endmodule
