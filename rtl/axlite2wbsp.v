////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axlite2wbsp.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Take an AXI lite input, and convert it into WB.
//
//	We'll treat AXI as two separate busses: one for writes, another for
//	reads, further, we'll insist that the two channels AXI uses for writes
//	combine into one channel for our purposes.
//
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
module axlite2wbsp #(
		// {{{
		parameter C_AXI_DATA_WIDTH	= 32,// Width of the AXI R&W data
		parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
		parameter		LGFIFO = 4,
`ifdef	FORMAL
		parameter		F_MAXSTALL = 3,
		parameter		F_MAXDELAY = 3,
`endif
		parameter	[0:0]	OPT_READONLY  = 1'b0,
		parameter	[0:0]	OPT_WRITEONLY = 1'b0,
		localparam		AXILLSB = $clog2(C_AXI_DATA_WIDTH/8)
		// }}}
	) (
		// {{{
		input	wire			i_clk,	// System clock
		input	wire			i_axi_reset_n,

		// AXI write address channel signals
		// {{{
		input	wire			i_axi_awvalid,
		output	wire			o_axi_awready,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_awaddr,
		input	wire	[2:0]		i_axi_awprot,
		// }}}
		// AXI write data channel signals
		// {{{
		input	wire				i_axi_wvalid,
		output	wire				o_axi_wready, 
		input	wire	[C_AXI_DATA_WIDTH-1:0]	i_axi_wdata,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0] i_axi_wstrb,
		// }}}
		// AXI write response channel signals
		// {{{
		output	wire 			o_axi_bvalid,
		input	wire			i_axi_bready,
		output	wire [1:0]		o_axi_bresp,
		// }}}
		// AXI read address channel signals
		// {{{
		input	wire			i_axi_arvalid,
		output	wire			o_axi_arready,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr,
		input	wire	[2:0]		i_axi_arprot,
		// }}}
		// AXI read data channel signals
		// {{{
		output	wire			o_axi_rvalid,
		input	wire			i_axi_rready,
		output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata,
		output	wire [1:0]		o_axi_rresp,
		// }}}
		// Wishbone signals
		// {{{
		// We'll share the clock and the reset
		output	wire			o_reset,
		output	wire			o_wb_cyc,
		output	wire			o_wb_stb,
		output	wire			o_wb_we,
		output	wire [C_AXI_ADDR_WIDTH-AXILLSB-1:0]	o_wb_addr,
		output	wire [C_AXI_DATA_WIDTH-1:0]		o_wb_data,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]		o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire [(C_AXI_DATA_WIDTH-1):0]		i_wb_data,
		input	wire			i_wb_err
		// }}}
		// }}}
	);

	// Local definitions
	// {{{
	localparam DW = C_AXI_DATA_WIDTH;
	localparam AW = C_AXI_ADDR_WIDTH-AXILLSB;
	//
	//
	//

	wire	[(AW-1):0]			w_wb_addr, r_wb_addr;
	wire	[(DW-1):0]			w_wb_data;
	wire	[(DW/8-1):0]			w_wb_sel, r_wb_sel;
	wire	r_wb_err, r_wb_cyc, r_wb_stb, r_wb_stall, r_wb_ack;
	wire	w_wb_err, w_wb_cyc, w_wb_stb, w_wb_stall, w_wb_ack;

	// verilator lint_off UNUSED
	wire	r_wb_we, w_wb_we;

	assign	r_wb_we = 1'b0;
	assign	w_wb_we = 1'b1;
	// verilator lint_on  UNUSED

`ifdef	FORMAL
	// {{{
	// Verilator lint_off UNUSED
	localparam		F_LGDEPTH = LGFIFO+1;
	wire	[LGFIFO:0]	f_wr_fifo_first, f_rd_fifo_first,
				f_wr_fifo_mid,   f_rd_fifo_mid,
				f_wr_fifo_last,  f_rd_fifo_last;
	// Verilator lint_on  UNUSED
	wire	[(F_LGDEPTH-1):0]	f_wb_nreqs, f_wb_nacks,
					f_wb_outstanding;
	wire	[(F_LGDEPTH-1):0]	f_wb_wr_nreqs, f_wb_wr_nacks,
					f_wb_wr_outstanding;
	wire	[(F_LGDEPTH-1):0]	f_wb_rd_nreqs, f_wb_rd_nacks,
					f_wb_rd_outstanding;
	wire			f_pending_awvalid, f_pending_wvalid;
	// }}}
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite write channel to WB processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (!OPT_READONLY)
	begin : AXI_WR
		// {{{
		axilwr2wbsp #(
			// {{{
			// .F_LGDEPTH(F_LGDEPTH),
			// .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH), // .AW(AW),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_write_decoder (
			// {{{
			.i_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
			//
			.i_axi_awvalid(i_axi_awvalid),
			.o_axi_awready(o_axi_awready),
			.i_axi_awaddr( i_axi_awaddr),
			.i_axi_awprot( i_axi_awprot),
			//
			.i_axi_wvalid( i_axi_wvalid),
			.o_axi_wready( o_axi_wready),
			.i_axi_wdata(  i_axi_wdata),
			.i_axi_wstrb(  i_axi_wstrb),
			//
			.o_axi_bvalid(o_axi_bvalid),
			.i_axi_bready(i_axi_bready),
			.o_axi_bresp(o_axi_bresp),
			//
			.o_wb_cyc(  w_wb_cyc),
			.o_wb_stb(  w_wb_stb),
			.o_wb_addr( w_wb_addr),
			.o_wb_data( w_wb_data),
			.o_wb_sel(  w_wb_sel),
			.i_wb_stall(w_wb_stall),
			.i_wb_ack(  w_wb_ack),
			.i_wb_err(  w_wb_err)
`ifdef	FORMAL
			// {{{
			,
			.f_first(f_wr_fifo_first),
			.f_mid(  f_wr_fifo_mid),
			.f_last( f_wr_fifo_last),
			.f_wpending({ f_pending_awvalid, f_pending_wvalid })
			// }}}
`endif
			// }}}
		);
		// }}}
	end else begin : EMPTY_WRITES
		// {{{
		assign	w_wb_cyc  = 0;
		assign	w_wb_stb  = 0;
		assign	w_wb_addr = 0;
		assign	w_wb_data = 0;
		assign	w_wb_sel  = 0;
		assign	o_axi_awready = 0;
		assign	o_axi_wready  = 0;
		assign	o_axi_bvalid  = (i_axi_wvalid);
		assign	o_axi_bresp   = 2'b11;
`ifdef	FORMAL
		assign	f_wr_fifo_first = 0;
		assign	f_wr_fifo_mid   = 0;
		assign	f_wr_fifo_last  = 0;
		assign	f_pending_awvalid=0;
		assign	f_pending_wvalid =0;
`endif
		// }}}
	end endgenerate
	assign	w_wb_we = 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite read channel to WB processing
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (!OPT_WRITEONLY)
	begin : AXI_RD
		// {{{
		axilrd2wbsp #(
			// {{{
			// .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.LGFIFO(LGFIFO)
			// }}}
		) axi_read_decoder(
			// {{{
			.i_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
			//
			.i_axi_arvalid(i_axi_arvalid),
			.o_axi_arready(o_axi_arready),
			.i_axi_araddr( i_axi_araddr),
			.i_axi_arprot( i_axi_arprot),
			//
			.o_axi_rvalid(o_axi_rvalid),
			.i_axi_rready(i_axi_rready),
			.o_axi_rdata( o_axi_rdata),
			.o_axi_rresp( o_axi_rresp),
			//
			.o_wb_cyc(  r_wb_cyc),
			.o_wb_stb(  r_wb_stb),
			.o_wb_addr( r_wb_addr),
			.o_wb_sel(  r_wb_sel),
			.i_wb_stall(r_wb_stall),
			.i_wb_ack(  r_wb_ack),
			.i_wb_data( i_wb_data),
			.i_wb_err(  r_wb_err)
`ifdef	FORMAL
			// {{{
			,
			.f_first(f_rd_fifo_first),
			.f_mid(  f_rd_fifo_mid),
			.f_last( f_rd_fifo_last)
			// }}}
`endif
			// }}}
		);
		// }}}
	end else begin : EMPTY_READS
		// {{{
		assign	r_wb_cyc  = 0;
		assign	r_wb_stb  = 0;
		assign	r_wb_addr = 0;
		//
		assign o_axi_arready = 1'b1;
		assign o_axi_rvalid  = (i_axi_arvalid)&&(o_axi_arready);
		assign o_axi_rresp   = (i_axi_arvalid) ? 2'b11 : 2'b00;
		assign o_axi_rdata   = 0;
`ifdef	FORMAL
		assign	f_rd_fifo_first = 0;
		assign	f_rd_fifo_mid   = 0;
		assign	f_rd_fifo_last  = 0;
`endif
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The arbiter that pastes the two sides together
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	generate if (OPT_READONLY)
	begin : ARB_RD
		// {{{
		assign	o_wb_cyc  = r_wb_cyc;
		assign	o_wb_stb  = r_wb_stb;
		assign	o_wb_we   = 1'b0;
		assign	o_wb_addr = r_wb_addr;
		assign	o_wb_data = 32'h0;
		assign	o_wb_sel  = r_wb_sel;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_stall= i_wb_stall;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_err  = i_wb_err;

`ifdef	FORMAL
		fwb_master #(.DW(DW), .AW(AW),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(F_MAXSTALL),
			.F_MAX_ACK_DELAY(F_MAXDELAY))
		f_wb(i_clk, !i_axi_reset_n,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

		assign f_wb_rd_nreqs = f_wb_nreqs;
		assign f_wb_rd_nacks = f_wb_nacks;
		assign f_wb_rd_outstanding = f_wb_outstanding;
		//
		assign f_wb_wr_nreqs = 0;
		assign f_wb_wr_nacks = 0;
		assign f_wb_wr_outstanding = 0;
`endif
		// }}}
	end else if (OPT_WRITEONLY)
	begin : ARB_WR
		// {{{
		assign	o_wb_cyc  = w_wb_cyc;
		assign	o_wb_stb  = w_wb_stb;
		assign	o_wb_we   = 1'b1;
		assign	o_wb_addr = w_wb_addr;
		assign	o_wb_data = w_wb_data;
		assign	o_wb_sel  = w_wb_sel;
		assign	w_wb_ack  = i_wb_ack;
		assign	w_wb_stall= i_wb_stall;
		assign	w_wb_ack  = i_wb_ack;
		assign	w_wb_err  = i_wb_err;

`ifdef FORMAL
		fwb_master #(.DW(DW), .AW(AW),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(F_MAXSTALL),
			.F_MAX_ACK_DELAY(F_MAXDELAY))
		f_wb(i_clk, !i_axi_reset_n,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

		assign f_wb_wr_nreqs = f_wb_nreqs;
		assign f_wb_wr_nacks = f_wb_nacks;
		assign f_wb_wr_outstanding = f_wb_outstanding;
		//
		assign f_wb_rd_nreqs = 0;
		assign f_wb_rd_nacks = 0;
		assign f_wb_rd_outstanding = 0;
`endif
		// }}}
	end else begin : ARB_WB
		// {{{
		wbarbiter #(
			// {{{
			.DW(DW), .AW(AW)
`ifdef	FORMAL
			, .F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(F_MAXSTALL),
			.F_MAX_ACK_DELAY(F_MAXDELAY)
`endif
			// }}}
		) readorwrite(
			// {{{
			.i_clk(i_clk), .i_reset(!i_axi_reset_n),
			// Channel A - Reads
			// {{{
			.i_a_cyc(r_wb_cyc), .i_a_stb(r_wb_stb),
				.i_a_we(1'b0),
				.i_a_adr(r_wb_addr),
				.i_a_dat(w_wb_data),
				.i_a_sel(r_wb_sel),
				.o_a_stall(r_wb_stall),
				.o_a_ack(r_wb_ack),
				.o_a_err(r_wb_err),
			// }}}
			// Channel B
			// {{{
			.i_b_cyc(w_wb_cyc), .i_b_stb(w_wb_stb),
				.i_b_we(1'b1),
				.i_b_adr(w_wb_addr),
				.i_b_dat(w_wb_data),
				.i_b_sel(w_wb_sel),
				.o_b_stall(w_wb_stall),
				.o_b_ack(w_wb_ack),
				.o_b_err(w_wb_err),
			// }}}
			// Arbitrated outgoing channel
			// {{{
			.o_cyc(o_wb_cyc), .o_stb(o_wb_stb), .o_we(o_wb_we),
				.o_adr(o_wb_addr),
				.o_dat(o_wb_data),
				.o_sel(o_wb_sel),
				.i_stall(i_wb_stall),
				.i_ack(i_wb_ack),
				.i_err(i_wb_err)
			// }}}
`ifdef	FORMAL
			// {{{
			,
			.f_nreqs(f_wb_nreqs), .f_nacks(f_wb_nacks),
				.f_outstanding(f_wb_outstanding),
			.f_a_nreqs(f_wb_rd_nreqs), .f_a_nacks(f_wb_rd_nacks),
				.f_a_outstanding(f_wb_rd_outstanding),
			.f_b_nreqs(f_wb_wr_nreqs), .f_b_nacks(f_wb_wr_nacks),
				.f_b_outstanding(f_wb_wr_outstanding)
			// }}}
`endif
			// }}}
		);
		// }}}
	end endgenerate
	// }}}
	assign	o_reset = (i_axi_reset_n == 1'b0);

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
	// Formal declarations
	// {{{
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;


	wire	[(F_LGDEPTH-1):0]	f_axi_rd_outstanding,
					f_axi_wr_outstanding,
					f_axi_awr_outstanding;

	wire	[LGFIFO:0]	f_awr_fifo_axi_used,
				f_rd_fifo_axi_used;
	// }}}

	initial	assume(!i_axi_reset_n);
	always @(*)
	if (!f_past_valid)
		assume(!i_axi_reset_n);

	faxil_slave #(
		// {{{
		// .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_LGDEPTH),
		.F_AXI_MAXWAIT(0),
		.F_AXI_MAXDELAY(0)
		// }}}
	) f_axi(
		// {{{
		.i_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
		// AXI write address channnel
		.i_axi_awvalid(i_axi_awvalid),
		.i_axi_awready(o_axi_awready),
		.i_axi_awaddr( i_axi_awaddr),
		.i_axi_awprot( i_axi_awprot),
		// AXI write data channel
		.i_axi_wvalid( i_axi_wvalid),
		.i_axi_wready( o_axi_wready),
		.i_axi_wdata(  i_axi_wdata),
		.i_axi_wstrb(  i_axi_wstrb),
		// AXI write acknowledgement channel
		.i_axi_bvalid(o_axi_bvalid),
		.i_axi_bready(i_axi_bready),
		.i_axi_bresp( o_axi_bresp),
		// AXI read address channel
		.i_axi_arvalid(i_axi_arvalid),
		.i_axi_arready(o_axi_arready),
		.i_axi_araddr( i_axi_araddr),
		.i_axi_arprot( i_axi_arprot),
		// AXI read data return
		.i_axi_rvalid( o_axi_rvalid),
		.i_axi_rready( i_axi_rready),
		.i_axi_rdata(  o_axi_rdata),
		.i_axi_rresp(  o_axi_rresp),
		// Quantify where we are within a transaction
		.f_axi_rd_outstanding( f_axi_rd_outstanding),
		.f_axi_wr_outstanding( f_axi_wr_outstanding),
		.f_axi_awr_outstanding(f_axi_awr_outstanding)
		// }}}
	);

	assign	f_awr_fifo_axi_used = f_wr_fifo_first - f_wr_fifo_last;
	assign	f_rd_fifo_axi_used  = f_rd_fifo_first - f_rd_fifo_last;

	always @(*)
	begin
		assert(f_axi_rd_outstanding  == f_rd_fifo_axi_used);
		assert(f_axi_awr_outstanding == f_awr_fifo_axi_used+ (f_pending_awvalid?1:0));
		assert(f_axi_wr_outstanding  == f_awr_fifo_axi_used+ (f_pending_wvalid?1:0));
	end

	always @(*)
	if (OPT_READONLY)
	begin
		assert(f_axi_awr_outstanding == 0);
		assert(f_axi_wr_outstanding  == 0);
	end

	always @(*)
	if (OPT_WRITEONLY)
	begin
		assert(f_axi_rd_outstanding == 0);
	end

	//
	initial assert((!OPT_READONLY)||(!OPT_WRITEONLY));

	always @(*)
	if (OPT_READONLY)
	begin
		assume(i_axi_awvalid == 0);
		assume(i_axi_wvalid == 0);

		assert(o_axi_bvalid == 0);
	end

	always @(*)
	if (OPT_WRITEONLY)
	begin
		assume(i_axi_arvalid == 0);
		assert(o_axi_rvalid == 0);
	end

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_wb_nreqs, f_wb_nacks,
		f_wb_outstanding, f_wb_wr_nreqs, f_wb_wr_nacks,
		f_wb_wr_outstanding, f_wb_rd_nreqs, f_wb_rd_nacks,
		f_wb_rd_outstanding };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
