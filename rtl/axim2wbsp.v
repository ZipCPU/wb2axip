`error This full featured AXI to WB converter does not (yet) work
////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axim2wbsp.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	So ... this converter works in the other direction from
//		wbm2axisp.  This converter takes AXI commands, and organizes
//	them into pipelined wishbone commands.
//
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
//
// Copyright (C) 2016-2019, Gisselquist Technology, LLC
//
// This file is part of the pipelined Wishbone to AXI converter project, a
// project that contains multiple bus bridging designs and formal bus property
// sets.
//
// The bus bridge designs and property sets are free RTL designs: you can
// redistribute them and/or modify any of them under the terms of the GNU
// Lesser General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
//
// The bus bridge designs and property sets are distributed in the hope that
// they will be useful, but WITHOUT ANY WARRANTY; without even the implied
// warranty of MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with these designs.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module axim2wbsp( i_clk, i_axi_reset_n,
	//
	o_axi_awready, // Slave is ready to accept
	i_axi_awid, i_axi_awaddr, i_axi_awlen, i_axi_awsize, i_axi_awburst,
	i_axi_awlock, i_axi_awcache, i_axi_awprot, i_axi_awqos, i_axi_awvalid,
	//
	o_axi_wready, i_axi_wdata, i_axi_wstrb, i_axi_wlast, i_axi_wvalid,
	//
	o_axi_bid, o_axi_bresp, o_axi_bvalid, i_axi_bready,
	//
	o_axi_arready,	// Read address ready
	i_axi_arid,	// Read ID
	i_axi_araddr,	// Read address
	i_axi_arlen,	// Read Burst Length
	i_axi_arsize,	// Read Burst size
	i_axi_arburst,	// Read Burst type
	i_axi_arlock,	// Read lock type
	i_axi_arcache,	// Read Cache type
	i_axi_arprot,	// Read Protection type
	i_axi_arqos,	// Read Protection type
	i_axi_arvalid,	// Read address valid
	//
	o_axi_rid,	// Response ID
	o_axi_rresp,	// Read response
	o_axi_rvalid,	// Read reponse valid
	o_axi_rdata,	// Read data
	o_axi_rlast,	// Read last
	i_axi_rready,	// Read Response ready
	// Wishbone interface
	o_reset, o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
	i_wb_ack, i_wb_stall, i_wb_data, i_wb_err);
	//
	parameter C_AXI_ID_WIDTH	= 2; // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 32;// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28;	// AXI Address width
	localparam DW = C_AXI_DATA_WIDTH;
	localparam AW =   (C_AXI_DATA_WIDTH==  8) ? (C_AXI_ADDR_WIDTH)
			:((C_AXI_DATA_WIDTH== 16) ? (C_AXI_ADDR_WIDTH-1)
			:((C_AXI_DATA_WIDTH== 32) ? (C_AXI_ADDR_WIDTH-2)
			:((C_AXI_DATA_WIDTH== 64) ? (C_AXI_ADDR_WIDTH-3)
			:((C_AXI_DATA_WIDTH==128) ? (C_AXI_ADDR_WIDTH-4)
			:(C_AXI_ADDR_WIDTH-5)))));
	parameter	LGFIFO = 4;
	parameter	[0:0]	F_STRICT_ORDER    = 0;
	parameter	[0:0]	F_CONSECUTIVE_IDS = 0;
	parameter	[0:0]	F_OPT_BURSTS      = 1'b0;
	parameter	[0:0]	F_OPT_CLK2FFLOGIC = 1'b0;
	parameter		F_MAXSTALL = 3;
	parameter		F_MAXDELAY = 3;
	parameter	[0:0]	OPT_READONLY  = 1'b1;
	parameter	[0:0]	OPT_WRITEONLY = 1'b0;
	parameter	[7:0]	OPT_MAXBURST = 8'h3;
	//
	input	wire			i_clk;	// System clock
	input	wire			i_axi_reset_n;

// AXI write address channel signals
	output	wire			o_axi_awready; // Slave is ready to accept
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_awid;	// Write ID
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_awaddr;	// Write address
	input	wire	[7:0]		i_axi_awlen;	// Write Burst Length
	input	wire	[2:0]		i_axi_awsize;	// Write Burst size
	input	wire	[1:0]		i_axi_awburst;	// Write Burst type
	input	wire	[0:0]		i_axi_awlock;	// Write lock type
	input	wire	[3:0]		i_axi_awcache;	// Write Cache type
	input	wire	[2:0]		i_axi_awprot;	// Write Protection type
	input	wire	[3:0]		i_axi_awqos;	// Write Quality of Svc
	input	wire			i_axi_awvalid;	// Write address valid

// AXI write data channel signals
	output	wire			o_axi_wready;  // Write data ready
	input	wire	[C_AXI_DATA_WIDTH-1:0]	i_axi_wdata;	// Write data
	input	wire	[C_AXI_DATA_WIDTH/8-1:0] i_axi_wstrb;	// Write strobes
	input	wire			i_axi_wlast; // Last write transaction
	input	wire			i_axi_wvalid;	// Write valid

// AXI write response channel signals
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_bid;	// Response ID
	output	wire [1:0]		o_axi_bresp;	// Write response
	output	wire 			o_axi_bvalid;  // Write reponse valid
	input	wire			i_axi_bready;  // Response ready

// AXI read address channel signals
	output	wire			o_axi_arready;	// Read address ready
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid;	// Read ID
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr;	// Read address
	input	wire	[7:0]		i_axi_arlen;	// Read Burst Length
	input	wire	[2:0]		i_axi_arsize;	// Read Burst size
	input	wire	[1:0]		i_axi_arburst;	// Read Burst type
	input	wire	[0:0]		i_axi_arlock;	// Read lock type
	input	wire	[3:0]		i_axi_arcache;	// Read Cache type
	input	wire	[2:0]		i_axi_arprot;	// Read Protection type
	input	wire	[3:0]		i_axi_arqos;	// Read Protection type
	input	wire			i_axi_arvalid;	// Read address valid

// AXI read data channel signals
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_rid;     // Response ID
	output	wire [1:0]		o_axi_rresp;   // Read response
	output	wire			o_axi_rvalid;  // Read reponse valid
	output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata;    // Read data
	output	wire			o_axi_rlast;    // Read last
	input	wire			i_axi_rready;  // Read Response ready

	// We'll share the clock and the reset
	output	wire			o_reset;
	output	wire			o_wb_cyc;
	output	wire			o_wb_stb;
	output	wire			o_wb_we;
	output	wire [(AW-1):0]	o_wb_addr;
	output	wire [(C_AXI_DATA_WIDTH-1):0]	o_wb_data;
	output	wire [(C_AXI_DATA_WIDTH/8-1):0]	o_wb_sel;
	input	wire			i_wb_ack;
	input	wire			i_wb_stall;
	input	wire [(C_AXI_DATA_WIDTH-1):0]	i_wb_data;
	input	wire			i_wb_err;


	//
	//
	//


	wire	[(AW-1):0]			w_wb_addr, r_wb_addr;
	wire	[(C_AXI_DATA_WIDTH-1):0]	w_wb_data;
	wire	[(C_AXI_DATA_WIDTH/8-1):0]	w_wb_sel;
	wire	r_wb_err, r_wb_cyc, r_wb_stb, r_wb_stall, r_wb_ack;
	wire	w_wb_err, w_wb_cyc, w_wb_stb, w_wb_stall, w_wb_ack;

	// verilator lint_off UNUSED
	wire	r_wb_we, w_wb_we;

	assign	r_wb_we = 1'b0;
	assign	w_wb_we = 1'b1;
	// verilator lint_on  UNUSED

`ifdef	FORMAL
	wire	[(LGFIFO-1):0]	f_wr_fifo_ahead, f_wr_fifo_dhead,
				f_wr_fifo_neck, f_wr_fifo_torso,
				f_wr_fifo_tail,
				f_rd_fifo_head, f_rd_fifo_neck,
				f_rd_fifo_torso, f_rd_fifo_tail;
	wire	[(LGFIFO-1):0]		f_wb_nreqs, f_wb_nacks,
					f_wb_outstanding;
	wire	[(LGFIFO-1):0]		f_wb_wr_nreqs, f_wb_wr_nacks,
					f_wb_wr_outstanding;
	wire	[(LGFIFO-1):0]		f_wb_rd_nreqs, f_wb_rd_nacks,
					f_wb_rd_outstanding;
`endif

	generate if (!OPT_READONLY)
	begin : AXI_WR
	aximwr2wbsp #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH), .AW(AW),
		.LGFIFO(LGFIFO))
		axi_write_decoder(
			.i_axi_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
			//
			.o_axi_awready(o_axi_awready),
			.i_axi_awid(   i_axi_awid),
			.i_axi_awaddr( i_axi_awaddr),
			.i_axi_awlen(  i_axi_awlen),
			.i_axi_awsize( i_axi_awsize),
			.i_axi_awburst(i_axi_awburst),
			.i_axi_awlock( i_axi_awlock),
			.i_axi_awcache(i_axi_awcache),
			.i_axi_awprot( i_axi_awprot),
			.i_axi_awqos(  i_axi_awqos),
			.i_axi_awvalid(i_axi_awvalid),
			//
			.o_axi_wready( o_axi_wready),
			.i_axi_wdata(  i_axi_wdata),
			.i_axi_wstrb(  i_axi_wstrb),
			.i_axi_wlast(  i_axi_wlast),
			.i_axi_wvalid( i_axi_wvalid),
			//
			.o_axi_bid(o_axi_bid),
			.o_axi_bresp(o_axi_bresp),
			.o_axi_bvalid(o_axi_bvalid),
			.i_axi_bready(i_axi_bready),
			//
			.o_wb_cyc(  w_wb_cyc),
			.o_wb_stb(  w_wb_stb),
			.o_wb_addr( w_wb_addr),
			.o_wb_data( w_wb_data),
			.o_wb_sel(  w_wb_sel),
			.i_wb_ack(  w_wb_ack),
			.i_wb_stall(w_wb_stall),
			.i_wb_err(  w_wb_err)
`ifdef	FORMAL
			,
			.f_fifo_ahead(f_wr_fifo_ahead),
			.f_fifo_dhead(f_wr_fifo_dhead),
			.f_fifo_neck( f_wr_fifo_neck),
			.f_fifo_torso(f_wr_fifo_torso),
			.f_fifo_tail( f_wr_fifo_tail)
`endif
		);
	end else begin
		assign	w_wb_cyc  = 0;
		assign	w_wb_stb  = 0;
		assign	w_wb_addr = 0;
		assign	w_wb_data = 0;
		assign	w_wb_sel  = 0;
		assign	o_axi_awready = 0;
		assign	o_axi_wready  = 0;
		assign	o_axi_bvalid  = (i_axi_wvalid)&&(i_axi_wlast);
		assign	o_axi_bresp   = 2'b11;
		assign	o_axi_bid     = i_axi_awid;
`ifdef	FORMAL
		assign	f_wr_fifo_ahead  = 0;
		assign	f_wr_fifo_dhead  = 0;
		assign	f_wr_fifo_neck  = 0;
		assign	f_wr_fifo_torso = 0;
		assign	f_wr_fifo_tail  = 0;
`endif
	end endgenerate
	assign	w_wb_we = 1'b1;

	generate if (!OPT_WRITEONLY)
	begin : AXI_RD
	aximrd2wbsp #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH), .AW(AW),
		.LGFIFO(LGFIFO))
		axi_read_decoder(
			.i_axi_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
			//
			.o_axi_arready(o_axi_arready),
			.i_axi_arid(   i_axi_arid),
			.i_axi_araddr( i_axi_araddr),
			.i_axi_arlen(  i_axi_arlen),
			.i_axi_arsize( i_axi_arsize),
			.i_axi_arburst(i_axi_arburst),
			.i_axi_arlock( i_axi_arlock),
			.i_axi_arcache(i_axi_arcache),
			.i_axi_arprot( i_axi_arprot),
			.i_axi_arqos(  i_axi_arqos),
			.i_axi_arvalid(i_axi_arvalid),
			//
			.o_axi_rid(   o_axi_rid),
			.o_axi_rresp( o_axi_rresp),
			.o_axi_rvalid(o_axi_rvalid),
			.o_axi_rdata( o_axi_rdata),
			.o_axi_rlast( o_axi_rlast),
			.i_axi_rready(i_axi_rready),
			//
			.o_wb_cyc(  r_wb_cyc),
			.o_wb_stb(  r_wb_stb),
			.o_wb_addr( r_wb_addr),
			.i_wb_ack(  r_wb_ack),
			.i_wb_stall(r_wb_stall),
			.i_wb_data( i_wb_data),
			.i_wb_err(  r_wb_err)
`ifdef	FORMAL
			,
			.f_fifo_head(f_rd_fifo_head),
			.f_fifo_neck(f_rd_fifo_neck),
			.f_fifo_torso(f_rd_fifo_torso),
			.f_fifo_tail(f_rd_fifo_tail)
`endif
			);
	end else begin
		assign	r_wb_cyc  = 0;
		assign	r_wb_stb  = 0;
		assign	r_wb_addr = 0;
		//
		assign o_axi_arready = 1'b1;
		assign o_axi_rvalid  = (i_axi_arvalid)&&(o_axi_arready);
		assign o_axi_rid    = (i_axi_arid);
		assign o_axi_rvalid  = (i_axi_arvalid);
		assign o_axi_rlast   = (i_axi_arvalid);
		assign o_axi_rresp   = (i_axi_arvalid) ? 2'b11 : 2'b00;
		assign o_axi_rdata   = 0;
`ifdef	FORMAL
		assign	f_rd_fifo_head  = 0;
		assign	f_rd_fifo_neck  = 0;
		assign	f_rd_fifo_torso = 0;
		assign	f_rd_fifo_tail  = 0;
`endif
	end endgenerate

	generate if (OPT_READONLY)
	begin : ARB_RD
		assign	o_wb_cyc  = r_wb_cyc;
		assign	o_wb_stb  = r_wb_stb;
		assign	o_wb_we   = 1'b0;
		assign	o_wb_addr = r_wb_addr;
		assign	o_wb_data = 32'h0;
		assign	o_wb_sel  = 0;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_stall= i_wb_stall;
		assign	r_wb_ack  = i_wb_ack;
		assign	r_wb_err  = i_wb_err;

`ifdef	FORMAL
		fwb_master #(.DW(DW), .AW(AW),
			.F_LGDEPTH(LGFIFO),
			.F_MAX_STALL(F_MAXSTALL),
			.F_MAX_ACK_DELAY(F_MAXDELAY),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC))
		f_wb(i_clk, !i_axi_reset_n,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

		assign f_wb_rd_nreqs = f_wb_nreqs;
		assign f_wb_rd_nacks = f_wb_nacks;
		assign f_wb_rd_outstanding = f_wb_outstanding;
`endif
	end else if (OPT_WRITEONLY)
	begin : ARB_WR
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
			.F_LGDEPTH(LGFIFO),
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
`endif
	end else begin : ARB_WB
		wbarbiter	#(.DW(DW), .AW(AW),
			.F_LGDEPTH(LGFIFO),
			.F_MAX_STALL(F_MAXSTALL),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_MAX_ACK_DELAY(F_MAXDELAY))
			readorwrite(i_clk, !i_axi_reset_n,
			r_wb_cyc, r_wb_stb, 1'b0, r_wb_addr, w_wb_data, w_wb_sel,
				r_wb_ack, r_wb_stall, r_wb_err,
			w_wb_cyc, w_wb_stb, 1'b1, w_wb_addr, w_wb_data, w_wb_sel,
				w_wb_ack, w_wb_stall, w_wb_err,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_err
`ifdef	FORMAL
			,
			f_wb_rd_nreqs, f_wb_rd_nacks, f_wb_rd_outstanding,
			f_wb_wr_nreqs, f_wb_wr_nacks, f_wb_wr_outstanding,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding
`endif
			);
	end endgenerate

	assign	o_reset = (i_axi_reset_n == 1'b0);

`ifdef	FORMAL

`ifdef	AXIM2WBSP
	generate if (F_OPT_CLK2FFLOGIC)
	begin
		reg	f_last_clk;

		initial	f_last_clk = 0;
		always @($global_clock)
		begin
			assume(i_clk == f_last_clk);
			f_last_clk <= !f_last_clk;

			if ((f_past_valid)&&(!$rose(i_clk)))
				assume($stable(i_axi_reset_n));
		end
	end endgenerate
`else
`endif

	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	initial	assume(!i_axi_reset_n);
	always @(*)
		if (!f_past_valid)
			assume(!i_axi_reset_n);

	generate if (F_OPT_CLK2FFLOGIC)
	begin

		always @($global_clock)
			if ((f_past_valid)&&(!$rose(i_clk)))
				assert($stable(i_axi_reset_n));
	end endgenerate

	wire	[(C_AXI_ID_WIDTH-1):0]		f_axi_rd_outstanding,
						f_axi_wr_outstanding,
						f_axi_awr_outstanding;
	wire	[((1<<C_AXI_ID_WIDTH)-1):0]	f_axi_rd_id_outstanding,
						f_axi_awr_id_outstanding,
						f_axi_wr_id_outstanding;
	wire	[8:0]				f_axi_wr_pending,
						f_axi_rd_count,
						f_axi_wr_count;

	/*
	generate if (!OPT_READONLY)
	begin : F_WB_WRITE
	fwb_slave #(.DW(DW), .AW(AW),
			.F_MAX_STALL(0),
			.F_MAX_ACK_DELAY(0),
			.F_LGDEPTH(C_AXI_ID_WIDTH),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wb_wr(i_clk, !i_axi_reset_n,
			w_wb_cyc, w_wb_stb, w_wb_we, w_wb_addr, w_wb_data,
				w_wb_sel,
			w_wb_ack, w_wb_stall, i_wb_data, w_wb_err,
			f_wb_wr_nreqs, f_wb_wr_nacks, f_wb_wr_outstanding);
	end else begin
		assign	f_wb_wr_nreqs = 0;
		assign	f_wb_wr_nacks = 0;
		assign	f_wb_wr_outstanding = 0;
	end endgenerate
	*/

	/*
	generate if (!OPT_WRITEONLY)
	begin : F_WB_READ
	fwb_slave #(.DW(DW), .AW(AW),
			.F_MAX_STALL(0),
			.F_MAX_ACK_DELAY(0),
			.F_LGDEPTH(C_AXI_ID_WIDTH),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wb_rd(i_clk, !i_axi_reset_n,
			r_wb_cyc, r_wb_stb, r_wb_we, r_wb_addr, w_wb_data, w_wb_sel,
				r_wb_ack, r_wb_stall, i_wb_data, r_wb_err,
			f_wb_rd_nreqs, f_wb_rd_nacks, f_wb_rd_outstanding);
	end else begin
		assign	f_wb_rd_nreqs = 0;
		assign	f_wb_rd_nacks = 0;
		assign	f_wb_rd_outstanding = 0;
	end endgenerate
	*/

	/*
	fwb_master #(.DW(DW), .AW(AW),
			.F_MAX_STALL(F_MAXSTALL),
			.F_MAX_ACK_DELAY(F_MAXDELAY),
			.F_LGDEPTH(C_AXI_ID_WIDTH))
		f_wb(i_clk, !i_axi_reset_n,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);
	*/

	faxi_slave #(
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.F_AXI_MAXSTALL(0),
			.F_AXI_MAXDELAY(0),
			.F_AXI_MAXBURST(OPT_MAXBURST),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC))
		f_axi(.i_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
			// AXI write address channnel
			.i_axi_awready(o_axi_awready),
			.i_axi_awid(   i_axi_awid),
			.i_axi_awaddr( i_axi_awaddr),
			.i_axi_awlen(  i_axi_awlen),
			.i_axi_awsize( i_axi_awsize),
			.i_axi_awburst(i_axi_awburst),
			.i_axi_awlock( i_axi_awlock),
			.i_axi_awcache(i_axi_awcache),
			.i_axi_awprot( i_axi_awprot),
			.i_axi_awqos(  i_axi_awqos),
			.i_axi_awvalid(i_axi_awvalid),
			// AXI write data channel
			.i_axi_wready( o_axi_wready),
			.i_axi_wdata(  i_axi_wdata),
			.i_axi_wstrb(  i_axi_wstrb),
			.i_axi_wlast(  i_axi_wlast),
			.i_axi_wvalid( i_axi_wvalid),
			// AXI write acknowledgement channel
			.i_axi_bid(   o_axi_bid),
			.i_axi_bresp( o_axi_bresp),
			.i_axi_bvalid(o_axi_bvalid),
			.i_axi_bready(i_axi_bready),
			// AXI read address channel
			.i_axi_arready(o_axi_arready),
			.i_axi_arid(   i_axi_arid),
			.i_axi_araddr( i_axi_araddr),
			.i_axi_arlen(  i_axi_arlen),
			.i_axi_arsize( i_axi_arsize),
			.i_axi_arburst(i_axi_arburst),
			.i_axi_arlock( i_axi_arlock),
			.i_axi_arcache(i_axi_arcache),
			.i_axi_arprot( i_axi_arprot),
			.i_axi_arqos(  i_axi_arqos),
			.i_axi_arvalid(i_axi_arvalid),
			// AXI read data return
			.i_axi_rid(    o_axi_rid),
			.i_axi_rresp(  o_axi_rresp),
			.i_axi_rvalid( o_axi_rvalid),
			.i_axi_rdata(  o_axi_rdata),
			.i_axi_rlast(  o_axi_rlast),
			.i_axi_rready( i_axi_rready),
			// Quantify where we are within a transaction
			.f_axi_rd_outstanding( f_axi_rd_outstanding),
			.f_axi_wr_outstanding( f_axi_wr_outstanding),
			.f_axi_awr_outstanding(f_axi_awr_outstanding),
			.f_axi_rd_id_outstanding(f_axi_rd_id_outstanding),
			.f_axi_awr_id_outstanding(f_axi_awr_id_outstanding),
			.f_axi_wr_id_outstanding(f_axi_wr_id_outstanding),
			.f_axi_wr_pending(f_axi_wr_pending),
			.f_axi_rd_count(f_axi_rd_count),
			.f_axi_wr_count(f_axi_wr_count));

	wire	f_axi_ard_req, f_axi_awr_req, f_axi_wr_req,
		f_axi_rd_ack, f_axi_wr_ack;

	assign	f_axi_ard_req = (i_axi_arvalid)&&(o_axi_arready);
	assign	f_axi_awr_req = (i_axi_awvalid)&&(o_axi_awready);
	assign	f_axi_wr_req  = (i_axi_wvalid)&&(o_axi_wready);
	assign	f_axi_wr_ack  = (o_axi_bvalid)&&(i_axi_bready);
	assign	f_axi_rd_ack  = (o_axi_rvalid)&&(i_axi_rready);

	wire	[(LGFIFO-1):0]	f_awr_fifo_axi_used,
				f_dwr_fifo_axi_used,
				f_rd_fifo_axi_used,
				f_wr_fifo_wb_outstanding,
				f_rd_fifo_wb_outstanding;

	assign	f_awr_fifo_axi_used = f_wr_fifo_ahead - f_wr_fifo_tail;
	assign	f_dwr_fifo_axi_used  = f_wr_fifo_dhead - f_wr_fifo_tail;
	assign	f_rd_fifo_axi_used  = f_rd_fifo_head  - f_rd_fifo_tail;
	assign	f_wr_fifo_wb_outstanding = f_wr_fifo_neck  - f_wr_fifo_torso;
	assign	f_rd_fifo_wb_outstanding = f_rd_fifo_neck  - f_rd_fifo_torso;

	// The number of outstanding requests must always be greater than
	// the number of AXI requests creating them--since the AXI requests
	// may be burst requests.
	//
	always @(*)
		if (OPT_READONLY)
		begin
			assert(f_axi_awr_outstanding == 0);
			assert(f_axi_wr_outstanding  == 0);
			assert(f_axi_awr_id_outstanding == 0);
			assert(f_axi_wr_id_outstanding  == 0);
			assert(f_axi_wr_pending == 0);
			assert(f_axi_wr_count == 0);
		end else begin
			assert(f_awr_fifo_axi_used >= f_axi_awr_outstanding);
			assert(f_dwr_fifo_axi_used >= f_axi_wr_outstanding);
			assert(f_wr_fifo_ahead >= f_axi_awr_outstanding);
		end

	/*
	always @(*)
		assert((!w_wb_cyc)
			||(f_wr_fifo_wb_outstanding
			// -(((w_wb_stall)&&(w_wb_stb))? 1'b1:1'b0)
			+(((w_wb_ack)&&(w_wb_err))? 1'b1:1'b0)
			== f_wb_wr_outstanding));
	*/

	wire	f_r_wb_req, f_r_wb_ack, f_r_wb_stall;
	assign	f_r_wb_req = (r_wb_stb)&&(!r_wb_stall);
	assign	f_r_wb_ack = (r_wb_cyc)&&((r_wb_ack)||(r_wb_err));
	assign	f_r_wb_stall=(r_wb_stb)&&(r_wb_stall);

/*
	always @(*)
		if ((i_axi_reset_n)&&(r_wb_cyc))
			assert(f_rd_fifo_wb_outstanding
				// -((f_r_wb_req)? 1'b1:1'b0)
				-((r_wb_stb)? 1'b1:1'b0)
				//+(((f_r_wb_ack)&&(!f_r_wb_req))? 1'b1:1'b0)
					== f_wb_rd_outstanding);
*/


	//
	assert property((!OPT_READONLY)||(!OPT_WRITEONLY));

	always @(*)
		if (OPT_READONLY)
		begin
			assume(i_axi_awvalid == 0);
			assume(i_axi_wvalid == 0);
		end
	always @(*)
		if (OPT_WRITEONLY)
			assume(i_axi_arvalid == 0);

	always @(*)
		if (i_axi_awvalid)
			assume(i_axi_awburst[1] == 1'b0);
	always @(*)
		if (i_axi_arvalid)
			assume(i_axi_arburst[1] == 1'b0);

	always @(*)
		if (F_OPT_BURSTS)
		begin
			assume((!i_axi_arvalid)||(i_axi_arlen<= OPT_MAXBURST));
			assume((!i_axi_awvalid)||(i_axi_awlen<= OPT_MAXBURST));
		end else begin
			assume((!i_axi_arvalid)||(i_axi_arlen == 0));
			assume((!i_axi_awvalid)||(i_axi_awlen == 0));
		end

`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
