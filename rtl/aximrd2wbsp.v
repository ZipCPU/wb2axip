////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximrd2wbsp.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Bridge an AXI read channel pair to a single wishbone read
//		channel.
//
// Rules:
// 	1. Any read channel error *must* be returned to the correct
//		read channel ID.  In other words, we can't pipeline between IDs
//	2. A FIFO must be used on getting a WB return, to make certain that
//		the AXI return channel is able to stall with no loss
//	3. No request can be accepted unless there is room in the return
//		channel for it
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
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
// module	aximrd2wbsp #(
module	aximrd2wbsp #(
	parameter C_AXI_ID_WIDTH	= 6, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 32,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
	parameter AW			= 26,	// AXI Address width
	parameter LGFIFO                =  9	// Must be >= 8
	// parameter	WBMODE		= "B4PIPELINE"
		// Could also be "BLOCK"
	) (
	input	wire			i_axi_clk,	// Bus clock
	input	wire			i_axi_reset_n,	// Bus reset

// AXI read address channel signals
	output	reg			o_axi_arready,	// Read address ready
	input wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr,	// Read address
	input	wire	[7:0]		i_axi_arlen,	// Read Burst Length
	input	wire	[2:0]		i_axi_arsize,	// Read Burst size
	input	wire	[1:0]		i_axi_arburst,	// Read Burst type
	input	wire	[0:0]		i_axi_arlock,	// Read lock type
	input	wire	[3:0]		i_axi_arcache,	// Read Cache type
	input	wire	[2:0]		i_axi_arprot,	// Read Protection type
	input	wire	[3:0]		i_axi_arqos,	// Read Protection type
	input	wire			i_axi_arvalid,	// Read address valid
  
// AXI read data channel signals   
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_rid,     // Response ID
	output	wire [1:0]		o_axi_rresp,   // Read response
	output	reg			o_axi_rvalid,  // Read reponse valid
	output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata,    // Read data
	output	wire 			o_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready

	// We'll share the clock and the reset
	output	reg				o_wb_cyc,
	output	reg				o_wb_stb,
	output	reg [(AW-1):0]			o_wb_addr,
	input	wire				i_wb_ack,
	input	wire				i_wb_stall,
	input	wire [(C_AXI_DATA_WIDTH-1):0]	i_wb_data,
	input	wire				i_wb_err
`ifdef	FORMAL
	// ,
	// output	wire	[LGFIFO-1:0]		f_fifo_head,
	// output	wire	[LGFIFO-1:0]		f_fifo_neck,
	// output	wire	[LGFIFO-1:0]		f_fifo_torso,
	// output	wire	[LGFIFO-1:0]		f_fifo_tail
`endif
	);

	localparam	DW = C_AXI_DATA_WIDTH;

	wire	w_reset;
	assign	w_reset = (i_axi_reset_n == 1'b0);


	wire	[C_AXI_ID_WIDTH+C_AXI_ADDR_WIDTH+25-1:0]	i_rd_request;
	reg	[C_AXI_ID_WIDTH+C_AXI_ADDR_WIDTH+25-1:0]	r_rd_request;
	wire	[C_AXI_ID_WIDTH+C_AXI_ADDR_WIDTH+25-1:0]	w_rd_request;

	reg	[LGFIFO:0]	next_ackptr, next_rptr;

	reg	[C_AXI_ID_WIDTH:0]	request_fifo	[0:((1<<LGFIFO)-1)];
	reg	[C_AXI_ID_WIDTH:0]	rsp_data;

	reg	[C_AXI_DATA_WIDTH:0]	response_fifo	[0:((1<<LGFIFO)-1)];
	reg	[C_AXI_DATA_WIDTH:0]	ack_data;

	reg				advance_ack;


	reg			r_valid, last_stb, last_ack, err_state;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_id;
	reg	[LGFIFO:0]	fifo_wptr, fifo_ackptr, fifo_rptr;
	reg		incr;
	reg	[7:0]	stblen;

	wire	[C_AXI_ID_WIDTH-1:0]	w_id;//    r_id;
	wire	[C_AXI_ADDR_WIDTH-1:0]	w_addr;//  r_addr;
	wire	[7:0]			w_len;//   r_len;
	wire	[2:0]			w_size;//  r_size;
	wire	[1:0]			w_burst;// r_burst;
	wire	[0:0]			w_lock;//  r_lock;
	wire	[3:0]			w_cache;// r_cache;
	wire	[2:0]			w_prot;//  r_prot;
	wire	[3:0]			w_qos;//   r_qos;
	wire	[LGFIFO:0]		fifo_fill;
	wire	[LGFIFO:0]		max_fifo_fill;
	wire				accept_request;



	assign	fifo_fill = (fifo_wptr - fifo_rptr);
	assign	max_fifo_fill = (1<<LGFIFO);

	assign	accept_request = (i_axi_reset_n)&&(!err_state)
			&&((!o_wb_cyc)||(!i_wb_err))
			&&((!o_wb_stb)||(last_stb && !i_wb_stall))
			&&(r_valid ||((i_axi_arvalid)&&(o_axi_arready)))
			// The request must fit into our FIFO before making
			// it
			&&(fifo_fill + {{(LGFIFO-8){1'b0}},w_len} +1
					< max_fifo_fill)
			// One ID at a time, lest we return a bus error
			// to the wrong AXI master
			&&((fifo_fill == 0)||(w_id == axi_id));


	assign	i_rd_request = { i_axi_arid, i_axi_araddr, i_axi_arlen,
				i_axi_arsize, i_axi_arburst, i_axi_arcache,
				i_axi_arlock, i_axi_arprot, i_axi_arqos };

	initial	r_rd_request = 0;
	initial	r_valid      = 0;
	always @(posedge i_axi_clk)
	if (!i_axi_reset_n)
	begin
		r_rd_request <= 0;
		r_valid <= 1'b0;
	end else if ((i_axi_arvalid)&&(o_axi_arready))
	begin
		r_rd_request <= i_rd_request;
		if (!accept_request)
			r_valid <= 1'b1;
	end else if (accept_request)
		r_valid <= 1'b0;

	always @(*)
		o_axi_arready = !r_valid;

	/*
	assign	r_id    = r_rd_request[25 + C_AXI_ADDR_WIDTH +: C_AXI_ID_WIDTH];
	assign	r_addr  = r_rd_request[25 +: C_AXI_ADDR_WIDTH];
	assign	r_len   = r_rd_request[17 +: 8];
	assign	r_size  = r_rd_request[14 +: 3];
	assign	r_burst = r_rd_request[12 +: 2];
	assign	r_lock  = r_rd_request[11 +: 1];
	assign	r_cache = r_rd_request[ 7 +: 4];
	assign	r_prot  = r_rd_request[ 4 +: 3];
	assign	r_qos   = r_rd_request[ 0 +: 4];
	*/

	assign	w_rd_request = (r_valid) ? (r_rd_request) : i_rd_request;

	assign	w_id    = w_rd_request[25 + C_AXI_ADDR_WIDTH +: C_AXI_ID_WIDTH];
	assign	w_addr  = w_rd_request[25 +: C_AXI_ADDR_WIDTH];
	assign	w_len   = w_rd_request[17 +: 8];
	assign	w_size  = w_rd_request[14 +: 3];
	assign	w_burst = w_rd_request[12 +: 2];
	assign	w_lock  = w_rd_request[11 +: 1];
	assign	w_cache = w_rd_request[ 7 +: 4];
	assign	w_prot  = w_rd_request[ 4 +: 3];
	assign	w_qos   = w_rd_request[ 0 +: 4];

	initial o_wb_cyc        = 0;
	initial o_wb_stb        = 0;
	initial stblen          = 0;
	initial incr            = 0;
	initial last_stb        = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
	begin
		o_wb_stb <= 1'b0;
		o_wb_cyc <= 1'b0;
		incr     <= 1'b0;
		stblen   <= 0;
		last_stb <= 0;
	end else if ((!o_wb_stb)||(!i_wb_stall))
	begin
		if (accept_request)
		begin
			// Process the new request
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			last_stb <= (w_len == 0);

			o_wb_addr <= w_addr[(C_AXI_ADDR_WIDTH-1):(C_AXI_ADDR_WIDTH-AW)];
			incr <= w_burst[0];
			stblen <= w_len;
			axi_id <= w_id;
		// end else if ((o_wb_cyc)&&(i_wb_err)||(err_state))
		end else if (o_wb_stb && !last_stb)
		begin
			// Step forward on the burst request
			last_stb <= (stblen == 1);

			o_wb_addr <= o_wb_addr + ((incr)? 1'b1:1'b0);
			stblen <= stblen - 1'b1;

			if (i_wb_err)
			begin
				stblen <= 0;
				o_wb_stb <= 1'b0;
				o_wb_cyc <= 1'b0;
			end
		end else if (!o_wb_stb || last_stb)
		begin
			// End the request
			o_wb_stb <= 1'b0;
			last_stb <= 1'b0;
			stblen <= 0;

			// Check for the last acknowledgment
			if ((i_wb_ack)&&(last_ack))
				o_wb_cyc <= 1'b0;
			if (i_wb_err)
				o_wb_cyc <= 1'b0;
		end
	end else if ((o_wb_cyc)&&(i_wb_err))
	begin
		stblen <= 0;
		o_wb_stb <= 1'b0;
		o_wb_cyc <= 1'b0;
		last_stb <= 1'b0;
	end

	always @(*)
		next_ackptr = fifo_ackptr + 1'b1;

	always @(*)
	begin
		last_ack = 1'b0;
		if (err_state)
			last_ack = 1'b1;
		else if ((o_wb_stb)&&(stblen == 0)&&(fifo_wptr == fifo_ackptr))
			last_ack = 1'b1;
		else if ((fifo_wptr == next_ackptr)&&(!o_wb_stb))
			last_ack = 1'b1;
	end

	initial	fifo_wptr = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
		fifo_wptr <= 0;
	else if (o_wb_cyc && i_wb_err)
		fifo_wptr <= fifo_wptr + {{(LGFIFO-8){1'b0}},stblen}
				+ ((o_wb_stb)? 1:0);
	else if ((o_wb_stb)&&(!i_wb_stall))
		fifo_wptr <= fifo_wptr + 1'b1;

	initial	fifo_ackptr = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
		fifo_ackptr <= 0;
	else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		fifo_ackptr <= fifo_ackptr + 1'b1;
	else if (err_state && (fifo_ackptr != fifo_wptr))
		fifo_ackptr <= fifo_ackptr + 1'b1;

	always @(posedge i_axi_clk)
	if ((o_wb_stb)&&(!i_wb_stall))
		request_fifo[fifo_wptr[LGFIFO-1:0]] <= { last_stb, axi_id };

	always @(posedge i_axi_clk)
	if ((o_wb_cyc && ((i_wb_ack)||(i_wb_err)))
		||(err_state && (fifo_ackptr != fifo_wptr)))
		response_fifo[fifo_ackptr[LGFIFO-1:0]]
			<= { (err_state||i_wb_err), i_wb_data };

	initial	fifo_rptr = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
		fifo_rptr <= 0;
	else if ((o_axi_rvalid)&&(i_axi_rready))
		fifo_rptr <= fifo_rptr + 1'b1;

	always @(*)
		next_rptr = fifo_rptr + 1'b1;

	always @(posedge i_axi_clk)
	if (advance_ack)
		ack_data <= response_fifo[fifo_rptr[LGFIFO-1:0]];

	always @(posedge i_axi_clk)
	if (advance_ack)
		rsp_data <= request_fifo[fifo_rptr[LGFIFO-1:0]];

	always @(*)
	if ((o_axi_rvalid)&&(i_axi_rready))
		advance_ack = (fifo_ackptr != next_rptr);
	else if ((!o_axi_rvalid)&&(fifo_ackptr != fifo_rptr))
		advance_ack = 1'b1;
	else
		advance_ack = 1'b0;

	initial	o_axi_rvalid = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
		o_axi_rvalid <= 1'b0;
	else if (advance_ack)
		o_axi_rvalid <= 1'b1;
	else if (i_axi_rready)
		o_axi_rvalid <= 1'b0;

	initial	err_state = 0;
	always @(posedge i_axi_clk)
	if (w_reset)
		err_state <= 1'b0;
	else if ((o_wb_cyc)&&(i_wb_err))
		err_state <= 1'b1;
	else if ((!o_wb_stb)&&(fifo_wptr == fifo_rptr))
		err_state <= 1'b0;

	assign	o_axi_rlast = rsp_data[C_AXI_ID_WIDTH];
	assign	o_axi_rid   = rsp_data[0 +: C_AXI_ID_WIDTH];
	assign	o_axi_rresp = {(2){ack_data[C_AXI_DATA_WIDTH]}};
	assign	o_axi_rdata = ack_data[0 +: C_AXI_DATA_WIDTH];

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[(C_AXI_ID_WIDTH+1)+(C_AXI_ADDR_WIDTH-AW)
		+27-1:0]	unused;
	assign	unused = { i_axi_arsize, i_axi_arburst[1],
		i_axi_arlock, i_axi_arcache, i_axi_arprot, i_axi_arqos,
		w_burst[1], w_size, w_lock, w_cache, w_prot, w_qos, w_addr[1:0],
			i_axi_araddr[(C_AXI_ADDR_WIDTH-AW-1):0] };
	// verilator lint_on  UNUSED

`ifdef	FORMAL
	reg	f_past_valid;
	initial f_past_valid = 1'b0;
	always @(posedge i_axi_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(w_reset);


	////////////////////////////////////////////////////////////////////////
	//
	// Ad-hoc assertions
	//
	//
	always @(*)
	if (o_wb_stb)
		assert(last_stb == (stblen == 0));
	else
		assert((!last_stb)&&(stblen == 0));

	////////////////////////////////////////////////////////////////////////
	//
	// Error state
	//
	//
	/*
	always @(*)
		assume(!i_wb_err);
	always @(*)
		assert(!err_state);
	*/
	always @(*)
	if ((!err_state)&&(o_axi_rvalid))
		assert(o_axi_rresp == 2'b00);

	////////////////////////////////////////////////////////////////////////
	//
	// FIFO pointers
	//
	//
	wire	[LGFIFO:0]	f_fifo_wb_used, f_fifo_ackremain, f_fifo_used;
	assign	f_fifo_used       = fifo_wptr   - fifo_rptr;
	assign	f_fifo_wb_used    = fifo_wptr   - fifo_ackptr;
	assign	f_fifo_ackremain  = fifo_ackptr - fifo_rptr;

	always @(*)
	if (o_wb_stb)
		assert(f_fifo_used + stblen + 1 < {(LGFIFO){1'b1}});
	else
		assert(f_fifo_used < {(LGFIFO){1'b1}});
	always @(*)
		assert(f_fifo_wb_used   <= f_fifo_used);
	always @(*)
		assert(f_fifo_ackremain <= f_fifo_used);

	// Reset properties
	always @(posedge i_axi_clk)
	if ((!f_past_valid)||($past(w_reset)))
	begin
		assert(fifo_wptr   == 0);
		assert(fifo_ackptr == 0);
		assert(fifo_rptr   == 0);
	end

	localparam	F_LGDEPTH = LGFIFO+1, F_LGRDFIFO = 72; // 9*F_LGFIFO;
	wire	[(9-1):0]		f_axi_rd_count;
	wire	[(F_LGRDFIFO-1):0]	f_axi_rdfifo;
	wire	[(F_LGDEPTH-1):0]	f_axi_rd_nbursts, f_axi_rd_outstanding,
					f_axi_awr_outstanding,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding;

	fwb_master #(.AW(AW), .DW(C_AXI_DATA_WIDTH), .F_MAX_STALL(2),
		.F_MAX_ACK_DELAY(3), .F_LGDEPTH(F_LGDEPTH),
		.F_OPT_DISCONTINUOUS(1))
		fwb(i_axi_clk, w_reset,
			o_wb_cyc, o_wb_stb, 1'b0, o_wb_addr, {(DW){1'b0}}, 4'hf,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

	always @(*)
	if (err_state)
		assert(f_wb_outstanding == 0);
	else
		assert(f_wb_outstanding == f_fifo_wb_used);


	faxi_slave	#(.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.F_OPT_BURSTS(1'b0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_AXI_MAXSTALL(0),
			.F_AXI_MAXDELAY(0))
		faxi(.i_clk(i_axi_clk), .i_axi_reset_n(!w_reset),
			.i_axi_awready(1'b0),
			.i_axi_awaddr(0),
			.i_axi_awlen(0),
			.i_axi_awsize(0),
			.i_axi_awburst(0),
			.i_axi_awlock(0),
			.i_axi_awcache(0),
			.i_axi_awprot(0),
			.i_axi_awqos(0),
			.i_axi_awvalid(1'b0),
			//
			.i_axi_wready(1'b0),
			.i_axi_wdata(0),
			.i_axi_wstrb(0),
			.i_axi_wlast(0),
			.i_axi_wvalid(1'b0),
			//
			.i_axi_bresp(0),
			.i_axi_bvalid(1'b0),
			.i_axi_bready(1'b0),
			//
			.i_axi_arready(o_axi_arready),
			.i_axi_araddr(i_axi_araddr),
			.i_axi_arlen(i_axi_arlen),
			.i_axi_arsize(i_axi_arsize),
			.i_axi_arburst(i_axi_arburst),
			.i_axi_arlock(i_axi_arlock),
			.i_axi_arcache(i_axi_arcache),
			.i_axi_arprot(i_axi_arprot),
			.i_axi_arqos(i_axi_arqos),
			.i_axi_arvalid(i_axi_arvalid),
			//
			.i_axi_rresp(o_axi_rresp),
			.i_axi_rvalid(o_axi_rvalid),
			.i_axi_rdata(o_axi_rdata),
			.i_axi_rlast(o_axi_rlast),
			.i_axi_rready(i_axi_rready),
			//
			.f_axi_rd_nbursts(f_axi_rd_nbursts),
			.f_axi_rd_outstanding(f_axi_rd_outstanding),
			.f_axi_wr_nbursts(),
			.f_axi_awr_outstanding(f_axi_awr_outstanding),
			.f_axi_awr_nbursts(),
			//
			.f_axi_rd_count(f_axi_rd_count),
			.f_axi_rdfifo(f_axi_rdfifo));

	always @(*)
		assert(f_axi_awr_outstanding == 0);

`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
