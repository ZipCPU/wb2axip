////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilrd2wbsp.v (AXI lite to wishbone slave, read channel)
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Bridge an AXI lite read channel pair to a single wishbone read
//		channel.
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
module	axilrd2wbsp(i_clk, i_axi_reset_n,
	// AXI read address channel signals
	o_axi_arready, i_axi_araddr, i_axi_arcache, i_axi_arprot, i_axi_arvalid,
	// AXI read data channel signals
	o_axi_rresp, o_axi_rvalid, o_axi_rdata, i_axi_rready,
	// We'll share the clock and the reset
	o_wb_cyc, o_wb_stb, o_wb_addr,
		i_wb_ack, i_wb_stall, i_wb_data, i_wb_err
`ifdef	FORMAL
	, f_first, f_mid, f_last
`endif
	);
	localparam C_AXI_DATA_WIDTH	= 32;// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28;	// AXI Address width
	localparam AW			= C_AXI_ADDR_WIDTH-2;// WB Address width
	parameter LGFIFO                =  3;

	input	wire			i_clk;	// Bus clock
	input	wire			i_axi_reset_n;	// Bus reset

// AXI read address channel signals
	output	reg			o_axi_arready;	// Read address ready
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr;	// Read address
	input	wire	[3:0]		i_axi_arcache;	// Read Cache type
	input	wire	[2:0]		i_axi_arprot;	// Read Protection type
	input	wire			i_axi_arvalid;	// Read address valid

// AXI read data channel signals
	output	reg [1:0]		o_axi_rresp;   // Read response
	output	reg			o_axi_rvalid;  // Read reponse valid
	output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata;    // Read data
	input	wire			i_axi_rready;  // Read Response ready

	// We'll share the clock and the reset
	output	reg				o_wb_cyc;
	output	reg				o_wb_stb;
	output	reg [(AW-1):0]			o_wb_addr;
	input	wire				i_wb_ack;
	input	wire				i_wb_stall;
	input	wire [(C_AXI_DATA_WIDTH-1):0]	i_wb_data;
	input	wire				i_wb_err;
`ifdef	FORMAL
	// Output connections only used in formal mode
	output	wire	[LGFIFO:0]		f_first;
	output	wire	[LGFIFO:0]		f_mid;
	output	wire	[LGFIFO:0]		f_last;
`endif

	localparam	DW = C_AXI_DATA_WIDTH;
	localparam	AXI_LSBS = $clog2(C_AXI_DATA_WIDTH)-3;

	wire	w_reset;
	assign	w_reset = (!i_axi_reset_n);

	reg			r_stb;
	reg	[AW-1:0]	r_addr;

	localparam		FLEN=(1<<LGFIFO);

	reg	[DW-1:0]	dfifo		[0:(FLEN-1)];
	reg			fifo_full, fifo_empty;

	reg	[LGFIFO:0]	r_first, r_mid, r_last, r_next;
	wire	[LGFIFO:0]	w_first_plus_one;
	wire	[LGFIFO:0]	next_first, next_last, next_mid, fifo_fill;
	reg			wb_pending;
	reg	[LGFIFO:0]	wb_outstanding;
	wire	[DW-1:0]	read_data;
	reg			err_state;
	reg	[LGFIFO:0]	err_loc;



	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if ((w_reset)||((o_wb_cyc)&&(i_wb_err))||(err_state))
		o_wb_stb <= 1'b0;
	else if (r_stb || ((i_axi_arvalid)&&(o_axi_arready)))
		o_wb_stb <= 1'b1;
	else if ((o_wb_cyc)&&(!i_wb_stall))
		o_wb_stb <= 1'b0;

	always @(*)
		o_wb_cyc = (wb_pending)||(o_wb_stb);

	always @(posedge i_clk)
	if (r_stb && !i_wb_stall)
		o_wb_addr <= r_addr;
	else if ((o_axi_arready)&&((!o_wb_stb)||(!i_wb_stall)))
		o_wb_addr <= i_axi_araddr[AW+1:AXI_LSBS];

	// Shadow request
	// r_stb, r_addr
	initial	r_stb = 1'b0;
	always @(posedge i_clk)
	begin
		if ((i_axi_arvalid)&&(o_axi_arready)&&(o_wb_stb)&&(i_wb_stall))
		begin
			r_stb  <= 1'b1;
			r_addr <= i_axi_araddr[AW+1:AXI_LSBS];
		end else if ((!i_wb_stall)||(!o_wb_cyc))
			r_stb <= 1'b0;

		if ((w_reset)||(o_wb_cyc)&&(i_wb_err)||(err_state))
			r_stb <= 1'b0;
	end

	initial	wb_pending     = 0;
	initial	wb_outstanding = 0;
	always @(posedge i_clk)
	if ((w_reset)||(!o_wb_cyc)||(i_wb_err)||(err_state))
	begin
		wb_pending     <= 1'b0;
		wb_outstanding <= 0;
	end else case({ (o_wb_stb)&&(!i_wb_stall), i_wb_ack })
	2'b01: begin
		wb_outstanding <= wb_outstanding - 1'b1;
		wb_pending <= (wb_outstanding >= 2);
		end
	2'b10: begin
		wb_outstanding <= wb_outstanding + 1'b1;
		wb_pending <= 1'b1;
		end
	default: begin end
	endcase

	assign	next_first = r_first + 1'b1;
	assign	next_last  = r_last + 1'b1;
	assign	next_mid   = r_mid + 1'b1;
	assign	fifo_fill  = (r_first - r_last);

	initial	fifo_full  = 1'b0;
	initial	fifo_empty = 1'b1;
	always @(posedge i_clk)
	if (w_reset)
	begin
		fifo_full  <= 1'b0;
		fifo_empty <= 1'b1;
	end else case({ (o_axi_rvalid)&&(i_axi_rready),
				(i_axi_arvalid)&&(o_axi_arready) })
	2'b01: begin
		fifo_full  <= (next_first[LGFIFO-1:0] == r_last[LGFIFO-1:0])
					&&(next_first[LGFIFO]!=r_last[LGFIFO]);
		fifo_empty <= 1'b0;
		end
	2'b10: begin
		fifo_full <= 1'b0;
		fifo_empty <= 1'b0;
		end
	default: begin end
	endcase

	initial	o_axi_arready = 1'b1;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_arready <= 1'b1;
	else if ((o_wb_cyc && i_wb_err) || err_state)
		// On any error, drop the ready flag until it's been flushed
		o_axi_arready <= 1'b0;
	else if ((i_axi_arvalid)&&(o_axi_arready)&&(o_wb_stb)&&(i_wb_stall))
		// On any request where we are already busy, r_stb will get
		// set and we drop arready
		o_axi_arready <= 1'b0;
	else if (!o_axi_arready && o_wb_stb && i_wb_stall)
		// If we've already stalled on o_wb_stb, remain stalled until
		// the bus clears
		o_axi_arready <= 1'b0;
	else if (fifo_full && (!o_axi_rvalid || !i_axi_rready))
		// If the FIFO is full, we must remain not ready until at
		// least one acknowledgment is accepted
		o_axi_arready <= 1'b0;
	else if ( (!o_axi_rvalid || !i_axi_rready)
			&& (i_axi_arvalid && o_axi_arready))
		o_axi_arready  <= (next_first[LGFIFO-1:0] != r_last[LGFIFO-1:0])
					||(next_first[LGFIFO]==r_last[LGFIFO]);
	else
		o_axi_arready <= 1'b1;

	initial	r_first = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_first <= 0;
	else if ((i_axi_arvalid)&&(o_axi_arready))
		r_first <= r_first + 1'b1;

	initial	r_mid = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_mid <= 0;
	else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		r_mid <= r_mid + 1'b1;
	else if ((err_state)&&(r_mid != r_first))
		r_mid <= r_mid + 1'b1;

	initial	r_last = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_last <= 0;
	else if ((o_axi_rvalid)&&(i_axi_rready))
		r_last <= r_last + 1'b1;

	always @(posedge i_clk)
	if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		dfifo[r_mid[(LGFIFO-1):0]] <= i_wb_data;

	always @(posedge i_clk)
	if ((o_wb_cyc)&&(i_wb_err))
		err_loc <= r_mid;

	assign	read_data = dfifo[r_last[LGFIFO-1:0]];
	assign	o_axi_rdata = read_data[DW-1:0];
	initial	o_axi_rresp = 2'b00;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_rresp <= 0;
	else if ((!o_axi_rvalid)||(i_axi_rready))
	begin
		if ((!err_state)&&((!o_wb_cyc)||(!i_wb_err)))
			o_axi_rresp <= 2'b00;
		else if ((!err_state)&&(o_wb_cyc)&&(i_wb_err))
		begin
			if (o_axi_rvalid)
				o_axi_rresp <= (r_mid == next_last) ? 2'b10 : 2'b00;
			else
				o_axi_rresp <= (r_mid == r_last) ? 2'b10 : 2'b00;
		end else if (err_state)
		begin
			if (next_last == err_loc)
				o_axi_rresp <= 2'b10;
			else if (o_axi_rresp[1])
				o_axi_rresp <= 2'b11;
		end else
			o_axi_rresp <= 0;
	end


	initial err_state  = 0;
	always @(posedge i_clk)
	if (w_reset)
		err_state <= 0;
	else if (r_first == r_last)
		err_state <= 0;
	else if ((o_wb_cyc)&&(i_wb_err))
		err_state <= 1'b1;

	initial	o_axi_rvalid = 1'b0;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_rvalid <= 0;
	else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		o_axi_rvalid <= 1'b1;
	else if ((o_axi_rvalid)&&(i_axi_rready))
	begin
		if (err_state)
			o_axi_rvalid <= (next_last != r_first);
		else
			o_axi_rvalid <= (next_last != r_mid);
	end

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[8:0]	unused;
	assign	unused = { i_axi_arcache, i_axi_arprot, i_axi_araddr[AXI_LSBS-1:0] };
	// verilator lint_on  UNUSED

`ifdef	FORMAL
	reg	f_past_valid;
	reg	f_fifo_empty;
	reg	[LGFIFO:0]	f_fifo_fill;

	initial f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	begin
		f_fifo_fill  = (r_first - r_last);
		f_fifo_empty = (f_fifo_fill == 0);
	end

	always @(*)
	if (!f_past_valid)
		assume(w_reset);

	always @(*)
	if (err_state)
		assert(!o_axi_arready);

	always @(*)
	if (err_state)
		assert((!o_wb_cyc)&&(!o_axi_arready));

	always @(*)
	if ((f_fifo_empty)&&(!w_reset))
		assert((!fifo_full)&&(r_first == r_last)&&(r_mid == r_last));

	always @(*)
	if (fifo_full)
		assert((!f_fifo_empty)
			&&(r_first[LGFIFO-1:0] == r_last[LGFIFO-1:0])
			&&(r_first[LGFIFO] != r_last[LGFIFO]));

	always @(*)
		assert(f_fifo_fill <= (1<<LGFIFO));

	always @(*)
	if (fifo_full)
		assert(!o_axi_arready);
	always @(*)
		assert(fifo_full == (f_fifo_fill == (1<<LGFIFO)));
	always @(*)
	if (f_fifo_fill == (1<<LGFIFO))
		assert(!o_axi_arready);
	always @(*)
		assert(wb_pending == (wb_outstanding != 0));

	assign	f_first = r_first;
	assign	f_mid   = r_mid;
	assign	f_last  = r_last;

	wire	[LGFIFO:0]	f_wb_nreqs, f_wb_nacks, f_wb_outstanding;
	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(LGFIFO+1)
		) fwb(i_clk, w_reset,
		o_wb_cyc, o_wb_stb, 1'b0, o_wb_addr, 32'h0, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		f_wb_nreqs,f_wb_nacks, f_wb_outstanding);

	always @(*)
	if (o_wb_cyc)
		assert(f_wb_outstanding == wb_outstanding);

	always @(*)
	if (o_wb_cyc)
		assert(wb_outstanding <= (1<<LGFIFO));

	wire	[LGFIFO:0]	wb_fill;
	assign	wb_fill = r_first - r_mid;
	always @(*)
		assert(wb_fill <= f_fifo_fill);
	always @(*)
	if (o_wb_stb)
		assert(wb_outstanding+1+((r_stb)?1:0) == wb_fill);

	else if (o_wb_cyc)
		assert(wb_outstanding == wb_fill);

	always @(*)
	if (r_stb)
	begin
		assert(o_wb_stb);
		assert(!o_axi_arready);
	end

	wire	[LGFIFO:0]	f_axi_rd_outstanding,
				f_axi_wr_outstanding,
				f_axi_awr_outstanding;

	faxil_slave #(
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(LGFIFO+1),
		.F_OPT_READ_ONLY(1'b1),
		.F_AXI_MAXWAIT(0),
		.F_AXI_MAXDELAY(0)
		) faxil(i_clk, i_axi_reset_n,
		//
		// AXI write address channel signals
		1'b0, i_axi_araddr, i_axi_arcache, i_axi_arprot, 1'b0,
		// AXI write data channel signals
		1'b0, 32'h0, 4'h0, 1'b0,
		// AXI write response channel signals
		2'b00, 1'b0, 1'b0,
		// AXI read address channel signals
		o_axi_arready, i_axi_araddr, i_axi_arcache, i_axi_arprot,
			i_axi_arvalid,
		// AXI read data channel signals
		o_axi_rresp, o_axi_rvalid, o_axi_rdata, i_axi_rready,
		f_axi_rd_outstanding, f_axi_wr_outstanding,
		f_axi_awr_outstanding);

	always @(*)
		assert(f_axi_wr_outstanding == 0);
	always @(*)
		assert(f_axi_awr_outstanding == 0);
	always @(*)
		assert(f_axi_rd_outstanding == f_fifo_fill);

	wire	[LGFIFO:0]	f_mid_minus_err, f_err_minus_last,
				f_first_minus_err;
	assign	f_mid_minus_err  = f_mid - err_loc;
	assign	f_err_minus_last = err_loc - f_last;
	assign	f_first_minus_err = f_first - err_loc;
	always @(*)
	if (o_axi_rvalid)
	begin
		if (!err_state)
			assert(!o_axi_rresp[1]);
		else if (err_loc == f_last)
			assert(o_axi_rresp == 2'b10);
		else if (f_err_minus_last < (1<<LGFIFO))
			assert(!o_axi_rresp[1]);
		else
			assert(o_axi_rresp[1]);
	end

	always @(*)
	if (err_state)
		assert(o_axi_rvalid == (r_first != r_last));
	else
		assert(o_axi_rvalid == (r_mid != r_last));

	always @(*)
	if (err_state)
		assert(f_first_minus_err <= (1<<LGFIFO));

	always @(*)
	if (err_state)
		assert(f_first_minus_err != 0);

	always @(*)
	if (err_state)
		assert(f_mid_minus_err <= f_first_minus_err);

	always @(*)
	if ((f_past_valid)&&(i_axi_reset_n)&&(f_axi_rd_outstanding > 0))
	begin
		if (err_state)
			assert((!o_wb_cyc)&&(f_wb_outstanding == 0));
		else if (!o_wb_cyc)
			assert((o_axi_rvalid)&&(f_axi_rd_outstanding>0)
					&&(wb_fill == 0));
	end

	// WB covers
	always @(*)
		cover(o_wb_cyc && o_wb_stb);

	always @(*)
	if (LGFIFO > 2)
		cover(o_wb_cyc && f_wb_outstanding > 2);

	always @(posedge i_clk)
		cover(o_wb_cyc && i_wb_ack
			&& $past(o_wb_cyc && i_wb_ack)
			&& $past(o_wb_cyc && i_wb_ack,2));

	// AXI covers
	always @(*)
		cover(o_axi_rvalid && i_axi_rready);

	always @(posedge i_clk)
		cover(i_axi_arvalid && o_axi_arready
			&& $past(i_axi_arvalid && o_axi_arready)
			&& $past(i_axi_arvalid && o_axi_arready,2));

	always @(posedge i_clk)
		cover(o_axi_rvalid && i_axi_rready
			&& $past(o_axi_rvalid && i_axi_rready)
			&& $past(o_axi_rvalid && i_axi_rready,2));
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
