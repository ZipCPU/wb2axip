////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilwr2wbsp.v (AXI lite to wishbone slave, read channel)
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Bridge an AXI lite write channel triplet to a single wishbone
//		write channel.  A full AXI lite to wishbone bridge will also
//	require the read channel and an arbiter.
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
module	axilwr2wbsp #(
		// {{{
		parameter C_AXI_DATA_WIDTH	= 32,
		parameter C_AXI_ADDR_WIDTH	= 28,
		localparam	AXI_LSBS = $clog2(C_AXI_DATA_WIDTH)-3,
		localparam AW			= C_AXI_ADDR_WIDTH-AXI_LSBS,
		parameter LGFIFO                =  3,
		localparam	DW = C_AXI_DATA_WIDTH
		// }}}
	) (
		// {{{
		input	wire			i_clk,
		input	wire			i_axi_reset_n,
		// AXI write address channel signals
		// {{{
		input	wire			i_axi_awvalid,
		output	reg			o_axi_awready,
		input	wire	[AW+1:0]	i_axi_awaddr,
		input	wire	[2:0]		i_axi_awprot,
		// }}}
		// AXI write data channel signals
		// {{{
		input	wire			i_axi_wvalid,
		output	reg			o_axi_wready,
		input	wire	[DW-1:0]	i_axi_wdata,
		input	wire	[DW/8-1:0]	i_axi_wstrb,
		// }}}
		// AXI write response channel signals
		// {{{
		output	reg			o_axi_bvalid,
		input	wire			i_axi_bready,
		output	reg	[1:0]		o_axi_bresp,
		// }}}
		// Wishbone signals
		// {{{
		// We'll share the clock and the reset
		output	reg				o_wb_cyc,
		output	reg				o_wb_stb,
		output	reg	[(AW-1):0]		o_wb_addr,
		output	reg	[(DW-1):0]		o_wb_data,
		output	reg	[(DW/8-1):0]		o_wb_sel,
		input	wire				i_wb_ack,
		input	wire				i_wb_stall,
		input	wire				i_wb_err
		// }}}
`ifdef		FORMAL
		// {{{
		// Output connections only used in formal mode
		, output	wire	[LGFIFO:0]	f_first,
		output	wire	[LGFIFO:0]		f_mid,
		output	wire	[LGFIFO:0]		f_last,
		output	wire	[1:0]			f_wpending
		// }}}
`endif
		// }}}
	);

	// Local declarations
	// {{{
	wire	w_reset;
	assign	w_reset = (!i_axi_reset_n);

	reg			r_awvalid, r_wvalid;
	reg	[AW-1:0]	r_addr;
	reg	[DW-1:0]	r_data;
	reg	[DW/8-1:0]	r_sel;

	reg			fifo_full, fifo_empty;

	reg	[LGFIFO:0]	r_first, r_mid, r_last;
	wire	[LGFIFO:0]	next_first, next_last;
	reg			wb_pending;
	reg	[LGFIFO:0]	wb_outstanding;

	reg	[LGFIFO:0]	err_loc;
	reg			err_state;

	wire	axi_write_accepted, pending_axi_write;
	// }}}

	assign	pending_axi_write =
		((r_awvalid) || (i_axi_awvalid && o_axi_awready))
		&&((r_wvalid)|| (i_axi_wvalid && o_axi_wready));

	assign	axi_write_accepted =
		(!o_wb_stb || !i_wb_stall) && (!fifo_full) && (!err_state)
			&& (pending_axi_write);

	// o_wb_cyc, o_wb_stb
	// {{{
	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if ((w_reset)||((o_wb_cyc)&&(i_wb_err))||(err_state))
		o_wb_stb <= 1'b0;
	else if (axi_write_accepted)
		o_wb_stb <= 1'b1;
	else if ((o_wb_cyc)&&(!i_wb_stall))
		o_wb_stb <= 1'b0;

	always @(*)
		o_wb_cyc = (wb_pending)||(o_wb_stb);
	// }}}

	// o_wb_addr, o_wb_data, o_wb_sel
	// {{{
	always @(posedge i_clk)
	if (!o_wb_stb || !i_wb_stall)
	begin
		if (r_awvalid)
			o_wb_addr <= r_addr;
		else
			o_wb_addr <= i_axi_awaddr[AW+1:AXI_LSBS];

		if (r_wvalid)
		begin
			o_wb_data <= r_data;
			o_wb_sel  <= r_sel;
		end else begin
			o_wb_data <= i_axi_wdata;
			o_wb_sel  <= i_axi_wstrb;
		end
	end
	// }}}

	// r_awvalid, r_addr
	// {{{
	initial	r_awvalid = 1'b0;
	always @(posedge i_clk)
	begin
		if ((i_axi_awvalid)&&(o_axi_awready))
		begin
			r_addr <= i_axi_awaddr[AW+1:AXI_LSBS];
			r_awvalid <= (!axi_write_accepted);
		end else if (axi_write_accepted)
			r_awvalid <= 1'b0;

		if (w_reset)
			r_awvalid <= 1'b0;
	end
	// }}}

	// r_wvalid
	// {{{
	initial	r_wvalid = 1'b0;
	always @(posedge i_clk)
	begin
		if ((i_axi_wvalid)&&(o_axi_wready))
		begin
			r_data <= i_axi_wdata;
			r_sel  <= i_axi_wstrb;
			r_wvalid <= (!axi_write_accepted);
		end else if (axi_write_accepted)
			r_wvalid <= 1'b0;

		if (w_reset)
			r_wvalid <= 1'b0;
	end
	// }}}

	// o_axi_awready
	// {{{
	initial	o_axi_awready = 1'b1;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_awready <= 1'b1;
	else if ((o_wb_stb && i_wb_stall)
			&&(r_awvalid || (i_axi_awvalid && o_axi_awready)))
		// Once a request has been received while the interface is
		// stalled, we must stall and wait for it to clear
		o_axi_awready <= 1'b0;
	else if (err_state && (r_awvalid || (i_axi_awvalid && o_axi_awready)))
		o_axi_awready <= 1'b0;
	else if ((r_awvalid || (i_axi_awvalid && o_axi_awready))
		&&(!r_wvalid && (!i_axi_wvalid || !o_axi_wready)))
		// If the write address is given without any corresponding
		// write data, immediately stall and wait for the write data
		o_axi_awready <= 1'b0;
	else if (!o_axi_awready && o_wb_stb && i_wb_stall)
		// Once stalled, remain stalled while the WB bus is stalled
		o_axi_awready <= 1'b0;
	else if (fifo_full && (r_awvalid || (!o_axi_bvalid || !i_axi_bready)))
		// Once the FIFO is full, we must remain stalled until at
		// least one acknowledgment has been accepted
		o_axi_awready <= 1'b0;
	else if ((!o_axi_bvalid || !i_axi_bready)
			&& (r_awvalid || (i_axi_awvalid && o_axi_awready)))
		// If ever the FIFO becomes full, we must immediately drop
		// the o_axi_awready signal
		o_axi_awready  <= (next_first[LGFIFO-1:0] != r_last[LGFIFO-1:0])
					&&(next_first[LGFIFO]==r_last[LGFIFO]);
	else
		o_axi_awready <= 1'b1;
	// }}}

	// o_axi_wready
	// {{{
	initial	o_axi_wready = 1'b1;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_wready <= 1'b1;
	else if ((o_wb_stb && i_wb_stall)
			&&(r_wvalid || (i_axi_wvalid && o_axi_wready)))
		// Once a request has been received while the interface is
		// stalled, we must stall and wait for it to clear
		o_axi_wready <= 1'b0;
	else if (err_state && (r_wvalid || (i_axi_wvalid && o_axi_wready)))
		o_axi_wready <= 1'b0;
	else if ((r_wvalid || (i_axi_wvalid && o_axi_wready))
		&&(!r_awvalid && (!i_axi_awvalid || !o_axi_awready)))
		// If the write address is given without any corresponding
		// write data, immediately stall and wait for the write data
		o_axi_wready <= 1'b0;
	else if (!o_axi_wready && o_wb_stb && i_wb_stall)
		// Once stalled, remain stalled while the WB bus is stalled
		o_axi_wready <= 1'b0;
	else if (fifo_full && (r_wvalid || (!o_axi_bvalid || !i_axi_bready)))
		// Once the FIFO is full, we must remain stalled until at
		// least one acknowledgment has been accepted
		o_axi_wready <= 1'b0;
	else if ((!o_axi_bvalid || !i_axi_bready)
			&& (i_axi_wvalid && o_axi_wready))
		// If ever the FIFO becomes full, we must immediately drop
		// the o_axi_wready signal
		o_axi_wready  <= (next_first[LGFIFO-1:0] != r_last[LGFIFO-1:0])
					&&(next_first[LGFIFO]==r_last[LGFIFO]);
	else
		o_axi_wready <= 1'b1;
	// }}}

	// wb_pending, wb_outstanding
	// {{{
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
	// }}}

	assign	next_first = r_first + 1'b1;
	assign	next_last  = r_last + 1'b1;

	// fifo_full, fifo_empty
	// {{{
	initial	fifo_full  = 1'b0;
	initial	fifo_empty = 1'b1;
	always @(posedge i_clk)
	if (w_reset)
	begin
		fifo_full  <= 1'b0;
		fifo_empty <= 1'b1;
	end else case({ (o_axi_bvalid)&&(i_axi_bready),
				(axi_write_accepted) })
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
	// }}}

	// r_first
	// {{{
	initial	r_first = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_first <= 0;
	else if (axi_write_accepted)
		r_first <= r_first + 1'b1;
	// }}}

	// r_mid
	// {{{
	initial	r_mid = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_mid <= 0;
	else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		r_mid <= r_mid + 1'b1;
	else if ((err_state)&&(r_mid != r_first))
		r_mid <= r_mid + 1'b1;
	// }}}

	// r_last
	// {{{
	initial	r_last = 0;
	always @(posedge i_clk)
	if (w_reset)
		r_last <= 0;
	else if ((o_axi_bvalid)&&(i_axi_bready))
		r_last <= r_last + 1'b1;
	// }}}

	// err_loc
	// {{{
	always @(posedge i_clk)
	if ((o_wb_cyc)&&(i_wb_err))
		err_loc <= r_mid;
	// }}}

	// o_axi_bresp
	// {{{
	initial	o_axi_bresp = 2'b00;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_bresp <= 0;
	else if ((!o_axi_bvalid)||(i_axi_bready))
	begin
		if ((!err_state)&&((!o_wb_cyc)||(!i_wb_err)))
			o_axi_bresp <= 2'b00;
		else if ((!err_state)&&(o_wb_cyc)&&(i_wb_err))
		begin
			if (o_axi_bvalid)
				o_axi_bresp <= (r_mid == next_last) ? 2'b10 : 2'b00;
			else
				o_axi_bresp <= (r_mid == r_last) ? 2'b10 : 2'b00;
		end else if (err_state)
		begin
			if (next_last == err_loc)
				o_axi_bresp <= 2'b10;
			else if (o_axi_bresp[1])
				o_axi_bresp <= 2'b11;
		end else
			o_axi_bresp <= 0;
	end
	// }}}

	// err_state
	// {{{
	initial err_state  = 0;
	always @(posedge i_clk)
	if (w_reset)
		err_state <= 0;
	else if (r_first == r_last)
		err_state <= 0;
	else if ((o_wb_cyc)&&(i_wb_err))
		err_state <= 1'b1;
	// }}}

	// o_axi_bvalid
	// {{{
	initial	o_axi_bvalid = 1'b0;
	always @(posedge i_clk)
	if (w_reset)
		o_axi_bvalid <= 0;
	else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		o_axi_bvalid <= 1'b1;
	else if ((o_axi_bvalid)&&(i_axi_bready))
	begin
		if (err_state)
			o_axi_bvalid <= (next_last != r_first);
		else
			o_axi_bvalid <= (next_last != r_mid);
	end
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_axi_awprot,
				fifo_empty, i_axi_awaddr[AXI_LSBS-1:0] };
	// verilator lint_on  UNUSED
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
	reg			f_past_valid;
	wire			f_axi_stalled;
	wire	[LGFIFO:0]	f_wb_nreqs, f_wb_nacks, f_wb_outstanding;
	wire	[LGFIFO:0]	wb_fill;
	wire	[LGFIFO:0]	f_axi_rd_outstanding,
				f_axi_wr_outstanding,
				f_axi_awr_outstanding;
	wire	[LGFIFO:0]	f_mid_minus_err, f_err_minus_last,
				f_first_minus_err;
	wire	[LGFIFO:0]	f_fifo_fill;

	initial f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

`ifdef	AXILWR2WBSP
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	always @(*)
	if (!f_past_valid)
		`ASSUME(w_reset);

	assign	f_fifo_fill  = (r_first - r_last);

	always @(*)
	if (err_state)
	begin
		assert(!r_awvalid || !o_axi_awready);
		assert(!r_wvalid  || !o_axi_wready);

		assert(!o_wb_cyc);
	end

	always @(*)
	if ((fifo_empty)&&(!w_reset))
		assert((!fifo_full)&&(r_first == r_last)&&(r_mid == r_last));

	always @(*)
	if (fifo_full)
	begin
		assert(!fifo_empty);
		assert(r_first[LGFIFO-1:0] == r_last[LGFIFO-1:0]);
		assert(r_first[LGFIFO] != r_last[LGFIFO]);
	end

	always @(*)
		assert(f_fifo_fill <= (1<<LGFIFO));

	always @(*)
	if (fifo_full)
	begin
		assert(!r_awvalid || !o_axi_awready);
		assert(!r_wvalid  || !o_axi_wready);
	end

	always @(*)
		assert(fifo_full == (f_fifo_fill >= (1<<LGFIFO)));
	always @(*)
		assert(wb_pending == (wb_outstanding != 0));


	assign	f_first    = r_first;
	assign	f_mid      = r_mid;
	assign	f_last     = r_last;
	assign	f_wpending = { r_awvalid, r_wvalid };

	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(LGFIFO+1)
		) fwb(i_clk, w_reset,
		o_wb_cyc, o_wb_stb, 1'b1, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_ack, i_wb_stall, {(DW){1'b0}}, i_wb_err,
		f_wb_nreqs,f_wb_nacks, f_wb_outstanding);

	always @(*)
	if (o_wb_cyc)
		assert(f_wb_outstanding == wb_outstanding);

	always @(*)
	if (o_wb_cyc)
		assert(wb_outstanding <= (1<<LGFIFO));

	assign	wb_fill = r_first - r_mid;
	always @(*)
		assert(wb_fill <= f_fifo_fill);
	always @(*)
	if (!w_reset)
	begin
		if (o_wb_stb)
		begin
			assert(wb_outstanding+1 == wb_fill);
		end else if (o_wb_cyc)
		begin
			assert(wb_outstanding == wb_fill);
		end else if (!err_state)
			assert((wb_fill == 0)&&(wb_outstanding == 0));
	end

	faxil_slave #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(LGFIFO+1),
		.F_OPT_WRITE_ONLY(1),
		.F_AXI_MAXWAIT(0),
		.F_AXI_MAXDELAY(0)
		// }}}
	) faxil(
		// {{{
		.i_clk(i_clk), .i_axi_reset_n(i_axi_reset_n),
		//
		// AXI write address channel signals
		.i_axi_awvalid(i_axi_awvalid), .i_axi_awready(o_axi_awready),
			.i_axi_awaddr(i_axi_awaddr),.i_axi_awprot(i_axi_awprot),
		// AXI write data channel signals
		.i_axi_wvalid(i_axi_wvalid), .i_axi_wready(o_axi_wready),
			.i_axi_wdata(i_axi_wdata), .i_axi_wstrb(i_axi_wstrb),
		// AXI write response channel signals
		.i_axi_bvalid(o_axi_bvalid), .i_axi_bready(i_axi_bready),
			.i_axi_bresp(o_axi_bresp),
		// AXI read address channel signals
		.i_axi_arvalid(1'b0), .i_axi_arready(1'b0),
			.i_axi_araddr(i_axi_awaddr),.i_axi_arprot(i_axi_awprot),
		// AXI read data channel signals
		.i_axi_rvalid(1'b0), .i_axi_rready(1'b0),
			.i_axi_rdata({(DW){1'b0}}),
			.i_axi_rresp(2'b00),
		.f_axi_rd_outstanding(f_axi_rd_outstanding),
		.f_axi_wr_outstanding(f_axi_wr_outstanding),
		.f_axi_awr_outstanding(f_axi_awr_outstanding)
		// }}}
	);

	always @(*)
		assert(f_axi_wr_outstanding - (r_wvalid ? 1:0)
				== f_axi_awr_outstanding - (r_awvalid ? 1:0));
	always @(*)
		assert(f_axi_rd_outstanding == 0);
	always @(*)
		assert(f_axi_wr_outstanding - (r_wvalid ? 1:0) == f_fifo_fill);
	always @(*)
		assert(f_axi_awr_outstanding - (r_awvalid ? 1:0) == f_fifo_fill);
	always @(*)
	if (r_wvalid)
		assert(f_axi_wr_outstanding > 0);

	always @(*)
	if (r_awvalid)
		assert(f_axi_awr_outstanding > 0);

	assign	f_mid_minus_err  = f_mid - err_loc;
	assign	f_err_minus_last = err_loc - f_last;
	assign	f_first_minus_err = f_first - err_loc;
	always @(*)
	if (o_axi_bvalid)
	begin
		if (!err_state)
		begin
			assert(!o_axi_bresp[1]);
		end else if (err_loc == f_last)
		begin
			assert(o_axi_bresp == 2'b10);
		end else if (f_err_minus_last < (1<<LGFIFO))
		begin
			assert(!o_axi_bresp[1]);
		end else
			assert(o_axi_bresp[1]);
	end

	always @(*)
	if (err_state)
	begin
		assert(o_axi_bvalid == (r_first != r_last));
	end else
		assert(o_axi_bvalid == (r_mid != r_last));

	always @(*)
	if (err_state)
		assert(f_first_minus_err <= (1<<LGFIFO));

	always @(*)
	if (err_state)
		assert(f_first_minus_err != 0);

	always @(*)
	if (err_state)
		assert(f_mid_minus_err <= f_first_minus_err);

	assign	f_axi_stalled = (fifo_full)||(err_state)
				||((o_wb_stb)&&(i_wb_stall));

	always @(*)
	if ((r_awvalid)&&(f_axi_stalled))
		assert(!o_axi_awready);
	always @(*)
	if ((r_wvalid)&&(f_axi_stalled))
		assert(!o_axi_wready);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover property checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		cover(o_wb_cyc && o_wb_stb && !i_wb_stall);
	always @(*)
		cover(o_wb_cyc && i_wb_ack);

	always @(posedge i_clk)
		cover(o_wb_cyc && $past(o_wb_cyc && o_wb_stb && !i_wb_stall));//

	always @(posedge i_clk)
		cover(o_wb_cyc && o_wb_stb && !i_wb_stall
			&& $past(o_wb_cyc && o_wb_stb && !i_wb_stall,2)
			&& $past(o_wb_cyc && o_wb_stb && !i_wb_stall,4)); //

	always @(posedge i_clk)
		cover(o_wb_cyc && o_wb_stb && !i_wb_stall
			&& $past(o_wb_cyc && o_wb_stb && !i_wb_stall)
			&& $past(o_wb_cyc && o_wb_stb && !i_wb_stall)); //

	always @(posedge i_clk)
		cover(o_wb_cyc && i_wb_ack
			&& $past(o_wb_cyc && i_wb_ack)
			&& $past(o_wb_cyc && i_wb_ack)); //

	// AXI covers
	always @(posedge i_clk)
		cover(o_axi_bvalid && i_axi_bready
			&& $past(o_axi_bvalid && i_axi_bready,1)
			&& $past(o_axi_bvalid && i_axi_bready,2)); //
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_wb_nreqs, f_wb_nacks };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
