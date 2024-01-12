////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rtl/wbxclk.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	To cross clock domains with a (pipelined) wishbone bus.
//
// Challenges:
//	1. Wishbone has no capacity for back pressure.  That means that we'll
//		need to be careful not to issue more STB requests than ACKs
//		that will fit in the return buffer.
//
//	    Imagine, for example, a faster return clock but a slave that needs
//		many clocks to get going.  During that time, many requests
//		might be issued.  If they all suddenly get returned at once,
//		flooding the return ACK FIFO, then we have a problem.
//
//	2. Bus aborts.  If we ever have to abort a transaction, that's going
//		to be a pain.  The FIFOs will need to be reset and the
//		downstream CYC line dropped.  This needs to be done
//		synchronously in both domains, but there's no real choice but
//		to make the crossing asynchronous.
//
//	3. Synchronous CYC.  Lowering CYC is a normal part of the protocol, as
//		is raising CYC.  CYC is used as a bus locking scheme, so we'll
//		need to know when it is (properly) lowered downstream.  This
//		can be done by passing a synchronous CYC drop request through
//		the pipeline in addition to the bus aborts above.
//
//	Status:
//		Formally verified against a set of bus properties, not yet
//		used in any real or simulated designs
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
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
module	wbxclk #(
		// {{{
		parameter	AW=32,
				DW=32,
				LGFIFO = 5
		// }}}
	) (
		// {{{
		input	wire			i_wb_clk, i_reset,
		// Input/master bus
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(DW/8-1):0]	i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[(DW-1):0]	o_wb_data,
		output	reg			o_wb_err,
		// Delayed bus
		input	wire			i_xclk_clk,
		output	reg			o_xclk_cyc,
		output	reg			o_xclk_stb,
		output	reg			o_xclk_we,
		output	reg	[(AW-1):0]	o_xclk_addr,
		output	reg	[(DW-1):0]	o_xclk_data,
		output	reg	[(DW/8-1):0]	o_xclk_sel,
		input	wire			i_xclk_stall,
		input	wire			i_xclk_ack,
		input	wire	[(DW-1):0]	i_xclk_data,
		input	wire			i_xclk_err
		// }}}
	);

	//
	// Declare our signals
	// {{{
	localparam	NFF = 2;
	reg		wb_active;
	reg [NFF-2:0]	bus_abort_pipe;
	reg [LGFIFO:0]	acks_outstanding;
	reg		ackfifo_single, ackfifo_empty, ackfifo_full;
	wire		ack_stb, err_stb;
	wire [DW-1:0]	ret_wb_data;
	wire		req_fifo_stall, no_returns;
	//
	// Verilator lint_off SYNCASYNCNET
	reg		bus_abort;
	// Verilator lint_on  SYNCASYNCNET
	//
	wire		req_stb, req_fifo_empty;
	reg		xclk_err_state, ign_ackfifo_stall;
	reg		xck_reset;
	reg [NFF-2:0]	xck_reset_pipe;
	wire		req_we;
	wire [AW-1:0]	req_addr;
	wire [DW-1:0]	req_data;
	wire [DW/8-1:0]	req_sel;
`ifdef	FORMAL
	wire	[LGFIFO:0]	ackfifo_prefill, reqfifo_prefill;
`endif
	// }}}

	//
	//
	// On the original wishbone clock ...
	//
	//	 FIFO/queue up our requests
	// {{{
	initial	wb_active = 1'b0;
	always	@(posedge i_wb_clk)
	if (i_reset || !i_wb_cyc)
		wb_active <= 1'b0;
	else if (i_wb_stb && !o_wb_stall)
		wb_active <= 1'b1;

	initial	{ bus_abort, bus_abort_pipe } = -1;
	always	@(posedge i_wb_clk)
	if (i_reset)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (!i_wb_cyc && (!ackfifo_empty))
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (o_wb_err)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (ackfifo_empty)
		{ bus_abort, bus_abort_pipe } <= { bus_abort_pipe, 1'b0 };
`ifdef	FORMAL
	always @(*)
	if (bus_abort_pipe)
		assert(bus_abort);
`endif
	// }}}

	//
	// The request FIFO itself
	// {{{
	afifo #(
`ifdef	FORMAL
		.OPT_REGISTER_READS(0),
		.F_OPT_DATA_STB(1'b0),
`endif
		.NFF(NFF), .LGFIFO(LGFIFO),
		.WIDTH(2+AW+DW+(DW/8))
	) reqfifo(.i_wclk(i_wb_clk), .i_wr_reset_n(!bus_abort),
		.i_wr((i_wb_stb&&!o_wb_stall) || (wb_active && !i_wb_cyc)),
		.i_wr_data({ i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel }),
		.o_wr_full(req_fifo_stall),
		//
		.i_rclk(i_xclk_clk), .i_rd_reset_n(!xck_reset),
		.i_rd(!o_xclk_stb || !i_xclk_stall),
		.o_rd_data({ req_stb, req_we, req_addr, req_data, req_sel }),
		.o_rd_empty(req_fifo_empty)
`ifdef	FORMAL
		, .f_fill(reqfifo_prefill)
`endif
	);
	// }}}

	//
	// Downstream bus--issuing requests
	// {{{
	initial	{ xck_reset, xck_reset_pipe } = -1;
	always	@(posedge i_xclk_clk or posedge bus_abort)
	if (bus_abort)
		{ xck_reset, xck_reset_pipe } <= -1;
	else
		{ xck_reset, xck_reset_pipe } <= { xck_reset_pipe, 1'b0 };
`ifdef	FORMAL
	always @(*)
	if (xck_reset_pipe)
		assert(xck_reset);
`endif

	initial	xclk_err_state = 1'b0;
	always @(posedge i_xclk_clk)
	if (xck_reset || (!req_fifo_empty && !req_stb))
		xclk_err_state <= 1'b0;
	else if (o_xclk_cyc && i_xclk_err)
		xclk_err_state <= 1'b1;

	initial	o_xclk_cyc = 1'b0;
	always @(posedge i_xclk_clk)
	if (xck_reset || (o_xclk_cyc && i_xclk_err))
		o_xclk_cyc <= 1'b0;
	else if (!req_fifo_empty && !req_stb)
		o_xclk_cyc <= 1'b0;
	else if (!req_fifo_empty && !xclk_err_state)
		o_xclk_cyc <= req_stb;

	initial	o_xclk_stb = 1'b0;
	always @(posedge i_xclk_clk)
	if (xck_reset || (o_xclk_cyc && i_xclk_err) || xclk_err_state)
		o_xclk_stb <= 1'b0;
	else if (!o_xclk_stb || !i_xclk_stall)
		o_xclk_stb <= req_stb && !req_fifo_empty;

	always @(posedge i_xclk_clk)
	if ((!o_xclk_stb || !i_xclk_stall) && req_stb && !req_fifo_empty)
		o_xclk_we <= req_we;

	always @(posedge i_xclk_clk)
	if (!o_xclk_stb || !i_xclk_stall)
	begin
		o_xclk_addr <= req_addr;
		o_xclk_data <= req_data;
		o_xclk_sel  <= req_sel;
	end
	// }}}


	//
	// Request counting
	// {{{
	initial	acks_outstanding = 0;
	initial	ackfifo_single = 0;
	initial	ackfifo_empty  = 1;
	initial	ackfifo_full   = 0;
	always @(posedge i_wb_clk)
	if (i_reset || !i_wb_cyc || o_wb_err)
	begin
		acks_outstanding <= 0;
		ackfifo_single   <= 0;
		ackfifo_empty    <= 1;
		ackfifo_full     <= 0;
	end else case({ (i_wb_stb && !o_wb_stall), o_wb_ack })
	2'b10: begin
		acks_outstanding <= acks_outstanding + 1;
		ackfifo_empty <= 0;
		ackfifo_single <= ackfifo_empty;
		ackfifo_full   <= (&acks_outstanding[LGFIFO-1:0]);
		end
	2'b01: begin
		acks_outstanding <= acks_outstanding - 1;
		ackfifo_empty <= (acks_outstanding <= 1);
		ackfifo_single <= (acks_outstanding == 2);
		ackfifo_full   <= 0;
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	begin
		assert(ackfifo_single == (acks_outstanding == 1));
		assert(ackfifo_empty == (acks_outstanding == 0));
		assert(ackfifo_full == (acks_outstanding >= (1<<LGFIFO)));
		assert(acks_outstanding <= (1<<LGFIFO));
	end
`endif

	assign	o_wb_stall = ackfifo_full || bus_abort || req_fifo_stall;
	// }}}

	//
	// The return FIFO
	// {{{
	afifo #(
		.OPT_REGISTER_READS(0),
		.NFF(NFF), .LGFIFO(LGFIFO),
		.WIDTH(2+DW)
`ifdef	FORMAL
		, .F_OPT_DATA_STB(1'b0)
`endif
	) ackfifo(.i_wclk(i_xclk_clk), .i_wr_reset_n(!xck_reset),
		.i_wr(o_xclk_cyc && ( i_xclk_ack || i_xclk_err )),
		.i_wr_data({ i_xclk_ack, i_xclk_err, i_xclk_data }),
		.o_wr_full(ign_ackfifo_stall),
		//
		.i_rclk(i_wb_clk), .i_rd_reset_n(!bus_abort),
		.i_rd(!no_returns),
		.o_rd_data({ ack_stb, err_stb, ret_wb_data }),
		.o_rd_empty(no_returns)
`ifdef	FORMAL
		, .f_fill(ackfifo_prefill)
`endif
	);
	// }}}

	//
	// Final return processing
	// {{{
	initial	{ o_wb_ack, o_wb_err } = 2'b00;
	always @(posedge i_wb_clk)
	if (i_reset || bus_abort || !i_wb_cyc || no_returns || o_wb_err)
		{ o_wb_ack, o_wb_err } <=  2'b00;
	else
		{ o_wb_ack, o_wb_err } <= { ack_stb, err_stb };

	always @(posedge i_wb_clk)
		o_wb_data <= ret_wb_data;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, req_fifo_stall, ign_ackfifo_stall,
			ackfifo_single };
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
	// Register/net/macro declarations
	// {{{
`ifdef	BMC
`define	BMC_ASSERT	assert
`else
`define	BMC_ASSERT	assume
`endif

	(* gclk *)	reg	gbl_clk;

	wire	[LGFIFO:0]	fwb_nreqs, fwb_nacks, fwb_outstanding;
	wire	[LGFIFO:0]	fxck_nreqs, fxck_nacks, fxck_outstanding;
	reg	[LGFIFO:0]	ackfifo_fill, reqfifo_fill;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assume a clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[3:0]	fwb_step, fxck_step;
	reg	[3:0]	fwb_count, fxck_count;

	always @(*)
	begin
		assume(fwb_step  >= 2);
		assume(fxck_step >= 2);

		assume(fwb_step  <= 4'b1000);
		assume(fxck_step <= 4'b1000);

	//	assume(fwb_step  == 4'b1000);
	//	assume(fxck_step  == 4'b0111);
		assume((fwb_step  == 4'b0111)
			|| (fxck_step == 4'b0111));
	end

	always @(posedge gbl_clk)
	begin
		fwb_count  <= fwb_count  + fwb_step;
		fxck_count <= fxck_count + fxck_step;
	end

	always @(*)
	begin
		assume(i_wb_clk   == fwb_count[3]);
		assume(i_xclk_clk == fxck_count[3]);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ....
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Cross clock stability assumptions
	// {{{
	always @(posedge gbl_clk)
	if (!$rose(i_wb_clk))
	begin
		assume($stable(i_reset));

		assume($stable(i_wb_cyc));
		assume($stable(i_wb_stb));
		assume($stable(i_wb_we));
		assume($stable(i_wb_addr));
		assume($stable(i_wb_data));
		assume($stable(i_wb_sel));
	end

	always @(posedge gbl_clk)
	if (!$rose(i_xclk_clk))
	begin
		assume($stable(i_xclk_ack));
		assume($stable(i_xclk_err));
		assume($stable(i_xclk_data));
		assume($stable(i_xclk_stall));
	end

	reg			past_wb_clk, past_wb_stb, past_wb_we,
				past_wb_cyc, past_wb_reset, past_wb_err;
	reg			past_xclk, past_xclk_stall, past_xclk_ack,
				past_xclk_err;
	reg	[DW-1:0]	past_xclk_data;
	reg			f_drop_cyc_request;

	always @(posedge gbl_clk)
	begin
		past_wb_clk  <= i_wb_clk;
		past_wb_reset<= i_reset;
		past_wb_cyc  <= i_wb_cyc;
		past_wb_stb  <= i_wb_stb;
		past_wb_we   <= i_wb_we;
		past_wb_err  <= o_wb_err;
	end

	always @(*)
	if (!i_wb_clk || past_wb_clk)
	begin
		assume(past_wb_reset== i_reset);
		assume(past_wb_cyc == i_wb_cyc);
		assume(past_wb_stb == i_wb_stb);
		assume(past_wb_we  == i_wb_we);
		assume(past_wb_err == o_wb_err);
	end else begin
		if (past_wb_err && past_wb_cyc)
			assume(!i_wb_cyc);
		if (fwb_outstanding > 0)
			assume(past_wb_we == i_wb_we);
	end

	always @(posedge gbl_clk)
	begin
		past_xclk       <= i_xclk_clk;
		past_xclk_stall <= i_xclk_stall;
		past_xclk_data  <= i_xclk_data;
		past_xclk_ack   <= i_xclk_ack;
		past_xclk_err   <= i_xclk_err;
	end

	always @(*)
	if (!i_xclk_clk || past_xclk)
	begin
		assume(past_xclk_stall == i_xclk_stall);
		assume(past_xclk_data  == i_xclk_data);
		assume(past_xclk_ack   == i_xclk_ack);
		assume(past_xclk_err   == i_xclk_err);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone bus property checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	fwb_slave #(
		// {{{
		.AW(AW), .DW(DW),
		.F_LGDEPTH(LGFIFO+1), .F_OPT_DISCONTINUOUS(1)
		// }}}
	) slv(
		// {{{
		i_wb_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
		o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
		fwb_nreqs, fwb_nacks, fwb_outstanding
		// }}}
	);

	fwb_master #(
		// {{{
		.AW(AW), .DW(DW),
		.F_LGDEPTH(LGFIFO+1), .F_OPT_DISCONTINUOUS(1),
		.F_MAX_STALL(4),
		.F_MAX_ACK_DELAY(7)
		// }}}
	) xclkwb(
		// {{{
		i_xclk_clk, xck_reset,
		o_xclk_cyc, o_xclk_stb, o_xclk_we, o_xclk_addr, o_xclk_data, o_xclk_sel,
		i_xclk_ack, i_xclk_stall, i_xclk_data, i_xclk_err,
		fxck_nreqs, fxck_nacks, fxck_outstanding
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Random/unsorted) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	always @(*)
	if (reqfifo_fill != (o_xclk_stb ? 1:0) && !req_stb)
		assert(ackfifo_fill == 0 || xclk_err_state);

	always @(*)
		reqfifo_fill = reqfifo_prefill + (o_xclk_stb ? 1:0);

	always @(*)
		ackfifo_fill = ackfifo_prefill // + (no_returns ? 0:1)
			+ ((o_wb_ack || o_wb_err) ? 1:0);

	always @(*)
	if (fwb_outstanding > 0)
		assert(wb_active);

	always @(*)
	if (f_drop_cyc_request && !bus_abort && !xclk_err_state)
	begin
		// req_stb is low, so cycle line has dropped normally

		// If the cycle line has since risen, there may be requests
		// within the request FIFO in addition to the drop-CYC message.
		if (i_wb_cyc && wb_active)
			assert(reqfifo_fill == fwb_outstanding + 1);

		// We wouldn't place a drop CYC message into the FIFO
		// unless XCLK-CYC  was already high
		assert(o_xclk_cyc && !o_xclk_stb);
		assert(ackfifo_fill == 0);
		assert(fxck_outstanding == 0);

		if (reqfifo_fill > 1)
			assert(wb_active);
		else
			assert(!wb_active);
	end else if (!bus_abort && xclk_err_state)
	begin
		//
		// Bus error downstream causes an abort
		assert(fxck_outstanding == 0);
		assert(xck_reset  || wb_active || !i_wb_cyc);
		assert(!o_xclk_stb);
		if (ackfifo_fill == 1)
			assert(no_returns || err_stb);
		else if (!xck_reset && ackfifo_fill == 1)
			assert(o_wb_err);
	end else if (!bus_abort && i_wb_cyc && !xck_reset && !xclk_err_state)
	begin
		//
		// Normal operation in operation
		//
		assert(reqfifo_fill <= fwb_outstanding + 1);
		assert(ackfifo_fill <= fwb_outstanding);
		assert(fxck_outstanding <= fwb_outstanding);
		if (o_xclk_cyc)
			assert(wb_active || f_drop_cyc_request);
		if (reqfifo_fill == (o_xclk_stb ? 1:0) || req_stb)
			// Either first request is for strobe, or other
			// request counters are valid
			assert(reqfifo_fill + ackfifo_fill
				+ fxck_outstanding == fwb_outstanding);
		else begin
			// First request is to drop CYC
			assert(reqfifo_fill== fwb_outstanding + 1);
			assert(ackfifo_fill == 0);
			assert(fxck_outstanding == 0);
			assert(!o_xclk_stb);
			assert(o_xclk_cyc);
		end
		if (acks_outstanding == 0)
			assert((reqfifo_fill == 0)||!req_stb);
	end

	always @(*)
	if (o_wb_ack && wb_active)
	begin
		assert(o_xclk_cyc || xclk_err_state);
		assert(!f_drop_cyc_request);
		assert(!xck_reset || bus_abort);
	end

	always @(*)
	if (!bus_abort && acks_outstanding == 0)
		assert(reqfifo_fill <= (f_drop_cyc_request ? 1:0)
			+ ((o_xclk_stb && xck_reset) ? 1:0));

	always @(*)
	if (ackfifo_fill != 0)
		assert(o_xclk_cyc || xck_reset || xclk_err_state);

	always @(*)
	if (fxck_outstanding > fwb_outstanding)
		assert((!i_wb_cyc && wb_active)
			|| i_reset || bus_abort || xck_reset);

	always @(*)
	if (!i_reset && xck_reset && !o_xclk_cyc)
		assert(!i_wb_cyc || fwb_outstanding == reqfifo_fill);

	always @(*)
	if (bus_abort && i_wb_cyc)
		assert(!wb_active);

	always @(*)
	if (acks_outstanding < (1<<LGFIFO))
	begin
		// assert(!reqfifo_full);
		assert(!ackfifo_full);
	end

	always @(*)
	if (!i_reset && !xck_reset && (fwb_outstanding > 0)
		&& ((fxck_outstanding > 0) || o_xclk_stb))
		assert(i_wb_we == o_xclk_we);

	always @(*)
	if (!i_reset && i_wb_cyc)
		assert(acks_outstanding == fwb_outstanding);

	always @(*)
	if (xclk_err_state)
		assert(!o_xclk_cyc);

	always @(*)
	if (!i_reset && !bus_abort && !i_wb_cyc)
	begin
		if (ackfifo_empty)
		begin
			if (reqfifo_fill > (o_xclk_stb ? 1:0))
				assert(!req_stb || xck_reset);
			assert(reqfifo_fill <= 1);
			if (xck_reset && !xck_reset_pipe)
				assert(!o_xclk_cyc);
		end else begin
			// ???
		end
	end

	always @(*)
		f_drop_cyc_request = !req_stb
				&& (reqfifo_fill > (o_xclk_stb ? 1:0));

	always @(*)
	if (!i_reset && !xck_reset && !bus_abort && i_wb_cyc)
	begin
		if (!o_xclk_cyc && !xclk_err_state)
			assert(acks_outstanding == reqfifo_fill
				- (f_drop_cyc_request ? 1:0));
		else if (!o_xclk_cyc && xclk_err_state)
			assert(acks_outstanding >= reqfifo_fill
				+ ackfifo_fill);
		else if (o_xclk_cyc && !xclk_err_state)
		begin
			assert(acks_outstanding >= reqfifo_fill
				- (f_drop_cyc_request ? 1:0));
			assert(acks_outstanding >= ackfifo_fill);
			assert(acks_outstanding >= fxck_outstanding);
			assert(acks_outstanding ==
				reqfifo_fill - (((reqfifo_fill > (o_xclk_stb ? 1:0))&&(!req_stb)) ? 1:0)
				+ ackfifo_fill
				+ fxck_outstanding);
		end
		if (f_drop_cyc_request)
			assert(acks_outstanding +1 == reqfifo_fill);
		else if (reqfifo_fill == 0)
			assert(!wb_active || o_xclk_cyc || xclk_err_state);
	end else if (!i_reset && !xck_reset && !bus_abort && f_drop_cyc_request)
	begin
		assert(acks_outstanding +1 == reqfifo_fill);
		assert(ackfifo_fill == 0);
		assert(fxck_outstanding == 0);
		assert(!o_xclk_stb);
		assert(o_xclk_cyc);
	end


	always @(*)
	if (!bus_abort && wb_active && reqfifo_fill == 0 && !xclk_err_state)
		assert(o_xclk_cyc);

	always @(*)
	if (f_drop_cyc_request && !bus_abort)
		assert(!xck_reset);

	always @(*)
		assert(!xclk_err_state || acks_outstanding != 0 || xck_reset);

	always @(*)
	if (o_xclk_cyc && !i_wb_cyc)
	begin
		// assert(bus_abort || !xclk_err_state);
		if (!wb_active && !bus_abort && !xck_reset)
			assert(f_drop_cyc_request);
	end else if (i_wb_cyc)
	begin
		if (wb_active && !xck_reset)
			assert(o_xclk_cyc || xclk_err_state
				||(reqfifo_fill >= acks_outstanding));
	end

	// always @(*)
	// if (acks_outstanding >= (1<<LGFIFO))
	//	assert(o_xclk_cyc || xclk_err_state || xck_reset);	// !!!!

	//
	// !!!!!!!!!!!
	//
	// Fig me here
	always @(*)
	if (wb_active && !bus_abort && !xck_reset && i_wb_cyc && !xclk_err_state)
	begin
		if (reqfifo_fill == 0)
			assert(o_xclk_cyc);
	end

	always @(*)
	if (fxck_outstanding > 0 || o_xclk_stb)
		assert(!ign_ackfifo_stall);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Sub properties for the REQ FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if ((acks_outstanding > 0)&&(reqfifo_fill != (o_xclk_stb ? 1:0)))
	begin
		// Something valuable is in the request FIFO
		if (i_wb_cyc && !f_drop_cyc_request)
			`BMC_ASSERT(req_we == i_wb_we);
		else if (req_stb && o_xclk_stb)
			`BMC_ASSERT(o_xclk_we == req_we);

		// if (acks_outstanding > 0)
		if (!o_xclk_cyc || o_xclk_stb ||
				fxck_outstanding > 0 || ackfifo_fill > 0)
			`BMC_ASSERT(req_stb);
	end // else the request FIFO is empty, nothing is in it
		// No assumptions therefore need be made

	always @(*)
	if (!bus_abort && reqfifo_fill == acks_outstanding)
		`BMC_ASSERT(!req_fifo_stall || !f_drop_cyc_request);

	always @(*)
	if (!i_reset && o_xclk_cyc && (reqfifo_fill != (o_xclk_stb ? 1:0)))
		`BMC_ASSERT(!req_stb || req_we == o_xclk_we
			|| fxck_outstanding == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Sub properties for the ACK FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!no_returns)
	begin
		`BMC_ASSERT(ack_stb ^ err_stb);

		if ((ackfifo_fill ==(o_wb_ack ? 2:1)) && xclk_err_state)
			`BMC_ASSERT(err_stb);
		else if (ackfifo_fill > (o_wb_ack ? 2:1))
			`BMC_ASSERT(!err_stb);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg		cvr_abort;
	reg	[3:0]	cvr_replies, cvr_post_abort;

	initial	cvr_abort = 0;
	always @(posedge i_wb_clk)
	if (i_reset)
		cvr_abort <= 0;
	else if (o_wb_err && acks_outstanding > 2)
		cvr_abort <= 1;

	initial	cvr_replies = 0;
	always @(posedge i_wb_clk)
	if (i_reset)
		cvr_replies <= 0;
	else if (o_wb_ack || o_wb_err)
		cvr_replies <= cvr_replies + 1;

	initial	cvr_post_abort = 0;
	always @(posedge i_wb_clk)
	if (i_reset)
		cvr_post_abort <= 0;
	else if (cvr_abort && o_wb_ack)
		cvr_post_abort <= cvr_post_abort + 1;

	always @(*)
	begin
		cover(cvr_replies > 1);	// 33
		cover(cvr_replies > 3);	// 38
		cover(cvr_replies > 9);

		cover(cvr_abort);	// 31
		cover(cvr_post_abort > 1 && cvr_replies > 1);	// 63
		cover(cvr_post_abort > 1 && cvr_replies > 2);	// 63
		cover(cvr_post_abort > 1 && cvr_replies > 3);	// 65
		cover(cvr_post_abort > 2 && cvr_replies > 3);	// 65
		cover(cvr_post_abort > 3 && cvr_replies > 3);	// 68
		cover(cvr_post_abort > 4 && cvr_replies > 3);	// 70
		cover(cvr_post_abort > 3 && cvr_replies > 6);	// 72
	end

	always @(posedge gbl_clk)
	if (!i_reset)
		cover(cvr_replies > 9 && !i_wb_clk && acks_outstanding == 0
			&& fwb_nreqs == fwb_nacks && fwb_nreqs == cvr_replies
			&& !bus_abort && fwb_count != fxck_count);

	always @(posedge gbl_clk)
	if (!i_reset)
		cover(cvr_replies > 9 && !i_wb_clk && acks_outstanding == 0
			&& fwb_nreqs == fwb_nacks && fwb_nreqs == cvr_replies
			&& !bus_abort && fwb_count != fxck_count
			&& fwb_step != fxck_step);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Simplifying (careless) assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// None (at present)

	// }}}
`endif
// }}}
endmodule
