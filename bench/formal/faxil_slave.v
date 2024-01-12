////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxil_slave.v (Formal properties of an AXI lite slave)
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
// Copyright (C) 2018-2024, Gisselquist Technology, LLC
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
module faxil_slave #(
	// {{{
	parameter  C_AXI_DATA_WIDTH	= 32,// Fixed, width of the AXI R&W data
	parameter  C_AXI_ADDR_WIDTH	= 28,// AXI Address width (log wordsize)
	// F_OPT_XILINX, Certain Xilinx cores impose additional rules upon AXI
	// write transactions, limiting how far the write and write address
	// can be apart.  If F_OPT_XILINX is set, these rules will be applied
	// here as well.  See in-line for more details.
	parameter [0:0]	F_OPT_XILINX = 1'b0,
	// F_OPT_WRITE_ONLY, if set, will assume the master is always idle on
	// te read channel, allowing you to test/focus on the write interface
	parameter [0:0]	F_OPT_WRITE_ONLY  = 1'b0,
	// F_OPT_READ_ONLY, if set, will assume the master is always idle on
	// the write channel, while asserting that all of the associated returns
	// and counters are zero
	parameter [0:0]	F_OPT_READ_ONLY = 1'b0,
	// F_OPT_BRESP: Allow any type of write response.  If set clear, then
	// error responses are disallowed.
	parameter [0:0]	F_OPT_BRESP = 1'b1,
	// F_OPT_RRESP, if cleared, will disallow error responses
	parameter [0:0]	F_OPT_RRESP = 1'b1,
	// F_OPT_ASSUME_RESET, if set, will cause the design to *assume* the
	// existence of a correct reset, rather than asserting it.  It is
	// appropriate anytime the reset logic is outside of the circuit being
	// examined
	parameter [0:0]			F_OPT_ASSUME_RESET = 1'b1,
	parameter [0:0]			F_OPT_NO_RESET = 1'b1,
	//
	// F_OPT_ASYNC_RESET is for those designs that will reset the channels
	// using an asynchronous reset.  In these cases, the stability
	// properties only apply when the async reset is not asserted.
	// Likewise, when F_OPT_ASYNC_RESET is set, the reset assertions are
	// applied *on the same clock cycle*, in addition to one cycle later.
	parameter [0:0]			F_OPT_ASYNC_RESET = 1'b0,
	parameter 			F_OPT_COVER_BURST = 0,
	// F_LGDEPTH is the number of bits necessary to count the maximum
	// number of items in flight.
	parameter			F_LGDEPTH	= 4,
	// F_AXI_MAXWAIT is the maximum number of clock cycles the
	// master should have to wait for a slave to raise its ready flag to
	// accept a request.  Set to zero for no limit.
	parameter			F_AXI_MAXWAIT  = 12,
	// F_AXI_MAXRSTALL is the maximum number of clock cycles the
	// slave should have to wait with a return valid signal high, but
	// while the master's return ready signal is low.  Set to zero for no
	// limit.
	parameter			F_AXI_MAXRSTALL= 12,
	// F_AXI_MAXDELAY is the maximum number of clock cycles between request
	// and response within the slave.  Set this to zero for no limit.
	parameter			F_AXI_MAXDELAY = 12,
	//
	parameter [0:0]			F_OPT_INITIAL = 1'b1,

	//
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH
	// }}}
	) (
		// {{{
		input	wire			i_clk,	// System clock
		input	wire			i_axi_reset_n,

		// AXI write address channel signals
		// {{{
		input	wire			i_axi_awvalid,
		input	wire			i_axi_awready,
		input	wire	[AW-1:0]	i_axi_awaddr,	// Write address
		input	wire	[2:0]		i_axi_awprot,	// Protection
		// }}}
		// AXI write data channel signals
		// {{{
		input	wire			i_axi_wvalid,
		input	wire			i_axi_wready,
		input	wire	[DW-1:0]	i_axi_wdata,	// Write data
		input	wire	[DW/8-1:0]	i_axi_wstrb,	// Write strobes
		// }}}
		// AXI write response channel signals
		// {{{
		input	wire			i_axi_bvalid,
		input	wire			i_axi_bready,
		input	wire	[1:0]		i_axi_bresp,	// Wr response
		// }}}
		// AXI read address channel signals
		// {{{
		input	wire			i_axi_arvalid,
		input	wire			i_axi_arready,
		input	wire	[AW-1:0]	i_axi_araddr,	// Read address
		input	wire	[2:0]		i_axi_arprot,	// Protection
		// }}}
		// AXI read data channel signals
		// {{{
		input	wire			i_axi_rvalid,
		input	wire			i_axi_rready,
		input	wire	[DW-1:0]	i_axi_rdata,	// Read data
		input	wire	[1:0]		i_axi_rresp,	// Read response
		// }}}
		output	reg	[(F_LGDEPTH-1):0]	f_axi_rd_outstanding,
		output	reg	[(F_LGDEPTH-1):0]	f_axi_wr_outstanding,
		output	reg	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding
		// }}}
	);

	localparam	MAX_SLAVE_TIMEOUT = (F_AXI_MAXWAIT > F_AXI_MAXDELAY)
				? (F_AXI_MAXWAIT) : F_AXI_MAXDELAY;
	localparam	MAX_TIMEOUT = (F_AXI_MAXRSTALL>MAX_SLAVE_TIMEOUT)
				? (F_AXI_MAXRSTALL) : MAX_SLAVE_TIMEOUT;
	localparam	LGTIMEOUT = $clog2(MAX_TIMEOUT+1);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

	// wire	w_fifo_full;
	wire	axi_rd_ack, axi_wr_ack, axi_ard_req, axi_awr_req, axi_wr_req;
		// axi_rd_err, axi_wr_err;
	reg		f_past_valid;
	reg	[3:0]	f_reset_length;
	// integer	k;

	assign	axi_ard_req = (i_axi_arvalid)&&(i_axi_arready) && i_axi_reset_n;
	assign	axi_awr_req = (i_axi_awvalid)&&(i_axi_awready) && i_axi_reset_n;
	assign	axi_wr_req  = (i_axi_wvalid )&&(i_axi_wready) && i_axi_reset_n;
	//
	assign	axi_rd_ack = (i_axi_rvalid)&&(i_axi_rready) && i_axi_reset_n;
	assign	axi_wr_ack = (i_axi_bvalid)&&(i_axi_bready) && i_axi_reset_n;
	// assign axi_rd_err = (axi_rd_ack)&&(i_axi_rresp[1]) && i_axi_reset_n;
	// assign axi_wr_err = (axi_wr_ack)&&(i_axi_bresp[1]) && i_axi_reset_n;

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	//
	// Setup
	//

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Reset properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Insist that the reset signal start out asserted (negative), and
	// remain so for 16 clocks.
	//

	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_INITIAL_RESET
		always @(*)
		if (!f_past_valid)
			assume(!i_axi_reset_n);
	end else begin : ASSERT_INITIAL_RESET
		always @(*)
		if (!f_past_valid)
			assert(!i_axi_reset_n);
	end endgenerate


	//
	// If asserted, the reset must be asserted for a minimum of 16 clocks
	initial	f_reset_length = 0;
	always @(posedge i_clk)
	if (F_OPT_NO_RESET || i_axi_reset_n)
		f_reset_length <= 0;
	else if (!(&f_reset_length))
		f_reset_length <= f_reset_length + 1'b1;


	//
	// If the reset is not generated within this particular core, then it
	// can be assumed if F_OPT_ASSUME_RESET is set
	generate if (F_OPT_ASSUME_RESET && !F_OPT_NO_RESET)
	begin : ASSUME_RESET
		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assume(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assume(!i_axi_reset_n);

	end else if (!F_OPT_NO_RESET)
	begin : ASSERT_RESET

		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assert(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assert(!i_axi_reset_n);

	end endgenerate

	//
	// All of the xVALID signals *MUST* be set low on the clock following
	// a reset.  Not in the spec, but also checked here is that they must
	// also be set low initially.
	always @(posedge i_clk)
	if ((!f_past_valid && F_OPT_INITIAL)
				||(f_past_valid && !$past(i_axi_reset_n)))
	begin
		`SLAVE_ASSUME(!i_axi_arvalid);
		`SLAVE_ASSUME(!i_axi_awvalid);
		`SLAVE_ASSUME(!i_axi_wvalid);
		//
		`SLAVE_ASSERT(!i_axi_bvalid);
		`SLAVE_ASSERT(!i_axi_rvalid);
	end

	generate if (F_OPT_ASYNC_RESET)
	begin
		always @(*)
		if (!i_axi_reset_n)
		begin
			`SLAVE_ASSUME(!i_axi_arvalid);
			`SLAVE_ASSUME(!i_axi_awvalid);
			`SLAVE_ASSUME(!i_axi_wvalid);
			//
			`SLAVE_ASSERT(!i_axi_bvalid);
			`SLAVE_ASSERT(!i_axi_rvalid);
		end
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// xRESP checking
	// {{{
	////////////////////////////////////////////////////////////////////////

	always @(*)
	if ((i_axi_bvalid)&&(!F_OPT_BRESP)&&(F_OPT_INITIAL || i_axi_reset_n))
		`SLAVE_ASSERT(i_axi_bresp == 0);
	always @(*)
	if ((i_axi_rvalid)&&(!F_OPT_RRESP)&&(F_OPT_INITIAL || i_axi_reset_n))
		`SLAVE_ASSERT(i_axi_rresp == 0);
	always @(*)
	if (i_axi_bvalid&&(F_OPT_INITIAL || i_axi_reset_n))
		`SLAVE_ASSERT(i_axi_bresp != 2'b01); // Exclusive access not allowed
	always @(*)
	if (i_axi_rvalid&&(F_OPT_INITIAL || i_axi_reset_n))
		`SLAVE_ASSERT(i_axi_rresp != 2'b01); // Exclusive access not allowed

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stability properties--what happens if valid and not ready
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Assume any response from the bus will not change prior to that
	// response being accepted
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_axi_reset_n))
			&&(!F_OPT_ASYNC_RESET || i_axi_reset_n))
	begin
		// Write address channel
		if ((f_past_valid)&&($past(i_axi_awvalid && !i_axi_awready)))
		begin
			`SLAVE_ASSUME(i_axi_awvalid);
			`SLAVE_ASSUME($stable(i_axi_awaddr));
			`SLAVE_ASSUME($stable(i_axi_awprot));
		end

		// Write data channel
		if ((f_past_valid && (!F_OPT_ASYNC_RESET || i_axi_reset_n))
				&&($past(i_axi_wvalid && !i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME($stable(i_axi_wstrb));
			`SLAVE_ASSUME($stable(i_axi_wdata));
		end

		// Incoming Read address channel
		if ((f_past_valid && (!F_OPT_ASYNC_RESET || i_axi_reset_n))
			&&($past(i_axi_arvalid && !i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			`SLAVE_ASSUME($stable(i_axi_araddr));
			`SLAVE_ASSUME($stable(i_axi_arprot));
		end

		if ((f_past_valid && (!F_OPT_ASYNC_RESET || i_axi_reset_n))
			&&($past(i_axi_rvalid && !i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			`SLAVE_ASSERT($stable(i_axi_rresp));
			`SLAVE_ASSERT($stable(i_axi_rdata));
		end

		if ((f_past_valid && (!F_OPT_ASYNC_RESET || i_axi_reset_n))
			&&($past(i_axi_bvalid && !i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT($stable(i_axi_bresp));
		end
	end

	// Nothing should be returned or requested on the first clock
	generate if (F_OPT_INITIAL)
	begin : INITIAL_VALUE_CHECKS
		initial	`SLAVE_ASSUME(!i_axi_arvalid);
		initial	`SLAVE_ASSUME(!i_axi_awvalid);
		initial	`SLAVE_ASSUME(!i_axi_wvalid);
		//
		initial	`SLAVE_ASSERT(!i_axi_bvalid);
		initial	`SLAVE_ASSERT(!i_axi_rvalid);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist upon a maximum delay before a request is accepted
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	generate if (F_AXI_MAXWAIT > 0)
	begin : CHECK_STALL_COUNT
		reg	[LGTIMEOUT-1:0]		f_axi_awstall,
						f_axi_wstall,
						f_axi_arstall;

		//
		// AXI write address channel
		//
		// Count the number of times AWVALID is true while AWREADY
		// is false.  These are stalls, and we want to insist on a
		// minimum number of them.  However, if BVALID && !BREADY,
		// then there's a reason for not accepting anything more.
		// Similarly, many cores will only ever accept one request
		// at a time, hence we won't count things as stalls if
		// WR-PENDING > 0.
		initial	f_axi_awstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_awvalid)||(i_axi_awready)
				||(i_axi_bvalid))
			f_axi_awstall <= 0;
		else if ((f_axi_awr_outstanding >= f_axi_wr_outstanding)
			&&(i_axi_awvalid && !i_axi_wvalid))
			// If we are waiting for the write channel to be valid
			// then don't count stalls
			f_axi_awstall <= 0;
		else
			f_axi_awstall <= f_axi_awstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_awstall < F_AXI_MAXWAIT);

		//
		// AXI write data channel
		//
		// Count the number of clock cycles that the write data
		// channel is stalled, that is while WVALID && !WREADY.
		// Since things can back up if BVALID & !BREADY, we avoid
		// counting clock cycles in that circumstance
		initial	f_axi_wstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_wvalid)||(i_axi_wready)
				||(i_axi_bvalid))
			f_axi_wstall <= 0;
		else if ((f_axi_wr_outstanding >= f_axi_awr_outstanding)
			&&(!i_axi_awvalid && i_axi_wvalid))
			// If we are waiting for the write address channel
			// to be valid, then don't count stalls
			f_axi_wstall <= 0;
		else
			f_axi_wstall <= f_axi_wstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_wstall < F_AXI_MAXWAIT);

		//
		// AXI read address channel
		//
		// Similar to the first two above, once the master raises
		// ARVALID, insist that the slave respond within a minimum
		// number of clock cycles.  Exceptions include any time
		// RVALID is true, since that can back up the whole system,
		// and any time the number of bursts is greater than zero,
		// since many slaves can only accept one request at a time.
		initial	f_axi_arstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_arvalid)||(i_axi_arready)
				||(i_axi_rvalid))
			f_axi_arstall <= 0;
		else
			f_axi_arstall <= f_axi_arstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_arstall < F_AXI_MAXWAIT);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist upon a maximum delay before any response is accepted
	//
	// These are separate from the earlier ones, in case you wish to
	// control them separately.  For example, an interconnect might be
	// forced to let a channel wait indefinitely for access, but it might
	// not be appropriate to require the response to be able to wait
	// indefinitely as well
	//
	////////////////////////////////////////////////////////////////////////
	//
	generate if (F_AXI_MAXRSTALL > 0)
	begin : CHECK_RESPONSE_STALLS
		reg	[LGTIMEOUT-1:0]		f_axi_bstall,
						f_axi_rstall;

		// AXI write response channel
		//
		// Insist on a maximum number of clocks that BVALID can be
		// high while BREADY is low
		initial	f_axi_bstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_bvalid)||(i_axi_bready))
			f_axi_bstall <= 0;
		else
			f_axi_bstall <= f_axi_bstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_bstall < F_AXI_MAXRSTALL);

		// AXI read response channel
		//
		// Insist on a maximum number of clocks that RVALID can be
		// high while RREADY is low
		initial	f_axi_rstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_rvalid)||(i_axi_rready))
			f_axi_rstall <= 0;
		else
			f_axi_rstall <= f_axi_rstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_rstall < F_AXI_MAXRSTALL);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Xilinx extensions/guarantees to the AXI protocol
	//
	//	1. The address line will never be more than two clocks ahead of
	//		the write data channel, and
	//	2. The write data channel will never be more than one clock
	//		ahead of the address channel.
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (F_OPT_XILINX)
	begin
		// Rule number one:
		always @(posedge i_clk)
		if ((i_axi_reset_n)&&($past(i_axi_reset_n))
			&&($past(i_axi_awvalid && !i_axi_wvalid,2))
				&&($past(f_axi_awr_outstanding>=f_axi_wr_outstanding,2))
				&&(!$past(i_axi_wvalid)))
			`SLAVE_ASSUME(i_axi_wvalid);

		always @(posedge i_clk)
		if ((i_axi_reset_n)
				&&(f_axi_awr_outstanding > 1)
				&&(f_axi_awr_outstanding-1 > f_axi_wr_outstanding))
			`SLAVE_ASSUME(i_axi_wvalid);

		always @(posedge i_clk)
		if ((i_axi_reset_n)
				&&($past(f_axi_awr_outstanding > f_axi_wr_outstanding))
				&&(!$past(axi_wr_req)))
			`SLAVE_ASSUME(i_axi_wvalid);


		// Rule number two:
		always @(posedge i_clk)
		if ((i_axi_reset_n)&&(f_axi_awr_outstanding < f_axi_wr_outstanding))
			`SLAVE_ASSUME(i_axi_awvalid);
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Count outstanding transactions.  With these measures, we count
	// once per any burst.
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Count outstanding write address channel requests
	initial	f_axi_awr_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_outstanding <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
		2'b10: f_axi_awr_outstanding <= f_axi_awr_outstanding + 1'b1;
		2'b01: f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
		default: begin end
	endcase

	//
	// Count outstanding write data channel requests
	initial	f_axi_wr_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_wr_outstanding <= 0;
	else case({ (axi_wr_req), (axi_wr_ack) })
	2'b01: f_axi_wr_outstanding <= f_axi_wr_outstanding - 1'b1;
	2'b10: f_axi_wr_outstanding <= f_axi_wr_outstanding + 1'b1;
	default: begin end
	endcase

	//
	// Count outstanding read requests
	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + 1'b1;
	default: begin end
	endcase

	//
	// Do not let the number of outstanding requests overflow
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_wr_outstanding  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_outstanding < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});

	//
	// That means that requests need to stop when we're almost full
	always @(posedge i_clk)
	if ((F_OPT_INITIAL || i_axi_reset_n) && f_axi_awr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_awready);
	always @(posedge i_clk)
	if ((F_OPT_INITIAL || i_axi_reset_n) && f_axi_wr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_wready);
	always @(posedge i_clk)
	if ((F_OPT_INITIAL || i_axi_reset_n) && f_axi_rd_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_arready);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist that all responses are returned in less than a maximum delay
	// In this case, we count responses within a burst, rather than entire
	// bursts.
	//
	//
	// A unique feature to the backpressure mechanism within AXI is that
	// we have to reset our delay counters in the case of any push back,
	// since the response can't move forward if the master isn't (yet)
	// ready for it.
	//
	////////////////////////////////////////////////////////////////////////
	generate if (F_AXI_MAXDELAY > 0)
	begin : CHECK_MAX_DELAY

		reg	[LGTIMEOUT-1:0]		f_axi_wr_ack_delay,
						f_axi_rd_ack_delay;

		//
		// Count the clock cycles a write request (address + data) has
		// been outstanding and without any response
		initial	f_axi_wr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)
				||(f_axi_awr_outstanding==0)
				||(f_axi_wr_outstanding==0))
			f_axi_wr_ack_delay <= 0;
		else if (f_axi_wr_outstanding > 0)
			f_axi_wr_ack_delay <= f_axi_wr_ack_delay + 1'b1;

		//
		// Count the clock cycles that any read request has been
		// outstanding, but without any response.
		initial	f_axi_rd_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_rvalid)||(f_axi_rd_outstanding==0))
			f_axi_rd_ack_delay <= 0;
		else
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;


		//
		// Assert that write responses will be returned in a timely
		// fashion
		always @(*)
			`SLAVE_ASSERT(f_axi_wr_ack_delay < F_AXI_MAXDELAY);

		//
		// Assert that read responses will be returned in a timely
		// fashion
		always @(*)
			`SLAVE_ASSERT(f_axi_rd_ack_delay < F_AXI_MAXDELAY);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Assume acknowledgements must follow requests
	//
	// The f_axi*outstanding counters count the number of requests.  No
	// acknowledgment should issue without a pending request
	// burst.  Further, the spec is clear: you can't acknowledge something
	// on the same clock you get the request.  There must be at least one
	// clock delay.
	//
	//
	////////////////////////////////////////////////////////////////////////

	//
	// AXI write response channel
	//
	always @(posedge i_clk)
	if (i_axi_bvalid && (F_OPT_INITIAL || i_axi_reset_n))
	begin
		// No BVALID w/o an outstanding request
		`SLAVE_ASSERT(f_axi_awr_outstanding > 0);
		`SLAVE_ASSERT(f_axi_wr_outstanding  > 0);
	end

	//
	// AXI read data channel signals
	//
	always @(posedge i_clk)
	if (i_axi_rvalid && (F_OPT_INITIAL || i_axi_reset_n))
		// No RVALID w/o an outstanding request
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// F_OPT_WRITE_ONLY or F_OPT_READ_ONLY
	//
	// Optionally disable either read or write channels (or both??)
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	assert((!F_OPT_WRITE_ONLY)||(!F_OPT_READ_ONLY));

	generate if (F_OPT_WRITE_ONLY)
	begin : NO_READS

		// If there are no read requests (assumed), there should be
		// no read responses
		always @(*)
			`SLAVE_ASSUME(i_axi_arvalid == 0);
		always @(*)
			assert(f_axi_rd_outstanding == 0);
		always @(*)
			`SLAVE_ASSERT(i_axi_rvalid == 0);

	end endgenerate

	generate if (F_OPT_READ_ONLY)
	begin : NO_WRITES

		// If there are no write requests (assumed, address or data),
		// there should be no read responses
		always @(*)
			`SLAVE_ASSUME(i_axi_awvalid == 0);
		always @(*)
			`SLAVE_ASSUME(i_axi_wvalid == 0);
		always @(*)
			assert(f_axi_wr_outstanding == 0);
		always @(*)
			assert(f_axi_awr_outstanding == 0);
		always @(*)
			`SLAVE_ASSERT(i_axi_bvalid == 0);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Cover properties
	//
	// We'll use this to prove that transactions are even possible, and
	// hence that we haven't so constrained the bus that nothing can take
	// place.
	//
	//
	////////////////////////////////////////////////////////////////////////

	//
	// AXI write response channel
	//
	generate if (!F_OPT_READ_ONLY)
	begin
		always @(posedge i_clk)
			// Make sure we can get a write acknowledgment
			cover((i_axi_bvalid)&&(i_axi_bready));
	end endgenerate

	//
	// AXI read response channel
	//
	generate if (!F_OPT_WRITE_ONLY)
	begin
		always @(posedge i_clk)
			// Make sure we can get a response from the read channel
			cover((i_axi_rvalid)&&(i_axi_rready));
	end endgenerate

	generate if (!F_OPT_READ_ONLY && F_OPT_COVER_BURST > 0)
	begin : COVER_WRITE_BURSTS

		reg	[31:0]	cvr_writes;

		initial	cvr_writes = 0;
		always @(posedge i_clk)
		if (!i_axi_reset_n)
			cvr_writes <= 0;
		else if (i_axi_bvalid && i_axi_bready && i_axi_bresp == 2'b00
				&& !(&cvr_writes))
			cvr_writes <= cvr_writes + 1;

		always @(*)
			cover(cvr_writes == F_OPT_COVER_BURST);

	end endgenerate

	generate if (!F_OPT_WRITE_ONLY && F_OPT_COVER_BURST > 0)
	begin : COVER_READ_BURSTS

		reg	[31:0]	cvr_reads;

		initial	cvr_reads = 0;
		always @(posedge i_clk)
		if (!i_axi_reset_n)
			cvr_reads <= 0;
		else if (i_axi_rvalid && i_axi_rready && i_axi_rresp == 2'b00
				&& !(&cvr_reads))
			cvr_reads <= cvr_reads + 1;

		always @(*)
			cover(cvr_reads == F_OPT_COVER_BURST);

	end endgenerate

`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
endmodule
