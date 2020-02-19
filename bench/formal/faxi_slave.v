////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxi_slave.v (Formal properties of an AXI4 (full) slave)
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This file contains a subset of the formal properties which I've
//		used to formally verify that a core truly follows the full
//	AXI4 specification.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2020, Gisselquist Technology, LLC
//
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
//
module faxi_slave #(
	parameter C_AXI_ID_WIDTH	= 3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width (log wordsize)
	parameter [7:0] OPT_MAXBURST	= 8'hff,// Maximum burst length, minus 1
	parameter [0:0] OPT_EXCLUSIVE	= 1,// Exclusive access allowed
	parameter [0:0] OPT_NARROW_BURST = 1,// Narrow bursts allowed by default
	parameter [0:0]	OPT_ASYNC_RESET  = 0,
	// F_OPT_ASSUME_RESET, if set, will cause the design to *assume* the
	// existence of a correct reset, rather than asserting it.  It is
	// appropriate anytime the reset logic is outside of the circuit being
	// examined
	parameter [0:0]			F_OPT_ASSUME_RESET = 1'b1,
	parameter [0:0]			F_OPT_NO_RESET = 1'b1,
	// F_LGDEPTH is the number of bits necessary to count the maximum
	// number of items in flight.
	parameter				F_LGDEPTH      = 10,
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXSTALL = 3,
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXRSTALL= 3,
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXDELAY = 3,
	localparam			F_OPT_BURSTS    = (OPT_MAXBURST != 0),
	//
	localparam IW			= C_AXI_ID_WIDTH,
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH
	) (
	input	wire			i_clk,	// System clock
	input	wire			i_axi_reset_n,

// AXI write address channel signals
	input	wire			i_axi_awready,//Slave is ready to accept
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_awid,	// Write ID
	input	wire	[AW-1:0]	i_axi_awaddr,	// Write address
	input	wire	[7:0]		i_axi_awlen,	// Write Burst Length
	input	wire	[2:0]		i_axi_awsize,	// Write Burst size
	input	wire	[1:0]		i_axi_awburst,	// Write Burst type
	input	wire	[0:0]		i_axi_awlock,	// Write lock type
	input	wire	[3:0]		i_axi_awcache,	// Write Cache type
	input	wire	[2:0]		i_axi_awprot,	// Write Protection type
	input	wire	[3:0]		i_axi_awqos,	// Write Quality of Svc
	input	wire			i_axi_awvalid,	// Write address valid

// AXI write data channel signals
	input	wire			i_axi_wready,  // Write data ready
	input	wire	[DW-1:0]	i_axi_wdata,	// Write data
	input	wire	[DW/8-1:0]	i_axi_wstrb,	// Write strobes
	input	wire			i_axi_wlast,	// Last write transaction
	input	wire			i_axi_wvalid,	// Write valid

// AXI write response channel signals
	input	wire [C_AXI_ID_WIDTH-1:0] i_axi_bid,	// Response ID
	input	wire	[1:0]		i_axi_bresp,	// Write response
	input	wire			i_axi_bvalid,  // Write reponse valid
	input	wire			i_axi_bready,  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready,	// Read address ready
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
	input	wire	[AW-1:0]	i_axi_araddr,	// Read address
	input	wire	[7:0]		i_axi_arlen,	// Read Burst Length
	input	wire	[2:0]		i_axi_arsize,	// Read Burst size
	input	wire	[1:0]		i_axi_arburst,	// Read Burst type
	input	wire	[0:0]		i_axi_arlock,	// Read lock type
	input	wire	[3:0]		i_axi_arcache,	// Read Cache type
	input	wire	[2:0]		i_axi_arprot,	// Read Protection type
	input	wire	[3:0]		i_axi_arqos,	// Read Protection type
	input	wire			i_axi_arvalid,	// Read address valid

// AXI read data channel signals
	input wire [C_AXI_ID_WIDTH-1:0] i_axi_rid,     // Response ID
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input	wire	[DW-1:0]	i_axi_rdata,    // Read data
	input	wire			i_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[F_LGDEPTH-1:0]		f_axi_awr_nbursts,
	output	reg	[9-1:0]			f_axi_wr_pending,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_outstanding,
	// ...
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	F_AXI_MAXWAIT = F_AXI_MAXSTALL;

	// Because of the nature and size of bursts, which can be up to
	// 256 in length (AxLEN), the F_LGDEPTH parameter necessary to capture
	// this *must* be at least 8 bits wide
	always @(*)
		assert(F_LGDEPTH > 8);

	// Only power of two data sizes are supported from 8-bits on up to
	// 1024
	always @(*)
		assert((DW == 8)
			||(DW ==  16)
			||(DW ==  32)
			||(DW ==  64)
			||(DW == 128)
			||(DW == 256)
			||(DW == 512)
			||(DW == 1024));

//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************


	wire	axi_rd_ack, axi_wr_ack, axi_ard_req, axi_awr_req, axi_wr_req,
		axi_rd_err, axi_wr_err;
	//
	assign	axi_ard_req = (i_axi_arvalid)&&(i_axi_arready);
	assign	axi_awr_req = (i_axi_awvalid)&&(i_axi_awready);
	assign	axi_wr_req  = (i_axi_wvalid )&&(i_axi_wready);
	//
	assign	axi_rd_ack = (i_axi_rvalid)&&(i_axi_rready);
	assign	axi_wr_ack = (i_axi_bvalid)&&(i_axi_bready);
	assign	axi_rd_err = (axi_rd_ack)&&(i_axi_rresp[1]);
	assign	axi_wr_err = (axi_wr_ack)&&(i_axi_bresp[1]);
	//
	// ...
	//

	// Within the slave core, we will *assume* properties from the master,
	// and *assert* properties of signals coming from the slave and
	// returning to the master.  This order will be reversed within the
	// master, and the following two definitions help us do that.
	//
	// Similarly, we will always *assert* local values of our own necessary
	// for checks below.  Those will use the assert() keyword, rather than
	// either of these two macros.
`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	//
	// Setup
	//
	integer	k;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!i_axi_reset_n);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Reset properties
	//
	// Insist that the reset signal start out asserted (negative), and
	// remain so for 16 clocks.
	//
	////////////////////////////////////////////////////////////////////////
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
	//
	// If asserted, the reset must be asserted for a minimum of 16 clocks
	initial	f_reset_length = 0;
	always @(posedge i_clk)
	if (F_OPT_NO_RESET || i_axi_reset_n)
		f_reset_length <= 0;
	else if (!(&f_reset_length))
		f_reset_length <= f_reset_length + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&& !F_OPT_NO_RESET
			&& (!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
		`SLAVE_ASSUME(!i_axi_reset_n);

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
	if ((!f_past_valid)||(!$past(i_axi_reset_n)))
	begin
		`SLAVE_ASSUME(!i_axi_arvalid);
		`SLAVE_ASSUME(!i_axi_awvalid);
		`SLAVE_ASSUME(!i_axi_wvalid);
		//
		`SLAVE_ASSERT(!i_axi_bvalid);
		`SLAVE_ASSERT(!i_axi_rvalid);
	end

	generate if (OPT_ASYNC_RESET)
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

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Stability properties--what happens if valid and not ready
	//
	//
	////////////////////////////////////////////////////////////////////////

	// Assume any response from the bus will not change prior to that
	// response being accepted
	always @(posedge i_clk)
	if ((f_past_valid)&& $past(i_axi_reset_n)
		&& (!OPT_ASYNC_RESET || i_axi_reset_n))
	begin
		// Write address channel
		if ((f_past_valid)&&($past(i_axi_awvalid && !i_axi_awready)))
		begin
			`SLAVE_ASSUME(i_axi_awvalid);
			`SLAVE_ASSUME($stable(i_axi_awaddr));
			`SLAVE_ASSUME($stable(i_axi_awid));
			`SLAVE_ASSUME($stable(i_axi_awlen));
			`SLAVE_ASSUME($stable(i_axi_awsize));
			`SLAVE_ASSUME($stable(i_axi_awburst));
			`SLAVE_ASSUME($stable(i_axi_awlock));
			`SLAVE_ASSUME($stable(i_axi_awcache));
			`SLAVE_ASSUME($stable(i_axi_awprot));
			`SLAVE_ASSUME($stable(i_axi_awqos));
		end

		// Write data channel
		if ((f_past_valid)&&($past(i_axi_wvalid && !i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME($stable(i_axi_wstrb));
			`SLAVE_ASSUME($stable(i_axi_wdata));
			`SLAVE_ASSUME($stable(i_axi_wlast));
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid && !i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			`SLAVE_ASSUME($stable(i_axi_arid));
			`SLAVE_ASSUME($stable(i_axi_araddr));
			`SLAVE_ASSUME($stable(i_axi_arlen));
			`SLAVE_ASSUME($stable(i_axi_arsize));
			`SLAVE_ASSUME($stable(i_axi_arburst));
			`SLAVE_ASSUME($stable(i_axi_arlock));
			`SLAVE_ASSUME($stable(i_axi_arcache));
			`SLAVE_ASSUME($stable(i_axi_arprot));
			`SLAVE_ASSUME($stable(i_axi_arqos));
		end

		// Assume any response from the bus will not change prior to
		// that response being accepted
		if ((f_past_valid)&&($past(i_axi_rvalid && !i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			`SLAVE_ASSERT($stable(i_axi_rid));
			`SLAVE_ASSERT($stable(i_axi_rresp));
			`SLAVE_ASSERT($stable(i_axi_rdata));
			`SLAVE_ASSERT($stable(i_axi_rlast));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid && !i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT($stable(i_axi_bid));
			`SLAVE_ASSERT($stable(i_axi_bresp));
		end
	end

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
		reg	[(F_LGDEPTH-1):0]	f_axi_awstall,
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
				||(f_axi_wr_pending > 0))
			f_axi_awstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
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
				||(f_axi_wr_pending == 0 && i_axi_wvalid))
			f_axi_wstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
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
				||(i_axi_rvalid)||(f_axi_rd_nbursts > 0))
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

	generate if (F_AXI_MAXRSTALL > 0)
	begin : CHECK_RESPONSE_STALLS
		//
		// AXI write address channel
		//
		//
		reg	[(F_LGDEPTH-1):0]	f_axi_wvstall,
						f_axi_bstall,
						f_axi_rstall;

		// AXI write channel valid
		//
		// The first master stall check: guarantee that the master
		// provides the required write data in fairly short order,
		// and without much delay.  That is, once AWVALID && AWREADY
		// are true, the slave needs to provide the W* values
		initial	f_axi_wvstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_wvalid)
				||(i_axi_bvalid && !i_axi_bready)
				||(f_axi_wr_pending == 0))
			f_axi_wvstall <= 0;
		else
			f_axi_wvstall <= f_axi_wvstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_wvstall < F_AXI_MAXRSTALL);

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
	// Count outstanding transactions.  With these measures, we count
	// once per any burst.
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// ...

	initial	f_axi_wr_pending = 0;
	// ...
	always @(posedge i_clk)
	if (!i_axi_reset_n)
	begin
		f_axi_wr_pending <= 0;
		// ...
	end else case({ axi_awr_req, axi_wr_req })
	2'b10: begin
		f_axi_wr_pending <= i_axi_awlen+1;
		// ...
		end
	2'b01: begin
		`SLAVE_ASSUME(f_axi_wr_pending > 0);
		f_axi_wr_pending <= f_axi_wr_pending - 1'b1;
		`SLAVE_ASSUME(!i_axi_wlast || (f_axi_wr_pending == 1));
		// ...
		end
	2'b11: begin
		// ...
		if (f_axi_wr_pending > 0)
			f_axi_wr_pending <= i_axi_awlen+1;
		else begin
			f_axi_wr_pending <= i_axi_awlen;
			// ...
		end end
	default: begin end
	endcase

	// ...
	//
	// Insist that no WVALID value show up prior to a AWVALID value.  The
	// address *MUST* come first.  Further, while waiting for the write
	// data, NO OTHER WRITE ADDRESS may be permitted.  This is not strictly
	// required by the specification, but it is required in order to make
	// these properties work (currently--I might revisit this later)
	//
	// ...

	//
	// Count the number of outstanding BVALID's to expect
	//
	initial	f_axi_awr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_nbursts <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
	2'b10: f_axi_awr_nbursts <= f_axi_awr_nbursts + 1'b1;
	2'b01: f_axi_awr_nbursts <= f_axi_awr_nbursts - 1'b1;
	default: begin end
	endcase

	//
	// Count the number of reads bursts outstanding.  This defines the
	// number of RDVALID && RLAST's we expect to see before becoming idle
	//
	initial	f_axi_rd_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_nbursts <= 0;
	else case({ (axi_ard_req), (axi_rd_ack)&&(i_axi_rlast) })
	2'b01: f_axi_rd_nbursts <= f_axi_rd_nbursts - 1'b1;
	2'b10: f_axi_rd_nbursts <= f_axi_rd_nbursts + 1'b1;
	endcase

	//
	// f_axi_rd_outstanding counts the number of RDVALID's we expect to
	// see before becoming idle.  This must always be greater than or
	// equal to the number of RVALID & RLAST's counted above
	//
	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen+1;
	2'b11: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen;
	endcase

	//
	// Do not let the number of outstanding requests overflow.  This is
	// a responsibility of the master to never allow 2^F_LGDEPTH-1
	// requests to be outstanding.
	//
	always @(*)
		`SLAVE_ASSERT(f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});
	always @(*)
		`SLAVE_ASSERT(f_axi_awr_nbursts < {(F_LGDEPTH){1'b1}});
	always @(*)
		`SLAVE_ASSERT(f_axi_wr_pending <= 256);
	always @(*)
		`SLAVE_ASSERT(f_axi_rd_nbursts  < {(F_LGDEPTH){1'b1}});

	////////////////////////////////////////////////////////////////////////
	//
	// Read Burst counting
	//
	always @(*)
		assert(f_axi_rd_nbursts <= f_axi_rd_outstanding);
	always @(*)
		assert((f_axi_rd_nbursts == 0)==(f_axi_rd_outstanding==0));
	//
	//
	// ...
	//
	// AXI read data channel signals
	//
	always @(*)
	if (i_axi_rvalid)
	begin
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);
		`SLAVE_ASSERT(f_axi_rd_nbursts > 0);
		// ...
	end
	always @(*)
		next_rd_nbursts = f_axi_rd_nbursts
				- (i_axi_rvalid && i_axi_rlast ? 1:0);

	always @(*)
		next_rd_outstanding = f_axi_rd_outstanding
				- (i_axi_rvalid ? 1:00);
	// ...
	always @(*)
		`SLAVE_ASSERT(next_rd_nbursts   <= next_rd_outstanding);
	// ...
	always @(*)
		`SLAVE_ASSERT({ 8'h00, next_rd_outstanding }
				<= { next_rd_nbursts, 8'h00 });
	//
	// ...
	//
	always @(*)
		assert({ 8'h00, f_axi_rd_outstanding } <= { f_axi_rd_nbursts, 8'h0 });

	//
	// ...
	//



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

		reg	[(F_LGDEPTH-1):0]	f_axi_awr_ack_delay,
						f_axi_rd_ack_delay;

		initial	f_axi_awr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(i_axi_wvalid)
					||((f_axi_awr_nbursts == 1)
						&&(f_axi_wr_pending>0))
					||(f_axi_awr_nbursts == 0))
			f_axi_awr_ack_delay <= 0;
		else
			f_axi_awr_ack_delay <= f_axi_awr_ack_delay + 1'b1;

		initial	f_axi_rd_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_rvalid)||(f_axi_rd_outstanding==0))
			f_axi_rd_ack_delay <= 0;
		else
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_awr_ack_delay < F_AXI_MAXDELAY);

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_ack_delay < F_AXI_MAXDELAY);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Assume acknowledgements must follow requests
	//
	// The outstanding count is a count of bursts, but the acknowledgements
	// we are looking for are individual.  Hence, there should be no
	// individual acknowledgements coming back if there's no outstanding
	// burst.
	//
	//
	////////////////////////////////////////////////////////////////////////

	//
	// AXI write response channel
	//
	//
	// ...
	//
	//
	// Cannot have outstanding values if there aren't any outstanding
	// bursts
	//
	// ...
	//
	always @(posedge i_clk)
	if (f_axi_awr_nbursts == 0)
		`SLAVE_ASSERT(f_axi_wr_pending == 0);
	//
	// ...
	//

	//
	// Because we can't accept multiple AW* requests prior to the
	// last WVALID && WLAST, the AWREADY signal *MUST* be high while
	// waiting
	//
	always @(*)
	if (f_axi_wr_pending > 1)
		`SLAVE_ASSERT(!i_axi_awready);

	////////////////////////////////////////////////////////////////////////
	//
	// Write address checking
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	begin
		//
		// ...
		//
		if (!OPT_NARROW_BURST)
		begin
			// In this case, all size parameters are fixed.
			// Let's remove them from the solvers logic choices
			// for optimization purposes
			//
			if (DW == 8)
				f_axi_wr_size <= 0;
			else if (DW == 16)
				f_axi_wr_size <= 1;
			else if (DW == 32)
				f_axi_wr_size <= 2;
			else if (DW == 64)
				f_axi_wr_size <= 3;
			else if (DW == 128)
				f_axi_wr_size <= 4;
			else if (DW == 256)
				f_axi_wr_size <= 5;
			else if (DW == 512)
				f_axi_wr_size <= 6;
			else // if (DW == 1024)
				f_axi_wr_size <= 7;
		end
	end

	//
	// ...
	//
	always @(*)
		wstb_addr = f_axi_wr_addr;


	// Insist the only the appropriate bits be valid
	// For example, if the lower address bit is one, then the
	// strobe LSB cannot be 1, but must be zero.  This is just
	// enforcing the rules of the sub-address which must match
	// the write strobe.  An STRB of 0 is always allowed.
	//
	always @(*)
	if (i_axi_wvalid)
		`SLAVE_ASSUME(wstb_valid);

	//
	// Write induction properties
	//
	// These are actual assert()s and not `SLAVE_ASSERT or `SLAVE_ASSUMEs
	// because they are testing the functionality of this core and its local
	// logical registers, not so much the functionality of the core we are
	// testing
	//
	reg	[7:0]	val_wr_len;
	always @(*)
		val_wr_len = f_axi_wr_pending[7:0]-1;

	always @(*)
	if (f_axi_wr_pending > 0)
		assert(f_axi_wr_pending <= f_axi_wr_len + 1);
	always @(*)
		assert(f_axi_wr_pending <= 9'h100);

	always @(*)
	if ((f_axi_wr_pending > 0)&&(f_axi_wr_burst == 2'b10))
		assert((f_axi_wr_len == 1)
			||(f_axi_wr_len == 3)
			||(f_axi_wr_len == 7)
			||(f_axi_wr_len == 15));

	////////////////////////////////////////////////////////////////////////
	//
	// Read address checking
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	begin
		//
		// ...
		//
		if (!OPT_NARROW_BURST)
		begin
			// In this case, all size parameters are fixed.
			// Let's remove them from the solvers logic choices
			// for optimization purposes
			//
			if (DW == 8)
				f_axi_rd_cksize <= 0;
			else if (DW == 16)
				f_axi_rd_cksize <= 1;
			else if (DW == 32)
				f_axi_rd_cksize <= 2;
			else if (DW == 64)
				f_axi_rd_cksize <= 3;
			else if (DW == 128)
				f_axi_rd_cksize <= 4;
			else if (DW == 256)
				f_axi_rd_cksize <= 5;
			else if (DW == 512)
				f_axi_rd_cksize <= 6;
			else // if (DW == 1024)
				f_axi_rd_cksize <= 7;
		end
	end

	//
	// Read induction properties
	//
	// These are actual assert()s and not `SLAVE_ASSERT or `SLAVE_ASSUMEs
	// because they are testing the functionality of this core and its local
	// logical registers, not so much the functionality of the core we are
	// testing
	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Exclusive properties
	//
	////////////////////////////////////////////////////////////////////////
	generate if (!OPT_EXCLUSIVE)
	begin : EXCLUSIVE_DISALLOWED
		localparam [1:0]	EXOKAY = 2'b01;

		//
		// Without exclusive access support, the master shall not issue
		// exclusive access requests
		always @(*)
		begin
		`SLAVE_ASSUME(!i_axi_awvalid || !i_axi_awlock);
		`SLAVE_ASSUME(!i_axi_arvalid || !i_axi_arlock);
		end

		// Similarly, without exclusive access support, the slave
		// shall not respond with an okay indicating that exclusive
		// access was supported.
		always @(*)
		begin
		`SLAVE_ASSERT(!i_axi_bvalid || i_axi_bresp != EXOKAY);
		`SLAVE_ASSERT(!i_axi_rvalid || i_axi_rresp != EXOKAY);
		end

	end else begin : EXCLUSIVE_ACCESS_CHECKER

		//
		// 1. Exclusive access burst lengths max out at 16
		// 2. Exclusive access bursts must be aligned
		// 3. Write must take place when the read channel is idle (on
		//	this ID)
		// (4. Further read accesses on this ID are not allowed)
		//
		always @(*)
		if (i_axi_awvalid && i_axi_awlock)
		begin
			// ...
		end

		always @(*)
		if (i_axi_arvalid && i_axi_arlock)
		begin
			// ...
		end

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// ...
	//
	////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////
	//
	// Option for no bursts, only single transactions
	//
	////////////////////////////////////////////////////////////////////////

	generate if (!F_OPT_BURSTS)
	begin

		always @(*)
		if (i_axi_awvalid)
			`SLAVE_ASSUME(i_axi_awlen == 0);

		always @(*)
		if (i_axi_wvalid)
			`SLAVE_ASSUME(i_axi_wlast);

		always @(*)
			assert(f_axi_wr_pending <= 1);

		always @(*)
			assert(f_axi_wr_len == 0);

		always @(*)
		if (i_axi_arvalid)
			`SLAVE_ASSUME(i_axi_arlen == 0);

		always @(*)
		if (i_axi_rvalid)
			`SLAVE_ASSERT(i_axi_rlast);

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_nbursts == f_axi_rd_outstanding);
		//
		// ...
		//
	end endgenerate


	////////////////////////////////////////////////////////////////////////
	//
	// Packet read checking
	//
	// Pick a read address request, and then track that one transaction
	// through the system
	//
	////////////////////////////////////////////////////////////////////////

	//
	// ...
	//
`endif
endmodule
