////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxil_master.v (Formal properties of an AXI lite master)
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2019, Gisselquist Technology, LLC
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
module faxil_master #(
	parameter  C_AXI_DATA_WIDTH	= 32,// Fixed, width of the AXI R&W data
	parameter  C_AXI_ADDR_WIDTH	= 28,// AXI Address width (log wordsize)
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH,
	parameter [0:0]	F_OPT_HAS_CACHE = 1'b0,
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
	parameter [0:0]	F_OPT_ASSUME_RESET = 1'b0,
	// F_LGDEPTH is the number of bits necessary to count the maximum
	// number of items in flight.
	parameter				F_LGDEPTH	= 4,
	// F_AXI_MAXWAIT is the maximum number of clock cycles the
	// master should have to wait for a slave to raise its ready flag to
	// accept a request.  Set to zero for no limit.
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXWAIT  = 12,
	// F_AXI_MAXRSTALL is the maximum number of clock cycles the
	// slave should have to wait with a return valid signal high, but
	// while the master's return ready signal is low.  Set to zero for no
	// limit.
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXRSTALL= 12,
	// F_AXI_MAXDELAY is the maximum number of clock cycles between request
	// and response within the slave.  Set this to zero for no limit.
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXDELAY = 12
	) (
	input	wire			i_clk,	// System clock
	input	wire			i_axi_reset_n,

// AXI write address channel signals
	input	wire			i_axi_awready,//Slave is ready to accept
	input	wire	[AW-1:0]	i_axi_awaddr,	// Write address
	input	wire	[3:0]		i_axi_awcache,	// Write Cache type
	input	wire	[2:0]		i_axi_awprot,	// Write Protection type
	input	wire			i_axi_awvalid,	// Write address valid

// AXI write data channel signals
	input	wire			i_axi_wready,  // Write data ready
	input	wire	[DW-1:0]	i_axi_wdata,	// Write data
	input	wire	[DW/8-1:0]	i_axi_wstrb,	// Write strobes
	input	wire			i_axi_wvalid,	// Write valid

// AXI write response channel signals
	input	wire	[1:0]		i_axi_bresp,	// Write response
	input	wire			i_axi_bvalid,  // Write reponse valid
	input	wire			i_axi_bready,  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready,	// Read address ready
	input	wire	[AW-1:0]	i_axi_araddr,	// Read address
	input	wire	[3:0]		i_axi_arcache,	// Read Cache type
	input	wire	[2:0]		i_axi_arprot,	// Read Protection type
	input	wire			i_axi_arvalid,	// Read address valid

// AXI read data channel signals
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input	wire	[DW-1:0]	i_axi_rdata,   // Read data
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[(F_LGDEPTH-1):0]	f_axi_rd_outstanding,
	output	reg	[(F_LGDEPTH-1):0]	f_axi_wr_outstanding,
	output	reg	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

	// wire	w_fifo_full;
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

`define	SLAVE_ASSUME	assert
`define	SLAVE_ASSERT	assume

	//
	// Setup
	//
	reg	f_past_valid;
	integer	k;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_INIITAL_RESET
		always @(*)
		if (!f_past_valid)
			assume(!i_axi_reset_n);
	end else begin : ASSERT_INIITAL_RESET
		always @(*)
		if (!f_past_valid)
			assert(!i_axi_reset_n);
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Reset properties
	//
	//
	////////////////////////////////////////////////////////////////////////

	//
	// If asserted, the reset must be asserted for a minimum of 16 clocks
	reg	[3:0]	f_reset_length;
	initial	f_reset_length = 0;
	always @(posedge i_clk)
	if (i_axi_reset_n)
		f_reset_length <= 0;
	else if (!(&f_reset_length))
		f_reset_length <= f_reset_length + 1'b1;


	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_RESET
		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assume(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assume(!i_axi_reset_n);

	end else begin : ASSERT_RESET

		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
			assert(!i_axi_reset_n);

		always @(*)
		if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
			assert(!i_axi_reset_n);

	end endgenerate

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

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Constant input assumptions (cache and prot)
	//
	//
	////////////////////////////////////////////////////////////////////////

	always @(*)
	if (i_axi_awvalid)
	begin
		`SLAVE_ASSUME(i_axi_awprot  == 3'h0);
		if (F_OPT_HAS_CACHE)
			// Normal non-cachable, but bufferable
			`SLAVE_ASSUME(i_axi_awcache == 4'h3);
		else
			// No caching capability
			`SLAVE_ASSUME(i_axi_awcache == 4'h0);
	end

	always @(*)
	if (i_axi_arvalid)
	begin
		`SLAVE_ASSUME(i_axi_arprot  == 3'h0);
		if (F_OPT_HAS_CACHE)
			// Normal non-cachable, but bufferable
			`SLAVE_ASSUME(i_axi_arcache == 4'h3);
		else
			// No caching capability
			`SLAVE_ASSUME(i_axi_arcache == 4'h0);
	end

	always @(*)
	if ((i_axi_bvalid)&&(!F_OPT_BRESP))
		`SLAVE_ASSERT(i_axi_bresp == 0);
	always @(*)
	if ((i_axi_rvalid)&&(!F_OPT_RRESP))
		`SLAVE_ASSERT(i_axi_rresp == 0);
	always @(*)
	if (i_axi_bvalid)
		`SLAVE_ASSERT(i_axi_bresp != 2'b01); // Exclusive access not allowed
	always @(*)
	if (i_axi_rvalid)
		`SLAVE_ASSERT(i_axi_rresp != 2'b01); // Exclusive access not allowed


	////////////////////////////////////////////////////////////////////////
	//
	//
	// Stability assumptions
	//
	//
	////////////////////////////////////////////////////////////////////////

	// Assume any response from the bus will not change prior to that
	// response being accepted
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_axi_reset_n)))
	begin
		// Write address channel
		if ((f_past_valid)&&($past(i_axi_awvalid))&&(!$past(i_axi_awready)))
		begin
			`SLAVE_ASSUME(i_axi_awvalid);
			`SLAVE_ASSUME($stable(i_axi_awaddr));
		end

		// Write data channel
		if ((f_past_valid)&&($past(i_axi_wvalid))&&(!$past(i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME($stable(i_axi_wstrb));
			`SLAVE_ASSUME($stable(i_axi_wdata));
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid))&&(!$past(i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			`SLAVE_ASSUME($stable(i_axi_araddr));
		end

		if ((f_past_valid)&&($past(i_axi_rvalid))&&(!$past(i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			`SLAVE_ASSERT($stable(i_axi_rresp));
			`SLAVE_ASSERT($stable(i_axi_rdata));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid))&&(!$past(i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT($stable(i_axi_bresp));
		end
	end

	// Nothing should be returned or requested on the first clock
	initial	`SLAVE_ASSUME(!i_axi_arvalid);
	initial	`SLAVE_ASSUME(!i_axi_awvalid);
	initial	`SLAVE_ASSUME(!i_axi_wvalid);
	//
	initial	`SLAVE_ASSERT(!i_axi_bvalid);
	initial	`SLAVE_ASSERT(!i_axi_rvalid);

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
		//
		// AXI write address channel
		//
		//
		reg	[(F_LGDEPTH-1):0]	f_axi_awstall,
						f_axi_wstall,
						f_axi_arstall;

		initial	f_axi_awstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_awvalid)||(i_axi_awready))
			f_axi_awstall <= 0;
		else if ((f_axi_awr_outstanding >= f_axi_wr_outstanding)
			&&(i_axi_awvalid && !i_axi_wvalid))
			// If we are waiting for the write channel to be valid
			// then don't count stalls
			f_axi_awstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
			f_axi_awstall <= f_axi_awstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_awstall < F_AXI_MAXWAIT);

		//
		// AXI write data channel
		//
		//
		initial	f_axi_wstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_wvalid)||(i_axi_wready))
			f_axi_wstall <= 0;
		else if ((f_axi_wr_outstanding >= f_axi_awr_outstanding)
			&&(!i_axi_awvalid && i_axi_wvalid))
			// If we are waiting for the write address channel
			// to be valid, then don't count stalls
			f_axi_wstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
			f_axi_wstall <= f_axi_wstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_wstall < F_AXI_MAXWAIT);

		//
		// AXI read address channel
		//
		//
		initial	f_axi_arstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_arvalid)||(i_axi_arready))
			f_axi_arstall <= 0;
		else if ((!i_axi_rvalid)||(i_axi_rready))
			f_axi_arstall <= f_axi_arstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_arstall < F_AXI_MAXWAIT);

	end endgenerate

	generate if (F_AXI_MAXRSTALL > 0)
	begin
		reg	[(F_LGDEPTH-1):0]	f_axi_bstall,
						f_axi_rstall;

		// AXI write response channel
		initial	f_axi_bstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_bvalid)||(i_axi_bready))
			f_axi_bstall <= 0;
		else
			f_axi_bstall <= f_axi_bstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_bstall < F_AXI_MAXRSTALL);

		// AXI read response channel
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

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Count outstanding transactions.  With these measures, we count
	// once per any burst.
	//
	//
	////////////////////////////////////////////////////////////////////////
	initial	f_axi_awr_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_outstanding <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
		2'b10: f_axi_awr_outstanding <= f_axi_awr_outstanding + 1'b1;
		2'b01: f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
		default: begin end
	endcase

	initial	f_axi_wr_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_wr_outstanding <= 0;
	else case({ (axi_wr_req), (axi_wr_ack) })
	2'b01: f_axi_wr_outstanding <= f_axi_wr_outstanding - 1'b1;
	2'b10: f_axi_wr_outstanding <= f_axi_wr_outstanding + 1'b1;
	endcase

	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + 1'b1;
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
	if (f_axi_awr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_awvalid);
	always @(posedge i_clk)
	if (f_axi_wr_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_wvalid);
	always @(posedge i_clk)
	if (f_axi_rd_outstanding == { {(F_LGDEPTH-1){1'b1}}, 1'b0} )
		assert(!i_axi_arvalid);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Insist that all responses are returned in less than a maximum delay
	// In this case, we count responses within a burst, rather than entire
	// bursts.
	//
	//
	////////////////////////////////////////////////////////////////////////
	generate if (F_AXI_MAXDELAY > 0)
	begin : CHECK_MAX_DELAY

		reg	[(F_LGDEPTH-1):0]	f_axi_wr_ack_delay,
						f_axi_rd_ack_delay;

		initial	f_axi_rd_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_rvalid)||(f_axi_rd_outstanding==0))
			f_axi_rd_ack_delay <= 0;
		else
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;

		initial	f_axi_wr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(f_axi_wr_outstanding==0))
			f_axi_wr_ack_delay <= 0;
		else if (f_axi_wr_outstanding > 0)
			f_axi_wr_ack_delay <= f_axi_wr_ack_delay + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_ack_delay < F_AXI_MAXDELAY);

		always @(*)
			`SLAVE_ASSERT(f_axi_wr_ack_delay < F_AXI_MAXDELAY);

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
	if (i_axi_bvalid)
	begin
		`SLAVE_ASSERT(f_axi_awr_outstanding > 0);
		`SLAVE_ASSERT(f_axi_wr_outstanding  > 0);
	end

	//
	// AXI read data channel signals
	//
	always @(posedge i_clk)
	if (i_axi_rvalid)
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Optionally disable either read or write channels (or both??)
	//
	//
	////////////////////////////////////////////////////////////////////////

	initial	assert((!F_OPT_WRITE_ONLY)||(!F_OPT_READ_ONLY));

	generate if (F_OPT_WRITE_ONLY)
	begin : NO_READS

		always @(*)
			`SLAVE_ASSUME(i_axi_arvalid == 0);
		always @(*)
			assert(f_axi_rd_outstanding == 0);
		always @(*)
			`SLAVE_ASSERT(i_axi_rvalid == 0);

	end endgenerate

	generate if (F_OPT_READ_ONLY)
	begin : NO_WRITES

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
	always @(posedge i_clk)
	if (!F_OPT_READ_ONLY)
		cover((i_axi_bvalid)&&(i_axi_bready));

	//
	// AXI read response channel
	//
	always @(posedge i_clk)
	if (!F_OPT_WRITE_ONLY)
		cover((i_axi_rvalid)&&(i_axi_rready));

`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
endmodule
