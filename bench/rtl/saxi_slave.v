////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	saxi_slave.v (Simulation properties of an AXI4 (full) slave)
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This file contains a set of SVA properties designed to help
//		verify whether or not an AXI4 core complies with the
//	specification within a given simulation.  As written, the properties are
//	not designed for formal verification and may (or may not) work in a
//	formal context.
//
//	My intent is to base a set of formal properties, useful for verifying
//	a design using induction, off of these properties.
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
module saxi_slave #(
		// {{{
		// AXI ID width
		parameter C_AXI_ID_WIDTH	= 3,
		// Data width
		parameter C_AXI_DATA_WIDTH	= 128,
		parameter C_AXI_ADDR_WIDTH	= 28,
		// OPT_MAXBURST - Maximum burst length, minus 1
		parameter [7:0] OPT_MAXBURST	= 8'hff,
		// Exclusive access allowed
		parameter [0:0] OPT_EXCLUSIVE	= 1,
		// User design uses async resets -- not the default
		parameter [0:0]	OPT_ASYNC_RESET  = 0,
		// F_OPT_ASSUME_RESET, if set, will cause the design to
		// *assume* the existence of a correct reset, rather than
		// asserting it.  (No difference under simulation.)  It is
		// appropriate anytime the reset logic is outside of the
		/// circuit being examined
		parameter [0:0]			F_OPT_ASSUME_RESET = 1'b1,
		// F_OPT_RESET_WIDTH -- insist on a minimum reset width.
		// (Xilinx recommends a minimum width of 16 clocks.  The
		// AXI specification isn't that specific.)
		parameter [0:0]			F_OPT_RESET_WIDTH = 1'b1,
		// F_LGDEPTH is the number of bits necessary to count the
		// maximum number of items in flight.
		parameter				F_LGDEPTH      = 10,
		// MAXSTALL -- the maximum number of stall cycles the slave can
		// make the master wait.
		parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXSTALL = 3,
		// MAXRSTALL (reverse stall) -- the maximum number of stall
		// cycles the master can make the slave wait
		parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXRSTALL= 3,
		// MAXDELAY -- maximum number of clock cycles to wait for an
		// accepted packet to be returned.
		parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXDELAY = 3,
		// F_OPT_BURSTS -- true if the maximum burst length is longer
		// than a single beat
		localparam	[0:0]	F_OPT_BURSTS    = (OPT_MAXBURST != 0),
		// IW, DW, AW, and NUM_IDS are just short-hand notations
		localparam IW			= C_AXI_ID_WIDTH,
		localparam DW			= C_AXI_DATA_WIDTH,
		localparam AW			= C_AXI_ADDR_WIDTH,
		localparam NUM_IDS		= (1<<C_AXI_ID_WIDTH)
	// }}}
	) (
		// {{{
		input	wire			i_clk,	// System clock
		input	wire			i_axi_aresetn,

		// AXI write address channel signals
		// {{{
		input	wire			i_axi_awvalid,
		input	wire			i_axi_awready,
		input	wire	[IW-1:0]	i_axi_awid,
		input	wire	[AW-1:0]	i_axi_awaddr,
		input	wire	[7:0]		i_axi_awlen,
		input	wire	[2:0]		i_axi_awsize,
		input	wire	[1:0]		i_axi_awburst,
		input	wire			i_axi_awlock,
		input	wire	[3:0]		i_axi_awcache,
		input	wire	[2:0]		i_axi_awprot,
		input	wire	[3:0]		i_axi_awqos,
		// }}}
		// AXI write data channel signals
		// {{{
		input	wire			i_axi_wvalid,
		input	wire			i_axi_wready, 
		input	wire	[DW-1:0]	i_axi_wdata,
		input	wire	[DW/8-1:0]	i_axi_wstrb,
		input	wire			i_axi_wlast,
		// }}}
		// AXI write response channel signals
		// {{{
		input	wire			i_axi_bvalid,
		input	wire			i_axi_bready, 
		input	wire	[IW-1:0]	i_axi_bid,
		input	wire	[1:0]		i_axi_bresp,
		// }}}
		// AXI read address channel signals
		// {{{
		input	wire			i_axi_arvalid,
		input	wire			i_axi_arready,
		input	wire	[IW-1:0]	i_axi_arid,
		input	wire	[AW-1:0]	i_axi_araddr,
		input	wire	[7:0]		i_axi_arlen,
		input	wire	[2:0]		i_axi_arsize,
		input	wire	[1:0]		i_axi_arburst,
		input	wire	[0:0]		i_axi_arlock,
		input	wire	[3:0]		i_axi_arcache,
		input	wire	[2:0]		i_axi_arprot,
		input	wire	[3:0]		i_axi_arqos,
		// }}}
		// AXI read data channel signals
		// {{{
		input	wire			i_axi_rvalid,
		input	wire			i_axi_rready,
		input wire [C_AXI_ID_WIDTH-1:0] i_axi_rid,
		input	wire	[DW-1:0]	i_axi_rdata,
		input	wire			i_axi_rlast,
		input	wire	[1:0]		i_axi_rresp
		// }}}
	//  }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Parameter declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam [1:0]	EXOKAY = 2'b01;
	localparam		F_AXI_MAXWAIT = F_AXI_MAXSTALL;

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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal register and wire declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
	reg	[F_LGDEPTH-1:0]		f_axi_awr_nbursts;
	reg	[9-1:0]			f_axi_wr_pending;
	reg	[F_LGDEPTH-1:0]		f_axi_rd_nbursts;
	reg	[F_LGDEPTH-1:0]		f_axi_rd_outstanding;
	//
	reg				awfifo_read;
	wire				awfifo_full, awfifo_empty;
	wire	[F_LGDEPTH:0]		awfifo_fill;
	wire [C_AXI_ID_WIDTH-1:0]	awfifo_id;
	wire [C_AXI_ADDR_WIDTH-1:0]	awfifo_addr;
	wire	[7:0]			awfifo_len;
	wire	[1:0]			awfifo_burst;
	wire	[2:0]			awfifo_size;
	wire				awfifo_lock;
	wire	[3:0]			awfifo_cache;
	wire	[2:0]			awfifo_prot;
	wire	[3:0]			awfifo_qos;

	reg	[C_AXI_ID_WIDTH-1:0]	f_axi_wr_this_id;
	reg	[C_AXI_ADDR_WIDTH-1:0]	f_axi_wr_this_addr;
	reg	[7:0]			f_axi_wr_this_len;
	reg	[1:0]			f_axi_wr_this_burst;
	reg	[2:0]			f_axi_wr_this_size;
	reg				f_axi_wr_this_lock;
	reg	[3:0]			f_axi_wr_this_cache;
	reg	[2:0]			f_axi_wr_this_prot;
	reg	[3:0]			f_axi_wr_this_qos;

	reg	[C_AXI_ID_WIDTH-1:0]	r_axi_wr_id;
	reg	[C_AXI_ADDR_WIDTH-1:0]	r_axi_wr_addr;
	reg	[7:0]			r_axi_wr_len;
	reg	[1:0]			r_axi_wr_burst;
	reg	[2:0]			r_axi_wr_size;
	reg				r_axi_wr_lock;
	reg	[3:0]			r_axi_wr_cache;
	reg	[2:0]			r_axi_wr_prot;
	reg	[3:0]			r_axi_wr_qos;
	wire	[C_AXI_ADDR_WIDTH-1:0]	next_write_addr;
	wire	[7:0]			f_axi_wr_this_incr;

	reg	[8:0]			r_wr_pending;

	reg				wfifo_read;
	wire				wfifo_full, wfifo_empty;
	wire	[F_LGDEPTH:0]		wfifo_fill;
	wire	[C_AXI_DATA_WIDTH-1:0]	wfifo_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wfifo_strb;
	wire 				wfifo_last;
	wire				valid_iwaddr, // Incoming write address
					valid_iraddr;
	reg				f_past_valid;
	reg				awr_aligned,
					ard_aligned;
	wire	[AW-1:0]		next_rd_addr;

	reg				wstb_valid;

	genvar	gk;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pre-setup
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Within the slave core, we will *assume* properties from the master,
	// and *assert* properties of signals coming from the slave and
	// returning to the master.  This order will be reversed within the
	// master, and the following two definitions help us do that.
`define	ASSUME		assume
`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	// f_past_valid
	// {{{
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Insist that the reset signal start out asserted (negative), and
	// remain so for 16 clocks.
	//

	// The reset should be active initially
	// {{{
	generate if (F_OPT_ASSUME_RESET)
	begin : ASSUME_INITIAL_RESET

		`ASSUME property (@(posedge i_clk)
			!f_past_valid |-> !i_axi_aresetn);

	end else begin : ASSERT_INITIAL_RESET

		assert property (@(posedge i_clk)
			!f_past_valid |-> !i_axi_aresetn);

	end endgenerate
	// }}}

	// If !F_OPT_NO_RESET, insist on a minimum 16-clock reset
	// {{{
	generate if (F_OPT_ASSUME_RESET && F_OPT_RESET_WIDTH > 1)
	begin
		`ASSUME property (@(posedge i_clk)
			(!f_past_valid || $fell(i_axi_aresetn))
				|-> !i_axi_aresetn [*F_OPT_RESET_WIDTH]);

	end else if (F_OPT_RESET_WIDTH > 1)
	begin

		`SLAVE_ASSUME property (@(posedge i_clk)
			(!f_past_valid || $fell(i_axi_aresetn))
				|-> !i_axi_aresetn [*F_OPT_RESET_WIDTH]);

	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clear everything on a reset
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	`SLAVE_ASSUME property (@(posedge i_clk)
		!i_axi_aresetn |=> !i_axi_awvalid && !i_axi_wvalid
				&& !i_axi_arvalid);

	`SLAVE_ASSERT property (@(posedge i_clk)
		!i_axi_aresetn |=> !i_axi_bvalid && !i_axi_rvalid);

	generate if (OPT_ASYNC_RESET)
	begin : ASYNC_RESET_CHECKING
		// {{{
		property ASYNC_CLEAR_REQUEST_ON_RESET;
			@(posedge i_clk)
			!i_axi_aresetn |-> !i_axi_awvalid && !i_axi_wvalid
					&& !i_axi_arvalid;
		endproperty

		property ASYNC_CLEAR_RETURN_ON_RESET;
			@(posedge i_clk)
			!i_axi_aresetn |-> !i_axi_bvalid && !i_axi_rvalid;
		endproperty

		`SLAVE_ASSUME property(ASYNC_CLEAR_REQUEST_ON_RESET);
		`SLAVE_ASSERT property(ASYNC_CLEAR_RETURN_ON_RESET);
		// }}}
	end endgenerate
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

	// Write address channel
	// {{{
	property STABLE_AW;
		@(posedge i_clk)
		i_axi_aresetn && i_axi_awvalid && !i_axi_awready
		##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
		|-> i_axi_awvalid
			&& $stable({ i_axi_awid, i_axi_awaddr, i_axi_awlen,
				i_axi_awsize, i_axi_awburst, i_axi_awlock,
				i_axi_awcache, i_axi_awprot, i_axi_awqos });
	endproperty
	// }}}

	// Write data channel
	// {{{
	property STABLE_W;
		@(posedge i_clk)
		i_axi_aresetn && i_axi_wvalid && !i_axi_wready
		##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
		|-> i_axi_wvalid
			&& $stable({ i_axi_wdata, i_axi_wstrb, i_axi_wlast });
	endproperty
	// }}}

	// Write return channel
	// {{{
	property STABLE_B;
		@(posedge i_clk)
		i_axi_aresetn && i_axi_bvalid && !i_axi_bready
		##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
		|-> i_axi_bvalid
			&& $stable({ i_axi_bid, i_axi_bresp });
	endproperty
	// }}}

	// Read address channel
	// {{{
	property STABLE_AR;
		@(posedge i_clk)
		i_axi_aresetn && i_axi_arvalid && !i_axi_arready
		##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
		|-> i_axi_arvalid
			&& $stable({ i_axi_arid, i_axi_araddr, i_axi_arlen,
				i_axi_arsize, i_axi_arburst, i_axi_arlock,
				i_axi_arcache, i_axi_arprot, i_axi_arqos });
	endproperty
	// }}}

	// Read return channel
	// {{{
	property STABLE_R;
		@(posedge i_clk)
		i_axi_aresetn && i_axi_rvalid && !i_axi_rready
		##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
		|-> i_axi_rvalid
			&& $stable({ i_axi_rid, i_axi_rdata, i_axi_rlast,
				i_axi_rresp });
	endproperty
	// }}}

	`SLAVE_ASSUME property(STABLE_AW);
	`SLAVE_ASSUME property(STABLE_W);
	`SLAVE_ASSUME property(STABLE_AR);

	`SLAVE_ASSERT property(STABLE_B);
	`SLAVE_ASSERT property(STABLE_R);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Insist upon a maximum number of stalls before a request is accepted
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (F_AXI_MAXWAIT > 0)
	begin : CHECK_STALL_COUNT

		// AXI write address channel
		// {{{
		// Insist that AW channel can stall no more than F_AXI_MAXWAIT
		// cycles before AWREADY is raised.  However, if
		// BVALID && !BREADY, then the slave  has a reason why it might
		// not want to accepting any more transactions.  Similarly,
		// many cores will only ever accept one request at a time,
		// hence we won't count things as stalls if we are still
		// waiting on write data--that's handled in another assertion
		// below.

		property MAX_AW_STALLS;
			@(posedge i_clk)
			disable iff (!i_axi_aresetn || f_axi_wr_pending > 0)
			i_axi_awvalid && !i_axi_awready [*F_AXI_MAXWAIT]
			|=> i_axi_awready;
		endproperty

		`SLAVE_ASSERT property(MAX_AW_STALLS);
		// }}}

		// AXI write data channel
		// {{{
		// Insist that the write data channel be stalled  no more than
		// F_AXI_MAXWAIT cycles.  Since things can back up if
		// BVALID & !BREADY, we avoid counting clock cycles in that
		// circumstance

		property MAX_WREADY_STALLS;
			@(posedge i_clk)
			disable iff (!i_axi_aresetn || f_axi_wr_pending == 0
					|| (i_axi_bvalid && !i_axi_bready))
			i_axi_wvalid && !i_axi_wready [*F_AXI_MAXWAIT]
			|=> i_axi_wready;
		endproperty

		`SLAVE_ASSERT property(MAX_WREADY_STALLS);
		// }}}

		// AXI read address channel
		// {{{
		// Similar to the first two above, once the master raises
		// ARVALID, insist that the slave accept the read address
		// request within a minimum number of clock cycles.
		// Exceptions include any time RVALID is true, since that can
		// back up the whole system, and any time the number of bursts
		// is greater than zero, since many slaves can only accept one
		// request at a time.

		property MAX_AR_STALLS;
			@(posedge i_clk)
			disable iff (!i_axi_aresetn || f_axi_rd_nbursts > 0)
			i_axi_arvalid && !i_axi_arready [*F_AXI_MAXWAIT]
			|=> i_axi_arready;
		endproperty

		`SLAVE_ASSERT property(MAX_AR_STALLS);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Insist upon a maximum delay before any response is accepted
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Note that this is a *response* channel property, so it is separate
	// from the earlier properties in case you wish to control it
	// separately.  For example, an interconnect might be forced to let a
	// channel wait indefinitely for access, but it might not be
	// appropriate to require the response to be able to wait indefinitely
	// as well.  So, here we check the response time.
	//
	//

	generate if (F_AXI_MAXRSTALL > 0)
	begin : CHECK_RESPONSE_STALLS
		// AXI write channel valid
		// {{{
		// The first master stall check: guarantee that the master
		// provides the required write data in fairly short order,
		// and without much delay.  That is, once AWVALID && AWREADY
		// are true, the slave needs to provide the W* values.
		// This is the only "forward" property check among our response
		// channel checks, since it's a master and not a slave property.

		property MAX_WDATA_STALLS;
			@(posedge i_clk)
			i_axi_aresetn
			&& (!i_axi_bvalid || i_axi_bready)
			&& (f_axi_wr_pending > 0)
			&& (!i_axi_wvalid) [*F_AXI_MAXRSTALL]
			|=> i_axi_wvalid;
		endproperty

		`SLAVE_ASSUME property(MAX_WDATA_STALLS);
		// }}}

		// AXI write response channel
		// {{{
		// Insist on a maximum number of clocks that BVALID can be
		// high while BREADY is low
		property MAX_B_STALLS;
			@(posedge i_clk)
			i_axi_bvalid && !i_axi_bready [*F_AXI_MAXRSTALL]
			|=> i_axi_bready;
		endproperty

		`SLAVE_ASSUME property(MAX_B_STALLS);
		// /}}}

		// AXI read response channel
		// {{{
		// Insist on a maximum number of clocks that RVALID can be
		// high while RREADY is low
		property MAX_R_STALLS;
			@(posedge i_clk)
			i_axi_rvalid && !i_axi_rready [*F_AXI_MAXRSTALL]
			|=> i_axi_rready;
		endproperty

		`SLAVE_ASSUME property(MAX_R_STALLS);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write property checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Validate the incoming address channel packet
	// {{{
	faxi_valaddr #(.C_AXI_DATA_WIDTH(DW), .C_AXI_ADDR_WIDTH(AW),
			.OPT_MAXBURST(OPT_MAXBURST),
			.OPT_EXCLUSIVE(OPT_EXCLUSIVE),
			.OPT_NARROW_BURST(1'b1))
		f_wraddr_validate(i_axi_awaddr, i_axi_awlen, i_axi_awsize,
			i_axi_awburst, i_axi_awlock,
			1'b1, awr_aligned, valid_iwaddr);

	`SLAVE_ASSUME property (@(posedge i_clk)
		i_axi_awvalid |-> valid_iwaddr);
	// }}}

	// Write address request FIFO
	// {{{
	// Queue write address requests so we can process them one packet
	// at a time.
	sfifo #(
		// {{{
		.BW(C_AXI_ID_WIDTH + C_AXI_ADDR_WIDTH + 8 + 2 + 3+1+4+3+4),
		.LGFLEN(F_LGDEPTH),
		.OPT_ASYNC_READ(1'b0),
		.OPT_WRITE_ON_FULL(1'b1),
		.OPT_READ_ON_EMPTY(1'b1)
		// }}}
	) awrequests (
		// {{{
		.i_clk(i_clk), .i_reset(!i_axi_aresetn),
		.i_wr(i_axi_awvalid && i_axi_awready),
		.i_data({ i_axi_awid, i_axi_awaddr, i_axi_awlen,
			i_axi_awburst, i_axi_awsize, i_axi_awlock,
			i_axi_awcache, i_axi_awprot, i_axi_awqos }),
		.o_full(awfifo_full), .o_fill(awfifo_fill),
		.i_rd(awfifo_read),
		.o_data({ awfifo_id, awfifo_addr, awfifo_len,
			awfifo_burst, awfifo_size, awfifo_lock,
			awfifo_cache, awfifo_prot, awfifo_qos }),
		.o_empty(awfifo_empty)
		// }}}
	);

	always @(*)
		awfifo_read = (r_wr_pending == 0);
	// }}}

	// Write data FIFO
	// {{{
	// In AXI, the write data can come before the address.  In such
	// circumstances, you need to hold on to that data in a queue (FIFO)
	// until the address is available so that you can compare the two
	// against each other for validity.
	sfifo #(
		// {{{
		.BW(C_AXI_DATA_WIDTH + (C_AXI_DATA_WIDTH/8) + 1),
		.LGFLEN(F_LGDEPTH),
		.OPT_ASYNC_READ(1'b0),
		.OPT_WRITE_ON_FULL(1'b1),
		.OPT_READ_ON_EMPTY(1'b1)
		// }}}
	) wrequests (
		// {{{
		.i_clk(i_clk), .i_reset(!i_axi_aresetn),
		.i_wr(i_axi_wvalid && i_axi_wready),
		.i_data({ i_axi_wdata, i_axi_wstrb, i_axi_wlast }),
		.o_full(wfifo_full), .o_fill(wfifo_fill),
		.i_rd(wfifo_read),
		.o_data({ wfifo_data, wfifo_strb, wfifo_last }),
		.o_empty(wfifo_empty)
		// }}}
	);

	always @(*)
		wfifo_read = (r_wr_pending > 0)||(awfifo_read && !awfifo_empty);
	// }}}

	// Make sure AWLOCK is low if !OPT_EXCLUSIVE
	// {{{
	generate if (!OPT_EXCLUSIVE)
	begin

		`SLAVE_ASSUME property (@(posedge i_clk)
			(!i_axi_awvalid || !i_axi_awlock));

	end endgenerate
	// }}}

	// Build f_axi_wr_this_*
	// {{{
	always @(*)
	if (r_wr_pending == 0)
	begin
		f_axi_wr_this_id    = awfifo_id;
		f_axi_wr_this_addr  = awfifo_addr;
		f_axi_wr_this_len   = awfifo_len;
		f_axi_wr_this_burst = awfifo_burst;
		f_axi_wr_this_size  = awfifo_size;
		f_axi_wr_this_lock  = awfifo_lock;
		f_axi_wr_this_cache = awfifo_cache;
		f_axi_wr_this_prot  = awfifo_prot;
		f_axi_wr_this_qos   = awfifo_qos;
	end else begin
		f_axi_wr_this_id    = r_axi_wr_id;
		f_axi_wr_this_addr  = r_axi_wr_addr;
		f_axi_wr_this_len   = r_axi_wr_len;
		f_axi_wr_this_burst = r_axi_wr_burst;
		f_axi_wr_this_size  = r_axi_wr_size;
		f_axi_wr_this_lock  = r_axi_wr_lock;
		f_axi_wr_this_cache = r_axi_wr_cache;
		f_axi_wr_this_prot  = r_axi_wr_prot;
		f_axi_wr_this_qos   = r_axi_wr_qos;
	end
	// }}}

	// r_axi_wr_*
	// {{{
	initial	r_wr_pending = 0;
	always @(posedge i_clk)
	begin
		if (awfifo_read && !awfifo_empty)
		begin
			r_axi_wr_id   <= awfifo_id;
			r_axi_wr_addr <= awfifo_addr;
			r_axi_wr_len  <= awfifo_len;
			r_axi_wr_burst<= awfifo_burst;
			r_axi_wr_size <= awfifo_size;
			r_axi_wr_lock <= awfifo_lock;
			r_axi_wr_cache<= awfifo_cache;
			r_axi_wr_prot <= awfifo_prot;
			r_axi_wr_qos  <= awfifo_qos;

			r_wr_pending <= awfifo_len + 1;
			if (wfifo_read && !wfifo_empty)
			begin
				r_axi_wr_addr <= next_write_addr;
				r_wr_pending  <= awfifo_len;
			end
		end else if (wfifo_read && !wfifo_empty)
		begin
			r_axi_wr_addr <= next_write_addr;
			r_wr_pending  <= r_wr_pending - 1;
		end

		if (!i_axi_aresetn)
			r_wr_pending <= 0;
	end
	// }}}

	// f_axi_wr_pending
	// {{{	
	always @(*)
	if (r_wr_pending == 0)
	begin
		f_axi_wr_pending = awfifo_len + 1;
		if (awfifo_empty || !awfifo_read)
			f_axi_wr_pending = 0;
	end else
		f_axi_wr_pending = r_wr_pending;
	// }}}

	// next_write_addr
	// {{{
	faxi_addr #(.AW(AW))
	get_next_write_addr(
		f_axi_wr_this_addr, f_axi_wr_this_size, f_axi_wr_this_burst,
		f_axi_wr_this_len,
		f_axi_wr_this_incr, next_write_addr);
	// }}}

	// Check WSTRB
	// {{{
	faxi_wstrb #(.C_AXI_DATA_WIDTH(DW))
		f_wstrbck (f_axi_wr_this_addr, f_axi_wr_this_size,
				wfifo_strb, wstb_valid);

	// Insist the only the appropriate bits be valid
	// For example, if the lower address bit is one, then the
	// strobe LSB cannot be 1, but must be zero.  This is just
	// enforcing the rules of the sub-address which must match
	// the write strobe.  An STRB of 0 is always allowed.
	//
	always @(*)
	if (!wfifo_empty)
		`SLAVE_ASSUME(wstb_valid);
	// }}}

	// Check WLAST
	`SLAVE_ASSUME property (@(posedge i_clk)
		!wfifo_empty && r_wr_pending > 0
		|-> ((r_wr_pending == 1) == wfifo_last));

	`SLAVE_ASSUME property (@(posedge i_clk)
		!wfifo_empty && r_wr_pending == 0 && !awfifo_empty
		|-> ((awfifo_len == 0) == wfifo_last));

	// Check BID and BRESP
	// {{{
	generate for(gk=0; gk<NUM_IDS; gk=gk+1)
	begin : CHECK_BID
		// {{{

		// Register/net declarations
		// {{{
		wire	[F_LGDEPTH:0]	bid_count;
		reg			block_fifo_write, block_fifo_check,
					block_fifo_read;
		wire			block_possible;
		wire			block_fifo_empty;
		// }}}

		always @(*)
			block_fifo_write = (wfifo_read && !wfifo_empty
				&& wfifo_last && f_axi_wr_this_id == gk);

		always @(*)
			block_fifo_check = (i_axi_bvalid && i_axi_bid == gk);

		always @(*)
			block_fifo_read = block_fifo_check && i_axi_bready;

		if (OPT_EXCLUSIVE)
		begin : EXCLUSIVE_WRITE_RETURN_CHECK
			// {{{
			wire		block_fifo_full;

			sfifo #(
				// {{{
				.BW(1),
				.LGFLEN(F_LGDEPTH),
				.OPT_ASYNC_READ(1'b0),
				.OPT_WRITE_ON_FULL(1'b1),
				.OPT_READ_ON_EMPTY(1'b0)
				// }}}
			) block_fifo (
				// {{{
				.i_clk(i_clk), .i_reset(!i_axi_aresetn),
				.i_wr(block_fifo_write),
				.i_data(f_axi_wr_this_lock),
				.o_full(block_fifo_full), .o_fill(bid_count),
				.i_rd(block_fifo_read),
				.o_data(block_possible),
				.o_empty(block_fifo_empty)
				// }}}
			);

			`SLAVE_ASSERT property (@(posedge i_clk)
				!block_possible
				|-> !block_fifo_check || i_axi_bresp != EXOKAY);
			// }}}
		end else begin : NO_EXCLUSIVE_WRITE_RETURNS
			// {{{
			reg	[F_LGDEPTH-1:0]	r_bid_count;

			initial	r_bid_count = 0;
			always @(posedge i_clk)
			if (!i_axi_aresetn)
				r_bid_count = 0;
			else case ({ block_fifo_write, block_fifo_read })
			2'b10: r_bid_count <= r_bid_count + 1;
			2'b01: r_bid_count <= r_bid_count - 1;
			default: begin end
			endcase

			assign	block_fifo_empty = (r_bid_count == 0);

			`SLAVE_ASSERT property (@(posedge i_clk)
				!block_fifo_check || i_axi_bresp != EXOKAY);
			// }}}
		end

		`SLAVE_ASSUME property (@(posedge i_clk)
			block_fifo_write && !block_fifo_read
			|-> (bid_count != {(F_LGDEPTH){1'b1}}));

		`SLAVE_ASSERT property (@(posedge i_clk)
			block_fifo_check |-> !block_fifo_empty);

		// }}}
	end endgenerate
	// }}}
	
	// f_axi_awr_nbursts
	// {{{
	// Count the number of outstanding BVALID's to expect
	initial	f_axi_awr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_aresetn)
		f_axi_awr_nbursts <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
	2'b10: f_axi_awr_nbursts <= f_axi_awr_nbursts + 1'b1;
	2'b01: f_axi_awr_nbursts <= f_axi_awr_nbursts - 1'b1;
	default: begin end
	endcase
	// }}}

	// f_axi_rd_nbursts
	// {{{
	// Count the number of reads bursts outstanding.  This defines the
	// number of RDVALID && RLAST's we expect to see before becoming idle
	//
	initial	f_axi_rd_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_aresetn)
		f_axi_rd_nbursts <= 0;
	else case({ (axi_ard_req), (axi_rd_ack)&&(i_axi_rlast) })
	2'b01: f_axi_rd_nbursts <= f_axi_rd_nbursts - 1'b1;
	2'b10: f_axi_rd_nbursts <= f_axi_rd_nbursts + 1'b1;
	endcase
	// }}}

	// f_axi_rd_outstanding
	// {{{
	// f_axi_rd_outstanding counts the number of RDVALID's we expect to
	// see before becoming idle.  This must always be greater than or
	// equal to the number of RVALID & RLAST's counted above
	//
	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_aresetn)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen+1;
	2'b11: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen;
	endcase
	// }}}

	//
	// Do not let the number of outstanding requests overflow.
	// {{{
	// This is a responsibility of both the master and the slave to never
	// allow 2^F_LGDEPTH-1 requests (or more) to be outstanding.
	//
	assert property (@(posedge i_clk)
		!i_axi_aresetn || f_axi_awr_nbursts  < {(F_LGDEPTH){1'b1}});
	assert property (@(posedge i_clk)
		!i_axi_aresetn || f_axi_wr_pending  <= 256);
	assert property (@(posedge i_clk)
		!i_axi_aresetn || f_axi_rd_nbursts  < {(F_LGDEPTH){1'b1}});
	assert property (@(posedge i_clk)
		!i_axi_aresetn || f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read property checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (!OPT_EXCLUSIVE)
	begin : NO_EXCLUSIVE_READS

		`SLAVE_ASSUME property (@(posedge i_clk)
			(!i_axi_arvalid || !i_axi_arlock));

		`SLAVE_ASSERT property (@(posedge i_clk)
			(!i_axi_rvalid || i_axi_rresp != EXOKAY));

	end endgenerate

	// Validate the read address packet
	// {{{
	faxi_valaddr #(.C_AXI_DATA_WIDTH(DW), .C_AXI_ADDR_WIDTH(AW),
			.OPT_MAXBURST(OPT_MAXBURST),
			.OPT_EXCLUSIVE(OPT_EXCLUSIVE),
			.OPT_NARROW_BURST(1'b1))
		f_rdaddr_validate(i_axi_araddr, i_axi_arlen,
			i_axi_arsize, i_axi_arburst, i_axi_arlock,
			1'b1, ard_aligned, valid_iraddr);

	`SLAVE_ASSUME property (@(posedge i_clk)
		i_axi_arvalid |-> valid_iraddr);
	// }}}

	// Read return handling must be done on a per-ID basis
	generate for(gk=0; gk<NUM_IDS; gk=gk+1)
	begin : PER_READ_ID_PROCESSING
		// {{{

		// Register/wire declarations
		// {{{
		wire			arfifo_empty, arfifo_full;
		wire	[F_LGDEPTH:0]	arfifo_fill;
		reg			arfifo_write, arfifo_read;

		wire	[C_AXI_ADDR_WIDTH-1:0]	arfifo_addr;
		wire	[7:0]			arfifo_len;
		wire	[1:0]			arfifo_burst;
		wire	[2:0]			arfifo_size;
		wire				arfifo_lock;
		wire	[3:0]			arfifo_cache;
		wire	[2:0]			arfifo_prot;
		wire	[3:0]			arfifo_qos;

		reg	[C_AXI_ADDR_WIDTH-1:0]	f_axi_rd_this_addr;
		reg	[7:0]			f_axi_rd_this_len;
		reg	[1:0]			f_axi_rd_this_burst;
		reg	[2:0]			f_axi_rd_this_size;
		reg				f_axi_rd_this_lock;
		reg	[3:0]			f_axi_rd_this_cache;
		reg	[2:0]			f_axi_rd_this_prot;
		reg	[3:0]			f_axi_rd_this_qos;

		reg	[C_AXI_ID_WIDTH-1:0]	r_axi_rd_id;
		reg	[C_AXI_ADDR_WIDTH-1:0]	r_axi_rd_addr;
		reg	[7:0]			r_axi_rd_len;
		reg	[1:0]			r_axi_rd_burst;
		reg	[2:0]			r_axi_rd_size;
		reg				r_axi_rd_lock;
		reg	[3:0]			r_axi_rd_cache;
		reg	[2:0]			r_axi_rd_prot;
		reg	[3:0]			r_axi_rd_qos;
		wire	[C_AXI_ADDR_WIDTH-1:0]	next_read_addr;
		wire	[7:0]			f_axi_rd_this_incr;
		reg	[8:0]			r_rd_pending;
		// }}}

		// Read address FIFO
		// {{{
		// Record any read address request for comparing against the
		// subsequent response

		// arfifo_write - Write on any address request
		// {{{
		always @(*)
			arfifo_write = i_axi_arvalid && i_axi_arready
				&& i_axi_arid == gk;
		// }}}

		// arfifo_read
		// {{{
		// Read if nothing we know of is pending, or if we just
		// read the last value from the last burst.
		always @(*)
			arfifo_read = (r_rd_pending == 0)
			|| (i_axi_rvalid && i_axi_rready && i_axi_rlast
				&& i_axi_rid == gk);
		// }}}

		sfifo #(
			// {{{
			.BW(C_AXI_ADDR_WIDTH+8+2+3+1+4+3+4),
			.LGFLEN(F_LGDEPTH),
			.OPT_ASYNC_READ(1'b0),
			.OPT_WRITE_ON_FULL(1'b1),
			.OPT_READ_ON_EMPTY(1'b1)
			// }}}
		) arrequests (
			// {{{
			.i_clk(i_clk), .i_reset(!i_axi_aresetn),
			.i_wr(arfifo_write),
			.i_data({ i_axi_araddr, i_axi_arlen,
				i_axi_arburst, i_axi_arsize, i_axi_arlock,
				i_axi_arcache, i_axi_arprot, i_axi_arqos }),
			.o_full(arfifo_full), .o_fill(arfifo_fill),
			.i_rd(arfifo_read),
			.o_data({ arfifo_addr, arfifo_len,
				arfifo_burst, arfifo_size, arfifo_lock,
				arfifo_cache, arfifo_prot, arfifo_qos }),
			.o_empty(arfifo_empty)
			// }}}
		);
		// }}}

		// f_axi_rd_this_*
		// {{{
		// These record the current burst that is being returned by
		// this ID (if any).  The current burst might still be in the
		// FIFO, so this is combinatorial.
		always @(*)
		if (r_rd_pending == 0)
		begin
			f_axi_rd_this_addr  = arfifo_addr;
			f_axi_rd_this_len   = arfifo_len;
			f_axi_rd_this_burst = arfifo_burst;
			f_axi_rd_this_size  = arfifo_size;
			f_axi_rd_this_lock  = arfifo_lock;
			f_axi_rd_this_cache = arfifo_cache;
			f_axi_rd_this_prot  = arfifo_prot;
			f_axi_rd_this_qos   = arfifo_qos;
		end else begin
			f_axi_rd_this_addr  = r_axi_rd_addr;
			f_axi_rd_this_len   = r_axi_rd_len;
			f_axi_rd_this_burst = r_axi_rd_burst;
			f_axi_rd_this_size  = r_axi_rd_size;
			f_axi_rd_this_lock  = r_axi_rd_lock;
			f_axi_rd_this_cache = r_axi_rd_cache;
			f_axi_rd_this_prot  = r_axi_rd_prot;
			f_axi_rd_this_qos   = r_axi_rd_qos;
		end
		// }}}

		// r_axi_rd_*
		// {{{
		// Register the details of the next read burst to be returned.
		// We'll adjust the pending value and the address along the
		// way.  Hence, the address should always point to the address
		// of the next value to be read, and the r_rd_pending to the
		// next item to be read.

		initial	r_rd_pending = 0;
		always @(posedge i_clk)
		if (!i_axi_aresetn)
			r_rd_pending <= 0;
		else if (arfifo_read)
		begin
			r_rd_pending   = arfifo_len + 1;
			if (arfifo_empty)
				r_rd_pending = 0;
		end else if (i_axi_rvalid && i_axi_rready && i_axi_rid == gk
				&& r_rd_pending > 0)
			r_rd_pending = r_rd_pending - 1;

		always @(posedge i_clk)
		if (arfifo_read)
		begin
			r_axi_rd_addr  = arfifo_addr;
			r_axi_rd_len   = arfifo_len;
			r_axi_rd_burst = arfifo_burst;
			r_axi_rd_size  = arfifo_size;
			r_axi_rd_lock  = arfifo_lock;
			r_axi_rd_cache = arfifo_cache;
			r_axi_rd_prot  = arfifo_prot;
			r_axi_rd_qos   = arfifo_qos;
		end else if (i_axi_rvalid && i_axi_rready && i_axi_rid == gk
				&& r_rd_pending > 0)
			r_axi_rd_addr= next_read_addr;
		// }}}

		// next_read_addr
		// {{{
		// Compute the next read address, after the current one, using
		// the current burst values.
		faxi_addr #(.AW(AW))
		get_next_read_addr(
			f_axi_rd_this_addr, f_axi_rd_this_size,
			f_axi_rd_this_burst, f_axi_rd_this_len,
			f_axi_rd_this_incr, next_read_addr);
		// }}}

		`SLAVE_ASSERT property (@(posedge i_clk)
			i_axi_aresetn && i_axi_rvalid && i_axi_rid == gk
			|-> (r_rd_pending > 0));

		`SLAVE_ASSERT property (@(posedge i_clk)
			i_axi_aresetn && i_axi_rvalid && i_axi_rid == gk
			|-> (i_axi_rlast == (r_rd_pending == 1)));

		`SLAVE_ASSERT property (@(posedge i_clk)
			i_axi_aresetn && i_axi_rvalid && i_axi_rid == gk
			&& !f_axi_rd_this_lock |-> i_axi_rresp != EXOKAY);

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Maximum response time delay
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Insist that all responses are returned in less than a maximum delay
	//
	// A unique feature to the backpressure mechanism within AXI is that
	// we have to reset our delay count in the case of any push back, since
	// the response can't move forward if the master isn't (yet) ready for
	// it.
	//

	generate if (F_AXI_MAXDELAY > 0)
	begin : CHECK_MAX_DELAY
		// {{{
		`SLAVE_ASSERT property (@(posedge i_clk)
			i_axi_aresetn && !i_axi_bvalid
			&& f_axi_awr_nbursts > awrfifo_fill
					+ ((f_axi_wr_pending>0) ? 1:0)
			[*F_AXI_MAXDELAY-1]
			##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
			|-> i_axi_bvalid);

		`SLAVE_ASSERT property (@(posedge i_clk)
			i_axi_aresetn && !i_axi_rvalid
			&& (f_axi_rd_outstanding > 0) [*F_AXI_MAXDELAY-1]
			##1 (!OPT_ASYNC_RESET || i_axi_aresetn)
			|-> i_axi_rvalid);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Exclusive properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	generate if (!OPT_EXCLUSIVE)
	begin : EXCLUSIVE_DISALLOWED
		// {{{
		// These properties are captured above
		// }}}
	end else begin : EXCLUSIVE_ACCESS_CHECKER
		// {{{

		//
		// 1. Exclusive access burst lengths max out at 16
		//	(Checked within valaddr)
		// 2. Exclusive access bursts must be aligned
		//	(NOT CHECKED)
		// 3. Write must take place when the read channel is idle (on
		//	this ID) -- (NOT CHECKED)
		// (4. Further read accesses on this ID are not allowed)
		//	(NOT CHECKED)
		//
		`SLAVE_ASSUME property (@(posedge i_clk)
			i_axi_aresetn && i_axi_awvalid && i_axi_awlock
			|-> !i_axi_awcache[0]);

		`SLAVE_ASSUME property (@(posedge i_clk)
			i_axi_aresetn && i_axi_arvalid && i_axi_arlock
			|-> !i_axi_arcache[0]);

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AxCACHE properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Table A4-5 ??
	//

	`SLAVE_ASSUME property (@(posedge i_clk)
		i_axi_awvalid && !i_axi_awcache[1]
		|-> i_axi_awcache[3:2] == 2'b00);

	`SLAVE_ASSUME property (@(posedge i_clk)
		i_axi_arvalid && !i_axi_arcache[1]
		|-> i_axi_arcache[3:2] == 2'b00);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Option for no bursts, only single transactions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (!F_OPT_BURSTS)
	begin

		`SLAVE_ASSUME property(@(posedge i_clk)
			i_axi_awvalid |-> i_axi_awlen == 0);

		`SLAVE_ASSUME property(@(posedge i_clk)
			i_axi_wvalid |-> i_axi_wlast);

		`SLAVE_ASSUME property(@(posedge i_clk)
			i_axi_arvalid |-> i_axi_arlen == 0);

		`SLAVE_ASSERT property(@(posedge i_clk)
			i_axi_rvalid |-> i_axi_rlast);

	end endgenerate
	// }}}
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
endmodule
