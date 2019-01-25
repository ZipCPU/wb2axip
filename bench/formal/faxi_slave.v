////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxi_slave.v (Formal properties of an AXI slave)
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	This file contains a set of formal properties which can be
//		used to formally verify that a core truly follows the full
//	AXI4 specification.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
module faxi_slave #(
	parameter C_AXI_ID_WIDTH	= 3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width (log wordsize)
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH,
	parameter [0:0] F_OPT_BURSTS    = 1'b1,	// Check burst lengths
	parameter [7:0] F_AXI_MAXBURST	= 8'hff,// Maximum burst length, minus 1
	parameter 	F_LGDEPTH	= 10,
	parameter 	F_LGFIFO	= 3,
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXSTALL = 3,
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXDELAY = 3
	) (
	input	wire			i_clk,	// System clock
	input	wire			i_axi_reset_n,

// AXI write address channel signals
	input	wire			i_axi_awready,//Slave is ready to accept
	// input wire	[C_AXI_ID_WIDTH-1:0]	i_axi_awid,	// Write ID
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
	// input wire [C_AXI_ID_WIDTH-1:0] i_axi_bid,	// Response ID
	input	wire	[1:0]		i_axi_bresp,	// Write response
	input	wire			i_axi_bvalid,  // Write reponse valid
	input	wire			i_axi_bready,  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready,	// Read address ready
	// input wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
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
	// input wire [C_AXI_ID_WIDTH-1:0] i_axi_rid,     // Response ID
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input	wire	[DW-1:0]	i_axi_rdata,    // Read data
	input	wire			i_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_rd_outstanding,
	output	reg	[F_LGDEPTH-1:0]		f_axi_wr_nbursts,
	output	reg	[F_LGDEPTH-1:0]		f_axi_awr_outstanding,
	output	reg	[F_LGDEPTH-1:0]		f_axi_awr_nbursts,
		// Address writes without write valids
	//
	// output	reg	[(9-1):0]	f_axi_wr_pending,
	// 
	// RD_COUNT: increment on read w/o last, cleared on read w/ last
	output	reg	[(9-1):0]		f_axi_rd_count,
	output	reg	[(72-1):0]	f_axi_rdfifo
);
	reg	[(9-1):0]	f_axi_wr_count;

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	LG_AXI_DW	= ( C_AXI_DATA_WIDTH ==   8) ? 3
					: ((C_AXI_DATA_WIDTH ==  16) ? 4
					: ((C_AXI_DATA_WIDTH ==  32) ? 5
					: ((C_AXI_DATA_WIDTH ==  64) ? 6
					: ((C_AXI_DATA_WIDTH == 128) ? 7
					: 8))));

	localparam	LG_WB_DW	= ( DW ==   8) ? 3
					: ((DW ==  16) ? 4
					: ((DW ==  32) ? 5
					: ((DW ==  64) ? 6
					: ((DW == 128) ? 7
					: 8))));
	localparam	LGFIFOLN = C_AXI_ID_WIDTH;
	localparam	FIFOLN = (1<<LGFIFOLN);
	localparam	F_AXI_MAXWAIT = F_AXI_MAXSTALL;


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

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert

	//
	// Setup
	//
	reg	f_past_valid;
	integer	k;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
	if (!f_past_valid)
		assume(!i_axi_reset_n);
// WAS AN ASSERT

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Reset properties
	//
	//
	////////////////////////////////////////////////////////////////////////
	localparam [0:0]	F_OPT_ASSUME_RESET = 1'b1;
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
	reg	[3:0]	f_reset_length;
	initial	f_reset_length = 0;
	always @(posedge i_clk)
	if (i_axi_reset_n)
		f_reset_length <= 0;
	else if (!(&f_reset_length))
		f_reset_length <= f_reset_length + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
		`SLAVE_ASSUME(!i_axi_reset_n);

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
	// Stability properties--what happens if valid and not ready
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
			`SLAVE_ASSUME(i_axi_awaddr  == $past(i_axi_awaddr));
			// `SLAVE_ASSUME($stable(i_axi_awid));
			`SLAVE_ASSUME($stable(i_axi_awlen));
			`SLAVE_ASSUME($stable(i_axi_awsize));
			`SLAVE_ASSUME($stable(i_axi_awburst));
			`SLAVE_ASSUME($stable(i_axi_awlock));
			`SLAVE_ASSUME($stable(i_axi_awcache));
			`SLAVE_ASSUME($stable(i_axi_awprot));
			`SLAVE_ASSUME($stable(i_axi_awqos));
		end

		// Write data channel
		if ((f_past_valid)&&($past(i_axi_wvalid))&&(!$past(i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME($stable(i_axi_wstrb));
			`SLAVE_ASSUME($stable(i_axi_wdata));
			`SLAVE_ASSUME($stable(i_axi_wlast));
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid))&&(!$past(i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			// `SLAVE_ASSUME($stable(i_axi_arid));
			`SLAVE_ASSUME($stable(i_axi_araddr));
			`SLAVE_ASSUME($stable(i_axi_arlen));
			`SLAVE_ASSUME($stable(i_axi_arsize));
			`SLAVE_ASSUME($stable(i_axi_arburst));
			`SLAVE_ASSUME($stable(i_axi_arlock));
			`SLAVE_ASSUME($stable(i_axi_arcache));
			`SLAVE_ASSUME($stable(i_axi_arprot));
			`SLAVE_ASSUME($stable(i_axi_arqos));
		end

		// Assume any response from the bus will not change prior to that
		// response being accepted
		if ((f_past_valid)&&($past(i_axi_rvalid))&&(!$past(i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			// `SLAVE_ASSERT($stable(i_axi_rid));
			`SLAVE_ASSERT($stable(i_axi_rresp));
			`SLAVE_ASSERT($stable(i_axi_rdata));
			`SLAVE_ASSERT($stable(i_axi_rlast));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid))&&(!$past(i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			/// `SLAVE_ASSERT($stable(i_axi_bid));
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

	generate if (F_AXI_MAXWAIT > 0)
	begin : CHECK_STALL_COUNT
		//
		// AXI write address channel
		//
		//
		reg	[(F_LGDEPTH-1):0]	f_axi_awstall,
						f_axi_wstall,
						f_axi_arstall,
						f_axi_bstall,
						f_axi_rstall;

		initial	f_axi_awstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_awvalid)||(i_axi_awready))
			f_axi_awstall <= 0;
		else if ((!i_axi_bvalid)||(i_axi_bready))
			f_axi_awstall <= f_axi_awstall + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_awstall < F_AXI_MAXWAIT);

		//
		// AXI write data channel
		//
		//
		// AXI explicitly allows write bursts with zero strobes.  This is part
		// of how a transaction is aborted (if at all).

		initial	f_axi_wstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_wvalid)||(i_axi_wready))
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

		// AXI write response channel
		initial	f_axi_bstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_bvalid)||(i_axi_bready))
			f_axi_bstall <= 0;
		else
			f_axi_bstall <= f_axi_bstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_bstall < F_AXI_MAXWAIT);

		// AXI read response channel
		initial	f_axi_rstall = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(!i_axi_rvalid)||(i_axi_rready))
			f_axi_rstall <= 0;
		else
			f_axi_rstall <= f_axi_rstall + 1'b1;

		always @(*)
			`SLAVE_ASSUME(f_axi_rstall < F_AXI_MAXWAIT);

	end endgenerate


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
	else case({ (axi_awr_req), (axi_wr_req) })
		2'b10: f_axi_awr_outstanding <= f_axi_awr_outstanding + i_axi_awlen-1;
		2'b01: f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
		2'b11: f_axi_awr_outstanding <= f_axi_awr_outstanding + i_axi_awlen; // +1 -1
		default: begin end
	endcase

	initial	f_axi_awr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_awr_nbursts <= 0;
	else case({ (axi_awr_req), (axi_wr_ack) })
	2'b10: f_axi_awr_nbursts <= f_axi_awr_nbursts + 1'b1;
	2'b01: f_axi_awr_nbursts <= f_axi_awr_nbursts - 1'b1;
	default: begin end
	endcase

	initial	f_axi_wr_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_wr_nbursts <= 0;
	else case({ (axi_wr_req)&&(i_axi_wlast), (axi_wr_ack) })
	2'b01: f_axi_wr_nbursts <= f_axi_wr_nbursts - 1'b1;
	2'b10: f_axi_wr_nbursts <= f_axi_wr_nbursts + 1'b1;
	default: begin end
	endcase

	initial	f_axi_rd_nbursts = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_nbursts <= 0;
	else case({ (axi_ard_req), (axi_rd_ack)&&(i_axi_rlast) })
	2'b01: f_axi_rd_nbursts <= f_axi_rd_nbursts - 1'b1;
	2'b10: f_axi_rd_nbursts <= f_axi_rd_nbursts + 1'b1;
	endcase

	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_outstanding <= 0;
	else case({ (axi_ard_req), (axi_rd_ack) })
	2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
	2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen+1;
	2'b11: f_axi_rd_outstanding <= f_axi_rd_outstanding + i_axi_arlen;
	endcase

	// Do not let the number of outstanding requests overflow
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_outstanding < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_nbursts < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_wr_nbursts  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_nbursts  < {(F_LGDEPTH){1'b1}});

	// Cannot have outstanding values if there aren't any outstanding
	// bursts
	always @(posedge i_clk)
	if (f_axi_awr_outstanding > 0)
		`SLAVE_ASSERT(f_axi_awr_nbursts > 0);
	// else if (f_axi_awr_outstanding == 0)
	//	Doesn't apply.  Might have awr_outstanding == 0 and
	//	awr_nbursts>0
	always @(posedge i_clk)
	if (f_axi_rd_outstanding > 0)
		`SLAVE_ASSERT(f_axi_rd_nbursts > 0);
	else
		`SLAVE_ASSERT(f_axi_rd_nbursts == 0);
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_nbursts <= f_axi_rd_outstanding);

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

		reg	[(C_AXI_ID_WIDTH):0]	f_axi_wr_ack_delay,
						f_axi_awr_ack_delay,
						f_axi_rd_ack_delay;

		initial	f_axi_rd_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_rvalid)||(f_axi_rd_outstanding==0))
			f_axi_rd_ack_delay <= 0;
		else
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;

		initial	f_axi_wr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||((i_axi_wvalid)&&(!i_axi_wlast))
				||(i_axi_bvalid)||(f_axi_awr_outstanding==0))
			f_axi_wr_ack_delay <= 0;
		else
			f_axi_wr_ack_delay <= f_axi_wr_ack_delay + 1'b1;

		initial	f_axi_awr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(i_axi_wvalid)
					||(f_axi_awr_nbursts == 0)
					||(f_axi_wr_nbursts == 0))
			f_axi_awr_ack_delay <= 0;
		else
			f_axi_awr_ack_delay <= f_axi_awr_ack_delay + 1'b1;

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_ack_delay < F_AXI_MAXDELAY);

		always @(*)
			`SLAVE_ASSERT(f_axi_wr_ack_delay < F_AXI_MAXDELAY);

		always @(posedge i_clk)
			`SLAVE_ASSERT(f_axi_awr_ack_delay < F_AXI_MAXDELAY);
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
	always @(posedge i_clk)
	if (i_axi_bvalid)
	begin
		`SLAVE_ASSERT(f_axi_awr_nbursts > 0);
		`SLAVE_ASSERT(f_axi_wr_nbursts > 0);
	end

	//
	// AXI read data channel signals
	//
	always @(posedge i_clk)
	if (i_axi_rvalid)
	begin
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);
		`SLAVE_ASSERT(f_axi_rd_nbursts > 0);
		if (!i_axi_rlast)
			`SLAVE_ASSERT(f_axi_rd_outstanding > 1);
	end

	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	////////////////////////////////////////////////////////////////////////

	generate if (!F_OPT_BURSTS)
	begin

		always @(posedge i_clk)
		if (i_axi_awvalid)
			`SLAVE_ASSUME(i_axi_awlen == 0);

		always @(posedge i_clk)
		if (i_axi_wvalid)
			`SLAVE_ASSUME(i_axi_wlast);

		always @(posedge i_clk)
		if (i_axi_arvalid)
			`SLAVE_ASSUME(i_axi_arlen == 0);

		always @(*)
			`SLAVE_ASSERT(f_axi_rd_nbursts == f_axi_rd_outstanding);
	end endgenerate

	reg	[7:0]	wrfifo	[0:((1<<F_LGDEPTH)-1)];
	reg	[7:0]	rdfifo	[0:((1<<F_LGDEPTH)-1)];
	reg	[F_LGDEPTH-1:0]	rd_rdaddr, wr_rdaddr, rd_wraddr, wr_wraddr;
	reg	[7:0]	rdfifo_data, wrfifo_data;
	reg	[F_LGDEPTH-1:0]	rdfifo_outstanding;
	wire	[7:0]		this_wlen;
	wire	[F_LGDEPTH-1:0]	wrfifo_fill, rdfifo_fill;

	/*
	always @(posedge i_clk)
	if (!i_axi_reset_n)
	begin
		f_axi_wburst_fifo <= 0;
	end else case({ axi_awr_req , axi_wr_req, i_axi_wrlast })
		3'b010:
			f_axi_wburst_fifo[7:0] <= f_axi_wburst_fifo[7:0]-1;
		3'b011: begin
			`SLAVE_ASSUME(f_axi_wburst_fifo[7:0] == 0);
			f_axi_wburst_fifo <= { 8'h0, f_axi_wburst_fifo[63:8] };
			end
		3'b100:
			`SLAVE_ASSUME(f_axi_awr_nbursts < 8);
			f_axi_wburst_fifo <= f_axi_wburst_fifo
				| ((i_axi_awlen)<<(f_axi_awr_nbursts * 8));
		3'b11:
			f_axi_wburst_fifo <= { 8'h0, f_axi_wburst_fifo[63:8] }
				| ((i_axi_awlen)<<((f_axi_awr_nbursts-1) * 8));
		default:
	endcase
	*/

       //
       // Count the number of write elements received since the last wlast
	initial	f_axi_wr_count = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_wr_count <= 0;
	else if (axi_wr_req)
	begin
		if (i_axi_wlast)
			f_axi_wr_count <= 1'b0;
		else
			f_axi_wr_count <= f_axi_wr_count + 1'b1;
	end

	//
	// Write information to the write FIFO
	initial	wr_wraddr = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		wr_wraddr <= 0;
	else if (axi_awr_req)
		wr_wraddr <= wr_wraddr + 1'b1;

	always @(posedge i_clk)
	if (axi_awr_req)
		wrfifo[wr_wraddr] <= { i_axi_awlen };

	//
	// Read information from the write queue
	always @(*)
		wrfifo_data = wrfifo[wr_rdaddr];

	assign	this_wlen = wrfifo_data;

	always @(*)
	if ((i_axi_wvalid)&&(i_axi_wlast)&&(f_axi_awr_nbursts>0))
		`SLAVE_ASSUME(i_axi_wlast == (this_wlen == f_axi_wr_count));

	// Advance the read pointer for the write FIFO
	initial	wr_rdaddr = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		wr_rdaddr <= 0;
	else if ((axi_wr_req)&&(i_axi_wlast))
		wr_rdaddr <= wr_rdaddr + 1'b1;

	assign	wrfifo_fill = wr_wraddr - wr_rdaddr;

	////////////////////////////////////////////////////////////////////////
	//
	// Read FIFO
	//
	parameter	NRDFIFO = 8;
	parameter	WRDFIFO = 9;


	initial	f_axi_rd_count = 0;
	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rd_count <= 0;
	else if (axi_rd_ack)
	begin
		if (i_axi_rlast)
			f_axi_rd_count <= 1'b0;
		else
			f_axi_rd_count <= f_axi_rd_count + 1'b1;
	end

	always @(*)
		`SLAVE_ASSUME(f_axi_rd_nbursts <= NRDFIFO);

/*
	always @(*)
	if (i_axi_rvalid)
	begin
		if (i_axi_rlast)
			`SLAVE_ASSERT(f_axi_rdfifo[WRDFIFO-1:0] == f_axi_rd_count);
		else
			`SLAVE_ASSERT(f_axi_rdfifo[WRDFIFO-1:0] < f_axi_rd_count);
	end

	always @(posedge i_clk)
	if (!i_axi_reset_n)
		f_axi_rdfifo <= 0;
	else casez({ axi_ard_req, axi_rd_ack, i_axi_rlast })
	3'b10?:	f_axi_rdfifo[ f_axi_rd_nbursts*WRDFIFO +: WRDFIFO]
						<= { 1'b0, i_axi_arlen };
	// 3'b010:	f_axi_rdfifo[ 8:0] <= f_axi_rdfifo[8:0] - 1'b1;
	3'b011:	f_axi_rdfifo <= { {(WRDFIFO){1'b0}},
				f_axi_rdfifo[NRDFIFO*WRDFIFO-1:WRDFIFO] };
	3'b111: begin
		f_axi_rdfifo <= { {(WRDFIFO){1'b0}},
				f_axi_rdfifo[NRDFIFO*WRDFIFO-1:WRDFIFO] };
		f_axi_rdfifo[ (f_axi_rd_nbursts-1)*WRDFIFO +: WRDFIFO]
				<= { 1'b0, i_axi_arlen };
		end
	default: begin end
	endcase

	always @(*)
	if (f_axi_rd_nbursts < NRDFIFO)
		assert(f_axi_rdfifo[NRDFIFO * WRDFIFO-1: f_axi_rd_nbursts*WRDFIFO] == 0);

	always @(*)
	begin
		rdfifo_outstanding = 0;
		for(k = 0; k < NRDFIFO; k=k+1)
		begin
			if (k < f_axi_rd_nbursts)
			begin
			rdfifo_outstanding = rdfifo_outstanding
				+ f_axi_rdfifo[k * WRDFIFO +: WRDFIFO] + 1;
			end
			assert(f_axi_rdfifo[k*WRDFIFO+(WRDFIFO-1)] == 1'b0);
		end
	end

	always @(posedge i_clk)
		assert(rdfifo_outstanding - f_axi_rd_count
					== f_axi_rd_outstanding);
*/

	always @(*)
		f_axi_rdfifo = 0;
endmodule
