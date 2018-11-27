////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxi_master.v (Formal properties of an AXI master)
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
// Copyright (C) 2017, Gisselquist Technology, LLC
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
module faxi_master #(
	parameter C_AXI_ID_WIDTH	= 3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width (log wordsize)
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH,
	parameter [0:0] F_STRICT_ORDER	= 0,	// Reorder, or not? 0 -> Reorder
	parameter [0:0] F_CONSECUTIVE_IDS= 0,	// 0=ID's must be consecutive
	parameter [0:0] F_OPT_BURSTS    = 1'b1,	// Check burst lengths
	parameter [0:0] F_CHECK_IDS	= 1'b1,	// Check ID's upon issue&return
	parameter [7:0] F_AXI_MAXBURST	= 8'hff,// Maximum burst length, minus 1
	parameter [0:0] F_OPT_CLK2FFLOGIC= 1'b0, // Multiple clock testing?
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXSTALL = 3,
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_AXI_MAXDELAY = 3
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
	input	wire [C_AXI_ID_WIDTH-1:0] i_axi_rid,     // Response ID
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input	wire	[DW-1:0]	i_axi_rdata,    // Read data
	input	wire			i_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[(C_AXI_ID_WIDTH-1):0]	f_axi_rd_outstanding,
	output	reg	[(C_AXI_ID_WIDTH-1):0]	f_axi_wr_outstanding,
	output	reg	[(C_AXI_ID_WIDTH-1):0]	f_axi_awr_outstanding,
	output	reg [((1<<C_AXI_ID_WIDTH)-1):0]	f_axi_rd_id_outstanding,
	output	reg [((1<<C_AXI_ID_WIDTH)-1):0]	f_axi_awr_id_outstanding,
	output	reg [((1<<C_AXI_ID_WIDTH)-1):0]	f_axi_wr_id_outstanding,
	// output	reg	[(9-1):0]	f_axi_wr_pending,
	// output	reg	[(9-1):0]	f_axi_rd_count,
	output	reg	[(9-1):0]	f_axi_wr_count
);
	reg [((1<<C_AXI_ID_WIDTH)-1):0]	f_axi_wr_id_complete;

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
	localparam	F_LGDEPTH = C_AXI_ID_WIDTH;
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
	always @(*)
	if (!f_past_valid)
		assert(!i_axi_reset_n);

	//
	// All signals must be synchronous with the clock
	//
	generate if (F_OPT_CLK2FFLOGIC)
	begin

		always @($global_clock)
		if (f_past_valid) begin
			// Assume our inputs will only change on the positive
			// edge of the clock
			if (!$rose(i_clk))
			begin
				// AXI inputs
				assume($stable(i_axi_awready));
				assume($stable(i_axi_wready));
				//
				assume($stable(i_axi_bid));
				assume($stable(i_axi_bresp));
				assume($stable(i_axi_bvalid));
				assume($stable(i_axi_arready));
				//
				assume($stable(i_axi_rid));
				assume($stable(i_axi_rresp));
				assume($stable(i_axi_rvalid));
				assume($stable(i_axi_rdata));
				assume($stable(i_axi_rlast));
				//
				// AXI outputs
				//
				assert($stable(i_axi_awvalid));
				assert($stable(i_axi_awid));
				assert($stable(i_axi_awlen));
				assert($stable(i_axi_awsize));
				assert($stable(i_axi_awlock));
				assert($stable(i_axi_awcache));
				assert($stable(i_axi_awprot));
				assert($stable(i_axi_awqos));
				//
				assert($stable(i_axi_wvalid));
				assert($stable(i_axi_wdata));
				assert($stable(i_axi_wstrb));
				assert($stable(i_axi_wlast));
				//
				assert($stable(i_axi_arvalid));
				assert($stable(i_axi_arid));
				assert($stable(i_axi_arlen));
				assert($stable(i_axi_arsize));
				assert($stable(i_axi_arburst));
				assert($stable(i_axi_arlock));
				assert($stable(i_axi_arprot));
				assert($stable(i_axi_arqos));
				//
				assert($stable(i_axi_bready));
				//
				assert($stable(i_axi_rready));
				//
				// Formal outputs
				//
				assert($stable(f_axi_rd_outstanding));
				assert($stable(f_axi_wr_outstanding));
				assert($stable(f_axi_awr_outstanding));
			end
		end
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

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_axi_reset_n))&&(!$past(&f_reset_length)))
		`SLAVE_ASSUME(!i_axi_reset_n);

	always @(*)
	if ((f_reset_length > 0)&&(f_reset_length < 4'hf))
		`SLAVE_ASSUME(!i_axi_reset_n);

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
		if ((f_past_valid)&&($past(i_axi_wvalid))&&(!$past(i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME(i_axi_wstrb  == $past(i_axi_wstrb));
			`SLAVE_ASSUME(i_axi_wdata  == $past(i_axi_wdata));
			`SLAVE_ASSUME(i_axi_wlast);
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid))&&(!$past(i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			`SLAVE_ASSUME(i_axi_arid == $past(i_axi_arid));
			`SLAVE_ASSUME(i_axi_araddr  == $past(i_axi_araddr));
			`SLAVE_ASSUME(i_axi_arlen   == $past(i_axi_arlen));
			`SLAVE_ASSUME(i_axi_arsize  == $past(i_axi_arsize));
			`SLAVE_ASSUME(i_axi_arburst == $past(i_axi_arburst));
			`SLAVE_ASSUME(i_axi_arlock  == $past(i_axi_arlock));
			`SLAVE_ASSUME(i_axi_arcache == $past(i_axi_arcache));
			`SLAVE_ASSUME(i_axi_arprot  == $past(i_axi_arprot));
			`SLAVE_ASSUME(i_axi_arqos   == $past(i_axi_arqos));
		end

		// Assume any response from the bus will not change prior to that
		// response being accepted
		if ((f_past_valid)&&($past(i_axi_rvalid))&&(!$past(i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			`SLAVE_ASSERT(i_axi_rid    == $past(i_axi_rid));
			`SLAVE_ASSERT(i_axi_rresp  == $past(i_axi_rresp));
			`SLAVE_ASSERT(i_axi_rdata  == $past(i_axi_rdata));
			`SLAVE_ASSERT(i_axi_rlast  == $past(i_axi_rlast));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid))&&(!$past(i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT(i_axi_bid    == $past(i_axi_bid));
			`SLAVE_ASSERT(i_axi_bresp  == $past(i_axi_bresp));
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
		else case({ (axi_awr_req), (axi_wr_ack) })
			2'b10: f_axi_awr_outstanding <= f_axi_awr_outstanding + 1'b1;
			2'b01: f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
			default: begin end
		endcase

	initial	f_axi_wr_outstanding = 0;
	always @(posedge i_clk)
		if (!i_axi_reset_n)
			f_axi_wr_outstanding <= 0;
		else case({ (axi_wr_req)&&(i_axi_wlast), (axi_wr_ack) })
		2'b01: f_axi_wr_outstanding <= f_axi_wr_outstanding - 1'b1;
		2'b10: f_axi_wr_outstanding <= f_axi_wr_outstanding + 1'b1;
		endcase

	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
		if (!i_axi_reset_n)
			f_axi_rd_outstanding <= 0;
		else case({ (axi_ard_req), (axi_rd_ack)&&(i_axi_rlast) })
		2'b01: f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
		2'b10: f_axi_rd_outstanding <= f_axi_rd_outstanding + 1'b1;
		endcase

	// Do not let the number of outstanding requests overflow
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_wr_outstanding  < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_awr_outstanding < {(F_LGDEPTH){1'b1}});
	always @(posedge i_clk)
		`SLAVE_ASSERT(f_axi_rd_outstanding  < {(F_LGDEPTH){1'b1}});

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
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(f_axi_wr_outstanding==0))
			f_axi_wr_ack_delay <= 0;
		else if (f_axi_wr_outstanding > 0)
			f_axi_wr_ack_delay <= f_axi_wr_ack_delay + 1'b1;

		initial	f_axi_awr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid)||(f_axi_awr_outstanding == 0))
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
	if ((!axi_awr_req)&&(i_axi_bvalid))
		`SLAVE_ASSERT(f_axi_awr_outstanding > 0);

	always @(posedge i_clk)
	if ((!axi_wr_req)&&(i_axi_bvalid))
		`SLAVE_ASSERT(f_axi_wr_outstanding > 0);

	//
	// AXI read data channel signals
	//
	always @(posedge i_clk)
	if ((!axi_ard_req)&&(i_axi_rvalid))
		`SLAVE_ASSERT(f_axi_rd_outstanding > 0);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Manage the ID buffer.  Basic rules apply such as you can't
	// make a request of an already requested ID # before that ID
	// is returned, etc.
	//
	// Elements in this buffer reference transactions--possibly burst
	// transactions and not necessarily the individual values.
	//
	//
	////////////////////////////////////////////////////////////////////////
	// Now, let's look into that FIFO.  Without it, we know nothing about
	// the ID's

	initial f_axi_rd_id_outstanding = 0;
	initial f_axi_wr_id_outstanding = 0;
	initial f_axi_awr_id_outstanding = 0;
	initial f_axi_wr_id_complete = 0;
	always @(posedge i_clk)
		if (!i_axi_reset_n)
		begin
			f_axi_rd_id_outstanding <= 0;
			f_axi_wr_id_outstanding <= 0;
			f_axi_wr_id_complete <= 0;
			f_axi_awr_id_outstanding <= 0;
		end else begin
		// When issuing a write
		if (axi_awr_req)
		begin
			if ((F_CONSECUTIVE_IDS)&&(F_CHECK_IDS))
				assert(f_axi_awr_id_outstanding[i_axi_awid+1'b1] == 1'b0);
			assert((!F_CHECK_IDS)
				||(f_axi_awr_id_outstanding[i_axi_awid] == 1'b0));
			assert((!F_CHECK_IDS)
				||(f_axi_wr_id_complete[i_axi_awid] == 1'b0));
			f_axi_awr_id_outstanding[i_axi_awid] <= 1'b1;
			f_axi_wr_id_complete[i_axi_awid] <= 1'b0;
		end

		if (axi_wr_req)
		begin
			if ((F_CONSECUTIVE_IDS)&&(F_CHECK_IDS))
				assert(f_axi_wr_id_outstanding[i_axi_awid+1'b1] == 1'b0);
			assert((!F_CHECK_IDS)
				||(f_axi_wr_id_outstanding[i_axi_awid] == 1'b0));
			f_axi_wr_id_outstanding[i_axi_awid] <= 1'b1;
			if (i_axi_wlast)
			begin
				assume(f_axi_wr_id_complete[i_axi_awid] == 1'b0);
				f_axi_wr_id_complete[i_axi_awid] <= 1'b1;
			end
		end

		// When issuing a read
		if (axi_ard_req)
		begin
			if ((F_CONSECUTIVE_IDS)&&(F_CHECK_IDS))
				assert(f_axi_rd_id_outstanding[i_axi_arid+1'b1] == 1'b0);
			assert((!F_CHECK_IDS)
				||(f_axi_rd_id_outstanding[i_axi_arid] == 1'b0));
			f_axi_rd_id_outstanding[i_axi_arid] <= 1'b1;
		end

		// When a write is acknowledged
		if (axi_wr_ack)
		begin
			if (F_CHECK_IDS)
			begin
				assume(f_axi_awr_id_outstanding[i_axi_bid]);
				assume(f_axi_wr_id_outstanding[i_axi_bid]);
				assume((!F_STRICT_ORDER)||(!F_CONSECUTIVE_IDS)
					||(!f_axi_wr_id_outstanding[i_axi_bid-1'b1]));
				assume((!F_STRICT_ORDER)||(!F_CONSECUTIVE_IDS)
					||(!f_axi_awr_id_outstanding[i_axi_bid-1'b1]));
				assume(f_axi_wr_id_complete[i_axi_bid]);
			end
			f_axi_awr_id_outstanding[i_axi_bid] <= 1'b0;
			f_axi_wr_id_outstanding[i_axi_bid]  <= 1'b0;
			f_axi_wr_id_complete[i_axi_bid]     <= 1'b0;
		end

		// When a read is acknowledged
		if (axi_rd_ack)
		begin
			if (F_CHECK_IDS)
			begin
				assume(f_axi_rd_id_outstanding[i_axi_rid]);
				assume((!F_STRICT_ORDER)||(!F_CONSECUTIVE_IDS)
					||(!f_axi_rd_id_outstanding[i_axi_rid-1'b1]));
			end

			if (i_axi_rlast)
				f_axi_rd_id_outstanding[i_axi_rid] <= 1'b0;
		end
	end


	reg	[LGFIFOLN:0]	f_axi_rd_id_outstanding_count,
				f_axi_awr_id_outstanding_count,
				f_axi_wr_id_outstanding_count;

	initial	f_axi_rd_id_outstanding_count = 0;
	initial	f_axi_awr_id_outstanding_count = 0;
	initial	f_axi_wr_id_outstanding_count = 0;
	always @(*)
	begin
		//
		f_axi_rd_id_outstanding_count = 0;
		for(k=0; k< FIFOLN; k=k+1)
			if (f_axi_rd_id_outstanding[k])
				f_axi_rd_id_outstanding_count
					= f_axi_rd_id_outstanding_count +1;
		//
		f_axi_wr_id_outstanding_count = 0;
		for(k=0; k< FIFOLN; k=k+1)
			if (f_axi_wr_id_outstanding[k])
				f_axi_wr_id_outstanding_count = f_axi_wr_id_outstanding_count +1;
		f_axi_awr_id_outstanding_count = 0;
		for(k=0; k< FIFOLN; k=k+1)
			if (f_axi_awr_id_outstanding[k])
				f_axi_awr_id_outstanding_count = f_axi_awr_id_outstanding_count +1;
	end

	always @(*)
		`SLAVE_ASSUME((!F_CHECK_IDS)||(f_axi_awr_outstanding== f_axi_awr_id_outstanding_count));

	always @(*)
		`SLAVE_ASSUME((!F_CHECK_IDS)||(f_axi_wr_outstanding == f_axi_wr_id_outstanding_count));

	always @(*)
		`SLAVE_ASSUME((!F_CHECK_IDS)||(f_axi_rd_outstanding == f_axi_rd_id_outstanding_count));

	always @(*)
		assume( ((f_axi_wr_id_complete)&(~f_axi_awr_id_outstanding)) == 0);

	generate if (F_OPT_BURSTS)
	begin
		reg	[(8-1):0]	f_rd_pending	[0:(FIFOLN-1)];
		reg	[(8-1):0]	f_wr_pending,
					f_rd_count, f_wr_count;

		reg	r_last_rd_id_valid,
			r_last_wr_id_valid;

		reg	[(C_AXI_ID_WIDTH-1):0]	r_last_wr_id, r_last_rd_id;

		initial	r_last_wr_id_valid = 1'b0;
		initial	r_last_rd_id_valid = 1'b0;
		always @(posedge i_clk)
		if (!i_axi_reset_n)
		begin
			r_last_wr_id_valid <= 1'b0;
			r_last_rd_id_valid <= 1'b0;
			f_wr_count <= 0;
			f_rd_count <= 0;
		end else begin
			if (axi_awr_req)
			begin
				f_wr_pending <= i_axi_awlen+9'h1;
				assert(f_wr_pending == 0);
				r_last_wr_id_valid <= 1'b1;
				`SLAVE_ASSUME(i_axi_awlen <= F_AXI_MAXBURST);
			end

			if (axi_ard_req)
				f_rd_pending[i_axi_arid] <= i_axi_arlen+9'h1;


			if ((axi_wr_req)&&(i_axi_wlast))
			begin
				f_wr_count <= 0;
				r_last_wr_id_valid <= 1'b0;
				assert(
					// Either this is the last
					// of a series of requests we've
					// been waiting for,
					(f_wr_pending == f_wr_count - 9'h1)
					// *or* the only value
					// associated with an as yet
					// to be counted request
					||((axi_awr_req)&&(i_axi_awlen == 0)));
			end else if (axi_wr_req)
				f_wr_count <= f_wr_count + 1'b1;

			if (axi_rd_ack)
			begin
				if (i_axi_rlast)
					r_last_rd_id_valid <= 1'b0;
				else
					r_last_rd_id_valid <= 1'b1;

				r_last_rd_id <= i_axi_rid;
				if ((axi_rd_ack)&&(r_last_rd_id_valid))
					`SLAVE_ASSERT(i_axi_rid == r_last_rd_id);
			end

			if ((axi_rd_ack)&&(i_axi_rlast))
				assert(f_rd_count == f_rd_pending[i_axi_rid]-9'h1);
			if ((axi_rd_ack)&&(i_axi_rlast))
				f_rd_count <= 0;
			else if (axi_rd_ack)
				f_rd_count <= f_rd_count + 1'b1;
		end
	end else begin
		always @(*) begin
			// Since we aren't allowing bursts, *every*
			// write data and read data must always be the last
			// value
			`SLAVE_ASSUME((i_axi_wlast)||(!i_axi_wvalid));
			`SLAVE_ASSERT((i_axi_rlast)||(!i_axi_rvalid));

			assert((!i_axi_arvalid)||(i_axi_arlen==0));
			assert((!i_axi_awvalid)||(i_axi_awlen==0));
		end

		always @(posedge i_clk)
			if (i_axi_awvalid)
				assert(i_axi_awlen == 0);
		always @(posedge i_clk)
			if (i_axi_arvalid)
				assert(i_axi_arlen == 0);
		always @(posedge i_clk)
			if (i_axi_wvalid)
				assert(i_axi_wlast);
		always @(posedge i_clk)
			if (i_axi_rvalid)
				assume(i_axi_rlast);
	end endgenerate

`endif
endmodule
