////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxil_slave.v (Formal properties of an AXI lite slave)
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
// Copyright (C) 2018, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module faxil_slave #(
	localparam C_AXI_DATA_WIDTH	= 32,// Fixed, width of the AXI R&W data
	parameter  C_AXI_ADDR_WIDTH	= 28,// AXI Address width (log wordsize)
	localparam DW			= C_AXI_DATA_WIDTH,
	localparam AW			= C_AXI_ADDR_WIDTH,
	parameter [0:0]	F_OPT_AXI_WSTRB = 1'b1,
	parameter [0:0]	F_OPT_HAS_CACHE = 1'b0,
	parameter [0:0]	F_OPT_BRESP = 1'b1,
	parameter [0:0]	F_OPT_RRESP = 1'b1,
	// parameter [0:0]	F_OPT_HAS_PROT = 1'b0,
	parameter	F_LGDEPTH	= 4,
	parameter	[(F_LGDEPTH-1):0]	F_AXI_MAXWAIT  = 12,
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
	input	wire	[DW-1:0]	i_axi_rdata,    // Read data
	input	wire			i_axi_rready,  // Read Response ready
	//
	output	reg	[(F_LGDEPTH-1):0]	f_axi_rd_outstanding,
	output	reg	[(F_LGDEPTH-1):0]	f_axi_wr_outstanding,
	output	reg	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	LG_AXI_DW	= 5;
	localparam	LG_WB_DW	= 5;


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
		assert(!i_axi_reset_n);

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
	// Constant input assumptions (cache and prot)
	//
	//
	////////////////////////////////////////////////////////////////////////

	always @(*)
	if (i_axi_awvalid)
	begin
		// if (F_OPT_HAS_PROT) else
		`SLAVE_ASSUME(i_axi_awprot  == 3'h0);
		if (!F_OPT_AXI_WSTRB)
			`SLAVE_ASSUME(&i_axi_wstrb);
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
		// if (F_OPT_HAS_PROT) else
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

		// Incoming Write address channel
		if ((f_past_valid)&&($past(i_axi_awvalid))&&(!$past(i_axi_awready)))
		begin
			`SLAVE_ASSUME(i_axi_awvalid);
			`SLAVE_ASSUME(i_axi_awaddr  == $past(i_axi_awaddr));
		end

		// Incoming Write data channel
		if ((f_past_valid)&&($past(i_axi_wvalid))&&(!$past(i_axi_wready)))
		begin
			`SLAVE_ASSUME(i_axi_wvalid);
			`SLAVE_ASSUME(i_axi_wstrb  == $past(i_axi_wstrb));
			`SLAVE_ASSUME(i_axi_wdata  == $past(i_axi_wdata));
		end

		// Incoming Read address channel
		if ((f_past_valid)&&($past(i_axi_arvalid))&&(!$past(i_axi_arready)))
		begin
			`SLAVE_ASSUME(i_axi_arvalid);
			`SLAVE_ASSUME(i_axi_araddr  == $past(i_axi_araddr));
		end

		if ((f_past_valid)&&($past(i_axi_rvalid))&&(!$past(i_axi_rready)))
		begin
			`SLAVE_ASSERT(i_axi_rvalid);
			`SLAVE_ASSERT(i_axi_rresp  == $past(i_axi_rresp));
			`SLAVE_ASSERT(i_axi_rdata  == $past(i_axi_rdata));
		end

		if ((f_past_valid)&&($past(i_axi_bvalid))&&(!$past(i_axi_bready)))
		begin
			`SLAVE_ASSERT(i_axi_bvalid);
			`SLAVE_ASSERT(i_axi_bresp  == $past(i_axi_bresp));
		end
	end

	// Nothing should be returning a result on the first clock
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
			else
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
		else
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
		else
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
		&&(!$past(i_axi_wvalid,2))&&($past(i_axi_awvalid,2))
			&&($past(f_axi_awr_outstanding >= f_axi_wr_outstanding,2))
		// ##1
			&&(!$past(i_axi_wvalid)))
		// |=>
		`SLAVE_ASSUME(i_axi_wvalid);

	// Rule number two:
	always @(posedge i_clk)
	if ((i_axi_reset_n)&&(!$past(i_axi_awvalid))&&($past(i_axi_wvalid))
			&&(f_axi_awr_outstanding <= f_axi_wr_outstanding))
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
		if ((!i_axi_reset_n)||(i_axi_rvalid))
			f_axi_rd_ack_delay <= 0;
		else if (f_axi_rd_outstanding > 0)
			f_axi_rd_ack_delay <= f_axi_rd_ack_delay + 1'b1;

		initial	f_axi_wr_ack_delay = 0;
		always @(posedge i_clk)
		if ((!i_axi_reset_n)||(i_axi_bvalid))
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
		cover((i_axi_bvalid)&&(i_axi_bready));

	//
	// AXI read response channel
	//
	always @(posedge i_clk)
		cover((i_axi_rvalid)&&(i_axi_rready));
endmodule
