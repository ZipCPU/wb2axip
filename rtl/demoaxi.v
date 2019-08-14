////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	demoaxi.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Demonstrate an AXI-lite bus design.  The goal of this design
//		is to support a completely pipelined AXI-lite transaction
//	which can transfer one data item per clock.
//
//	Note that the AXI spec requires that there be no combinatorial
//	logic between input ports and output ports.  Hence all of the *valid
//	and *ready signals produced here are registered.  This forces us into
//	the buffered handshake strategy.
//
//	Some curious variable meanings below:
//
//	!axi_arvalid is synonymous with having a request, but stalling because
//		of a current request sitting in axi_rvalid with !axi_rready
//	!axi_awvalid is also synonymous with having an axi address being
//		received, but either the axi_bvalid && !axi_bready, or
//		no write data has been received
//	!axi_wvalid is similar to axi_awvalid.
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
`default_nettype none

`timescale 1 ns / 1 ps

module	demoaxi
	#(
		// Users to add parameters here
		parameter [0:0] OPT_READ_SIDEEFFECTS = 1,
		// User parameters ends
		// Do not modify the parameters beyond this line
		// Width of S_AXI data bus
		parameter integer C_S_AXI_DATA_WIDTH	= 32,
		// Width of S_AXI address bus
		parameter integer C_S_AXI_ADDR_WIDTH	= 8
	) (
		// Users to add ports here
		// No user ports (yet) in this design
		// User ports ends

		// Do not modify the ports beyond this line
		// Global Clock Signal
		input wire  S_AXI_ACLK,
		// Global Reset Signal. This Signal is Active LOW
		input wire  S_AXI_ARESETN,
		// Write address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_AWADDR,
		// Write channel Protection type. This signal indicates the
    		// privilege and security level of the transaction, and whether
    		// the transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_AWPROT,
		// Write address valid. This signal indicates that the master
		// signaling valid write address and control information.
		input wire  S_AXI_AWVALID,
		// Write address ready. This signal indicates that the slave
		// is ready to accept an address and associated control signals.
		output wire  S_AXI_AWREADY,
		// Write data (issued by master, acceped by Slave)
		input wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_WDATA,
		// Write strobes. This signal indicates which byte lanes hold
    		// valid data. There is one write strobe bit for each eight
    		// bits of the write data bus.
		input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] S_AXI_WSTRB,
		// Write valid. This signal indicates that valid write
    		// data and strobes are available.
		input wire  S_AXI_WVALID,
		// Write ready. This signal indicates that the slave
    		// can accept the write data.
		output wire  S_AXI_WREADY,
		// Write response. This signal indicates the status
    		// of the write transaction.
		output wire [1 : 0] S_AXI_BRESP,
		// Write response valid. This signal indicates that the channel
    		// is signaling a valid write response.
		output wire  S_AXI_BVALID,
		// Response ready. This signal indicates that the master
    		// can accept a write response.
		input wire  S_AXI_BREADY,
		// Read address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_ARADDR,
		// Protection type. This signal indicates the privilege
    		// and security level of the transaction, and whether the
    		// transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_ARPROT,
		// Read address valid. This signal indicates that the channel
    		// is signaling valid read address and control information.
		input wire  S_AXI_ARVALID,
		// Read address ready. This signal indicates that the slave is
    		// ready to accept an address and associated control signals.
		output wire  S_AXI_ARREADY,
		// Read data (issued by slave)
		output wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_RDATA,
		// Read response. This signal indicates the status of the
    		// read transfer.
		output wire [1 : 0] S_AXI_RRESP,
		// Read valid. This signal indicates that the channel is
    		// signaling the required read data.
		output wire  S_AXI_RVALID,
		// Read ready. This signal indicates that the master can
    		// accept the read data and response information.
		input wire  S_AXI_RREADY
	);

	// AXI4LITE signals
	reg		axi_awready;
	reg		axi_wready;
	reg		axi_bvalid;
	reg		axi_arready;
	reg [C_S_AXI_DATA_WIDTH-1 : 0] 	axi_rdata;
	reg		axi_rvalid;

	// Example-specific design signals
	// local parameter for addressing 32 bit / 64 bit C_S_AXI_DATA_WIDTH
	// ADDR_LSB is used for addressing 32/64 bit registers/memories
	// ADDR_LSB = 2 for 32 bits (n downto 2)
	// ADDR_LSB = 3 for 64 bits (n downto 3)
	localparam integer ADDR_LSB = 2;
	localparam integer AW = C_S_AXI_ADDR_WIDTH-2;
	localparam integer DW = C_S_AXI_DATA_WIDTH;
	//----------------------------------------------
	//-- Signals for user logic register space example
	//------------------------------------------------
	reg [DW-1:0]	slv_mem	[0:63];

	// I/O Connections assignments

	assign S_AXI_AWREADY	= axi_awready;
	assign S_AXI_WREADY	= axi_wready;
	assign S_AXI_BRESP	= 2'b00; // The OKAY response
	assign S_AXI_BVALID	= axi_bvalid;
	assign S_AXI_ARREADY	= axi_arready;
	assign S_AXI_RDATA	= axi_rdata;
	assign S_AXI_RRESP	= 2'b00; // The OKAY response
	assign S_AXI_RVALID	= axi_rvalid;
	// Implement axi_*wready generation

	//////////////////////////////////////
	//
	// Read processing
	//
	//
	wire	valid_read_request,
		read_response_stall;

	assign	valid_read_request  =  S_AXI_ARVALID || !S_AXI_ARREADY;
	assign	read_response_stall =  S_AXI_RVALID  && !S_AXI_RREADY;

	//
	// The read response channel valid signal
	//
	initial	axi_rvalid = 1'b0;
	always @( posedge S_AXI_ACLK )
	if (!S_AXI_ARESETN)
		axi_rvalid <= 0;
	else if (read_response_stall)
		// Need to stay valid as long as the return path is stalled
		axi_rvalid <= 1'b1;
	else if (valid_read_request)
		axi_rvalid <= 1'b1;
	else
		// Any stall has cleared, so we can always
		// clear the valid signal in this case
		axi_rvalid <= 1'b0;

	reg [C_S_AXI_ADDR_WIDTH-1 : 0] 	pre_raddr, rd_addr;

	// Buffer the address
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARREADY)
		pre_raddr <= S_AXI_ARADDR;

	always @(*)
	if (!axi_arready)
		rd_addr = pre_raddr;
	else
		rd_addr = S_AXI_ARADDR;

	//
	// Read the data
	//
	always @(posedge S_AXI_ACLK)
	if (!read_response_stall
		&&(!OPT_READ_SIDEEFFECTS || valid_read_request))
		// If the outgoing channel is not stalled (above)
		// then read
		axi_rdata <= slv_mem[rd_addr[AW+ADDR_LSB-1:ADDR_LSB]];

	//
	// The read address channel ready signal
	//
	initial	axi_arready = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_arready <= 1'b1;
	else if (read_response_stall)
	begin
		// Outgoing channel is stalled
		//    As long as something is already in the buffer,
		//    axi_arready needs to stay low
		axi_arready <= !valid_read_request;
	end else
		axi_arready <= 1'b1;

	//////////////////////////////////////
	//
	// Write processing
	//
	//
	reg [C_S_AXI_ADDR_WIDTH-1 : 0]		pre_waddr, waddr;
	reg [C_S_AXI_DATA_WIDTH-1 : 0]		pre_wdata, wdata;
	reg [(C_S_AXI_DATA_WIDTH/8)-1 : 0]	pre_wstrb, wstrb;

	wire	valid_write_address, valid_write_data,
		write_response_stall;

	assign	valid_write_address = S_AXI_AWVALID || !axi_awready;
	assign	valid_write_data    = S_AXI_WVALID  || !axi_wready;
	assign	write_response_stall= S_AXI_BVALID  && !S_AXI_BREADY;

	//
	// The write address channel ready signal
	//
	initial	axi_awready = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_awready <= 1'b1;
	else if (write_response_stall)
	begin
		// The output channel is stalled
		//	If our buffer is full, we need to remain stalled
		//	Likewise if it is empty, and there's a request,
		//	  we'll need to stall.
		axi_awready <= !valid_write_address;
	end else if (valid_write_data)
		// The output channel is clear, and write data
		// are available
		axi_awready <= 1'b1;
	else
		// If we were ready before, then remain ready unless an
		// address unaccompanied by data shows up
		axi_awready <= ((axi_awready)&&(!S_AXI_AWVALID));
		// This is equivalent to
		// axi_awready <= !valid_write_address

	//
	// The write data channel ready signal
	//
	initial	axi_wready = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_wready <= 1'b1;
	else if (write_response_stall)
		// The output channel is stalled
		//	We can remain ready until valid
		//	write data shows up
		axi_wready <= !valid_write_data;
	else if (valid_write_address)
		// The output channel is clear, and a write address
		// is available
		axi_wready <= 1'b1;
	else
		// if we were ready before, and there's no new data avaialble
		// to cause us to stall, remain ready
		axi_wready <= (axi_wready)&&(!S_AXI_WVALID);
		// This is equivalent to
		// axi_wready <= !valid_write_data


	// Buffer the address
	always @(posedge S_AXI_ACLK)
	if (S_AXI_AWREADY)
		pre_waddr <= S_AXI_AWADDR;

	// Buffer the data
	always @(posedge S_AXI_ACLK)
	if (S_AXI_WREADY)
	begin
		pre_wdata <= S_AXI_WDATA;
		pre_wstrb <= S_AXI_WSTRB;
	end

	always @(*)
	if (!axi_awready)
		// Read the write address from our "buffer"
		waddr = pre_waddr;
	else
		waddr = S_AXI_AWADDR;

	always @(*)
	if (!axi_wready)
	begin
		// Read the write data from our "buffer"
		wstrb = pre_wstrb;
		wdata = pre_wdata;
	end else begin
		wstrb = S_AXI_WSTRB;
		wdata = S_AXI_WDATA;
	end

	//
	// Actually (finally) write the data
	//
	always @( posedge S_AXI_ACLK )
	// If the output channel isn't stalled, and
	if (!write_response_stall
		// If we have a valid address, and
		&& valid_write_address
		// If we have valid data
		&& valid_write_data)
	begin
		if (wstrb[0])
			slv_mem[waddr[AW+ADDR_LSB-1:ADDR_LSB]][7:0]
				<= wdata[7:0];
		if (wstrb[1])
			slv_mem[waddr[AW+ADDR_LSB-1:ADDR_LSB]][15:8]
				<= wdata[15:8];
		if (wstrb[2])
			slv_mem[waddr[AW+ADDR_LSB-1:ADDR_LSB]][23:16]
				<= wdata[23:16];
		if (wstrb[3])
			slv_mem[waddr[AW+ADDR_LSB-1:ADDR_LSB]][31:24]
				<= wdata[31:24];
	end

	//
	// The write response channel valid signal
	//
	initial	axi_bvalid = 1'b0;
	always @( posedge S_AXI_ACLK )
	if (!S_AXI_ARESETN)
		axi_bvalid <= 1'b0;
	//
	// The outgoing response channel should indicate a valid write if ...
		// 1. We have a valid address, and
	else if (valid_write_address
			// 2. We had valid data
			&& valid_write_data)
		// It doesn't matter here if we are stalled or not
		// We can keep setting ready as often as we want
		axi_bvalid <= 1'b1;
	else if (S_AXI_BREADY)
		// Otherwise, if BREADY was true, then it was just accepted
		// and can return to idle now
		axi_bvalid <= 1'b0;

	// Make Verilator happy
	// Verilator lint_off UNUSED
	wire	[4*ADDR_LSB+5:0]	unused;
	assign	unused = { S_AXI_AWPROT, S_AXI_ARPROT,
				S_AXI_AWADDR[ADDR_LSB-1:0],
				rd_addr[ADDR_LSB-1:0],
				waddr[ADDR_LSB-1:0],
				S_AXI_ARADDR[ADDR_LSB-1:0] };
	// Verilator lint_on UNUSED

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = 4;

	wire	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding,
					f_axi_wr_outstanding,
					f_axi_rd_outstanding;

	faxil_slave #(// .C_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
			// .F_OPT_NO_READS(1'b0),
			// .F_OPT_NO_WRITES(1'b0),
			.F_OPT_XILINX(1),
			.F_LGDEPTH(F_LGDEPTH))
		properties (
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awaddr(S_AXI_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot(S_AXI_AWPROT),
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		//
		.i_axi_wdata(S_AXI_WDATA),
		.i_axi_wstrb(S_AXI_WSTRB),
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		//
		.i_axi_bresp(S_AXI_BRESP),
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		//
		.i_axi_araddr(S_AXI_ARADDR),
		.i_axi_arprot(S_AXI_ARPROT),
		.i_axi_arcache(4'h0),
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		//
		.i_axi_rdata(S_AXI_RDATA),
		.i_axi_rresp(S_AXI_RRESP),
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		//
		.f_axi_rd_outstanding(f_axi_rd_outstanding),
		.f_axi_wr_outstanding(f_axi_wr_outstanding),
		.f_axi_awr_outstanding(f_axi_awr_outstanding));

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	///////
	//
	// Properties necessary to pass induction
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (!S_AXI_RVALID)
			assert(f_axi_rd_outstanding == 0);
		else if (!S_AXI_ARREADY)
			assert((f_axi_rd_outstanding == 2)||(f_axi_rd_outstanding == 1));
		else
			assert(f_axi_rd_outstanding == 1);
	end

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (axi_bvalid)
		begin
			assert(f_axi_awr_outstanding == 1+(axi_awready ? 0:1));
			assert(f_axi_wr_outstanding  == 1+(axi_wready  ? 0:1));
		end else begin
			assert(f_axi_awr_outstanding == (axi_awready ? 0:1));
			assert(f_axi_wr_outstanding  == (axi_wready  ? 0:1));
		end
	end


	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	// In addition to making sure the design returns a value, any value,
	// let's cover returning three values on adjacent clocks--just to prove
	// we can.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @( posedge S_AXI_ACLK )
	if ((f_past_valid)&&(S_AXI_ARESETN))
		cover(($past((S_AXI_BVALID && S_AXI_BREADY)))
			&&($past((S_AXI_BVALID && S_AXI_BREADY),2))
			&&(S_AXI_BVALID && S_AXI_BREADY));

	always @( posedge S_AXI_ACLK )
	if ((f_past_valid)&&(S_AXI_ARESETN))
		cover(($past((S_AXI_RVALID && S_AXI_RREADY)))
			&&($past((S_AXI_RVALID && S_AXI_RREADY),2))
			&&(S_AXI_RVALID && S_AXI_RREADY));

	// Let's go just one further, and verify we can do three returns in a
	// row.  Why?  It might just be possible that one value was waiting
	// already, and so we haven't yet tested that two requests could be
	// made in a row.
	always @( posedge S_AXI_ACLK )
	if ((f_past_valid)&&(S_AXI_ARESETN))
		cover(($past((S_AXI_BVALID && S_AXI_BREADY)))
			&&($past((S_AXI_BVALID && S_AXI_BREADY),2))
			&&($past((S_AXI_BVALID && S_AXI_BREADY),3))
			&&(S_AXI_BVALID && S_AXI_BREADY));

	always @( posedge S_AXI_ACLK )
	if ((f_past_valid)&&(S_AXI_ARESETN))
		cover(($past((S_AXI_RVALID && S_AXI_RREADY)))
			&&($past((S_AXI_RVALID && S_AXI_RREADY),2))
			&&($past((S_AXI_RVALID && S_AXI_RREADY),3))
			&&(S_AXI_RVALID && S_AXI_RREADY));

	//
	// Let's create a sophisticated cover statement designed to show off
	// how our core can handle stalls and non-valids, synchronizing
	// across multiple scenarios
	reg	[22:0]	fw_wrdemo_pipe, fr_wrdemo_pipe;
	always @(*)
	if (!S_AXI_ARESETN)
		fw_wrdemo_pipe = 0;
	else begin
		fw_wrdemo_pipe[0] = (S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[1] = fr_wrdemo_pipe[0]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[2] = fr_wrdemo_pipe[1]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		//
		//
		fw_wrdemo_pipe[3] = fr_wrdemo_pipe[2]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[4] = fr_wrdemo_pipe[3]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[5] = fr_wrdemo_pipe[4]
				&&(!S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[6] = fr_wrdemo_pipe[5]
				&&(S_AXI_AWVALID)
				&&( S_AXI_WVALID)
				&&( S_AXI_BREADY);
		fw_wrdemo_pipe[7] = fr_wrdemo_pipe[6]
				&&(!S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&( S_AXI_BREADY);
		fw_wrdemo_pipe[8] = fr_wrdemo_pipe[7]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[9] = fr_wrdemo_pipe[8]
//				&&(S_AXI_AWVALID)
//				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[10] = fr_wrdemo_pipe[9]
//				&&(S_AXI_AWVALID)
//				&&(S_AXI_WVALID)
				// &&(S_AXI_BREADY);
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[11] = fr_wrdemo_pipe[10]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(!S_AXI_BREADY);
		fw_wrdemo_pipe[12] = fr_wrdemo_pipe[11]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[13] = fr_wrdemo_pipe[12]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[14] = fr_wrdemo_pipe[13]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(f_axi_awr_outstanding == 0)
				&&(f_axi_wr_outstanding == 0)
				&&(S_AXI_BREADY);
		//
		//
		//
		fw_wrdemo_pipe[15] = fr_wrdemo_pipe[14]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[16] = fr_wrdemo_pipe[15]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[17] = fr_wrdemo_pipe[16]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[18] = fr_wrdemo_pipe[17]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(!S_AXI_BREADY);
		fw_wrdemo_pipe[19] = fr_wrdemo_pipe[18]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[20] = fr_wrdemo_pipe[19]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[21] = fr_wrdemo_pipe[20]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
		fw_wrdemo_pipe[22] = fr_wrdemo_pipe[21]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID)
				&&(S_AXI_BREADY);
	end

	always @(posedge S_AXI_ACLK)
		fr_wrdemo_pipe <= fw_wrdemo_pipe;

	always @(*)
	if (S_AXI_ARESETN)
	begin
		cover(fw_wrdemo_pipe[0]);
		cover(fw_wrdemo_pipe[1]);
		cover(fw_wrdemo_pipe[2]);
		cover(fw_wrdemo_pipe[3]);
		cover(fw_wrdemo_pipe[4]);
		cover(fw_wrdemo_pipe[5]);
		cover(fw_wrdemo_pipe[6]);
		cover(fw_wrdemo_pipe[7]); //
		cover(fw_wrdemo_pipe[8]);
		cover(fw_wrdemo_pipe[9]);
		cover(fw_wrdemo_pipe[10]);
		cover(fw_wrdemo_pipe[11]);
		cover(fw_wrdemo_pipe[12]);
		cover(fw_wrdemo_pipe[13]);
		cover(fw_wrdemo_pipe[14]);
		cover(fw_wrdemo_pipe[15]);
		cover(fw_wrdemo_pipe[16]);
		cover(fw_wrdemo_pipe[17]);
		cover(fw_wrdemo_pipe[18]);
		cover(fw_wrdemo_pipe[19]);
		cover(fw_wrdemo_pipe[20]);
		cover(fw_wrdemo_pipe[21]);
		cover(fw_wrdemo_pipe[22]);
	end

	//
	// Now let's repeat, but for a read demo
	reg	[10:0]	fw_rddemo_pipe, fr_rddemo_pipe;
	always @(*)
	if (!S_AXI_ARESETN)
		fw_rddemo_pipe = 0;
	else begin
		fw_rddemo_pipe[0] = (S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[1] = fr_rddemo_pipe[0]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[2] = fr_rddemo_pipe[1]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		//
		//
		fw_rddemo_pipe[3] = fr_rddemo_pipe[2]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[4] = fr_rddemo_pipe[3]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[5] = fr_rddemo_pipe[4]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[6] = fr_rddemo_pipe[5]
				&&(S_AXI_ARVALID)
				&&(!S_AXI_RREADY);
		fw_rddemo_pipe[7] = fr_rddemo_pipe[6]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[8] = fr_rddemo_pipe[7]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[9] = fr_rddemo_pipe[8]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rddemo_pipe[10] = fr_rddemo_pipe[9]
				&&(f_axi_rd_outstanding == 0);
	end

	initial	fr_rddemo_pipe = 0;
	always @(posedge S_AXI_ACLK)
		fr_rddemo_pipe <= fw_rddemo_pipe;

	always @(*)
	begin
		cover(fw_rddemo_pipe[0]);
		cover(fw_rddemo_pipe[1]);
		cover(fw_rddemo_pipe[2]);
		cover(fw_rddemo_pipe[3]);
		cover(fw_rddemo_pipe[4]);
		cover(fw_rddemo_pipe[5]);
		cover(fw_rddemo_pipe[6]);
		cover(fw_rddemo_pipe[7]);
		cover(fw_rddemo_pipe[8]);
		cover(fw_rddemo_pipe[9]);
		cover(fw_rddemo_pipe[10]);
	end
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
