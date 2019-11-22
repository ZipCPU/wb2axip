////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axildouble.v
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Create a special AXI slave which can be used to reduce crossbar
//		logic for multiple simplified AXI slaves.  This is a companion
//	core to the similar axisingle core, but allowing the slave to
//	decode the clock between multiple possible addresses.
//
//	To use this, the slave must follow specific (simplified AXI) rules:
//
//	Write interface
//	--------------------
//	1. The controller will guarantee that AWVALID == WVALID
//		(You can connect AWVALID to WVALID when connecting to your core)
//	2. The controller will guarantee that AWID == 0 for the slave
//		All ID logic will be handled internally
//	3. The controller will guarantee that AWLEN == 0 and WLAST == 1
//		Instead, the controller will handle all burst addressing
//		internally
//	4. This makes AWBURST irrelevant
//	5. Other wires are simplified as well: AWLOCK=0, AWCACHE=0, AWQOS=0
//	6. If OPT_EXCLUSIVE_ACCESS is set, the controller will handle lock
//		logic internally
//	7. The slave must guarantee that AWREADY == WREADY = 1
//		(This core doesn't have AWREADY or WREADY inputs)
//	8. The slave must also guarantee that BVALID == $past(AWVALID)
//		(This core internally generates BVALID, and so the slave's
//		BVALID return is actually ignored.)
//	9. The controller will also guarantee that BREADY = 1
//		(This core doesn't have a BVALID input)
//
//	The controller will maintain AWPROT in case the slave wants to
//	disallow particular writes, and AWSIZE so the slave can know how many
//	bytes are being accessed.
//
//	Read interface
//	--------------------
//	1. The controller will guarantee that RREADY = 1
//		(This core doesn't have an RREADY output)
//	2. The controller will guarantee that ARID = 0
//		All IDs are handled internally
//	3. The controller will guarantee that ARLEN == 0
//		All burst logic is handled internally
//	4. As before, this makes ARBURST irrelevant
//	5. Other wires are simplified: ARLOCK=0, ARCACHE = 0, ARQOS=0, etc
//	6. The slave must guarantee that RVALID == $past(ARVALID)
//		The controller actually ignores RVALID--but to be a valid slave,
//		this must be assumed.
//	7. The slave must also guarantee that RLAST == 1 anytime RVALID
//
//	As with the write side, the controller will fill in ARSIZE and ARPROT.
//	They may be used or ignored by the slave.
//
//	Why?  This simplifies slave logic.  Slaves may interact with the bus
//	using only the logic below:
//
//		always @(posedge S_AXI_ACLK)
//		if (AWVALID) case(AWADDR)
//		R1:	slvreg_1 <= WDATA;
//		R2:	slvreg_2 <= WDATA;
//		R3:	slvreg_3 <= WDATA;
//		R4:	slvreg_4 <= WDATA;
//		endcase
//
//		always @(*)
//			BRESP = 2'b00; // OKAY
//
//		always @(posedge S_AXI_ACLK)
//		if (ARVALID)
//		case(ARADDR)
//			R1: RDATA <= slvreg_1;
//			R2: RDATA <= slvreg_2;
//			R3: RDATA <= slvreg_3;
//			R4: RDATA <= slvreg_4;
//		endcase
//
//		always @(*)
//			RRESP = 2'b00; // OKAY
//
//	This core will then keep track of the more complex bus logic, locking,
//	burst length, burst ID's, etc, simplifying both slaves and connection
//	logic.  Slaves with the more complicated (and proper/accurate) logic,
//	that follow the rules above, should have no problems with this
//	additional logic.
//
// Performance:
//
//	Throughput: The slave can sustain one read/write per clock as long as
//	the upstream master keeps S_AXI_[BR]READY high.  If S_AXI_[BR]READY
//	ever drops, there's some flexibility provided by the return FIFO, so
//	the master might not notice a drop in throughput until the FIFO fills.
//
//	Latency: This core will create a four clock latency on all requests.
//
//	Logic: Actual logic depends upon how this is set up and built.  As
//	parameterized below, this core can fit within 639 Xilinx 6-LUTs and
//	39 M-LUTs.
//
//	Narrow bursts: This core supports narrow bursts by nature.  Whether the
//	subcores pay attention to WSTRB, AWSIZE, and ARSIZE is up to the
//	subcore itself.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// The WB2AXIP project is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.
//
// You should have received a copy of the GNU General Public License along with
// this program.  (It's in the $(ROOT)/doc directory.  Run make with no target
// there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
module	axidouble #(
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 32,
		parameter integer C_AXI_ID_WIDTH = 1,
		//
		// NS is the number of slave interfaces.  If you are interested
		// in a single slave interface, checkout the demofull.v core
		// in this same repository.
		parameter	NS = 8,
		//
		// Shorthand for address width, data width, and id width
		// AW, and DW, are short-hand abbreviations used locally.
		localparam AW = C_AXI_ADDR_WIDTH,
		localparam DW = C_AXI_DATA_WIDTH,
		localparam IW = C_AXI_ID_WIDTH,
		//
		// Each of the slave interfaces has an address range.  The
		// base address for each slave is given by AW bits of SLAVE_ADDR
		// below.
		parameter	[NS*AW-1:0]	SLAVE_ADDR = {
			{ 3'b111, {(AW-3){1'b0}} },
			{ 3'b110, {(AW-3){1'b0}} },
			{ 3'b101, {(AW-3){1'b0}} },
			{ 3'b100, {(AW-3){1'b0}} },
			{ 3'b011, {(AW-3){1'b0}} },
			{ 3'b010, {(AW-3){1'b0}} },
			{ 4'b0001,{(AW-4){1'b0}} },
			{ 4'b0000,{(AW-4){1'b0}} } },
		//
		//
		// The relevant bits of the slave address are given in
		// SLAVE_MASK below, at AW bits per slave.  To be valid,
		// SLAVE_ADDR & ~SLAVE_MASK must be zero.  Only the masked
		// bits will be used in any compare.
		//
		// Also, while not technically required, it is strongly
		// recommended that the bottom 12-bits of each AW bits of
		// the SLAVE_MASK bust be zero.
		parameter	[NS*AW-1:0]	SLAVE_MASK =
			(NS <= 1) ? 0
			: {	{(NS-2){ 3'b111, {(AW-3){1'b0}} }},
				{(2){   4'b1111, {(AW-4){1'b0}} }}
			},
		//
		// LGFLEN specifies the log (based two) of the number of
		// transactions that may need to be held outstanding internally.
		// If you really want high throughput, and if you expect any
		// back pressure at all, then increase LGFLEN.  Otherwise the
		// default value of 3 (FIFO size = 8) should be sufficient
		// to maintain full loading
		parameter	LGFLEN=3,
		//
		// This core will handle exclusive access if
		// OPT_EXCLUSIVE_ACCESS is set to one.  If set to 1, all
		// subcores will have exclusive access applied.  There is no
		// core-by-core means of enabling exclusive access at this time.
		parameter [0:0]	OPT_EXCLUSIVE_ACCESS = 1'b1
		//
	) (
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		// Write address channel coming from upstream
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[8-1:0]			S_AXI_AWLEN,
		input	wire	[3-1:0]			S_AXI_AWSIZE,
		input	wire	[2-1:0]			S_AXI_AWBURST,
		input	wire				S_AXI_AWLOCK,
		input	wire	[4-1:0]			S_AXI_AWCACHE,
		input	wire	[3-1:0]			S_AXI_AWPROT,
		input	wire	[4-1:0]			S_AXI_AWQOS,
		//
		// Write data channel coming from upstream
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire [C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		input	wire 				S_AXI_WLAST,
		//
		// Write responses sent back
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_BID,
		output	wire	[2-1:0]			S_AXI_BRESP,
		//
		// Read address request channel from upstream
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[8-1:0]			S_AXI_ARLEN,
		input	wire	[3-1:0]			S_AXI_ARSIZE,
		input	wire	[2-1:0]			S_AXI_ARBURST,
		input	wire				S_AXI_ARLOCK,
		input	wire	[4-1:0]			S_AXI_ARCACHE,
		input	wire	[3-1:0]			S_AXI_ARPROT,
		input	wire	[4-1:0]			S_AXI_ARQOS,
		//
		// Read data return channel back upstream
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_RID,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire				S_AXI_RLAST,
		output	wire	[2-1:0]			S_AXI_RRESP,
		//
		//
		// Now for the simplified downstream interface to a series
		// of downstream slaves.  All outgoing wires are shared between
		// the slaves save the AWVALID and ARVALID signals.  Slave
		// returns are not shared.
		//
		//
		// Simplified Write address channel.
		output	wire	[NS-1:0]		M_AXI_AWVALID,
		// input wire M_AXI_AWREADY is assumed to be 1
		output	wire	[0:0]			M_AXI_AWID,//    = 0
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[8-1:0]			M_AXI_AWLEN,//   = 0
		output	wire	[3-1:0]			M_AXI_AWSIZE,
		output	wire	[2-1:0]			M_AXI_AWBURST,//=INC
		output	wire				M_AXI_AWLOCK,//  = 0
		output	wire	[4-1:0]			M_AXI_AWCACHE,// = 0
		output	wire	[3-1:0]			M_AXI_AWPROT,//  = 0
		output	wire	[4-1:0]			M_AXI_AWQOS,//   = 0
		//
		// Simplified write data channel
		output	wire	[NS-1:0]		M_AXI_WVALID,//=AWVALID
		// input wire M_AXI_WVALID is *assumed* to be 1
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,//   = 1
		//
		// Simplified write response channel
		// input wire M_AXI_BVALID is *assumed* to be
		//	$past(M_AXI_AWVALID), and so ignored
		output	wire				M_AXI_BREADY,//  = 1
		input	wire	[NS*2-1:0]		M_AXI_BRESP,
		// The controller handles BID, so this can be ignored as well
		//
		// Simplified read address channel
		output	wire	[NS-1:0]		M_AXI_ARVALID,
		// input wire M_AXI_ARREADY is assumed to be 1
		output	wire	[0:0]			M_AXI_ARID,//    = 0
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[8-1:0]			M_AXI_ARLEN,//   = 0
		output	wire	[3-1:0]			M_AXI_ARSIZE,
		output	wire	[2-1:0]			M_AXI_ARBURST,//=INC
		output	wire				M_AXI_ARLOCK,//  = 0
		output	wire	[4-1:0]			M_AXI_ARCACHE,// = 0
		output	wire	[3-1:0]			M_AXI_ARPROT,//  = 0
		output	wire	[4-1:0]			M_AXI_ARQOS,//   = 0
		//
		// Simplified read data return channel
		// input wire M_AXI_RVALID is assumed to be $past(ARVALID,1)
		output	wire				M_AXI_RREADY,//  = 1
		input	wire [NS*C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire	[NS*2-1:0]		M_AXI_RRESP
		// input wire M_AXI_RLAST is assumed to be 1
	);
	//
	//
	// LGNS is the number of bits required in a slave index
	localparam	LGNS = $clog2(NS);
	//
	localparam [1:0]	OKAY = 2'b00,
				EXOKAY = 2'b01,
				SLVERR = 2'b10,
				INTERCONNECT_ERROR = 2'b11;
	localparam	ADDR_LSBS = $clog2(DW)-3;
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Unused wire assignments
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	M_AXI_AWID  = 0;
	assign	M_AXI_AWLEN = 0;
	assign	M_AXI_AWBURST = 2'b00;
	assign	M_AXI_AWLOCK  = 1'b0;
	assign	M_AXI_AWCACHE = 4'h0;
	// assign	M_AXI_AWPROT  = 3'h0;
	assign	M_AXI_AWQOS   = 4'h0;
	//
	assign	M_AXI_WVALID  = M_AXI_AWVALID;
	assign	M_AXI_WLAST   = 1'b1;
	//
	assign	M_AXI_BREADY  = 1'b1;
	//
	assign	M_AXI_ARID	= 1'b0;
	assign	M_AXI_ARLEN	= 8'h0; // Burst of one beat
	assign	M_AXI_ARBURST	= 2'b00; // INC
	assign	M_AXI_ARLOCK	= 1'b0;
	assign	M_AXI_ARCACHE	= 4'h0;
	// assign	M_AXI_ARPROT	= 3'h0;
	assign	M_AXI_ARQOS	= 4'h0;
	//
	assign	M_AXI_RREADY	= -1;

	////////////////////////////////////////////////////////////////////////

	reg	locked_burst, locked_write, lock_valid;
	integer			k;

	////////////////////////////////////////////////////////////////////////
	//
	// Write logic:
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire			awskd_stall;
	wire			awskid_valid, bffull, bempty, write_awskidready,
				dcd_awvalid;
	reg			write_bvalid, write_response;
	reg			bfull, write_no_index;
	wire	[NS:0]		raw_wdecode;
	reg	[NS:0]		last_wdecode, wdecode;
	wire	[AW-1:0]	m_awaddr;
	reg	[LGNS-1:0]	write_windex, write_bindex;
	wire	[3-1:0]		awskid_prot, m_axi_awprot;
	wire	[LGFLEN:0]	bfill;
	reg	[LGFLEN:0]	write_count;
	reg	[1:0]		write_resp;
	//
	reg	[C_AXI_ID_WIDTH-1:0]	write_id, write_bid, write_retid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	write_addr;
	wire	[C_AXI_ID_WIDTH-1:0]	awskid_awid;
	wire	[C_AXI_ADDR_WIDTH-1:0]	awskid_awaddr, next_waddr;
	reg			write_request, write_topofburst,
				write_beat_bvalid;
	reg	[3-1:0]		write_size;
	reg	[2-1:0]		write_burst;
	reg	[8-1:0]		write_len, write_awlen;
	wire	[8-1:0]		awskid_awlen;
	wire	[2-1:0]		awskid_awburst;
	wire	[3-1:0]		awskid_awsize;
	wire			awskid_awlock;
	//
	reg			write_top_beat;


	//
	// Incoming write address requests must go through a skidbuffer.  By
	// keeping OPT_OUTREG == 0, this shouldn't cost us any time, but should
	// instead buy us the ability to keep AWREADY high even if for reasons
	// we can't act on AWVALID & AWREADY on the same cycle
	skidbuffer #(.OPT_OUTREG(0),
			.DW(C_AXI_ID_WIDTH+AW+8+3+2+1+3))
	awskid(	.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID),
			.o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
				S_AXI_AWSIZE, S_AXI_AWBURST,
				S_AXI_AWLOCK, S_AXI_AWPROT }),
		.o_valid(awskid_valid), .i_ready(write_awskidready),
			.o_data({ awskid_awid, awskid_awaddr, awskid_awlen,
				awskid_awsize, awskid_awburst, awskid_awlock,
				awskid_prot }));

	//
	// On any write address request (post-skidbuffer), copy down the details
	// of that request.  Once these details are valid (i.e. on the next
	// clock), S_AXI_WREADY will be true.
	always @(posedge S_AXI_ACLK)
	if (awskid_valid && write_awskidready)
	begin
		write_id    <= awskid_awid;
		write_addr  <= awskid_awaddr;
		write_size  <= awskid_awsize;
		write_awlen <= awskid_awlen;
		write_burst <= awskid_awburst;
		// write_lock  <= awskid_awlock;
	end else if (S_AXI_WVALID && S_AXI_WREADY)
		// Following each write beat, we need to update our address
		write_addr <= next_waddr;

	//
	// Given the details of the address request, get the next address to
	// write to.
	axi_addr #(.AW(C_AXI_ADDR_WIDTH), .DW(C_AXI_DATA_WIDTH))
	get_next_write_address(write_addr,
			write_size, write_burst, write_awlen, next_waddr);


	//
	// Count through the beats of the burst in write_len.  write_topofburst
	// indicates the first beat in any new burst, but will be zero for all
	// subsequent burst beats.  write_request is true anytime we are trying
	// to write.
	initial	write_request    = 1'b0;
	initial	write_topofburst = 1'b1;
	initial	write_len        = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		write_request    <= 1'b0;
		write_topofburst <= 1'b1;
		write_len        <= 0;
	end else if (awskid_valid && write_awskidready)
	begin
		write_request    <= 1'b1;
		write_topofburst <= 1'b1;
		write_len        <= awskid_awlen;
	end else if (S_AXI_WVALID && S_AXI_WREADY)
	begin
		write_topofburst <= 1'b0;
		if (S_AXI_WLAST)
			write_request <= 1'b0;
		if (write_len > 0)
			write_len <= write_len - 1;
	end

	// Decode our incoming address in order to determine the next
	// slave the address addresses
	addrdecode #(.AW(AW), .DW(3), .NS(NS),
		.SLAVE_ADDR(SLAVE_ADDR),
		.SLAVE_MASK(SLAVE_MASK),
		.OPT_REGISTERED(1'b1))
	wraddr(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(awskid_valid && write_awskidready), .o_stall(awskd_stall),
			// .i_addr(awskid_valid && write_awskidready
			//	? awskid_awaddr : next_waddr),
			.i_addr(awskid_awaddr),
			.i_data(awskid_prot),
		.o_valid(dcd_awvalid), .i_stall(!S_AXI_WVALID),
			.o_decode(raw_wdecode), .o_addr(m_awaddr),
			.o_data(m_axi_awprot));

	// We only do our decode on the address request.  We need the decoded
	// values long after the top of the burst.  Therefore, let's use
	// dcd_awvalid to know we have a valid output from the decoder and
	// then we'll latch that (register it really) for the rest of the burst
	always @(posedge S_AXI_ACLK)
	if (dcd_awvalid)
		last_wdecode <= raw_wdecode;

	always @(*)
	begin
		if (dcd_awvalid)
			wdecode = raw_wdecode;
		else
			wdecode = last_wdecode;
	end

	//
	// It's now time to create our write request for the slave.  Slave
	// writes take place on the clock after address valid is true as long
	// as S_AXI_WVALID is true.  This places combinatorial logic onto the
	// outgoing AWVALID.  The sign that we are in the middle of a burst
	// will specifically be that WREADY is true.
	//

	//
	// If there were any part of this algorithm I disliked it would be the
	// AWVALID logic here.  It shouldn't nearly be this loaded.
	assign	S_AXI_WREADY  = write_request;
	assign	M_AXI_AWVALID = (S_AXI_WVALID && write_request
			&& (!locked_burst || locked_write)) ? wdecode[NS-1:0] : 0;
	assign	M_AXI_AWADDR  = write_addr;
	assign	M_AXI_AWPROT  = m_axi_awprot;
	assign	M_AXI_AWSIZE  = write_size;
	assign	M_AXI_WDATA   = S_AXI_WDATA;
	assign	M_AXI_WSTRB   = S_AXI_WSTRB;

	// We can accept a new value from the skid buffer as soon as the last
	// write value comes in, or equivalently if we are not in the middle
	// of a write.  This is all subject, of course, to our backpressure
	// FIFO not being full.
	assign	write_awskidready = ((S_AXI_WVALID&&S_AXI_WLAST)
						|| !S_AXI_WREADY) && !bfull;

	// Back out an index from our decoded slave value
	always @(*)
	begin
		write_windex = 0;
		for(k=0; k<NS; k=k+1)
		if (wdecode[k])
			write_windex = write_windex | k[LGNS-1:0];
	end

	always @(posedge S_AXI_ACLK)
	begin
		write_bindex <= write_windex;
		write_no_index <= wdecode[NS];
	end

	always @(posedge S_AXI_ACLK)
	// if (write_top_of_burst) // -- not necessary
		write_bid <= write_id;

	// write_bvalid will be true one clock after the last write is accepted.
	// This is the internal signal that would've come from a subordinate
	// slave's BVALID, save that we are generating it internally.
	initial	{ write_response, write_bvalid } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ write_response, write_bvalid } <= 0;
	else
		{ write_response, write_bvalid } <= { write_bvalid,
			(S_AXI_WVALID && S_AXI_WREADY&& S_AXI_WLAST) };

	//
	// Examine write beats, not just write bursts
	always @(posedge S_AXI_ACLK)
	begin
		write_top_beat    <= write_topofburst;
		write_beat_bvalid <= S_AXI_WVALID && S_AXI_WREADY;
	end

	// The response from any burst should be an DECERR (interconnect
	// error) if ever the addressed slave doesn't exist in our address map.
	// This is sticky: any attempt to generate a request to a non-existent
	// slave will generate an interconnect error.  Likewise, if the slave
	// ever returns a slave error, we'll propagate it back in the burst
	// return.  Finally, on an exclusive access burst, we'll return EXOKAY
	// if we could write the values.
	always @(posedge S_AXI_ACLK)
	if (write_beat_bvalid)
	begin
		if (write_no_index)
			write_resp <= INTERCONNECT_ERROR;
		else if (M_AXI_BRESP[2*write_bindex])
			write_resp <= { 1'b1, (write_top_beat)
						? 1'b0 : write_resp[0] };
		else if (write_top_beat || !write_resp[1])
			write_resp <= { 1'b0, (write_top_beat && locked_burst && locked_write) };
	end

	always @(posedge S_AXI_ACLK)
		write_retid <= write_bid;

	//
	// The pseudo-FIFO for the write side.  This counter will let us know
	// if any write response will ever overflow our write response FIFO,
	// allowing us to be able to confidently deal with any backpressure.
	initial	write_count = 0;
	initial	bfull = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		write_count <= 0;
		bfull <= 0;
	end else case({ (awskid_valid && write_awskidready),
			(S_AXI_BVALID & S_AXI_BREADY) })
	2'b01:	begin
		write_count <= write_count - 1;
		bfull <= 1'b0;
		end
	2'b10:	begin
		write_count <= write_count + 1;
		bfull <= (&write_count[LGFLEN-1:0]);
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
		assert(write_count <= { 1'b1, {(LGFLEN){1'b0}} });
	always @(*)
		assert(bfull == (write_count == { 1'b1, {(LGFLEN){1'b0}} }));
`endif

	//
	// Backpressure FIFO on write response returns
	sfifo #(.BW(C_AXI_ID_WIDTH+2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	bfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(write_response), .i_data({ write_retid, write_resp }),
			.o_full(bffull), .o_fill(bfill),
		.i_rd(S_AXI_BVALID && S_AXI_BREADY),
			.o_data({ S_AXI_BID, S_AXI_BRESP }),
			.o_empty(bempty));

	assign	S_AXI_BVALID = !bempty;

`ifdef	FORMAL
	always @(*)
		assert(write_count == bfill
			+ (write_response ? 1:0)
			+ (write_bvalid ? 1:0)
			+ (write_request ? 1:0));

	always @(*)
		assert(!bffull || !write_bvalid);
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire				rempty, rdfull;
	wire	[LGFLEN:0]		rfill;
	reg	[LGNS-1:0]		read_index, last_read_index;
	reg	[1:0]			read_resp;
	reg	[DW-1:0]		read_rdata;
	wire				read_rwait, arskd_stall;
	reg				read_rvalid, read_result, read_no_index;
	wire	[AW-1:0]		m_araddr;
	reg	[AW-1:0]		araddr;
	reg	[3-1:0]			arprot;
	wire	[NS:0]			raw_rdecode;

	reg	[C_AXI_ID_WIDTH-1:0]	arid, read_rvid, read_retid;
	reg	[3-1:0]			arsize;
	reg	[2-1:0]			arburst;
	reg				arlock, read_rvlock;
	reg				read_rvlast, read_retlast;
	reg	[8-1:0]			arlen, rlen;
	wire	[C_AXI_ADDR_WIDTH-1:0]	next_araddr;
	wire				issue_read;
	reg			read_full;
	reg	[LGFLEN:0]	read_count;
	reg			arvalid;
	reg	[NS:0]		last_rdecode, rdecode;


	//
	// Copy the burst information, for use in determining the next address
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARVALID && S_AXI_ARREADY)
	begin
		araddr  <= S_AXI_ARADDR;
		arid    <= S_AXI_ARID;
		arlen   <= S_AXI_ARLEN;
		arsize  <= S_AXI_ARSIZE;
		arburst <= S_AXI_ARBURST;
		arlock  <= S_AXI_ARLOCK;
		arprot  <= S_AXI_ARPROT;
	end else if (issue_read)
		araddr  <= next_araddr;

	// Count the number of remaining items in a burst.  Note that rlen
	// counts from N-1 to 0, not from N to 1.
	initial	rlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rlen   <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY)
		rlen    <= S_AXI_ARLEN;
	else if (issue_read && (rlen > 0))
		rlen <= rlen - 1;

	// Should the slave M_AXI_ARVALID be true in general?  Based upon
	// rlen above, but still needs to be gated across all slaves.
	initial	arvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		arvalid <= 1'b0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY)
		arvalid <= 1'b1;
	else if (issue_read && (rlen == 0))
		arvalid <= 1'b0;

	// Get the next AXI address
	axi_addr #(.AW(C_AXI_ADDR_WIDTH), .DW(C_AXI_DATA_WIDTH))
	get_next_read_address(araddr ,
			arsize, arburst, arlen, next_araddr);

	//
	// Decode which slave is being addressed by this read.
	wire	[0:0]	unused_pin;
	addrdecode #(.AW(AW), .DW(1), .NS(NS),
		.SLAVE_ADDR(SLAVE_ADDR),
		.SLAVE_MASK(SLAVE_MASK),
		.OPT_REGISTERED(1'b1))
	rdaddr(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_ARVALID && S_AXI_ARREADY || rlen>0),
			// Warning: there's no skid on this stall
			.o_stall(arskd_stall),
			.i_addr((S_AXI_ARVALID & S_AXI_ARREADY)
				? S_AXI_ARADDR : next_araddr),
			.i_data(1'b0),
		.o_valid(read_rwait), .i_stall(!issue_read),
			.o_decode(raw_rdecode), .o_addr(m_araddr),
			.o_data(unused_pin[0]));

	//
	// We want the value from the decoder on the first clock cycle.  It
	// may not be valid after that, so we'll hold on to it in last_rdecode
	initial	last_rdecode = 0;
	always @(posedge S_AXI_ACLK)
	if (read_rwait)
		last_rdecode <= raw_rdecode;

	always @(*)
	if (read_rwait)
		rdecode = raw_rdecode;
	else
		rdecode = last_rdecode;

	//
	// Finally, issue our read request any time the FIFO isn't full
	assign	issue_read    = !read_full;

	assign	M_AXI_ARVALID = issue_read ? rdecode[NS-1:0] : 0;
	assign	M_AXI_ARADDR  = m_araddr;
	assign	M_AXI_ARPROT  = arprot;
	assign	M_AXI_ARSIZE  = arsize;

	//
	// read_rvalid would be the RVALID response from the slave that would
	// be returned if we checked it.  read_result is the same thing--one
	// clock later.
	initial	{ read_result, read_rvalid } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ read_result, read_rvalid } <= 2'b00;
	else
		{ read_result, read_rvalid } <= { read_rvalid,
				(arvalid&issue_read) };

	// On the same clock when rvalid is true, we'll also want to know
	// if RLAST should be true (decoded here, not in the slave), and
	// whether or not the transaction is locked.  These values are valid
	// any time read_rvalid is true.
	always @(posedge S_AXI_ACLK)
	if (arvalid && issue_read)
	begin
		read_rvid   <= arid;
		read_rvlast <= (rlen == 0);
		read_rvlock <= OPT_EXCLUSIVE_ACCESS && arlock && lock_valid;
	end

	// read_result is true one clock after read_rvalid is true.  Copy
	// the ID and LAST values into this pipeline clock cycle
	always @(posedge S_AXI_ACLK)
	begin
		read_retid   <= read_rvid;
		read_retlast <= read_rvlast;
	end

	//
	// Decode the read value.
	//

	//
	// First step is to calculate the index of the slave
	always @(*)
	begin
		read_index = 0;

		for(k=0; k<NS; k=k+1)
		if (rdecode[k])
			read_index = read_index | k[LGNS-1:0];
	end

	//
	// Keep this index into the RVALID cycle
	always @(posedge S_AXI_ACLK)
		last_read_index <= read_index;

	// read_no_index is a flag to indicate that no slave was indexed.
	always @(posedge S_AXI_ACLK)
		read_no_index <= rdecode[NS];

	// Now we can use last_read_index to determine the return data.
	// read_rdata will be valid on the same clock $past(RVALID) or
	// read_return cycle
	always @(posedge S_AXI_ACLK)
		read_rdata <= M_AXI_RDATA[DW*last_read_index +: DW];

	//
	// As with read_rdata, read_resp is the response from the slave
	always @(posedge S_AXI_ACLK)
	if (read_no_index)
		read_resp <= INTERCONNECT_ERROR;
	else if (M_AXI_RRESP[2*last_read_index + 1])
		read_resp <= SLVERR;	// SLVERR
	else if (OPT_EXCLUSIVE_ACCESS && read_rvlock)
		read_resp <= EXOKAY;	// Exclusive access Okay
	else
		read_resp <= OKAY;	// OKAY

	//
	// Since we can't allow the incoming requests to overflow in the
	// presence of any back pressure, let's create a phantom FIFO here
	// counting the number of values either in the final pipeline or in
	// final read FIFO.  If read_full is true, the FIFO is full and we
	// cannot move any more data forward.
	initial	{ read_count, read_full } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ read_count, read_full } <= 0;
	else case({ read_rwait && issue_read, S_AXI_RVALID & S_AXI_RREADY})
	2'b10: begin
		read_count <= read_count + 1;
		read_full  <= &read_count[LGFLEN-1:0];
		end
	2'b01: begin
		read_count <= read_count - 1;
		read_full <= 1'b0;
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
		assert(read_count <= { 1'b1, {(LGFLEN){1'b0}} });
	always @(*)
		assert(read_full == (read_count == { 1'b1, {(LGFLEN){1'b0}} }));
`endif
	assign	S_AXI_ARREADY = (rlen == 0) && !read_full;

	//
	// Send the return results through a synchronous FIFO to handle
	// back-pressure.  Doing this costs us one clock of latency.
	sfifo #(.BW(C_AXI_ID_WIDTH+DW+1+2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	rfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(read_result), .i_data({ read_retid, read_rdata,
						read_retlast, read_resp }),
			.o_full(rdfull), .o_fill(rfill),
		.i_rd(S_AXI_RVALID && S_AXI_RREADY),
			.o_data({ S_AXI_RID, S_AXI_RDATA, S_AXI_RLAST, S_AXI_RRESP }),.o_empty(rempty));

	assign	S_AXI_RVALID = !rempty;

	////////////////////////////////////////////////////////////////////////
	//
	// Exclusive access / Bus locking logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_EXCLUSIVE_ACCESS)
	begin : EXCLUSIVE_ACCESS

		reg	[AW-1:0]	lock_addr, lock_last;
		reg	[4-1:0]		lock_len;
		reg	[3-1:0]		lock_size;

		initial	lock_valid   = 1'b0;
		initial	locked_burst = 1'b0;
		initial	locked_write = 1'b0;
		always @(posedge S_AXI_ACLK)
		begin

			//
			// Step one: Set the lock_valid signal.  This means
			// that a read request has been successful requesting
			// the lock for this address.
			//
			if (awskid_valid && write_awskidready)
			begin
				// On any write to the value inside our lock
				// range, disable the lock_valid signal
				if ((awskid_awaddr
					+ ({ {(AW-4){1'b0}},awskid_awlen[3:0]} << S_AXI_AWSIZE)
						>= lock_addr)
					&&(S_AXI_AWADDR <= lock_last))
					lock_valid <= 0;
			end

			if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLOCK)
			begin
				lock_valid <= !locked_write;
				lock_addr  <= S_AXI_ARADDR;
				lock_size  <= S_AXI_ARSIZE;
				lock_len   <= S_AXI_ARLEN[3:0];
				lock_last  <= S_AXI_ARADDR
					+ ({ {(AW-4){1'b0}}, lock_len }
							<< S_AXI_ARSIZE);
			end

			if (awskid_valid && write_awskidready)
			begin
				locked_burst <= 1'b0;
				locked_write <= awskid_awlock;

				if (awskid_awlock)
				begin
					locked_burst <= lock_valid;
					if (lock_addr != awskid_awaddr)
						locked_burst <= 1'b0;
					if (lock_size != awskid_awsize)
						locked_burst <= 1'b0;
					if ({ 4'h0, lock_len } != awskid_awlen)
						locked_burst <= 1'b0;
				end

				// Write if !locked_write || write_burst
				// EXOKAY on locked_write && write_burst
				// OKAY on all other writes where the slave
				//   does not assert an error
			end else if (S_AXI_WVALID && S_AXI_WREADY && S_AXI_WLAST)
				locked_burst <= 1'b0;

			if (!S_AXI_ARESETN)
			begin
				lock_valid  <= 1'b0;
				locked_burst <= 1'b0;
			end
		end
	end else begin : NO_EXCLUSIVE_ACCESS

		// Keep track of whether or not the current burst requests
		// exclusive access or not.  locked_write is an important
		// signal used to make certain that we do not write to our
		// slave on any locked write requests.  (Shouldn't happen,
		// since we aren't returning any EXOKAY's from reads ...)
		always @(posedge S_AXI_ACLK)
		if (awskid_valid && write_awskidready)
			locked_write <= awskid_awlock;
		else if (S_AXI_WVALID && S_AXI_WREADY && S_AXI_WLAST)
			locked_write <= 1'b0;

		always @(*)
			locked_burst <= 1'b0;

		always @(*)
			lock_valid = 1'b0;
	end endgenerate

	////////////////////////////////////////////////////////////////////////

	// Make Verilator happy
	//
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
			S_AXI_AWCACHE, S_AXI_ARCACHE,
			S_AXI_AWQOS,   S_AXI_ARQOS,
			dcd_awvalid, m_awaddr, unused_pin,
			bffull, rdfull, bfill, rfill,
			awskd_stall, arskd_stall };
	// verilator lint_on  UNUSED

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal verification properties
//
// The following are a subset of the formal properties used to verify this
// module.
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = LGFLEN+9;

	//
	// ...
	//

	faxi_slave #(	.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.F_AXI_MAXDELAY(5),
			.F_LGDEPTH(F_LGDEPTH))
		properties (
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awid(   S_AXI_AWID),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awlen(  S_AXI_AWLEN),
		.i_axi_awsize( S_AXI_AWSIZE),
		.i_axi_awburst(S_AXI_AWBURST),
		.i_axi_awlock( S_AXI_AWLOCK),
		.i_axi_awcache(S_AXI_AWCACHE),
		.i_axi_awprot( S_AXI_AWPROT),
		.i_axi_awqos(  S_AXI_AWQOS),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		.i_axi_wlast( S_AXI_WLAST),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bid(   S_AXI_BID),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_arid(   S_AXI_ARID),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arlen(  S_AXI_ARLEN),
		.i_axi_arsize( S_AXI_ARSIZE),
		.i_axi_arburst(S_AXI_ARBURST),
		.i_axi_arlock( S_AXI_ARLOCK),
		.i_axi_arcache(S_AXI_ARCACHE),
		.i_axi_arprot( S_AXI_ARPROT),
		.i_axi_arqos(  S_AXI_ARQOS),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rid(   S_AXI_RID),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rlast( S_AXI_RLAST),
		.i_axi_rresp( S_AXI_RRESP)
		//
		// ...
		//
		);

	//
	// ...
	//

	always @(*)
	if (!OPT_EXCLUSIVE_ACCESS)
	begin
		assert(!S_AXI_BVALID || S_AXI_BRESP != EXOKAY);
		assert(!S_AXI_RVALID || S_AXI_RRESP != EXOKAY);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Properties necessary to pass induction
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assert($onehot0(M_AXI_AWVALID));

	always @(*)
		assert($onehot0(M_AXI_ARVALID));

	//
	//
	// Write properties
	//
	//

	always @(*)
	if (S_AXI_WVALID && S_AXI_WREADY)
	begin
		if (locked_burst && !locked_write)
			assert(M_AXI_AWVALID == 0);
		else if (wdecode[NS])
			assert(M_AXI_AWVALID == 0);
		else begin
			assert($onehot(M_AXI_AWVALID));
			assert(M_AXI_AWVALID == wdecode[NS-1:0]);
		end
	end else
		assert(M_AXI_AWVALID == 0);

	//
	// ...
	//

	//
	//
	// Read properties
	//
	//

	//
	// ...
	//


	////////////////////////////////////////////////////////////////////////
	//
	// Simplifying (careless) assumptions
	//
	// Caution: these might void your proof
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	[0:0]	F_CHECK_WRITES = 1'b1;
	localparam	[0:0]	F_CHECK_READS  = 1'b1;

	generate if (!F_CHECK_WRITES)
	begin
		always @(*)
			assume(!S_AXI_AWVALID);
		always @(*)
			assert(!S_AXI_BVALID);
		always @(*)
			assert(!M_AXI_AWVALID);

		// ...
	end endgenerate

	generate if (!F_CHECK_READS)
	begin
		always @(*)
			assume(!S_AXI_ARVALID);
		always @(*)
			assert(!S_AXI_RVALID);
		always @(*)
			assert(M_AXI_ARVALID == 0);
		always @(*)
			assert(rdecode == 0);
		// ...
	end endgenerate

	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_arvalids, cvr_awvalids, cvr_reads, cvr_writes;
	(* anyconst *)	reg	cvr_burst;

	always @(*)
	if (cvr_burst && S_AXI_AWVALID)
		assume(S_AXI_AWLEN > 2);

	always @(*)
	if (cvr_burst && S_AXI_ARVALID)
		assume(S_AXI_ARLEN > 2);

	initial	cvr_awvalids = 0;
	always @(posedge S_AXI_ACLK)
	if (!cvr_burst || !S_AXI_ARESETN)
		cvr_awvalids <= 0;
	else if (S_AXI_AWVALID && S_AXI_AWREADY && !(&cvr_awvalids))
		cvr_awvalids <= cvr_awvalids + 1;

	initial	cvr_arvalids = 0;
	always @(posedge S_AXI_ACLK)
	if (!cvr_burst || !S_AXI_ARESETN)
		cvr_arvalids <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY && !(&cvr_arvalids))
		cvr_arvalids <= cvr_arvalids + 1;

	initial	cvr_writes = 0;
	always @(posedge S_AXI_ACLK)
	if (!cvr_burst || !S_AXI_ARESETN)
		cvr_writes <= 0;
	else if (S_AXI_BVALID && S_AXI_BREADY && !(&cvr_writes))
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_reads <= 0;
	else if (S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST
				&& !(&cvr_arvalids))
		cvr_reads <= cvr_reads + 1;

	generate if (F_CHECK_WRITES)
	begin : COVER_WRITES

		always @(*)
			cover(cvr_awvalids > 2);

		always @(*)
			cover(cvr_writes > 2);

		always @(*)
			cover(cvr_writes > 4);
	end endgenerate

	generate if (F_CHECK_READS)
	begin : COVER_READS
		always @(*)
			cover(cvr_arvalids > 2);

		always @(*)
			cover(cvr_reads > 2);

		always @(*)
			cover(cvr_reads > 4);
	end endgenerate

	always @(*)
		cover((cvr_writes > 2) && (cvr_reads > 2));

	generate if (OPT_EXCLUSIVE_ACCESS)
	begin : COVER_EXCLUSIVE_ACCESS

		always @(*)
			cover(S_AXI_BVALID && S_AXI_BRESP == EXOKAY);

	end endgenerate
`endif
endmodule
