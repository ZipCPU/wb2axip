////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axixbar.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Create a full crossbar between NM AXI sources (masters), and NS
//		AXI slaves.  Every master can talk to any slave, provided it
//	isn't already busy.
//
// Performance:	This core has been designed with the goal of being able to push
//		one transaction through the interconnect, from any master to
//	any slave, per clock cycle.  This may perhaps be its most unique
//	feature.  While throughput is good, latency is something else.
//
//	The arbiter requires a clock to switch, then another clock to send data
//	downstream.  This creates a minimum two clock latency up front.  The
//	return path suffers another clock of latency as well, placing the
//	minimum latency at four clocks.  The minimum write latency is at
//	least one clock longer, since the write data must wait for the write
//	address before proceeeding.
//
// Usage:	To use, you must first set NM and NS to the number of masters
//	and the number of slaves you wish to connect to.  You then need to
//	adjust the addresses of the slaves, found SLAVE_ADDR array.  Those
//	bits that are relevant in SLAVE_ADDR to then also be set in SLAVE_MASK.
//	Adjusting the data and address widths go without saying.
//
//	Lower numbered masters are given priority in any "fight".
//
//	Channel grants are given on the condition that 1) they are requested,
//	2) no other channel has a grant, 3) all of the responses have been
//	received from the current channel, and 4) the internal counters are
//	not overflowing.
//
//	The core limits the number of outstanding transactions on any channel to
//	1<<LGMAXBURST-1.
//
//	Channel grants are lost 1) after OPT_LINGER clocks of being idle, or
//	2) when another master requests an idle (but still lingering) channel
//	assignment, or 3) once all the responses have been returned to the
//	current channel, and the current master is requesting another channel.
//
//	A special slave is allocated for the case of no valid address.
//
//	Since the write channel has no address information, the write data
//	channel always be delayed by at least one clock from the write address
//	channel.
//
//	If OPT_LOWPOWER is set, then unused values will be set to zero.
//	This can also be used to help identify relevant values within any
//	trace.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
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
`default_nettype none
//
module	axixbar #(
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 32,
		parameter integer C_AXI_ID_WIDTH = 2,
		parameter	NM = 4,
		parameter	NS = 8,
		//
		// IW, AW, and DW, are short-hand abbreviations used locally.
		localparam	IW = C_AXI_ID_WIDTH,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		//
		// SLAVE_ADDR is an array of addresses, describing each of
		// the slave channels.  It works tightly with SLAVE_MASK,
		// so that when (ADDR & MASK == ADDR), the channel in question
		// has been requested.
		//
		// It is an internal in the setup of this core to doubly map
		// an address, such that (addr & SLAVE_MASK[k])==SLAVE_ADDR[k]
		// for two separate values of k.
		//
		// Any attempt to access an address that is a hole in this
		// address list will result in a returned xRESP value of
		// INTERCONNECT_ERROR (2'b11)
		parameter	[NS*AW-1:0]	SLAVE_ADDR = {
			3'b111,  {(AW-3){1'b0}},
			3'b110,  {(AW-3){1'b0}},
			3'b101,  {(AW-3){1'b0}},
			3'b100,  {(AW-3){1'b0}},
			3'b011,  {(AW-3){1'b0}},
			3'b010,  {(AW-3){1'b0}},
			4'b0001, {(AW-4){1'b0}},
			4'b0000, {(AW-4){1'b0}} },
		//
		// SLAVE_MASK: is an array, much like SLAVE_ADDR, describing
		// which of the bits in SLAVE_ADDR are relevant.  It is
		// important to maintain for every slave that
		// 	(~SLAVE_MASK[i] & SLAVE_ADDR[i]) == 0.
		// Verilator lint_off WIDTH
		parameter	[NS*AW-1:0]	SLAVE_MASK =
			(NS <= 1) ? { 4'b1111, {(AW-4){1'b0}}}
			: { {(NS-2){ 3'b111, {(AW-3){1'b0}} }},
				{(2){ 4'b1111, {(AW-4){1'b0}}}} },
		// Verilator lint_on  WIDTH
		//
		// OPT_LOWPOWER: If set, it forces all unused values to zero,
		// preventing them from unnecessarily toggling.  This will
		// raise the logic count of the core, but might also lower
		// the power used by the interconnect and the bus driven wires
		// which (in my experience) tend to have a high fan out.
		parameter [0:0]	OPT_LOWPOWER = 0,
		//
		// OPT_LINGER: Set this to the number of clocks an idle
		// channel shall be left open before being closed.  Once
		// closed, it will take a minimum of two clocks before the
		// channel can be opened and data transmitted through it again.
		parameter	OPT_LINGER = 4,
		//
		// OPT_QOS: If set, the QOS transmission values will be honored
		// when determining who wins arbitration for accessing a given
		// slave.  (This feature is not yet implemented)
		// parameter [0:0]	OPT_QOS = 1,
		//
		// LGMAXBURST: Specifies the log based two of the maximum
		// number of bursts transactions.  This is different from the
		// maximum number of outstanding beats.
		parameter	LGMAXBURST = 3
	) (
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		input	wire	[NM*C_AXI_ID_WIDTH-1:0]		S_AXI_AWID,
		input	wire	[NM*C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[NM*8-1:0]			S_AXI_AWLEN,
		input	wire	[NM*3-1:0]			S_AXI_AWSIZE,
		input	wire	[NM*2-1:0]			S_AXI_AWBURST,
		input	wire	[NM-1:0]			S_AXI_AWLOCK,
		input	wire	[NM*4-1:0]			S_AXI_AWCACHE,
		input	wire	[NM*3-1:0]			S_AXI_AWPROT,
		input	wire	[NM*4-1:0]			S_AXI_AWQOS,
		input	wire	[NM-1:0]			S_AXI_AWVALID,
		output	wire	[NM-1:0]			S_AXI_AWREADY,
		//
		input	wire	[NM*C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire	[NM*C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		input	wire	[NM-1:0]			S_AXI_WLAST,
		input	wire	[NM-1:0]			S_AXI_WVALID,
		output	wire	[NM-1:0]			S_AXI_WREADY,
		//
		output	wire	[NM*C_AXI_ID_WIDTH-1:0]		S_AXI_BID,
		output	wire	[NM*2-1:0]			S_AXI_BRESP,
		output	wire	[NM-1:0]			S_AXI_BVALID,
		input	wire	[NM-1:0]			S_AXI_BREADY,
		//
		input	wire	[NM*C_AXI_ID_WIDTH-1:0]		S_AXI_ARID,
		input	wire	[NM*C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[NM*8-1:0]			S_AXI_ARLEN,
		input	wire	[NM*3-1:0]			S_AXI_ARSIZE,
		input	wire	[NM*2-1:0]			S_AXI_ARBURST,
		input	wire	[NM-1:0]			S_AXI_ARLOCK,
		input	wire	[NM*4-1:0]			S_AXI_ARCACHE,
		input	wire	[NM*3-1:0]			S_AXI_ARPROT,
		input	wire	[NM*4-1:0]			S_AXI_ARQOS,
		input	wire	[NM-1:0]			S_AXI_ARVALID,
		output	wire	[NM-1:0]			S_AXI_ARREADY,
		//
		output	wire	[NM*C_AXI_ID_WIDTH-1:0]		S_AXI_RID,
		output	wire	[NM*C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire	[NM*2-1:0]			S_AXI_RRESP,
		output	wire	[NM-1:0]			S_AXI_RLAST,
		output	wire	[NM-1:0]			S_AXI_RVALID,
		input	wire	[NM-1:0]			S_AXI_RREADY,
		//
		//
		//
		output	wire	[NS*C_AXI_ID_WIDTH-1:0]		M_AXI_AWID,
		output	wire	[NS*C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[NS*8-1:0]			M_AXI_AWLEN,
		output	wire	[NS*3-1:0]			M_AXI_AWSIZE,
		output	wire	[NS*2-1:0]			M_AXI_AWBURST,
		output	wire	[NS-1:0]			M_AXI_AWLOCK,
		output	wire	[NS*4-1:0]			M_AXI_AWCACHE,
		output	wire	[NS*3-1:0]			M_AXI_AWPROT,
		output	wire	[NS*4-1:0]			M_AXI_AWQOS,
		output	wire	[NS-1:0]			M_AXI_AWVALID,
		input	wire	[NS-1:0]			M_AXI_AWREADY,
		//
		//
		output	wire	[NS*C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire	[NS*C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire	[NS-1:0]			M_AXI_WLAST,
		output	wire	[NS-1:0]			M_AXI_WVALID,
		input	wire	[NS-1:0]			M_AXI_WREADY,
		//
		input	wire	[NS*C_AXI_ID_WIDTH-1:0]		M_AXI_BID,
		input	wire	[NS*2-1:0]			M_AXI_BRESP,
		input	wire	[NS-1:0]			M_AXI_BVALID,
		output	wire	[NS-1:0]			M_AXI_BREADY,
		//
		output	wire	[NS*C_AXI_ID_WIDTH-1:0]		M_AXI_ARID,
		output	wire	[NS*C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[NS*8-1:0]			M_AXI_ARLEN,
		output	wire	[NS*3-1:0]			M_AXI_ARSIZE,
		output	wire	[NS*2-1:0]			M_AXI_ARBURST,
		output	wire	[NS-1:0]			M_AXI_ARLOCK,
		output	wire	[NS*4-1:0]			M_AXI_ARCACHE,
		output	wire	[NS*4-1:0]			M_AXI_ARQOS,
		output	wire	[NS*3-1:0]			M_AXI_ARPROT,
		output	wire	[NS-1:0]			M_AXI_ARVALID,
		input	wire	[NS-1:0]			M_AXI_ARREADY,
		//
		//
		input	wire	[NS*C_AXI_ID_WIDTH-1:0]		M_AXI_RID,
		input	wire	[NS*C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire	[NS*2-1:0]			M_AXI_RRESP,
		input	wire	[NS-1:0]			M_AXI_RLAST,
		input	wire	[NS-1:0]			M_AXI_RVALID,
		output	wire	[NS-1:0]			M_AXI_RREADY
	);
	//
	// Local parameters, derived from those above
	localparam	LGLINGER = (OPT_LINGER>1) ? $clog2(OPT_LINGER+1) : 1;
	//
	localparam	LGNM = (NM>1) ? $clog2(NM) : 1;
	localparam	LGNS = (NS>1) ? $clog2(NS+1) : 1;
	//
	// In order to use indexes, and hence fully balanced mux trees, it helps
	// to make certain that we have a power of two based lookup.  NMFULL
	// is the number of masters in this lookup, with potentially some
	// unused extra ones.  NSFULL is defined similarly.
	localparam	NMFULL = (NM>1) ? (1<<LGNM) : 1;
	localparam	NSFULL = (NS>1) ? (1<<LGNS) : 2;
	//
	localparam [1:0] INTERCONNECT_ERROR = 2'b11;
	localparam [0:0]	OPT_SKID_INPUT = 0;
	localparam [0:0]	OPT_BUFFER_DECODER = 1;

	genvar	N,M;
	integer	iN, iM;

	reg	[NSFULL-1:0]	wrequest		[0:NM-1];
	reg	[NSFULL-1:0]	rrequest		[0:NM-1];
	reg	[NSFULL-1:0]	wrequested		[0:NM];
	reg	[NSFULL-1:0]	rrequested		[0:NM];
	reg	[NS:0]		wgrant			[0:NM-1];
	reg	[NS:0]		rgrant			[0:NM-1];
	reg	[NM-1:0]	mwgrant;
	reg	[NM-1:0]	mrgrant;
	reg	[NS-1:0]	swgrant;
	reg	[NS-1:0]	srgrant;

	// verilator lint_off UNUSED
	wire	[LGMAXBURST-1:0]	w_mawpending	[0:NM-1];
	wire	[LGMAXBURST-1:0]	w_mrpending	[0:NM-1];
	// verilator lint_on  UNUSED
	reg	[NM-1:0]		mwfull;
	reg	[NM-1:0]		mrfull;
	reg	[NM-1:0]		mwempty;
	reg	[NM-1:0]		mrempty;
	//
	reg	[LGNS-1:0]		mwindex	[0:NMFULL-1];
	reg	[LGNS-1:0]		mrindex	[0:NMFULL-1];
	reg	[LGNM-1:0]		swindex	[0:NSFULL-1];
	reg	[LGNM-1:0]		srindex	[0:NSFULL-1];

	(* keep *) reg	[NM-1:0]		wdata_expected;

	// The shadow buffers
	reg	[NMFULL-1:0]	m_awvalid, m_wvalid, m_arvalid;
	reg	[NM-1:0]	dcd_awvalid, dcd_arvalid;

	wire	[C_AXI_ID_WIDTH-1:0]		m_awid		[0:NMFULL-1];
	wire	[C_AXI_ADDR_WIDTH-1:0]		m_awaddr	[0:NMFULL-1];
	wire	[7:0]				m_awlen		[0:NMFULL-1];
	wire	[2:0]				m_awsize	[0:NMFULL-1];
	wire	[1:0]				m_awburst	[0:NMFULL-1];
	wire	[NMFULL-1:0]			m_awlock;
	wire	[3:0]				m_awcache	[0:NMFULL-1];
	wire	[2:0]				m_awprot	[0:NMFULL-1];
	wire	[3:0]				m_awqos		[0:NMFULL-1];
	//
	reg	[C_AXI_ID_WIDTH-1:0]		r_wid		[0:NMFULL-1];
	wire	[C_AXI_DATA_WIDTH-1:0]		m_wdata		[0:NMFULL-1];
	wire	[C_AXI_DATA_WIDTH/8-1:0]	m_wstrb		[0:NMFULL-1];
	wire	[NMFULL-1:0]			m_wlast;

	wire	[C_AXI_ID_WIDTH-1:0]		m_arid		[0:NMFULL-1];
	wire	[C_AXI_ADDR_WIDTH-1:0]		m_araddr	[0:NMFULL-1];
	wire	[8-1:0]				m_arlen		[0:NMFULL-1];
	wire	[3-1:0]				m_arsize	[0:NMFULL-1];
	wire	[2-1:0]				m_arburst	[0:NMFULL-1];
	wire	[NMFULL-1:0]			m_arlock;
	wire	[4-1:0]				m_arcache	[0:NMFULL-1];
	wire	[2:0]				m_arprot	[0:NMFULL-1];
	wire	[3:0]				m_arqos		[0:NMFULL-1];
	//
	//
	reg	[NM-1:0]			berr_valid;
	reg	[IW-1:0]			berr_id		[0:NM-1];
	//
	reg	[NM-1:0]			rerr_none;
	reg	[NM-1:0]			rerr_last;
	reg	[8:0]				rerr_outstanding [0:NM-1];
	reg	[IW-1:0]			rerr_id		 [0:NM-1];

	wire	[NM-1:0]	skd_awvalid, skd_awstall;
	wire	[NM-1:0]	skd_arvalid, skd_arstall;
	wire	[IW-1:0]	skd_awid			[0:NM-1];
	wire	[AW-1:0]	skd_awaddr			[0:NM-1];
	wire	[8-1:0]		skd_awlen			[0:NM-1];
	wire	[3-1:0]		skd_awsize			[0:NM-1];
	wire	[2-1:0]		skd_awburst			[0:NM-1];
	wire	[NM-1:0]	skd_awlock;
	wire	[4-1:0]		skd_awcache			[0:NM-1];
	wire	[3-1:0]		skd_awprot			[0:NM-1];
	wire	[4-1:0]		skd_awqos			[0:NM-1];
	//
	wire	[IW-1:0]	skd_arid			[0:NM-1];
	wire	[AW-1:0]	skd_araddr			[0:NM-1];
	wire	[8-1:0]		skd_arlen			[0:NM-1];
	wire	[3-1:0]		skd_arsize			[0:NM-1];
	wire	[2-1:0]		skd_arburst			[0:NM-1];
	wire	[NM-1:0]	skd_arlock;
	wire	[4-1:0]		skd_arcache			[0:NM-1];
	wire	[3-1:0]		skd_arprot			[0:NM-1];
	wire	[4-1:0]		skd_arqos			[0:NM-1];

	reg	[NSFULL-1:0]	m_axi_awvalid;
	reg	[NSFULL-1:0]	m_axi_awready;
	reg	[AW-1:0]	m_axi_awaddr			[0:NSFULL-1];
	reg	[2-1:0]		m_axi_awburst			[0:NSFULL-1];
	reg	[3-1:0]		m_axi_awsize			[0:NSFULL-1];
	reg	[NSFULL-1:0]	m_axi_awlock;
	// Verilator lint_off UNUSED
	reg	[IW-1:0]	m_axi_awid	[0:NSFULL-1];
	reg	[7:0]		m_axi_awlen	[0:NSFULL-1];
	// Verilator lint_on  UNUSED

	reg	[NSFULL-1:0]	m_axi_wvalid;
	reg	[NSFULL-1:0]	m_axi_wready;
	reg	[NSFULL-1:0]	m_axi_wlast;
	reg	[NSFULL-1:0]	m_axi_bvalid;
	// Verilator lint_off UNUSED
	reg	[NSFULL-1:0]	m_axi_bready;
	// Verilator lint_on  UNUSED
	reg	[1:0]		m_axi_bresp	[0:NSFULL-1];
	reg	[IW-1:0]	m_axi_bid	[0:NSFULL-1];

	reg	[NSFULL-1:0]	m_axi_arvalid;
	// Verilator lint_off UNUSED
	reg	[7:0]		m_axi_arlen	[0:NSFULL-1];
	reg	[IW-1:0]	m_axi_arid	[0:NSFULL-1];
	reg	[NSFULL-1:0]	m_axi_arready;
	// Verilator lint_on  UNUSED
	reg	[NSFULL-1:0]	m_axi_rvalid;
	// Verilator lint_off UNUSED
	reg	[NSFULL-1:0]	m_axi_rready;
	// Verilator lint_on  UNUSED
	//
	reg	[IW-1:0]	m_axi_rid	[0:NSFULL-1];
	reg	[DW-1:0]	m_axi_rdata	[0:NSFULL-1];
	reg	[NSFULL-1:0]	m_axi_rlast;
	reg	[2-1:0]		m_axi_rresp	[0:NSFULL-1];

	reg	[NM-1:0]	slave_awaccepts;
	reg	[NM-1:0]	slave_waccepts;
	reg	[NM-1:0]	slave_raccepts;

	reg	[NM-1:0]	bskd_valid;
	reg	[NM-1:0]	rskd_valid, rskd_rlast;
	wire	[NM-1:0]	bskd_ready;
	wire	[NM-1:0]	rskd_ready;


	always @(*)
	begin
		m_axi_awvalid = -1;
		m_axi_awready = -1;
		m_axi_awlock  =  0;
		m_axi_wvalid = -1;
		m_axi_wready = -1;
		m_axi_wlast  = -1;
		m_axi_bvalid = 0;
		m_axi_bready = -1;

		m_axi_awvalid[NS-1:0] = M_AXI_AWVALID;
		m_axi_awready[NS-1:0] = M_AXI_AWREADY;
		m_axi_awlock[NS-1:0]  = M_AXI_AWLOCK;
		m_axi_wvalid[NS-1:0]  = M_AXI_WVALID;
		m_axi_wready[NS-1:0]  = M_AXI_WREADY;
		m_axi_wlast[NS-1:0]   = M_AXI_WLAST;
		m_axi_bvalid[NS-1:0]  = M_AXI_BVALID;
		m_axi_bready[NS-1:0]  = M_AXI_BREADY;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			m_axi_awid[iM]   = M_AXI_AWID[   iM*IW +: IW];
			m_axi_awaddr[iM] = M_AXI_AWADDR[ iM*AW +: AW];
			m_axi_awlen[iM]  = M_AXI_AWLEN[  iM* 8 +:  8];
			m_axi_awburst[iM]= M_AXI_AWBURST[iM* 2 +:  2];
			m_axi_awsize[iM] = M_AXI_AWSIZE[ iM* 3 +:  3];

			m_axi_bid[iM]   = M_AXI_BID[iM* IW +:  IW];
			m_axi_bresp[iM] = M_AXI_BRESP[iM* 2 +:  2];

			m_axi_rid[iM]   = M_AXI_RID[  iM*IW +: IW];
			m_axi_rdata[iM] = M_AXI_RDATA[iM*DW +: DW];
			m_axi_rresp[iM] = M_AXI_RRESP[iM* 2 +:  2];
			m_axi_rlast[iM] = M_AXI_RLAST[iM];
		end
		for(iM=NS; iM<NSFULL; iM=iM+1)
		begin
			m_axi_awid[iM]   = 0;
			m_axi_awaddr[iM] = 0;
			m_axi_awlen[iM]  = 0;
			m_axi_awburst[iM]= 0;
			m_axi_awsize[iM] = 0;

			m_axi_bresp[iM] = INTERCONNECT_ERROR;
			m_axi_bid[iM]   = 0;

			m_axi_rid[iM]   = 0;
			m_axi_rdata[iM] = 0;
			m_axi_rresp[iM] = INTERCONNECT_ERROR;
			m_axi_rlast[iM] = 1;
		end
	end

	generate for(N=0; N<NM; N=N+1)
	begin : W1_DECODE_WRITE_REQUEST
		wire	[NS:0]	wdecode;

		skidbuffer #(.DW(IW+AW+8+3+2+1+4+3+4),
					.OPT_OUTREG(OPT_SKID_INPUT))
		awskid(S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_AWVALID[N], S_AXI_AWREADY[N],
			{ S_AXI_AWID[N*IW +: IW], S_AXI_AWADDR[N*AW +: AW],
			  S_AXI_AWLEN[N*8 +: 8], S_AXI_AWSIZE[N*3 +: 3],
			  S_AXI_AWBURST[N*2 +: 2], S_AXI_AWLOCK[N],
			  S_AXI_AWCACHE[N*4 +: 4], S_AXI_AWPROT[N*3 +: 3],
			  S_AXI_AWQOS[N*4 +: 4] },
			skd_awvalid[N], !skd_awstall[N],
			{ skd_awid[N], skd_awaddr[N], skd_awlen[N],
			  skd_awsize[N], skd_awburst[N], skd_awlock[N],
			  skd_awcache[N], skd_awprot[N], skd_awqos[N] });

		addrdecode #(.AW(AW), .DW(IW+8+3+2+1+4+3+4), .NS(NS),
			.SLAVE_ADDR(SLAVE_ADDR),
			.SLAVE_MASK(SLAVE_MASK),
			.OPT_REGISTERED(OPT_BUFFER_DECODER))
		wraddr(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(skd_awvalid[N]), .o_stall(skd_awstall[N]),
				.i_addr(skd_awaddr[N]), .i_data({ skd_awid[N],
				skd_awlen[N], skd_awsize[N], skd_awburst[N],
				skd_awlock[N], skd_awcache[N], skd_awprot[N],
				skd_awqos[N] }),
			.o_valid(dcd_awvalid[N]),
				.i_stall(!dcd_awvalid[N]||!slave_awaccepts[N]),
				.o_decode(wdecode), .o_addr(m_awaddr[N]),
				.o_data({ m_awid[N], m_awlen[N], m_awsize[N],
				  m_awburst[N], m_awlock[N], m_awcache[N],
				  m_awprot[N], m_awqos[N]}));

		skidbuffer #(.DW(DW+DW/8+1),
					.OPT_OUTREG(OPT_SKID_INPUT))
		wskid(S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_WVALID[N], S_AXI_WREADY[N],
			{ S_AXI_WDATA[N*DW +: DW], S_AXI_WSTRB[N*DW/8 +: DW/8],
			  S_AXI_WLAST[N] },
			m_wvalid[N], slave_waccepts[N],
			{ m_wdata[N], m_wstrb[N], m_wlast[N] });

		always @(*)
		begin
			slave_awaccepts[N] = 1'b1;
			if (!mwgrant[N])
				slave_awaccepts[N] = 1'b0;
			if (mwfull[N])
				slave_awaccepts[N] = 1'b0;
			if (!wrequest[N][mwindex[N]])
				slave_awaccepts[N] = 1'b0;
			if (!wgrant[N][NS])
			begin
				if ((m_axi_awvalid[mwindex[N]] && !m_axi_awready[mwindex[N]]))
					slave_awaccepts[N] = 1'b0;
				if ((m_axi_wvalid[mwindex[N]] && !m_axi_wready[mwindex[N]]))
					slave_awaccepts[N] = 1'b0;
			end else if (!berr_valid[N] || !bskd_ready[N])
			begin
				// Can't accept an write address channel request
				// for the no-address-mapped channel if the
				// B* channel is stalled, lest we lose the ID
				// of the transaction
				slave_awaccepts[N] = 1'b0;
			end
		end

		always @(*)
		begin
			slave_waccepts[N] = 1'b1;
			if (!mwgrant[N])
				slave_waccepts[N] = 1'b0;
			if (!wdata_expected[N])
				slave_waccepts[N] = 1'b0;
			if (!wgrant[N][NS])
			begin
				if (m_axi_wvalid[mwindex[N]]
						&& !m_axi_wready[mwindex[N]])
					slave_waccepts[N] = 1'b0;
			end else if (berr_valid[N] || bskd_ready[N])
				slave_waccepts[N] = 1'b0;
		end

		always @(*)
		begin
			m_awvalid[N]= dcd_awvalid[N] && !mwfull[N];
			wrequest[N]= 0;
			if (!mwfull[N])
				wrequest[N][NS:0] = wdecode;
		end

	end for (N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_WSKID_BUFFERS

		assign	m_awid[N]    = 0;
		assign	m_awaddr[N]  = 0;
		assign	m_awlen[N]   = 0;
		assign	m_awsize[N]  = 0;
		assign	m_awburst[N] = 0;
		assign	m_awlock[N]  = 0;
		assign	m_awcache[N] = 0;
		assign	m_awprot[N]  = 0;
		assign	m_awqos[N]   = 0;

		always @(*)
			m_awvalid[N] = 0;
		//
		assign	m_wdata[N] = 0;
		assign	m_wstrb[N] = 0;
		assign	m_wlast[N] = 0;

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : R1_DECODE_READ_REQUEST
		wire	[NS:0]	rdecode;

		skidbuffer #(.DW(IW+AW+8+3+2+1+4+3+4),
					.OPT_OUTREG(OPT_SKID_INPUT))
		arskid(S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_ARVALID[N], S_AXI_ARREADY[N],
			{ S_AXI_ARID[N*IW +: IW], S_AXI_ARADDR[N*AW +: AW],
			  S_AXI_ARLEN[N*8 +: 8], S_AXI_ARSIZE[N*3 +: 3],
			  S_AXI_ARBURST[N*2 +: 2], S_AXI_ARLOCK[N],
			  S_AXI_ARCACHE[N*4 +: 4], S_AXI_ARPROT[N*3 +: 3],
			  S_AXI_ARQOS[N*4 +: 4] },
			skd_arvalid[N], !skd_arstall[N],
			{ skd_arid[N], skd_araddr[N], skd_arlen[N],
			  skd_arsize[N], skd_arburst[N], skd_arlock[N],
			  skd_arcache[N], skd_arprot[N], skd_arqos[N] });

		addrdecode #(.AW(AW), .DW(IW+8+3+2+1+4+3+4), .NS(NS),
			.SLAVE_ADDR(SLAVE_ADDR),
			.SLAVE_MASK(SLAVE_MASK),
			.OPT_REGISTERED(OPT_BUFFER_DECODER))
		rdaddr(.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(skd_arvalid[N]), .o_stall(skd_arstall[N]),
				.i_addr(skd_araddr[N]), .i_data({ skd_arid[N],
				skd_arlen[N], skd_arsize[N], skd_arburst[N],
				skd_arlock[N], skd_arcache[N], skd_arprot[N],
				skd_arqos[N] }),
			.o_valid(dcd_arvalid[N]),
				.i_stall(!m_arvalid[N] || !slave_raccepts[N]),
				.o_decode(rdecode), .o_addr(m_araddr[N]),
				.o_data({ m_arid[N], m_arlen[N], m_arsize[N],
				  m_arburst[N], m_arlock[N], m_arcache[N],
				  m_arprot[N], m_arqos[N]}));

		always @(*)
		begin
			m_arvalid[N] = dcd_arvalid[N] && !mrfull[N];
			rrequest[N] = 0;
			if (!mrfull[N])
				rrequest[N][NS:0] = rdecode;
		end

		always @(*)
		begin
			slave_raccepts[N] = 1'b1;
			if (!mrgrant[N])
				slave_raccepts[N] = 1'b0;
			if (mrfull[N])
				slave_raccepts[N] = 1'b0;
			// verilator lint_off  WIDTH
			if (!rrequest[N][mrindex[N]])
				slave_raccepts[N] = 1'b0;
			// verilator lint_on  WIDTH
			if (!rgrant[N][NS])
			begin
				if (m_axi_arvalid[mrindex[N]] && !m_axi_arready[mrindex[N]])
					slave_raccepts[N] = 1'b0;
			end else if (!mrempty[N] || !rerr_none[N] || rskd_valid[N])
				slave_raccepts[N] = 1'b0;
		end

	end for (N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_RSKID_BUFFERS

		always @(*)
			m_arvalid[N] = 0;
		assign	m_arid[N]    = 0;
		assign	m_araddr[N]  = 0;
		assign	m_arlen[N]   = 0;
		assign	m_arsize[N]  = 0;
		assign	m_arburst[N] = 0;
		assign	m_arlock[N]  = 0;
		assign	m_arcache[N] = 0;
		assign	m_arprot[N]  = 0;
		assign	m_arqos[N]   = 0;

	end endgenerate

	always @(*)
	begin : W2_DECONFLICT_WRITE_REQUESTS

		for(iN=0; iN<=NM; iN=iN+1)
			wrequested[iN] = 0;

		// Vivado may complain about too many bits for wrequested.
		// This is (currrently) expected.  mwindex is used to index
		// into wrequested, and mwindex has LGNS bits, where LGNS
		// is $clog2(NS+1) rather than $clog2(NS).  The extra bits
		// are defined to be zeros, but the point is there are defined.
		// Therefore, no matter what mwindex is, it will always
		// reference something valid.
		wrequested[NM] = 0;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			wrequested[0][iM] = 1'b0;
			for(iN=1; iN<NM ; iN=iN+1)
			begin
				// Continue to request any channel with
				// a grant and pending operations
				if (wrequest[iN-1][iM] && wgrant[iN-1][iM])
					wrequested[iN][iM] = 1;
				if (wrequest[iN-1][iM] && (!mwgrant[iN-1]||mwempty[iN-1]))
					wrequested[iN][iM] = 1;
				// Otherwise, if it's already claimed, then
				// it can't be claimed again
				if (wrequested[iN-1][iM])
					wrequested[iN][iM] = 1;
			end
			wrequested[NM][iM] = wrequest[NM-1][iM] || wrequested[NM-1][iM];
		end

	end

	always @(*)
	begin : R2_DECONFLICT_READ_REQUESTS

		for(iN=0; iN<NM ; iN=iN+1)
			rrequested[iN] = 0;

		// See the note above for wrequested.  This applies to
		// rrequested as well.
		rrequested[NM] = 0;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			rrequested[0][iM] = 0;
			for(iN=1; iN<NM ; iN=iN+1)
			begin
				// Continue to request any channel with
				// a grant and pending operations
				if (rrequest[iN-1][iM] && rgrant[iN-1][iM])
					rrequested[iN][iM] = 1;
				if (rrequest[iN-1][iM] && (!mrgrant[iN-1] || mrempty[iN-1]))
					rrequested[iN][iM] = 1;
				// Otherwise, if it's already claimed, then
				// it can't be claimed again
				if (rrequested[iN-1][iM])
					rrequested[iN][iM] = 1;
			end
			rrequested[NM][iM] = rrequest[NM-1][iM] || rrequested[NM-1][iM];
		end

	end

	generate for(M=0; M<NS; M=M+1)
	begin

		always @(*)
		begin
			swgrant[M] = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if (wgrant[iN][M])
				swgrant[M] = 1;
		end

		always @(*)
		begin
			srgrant[M] = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if (rgrant[iN][M])
				srgrant[M] = 1;
		end

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : W3_ARBITRATE_WRITE_REQUESTS
		reg			stay_on_channel;
		reg			requested_channel_is_available;
		reg			leave_channel;
		reg	[LGNS-1:0]	requested_index;

		always @(*)
		begin
			stay_on_channel = |(wrequest[N][NS:0] & wgrant[N]);

			if (mwgrant[N] && !mwempty[N])
				stay_on_channel = 1;
			if (berr_valid[N])
				stay_on_channel = 1;
		end

		always @(*)
		begin
			requested_channel_is_available = 
				|(wrequest[N][NS-1:0] & ~swgrant
						& ~wrequested[N][NS-1:0]);
			if (wrequest[N][NS])
				requested_channel_is_available = 1;

			if (NM < 2)
				requested_channel_is_available = m_awvalid[N];
		end

		reg	linger;
		if (OPT_LINGER == 0)
		begin
			always @(*)
				linger = 0;
		end else begin : WRITE_LINGER

			reg [LGLINGER-1:0]	linger_counter;

			initial	linger = 0;
			initial	linger_counter = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN || wgrant[N][NS])
			begin
				linger <= 0;
				linger_counter <= 0;
			end else if (!mwempty[N] || bskd_valid[N])
			begin
				linger_counter <= OPT_LINGER;
				linger <= 1;
			end else if (linger_counter > 0)
			begin
				linger <= (linger_counter > 1);
				linger_counter <= linger_counter - 1;
			end else
				linger <= 0;

		end

		always @(*)
		begin
			leave_channel = 0;
			if (!m_awvalid[N]
				&& (!linger || wrequested[NM][mwindex[N]]))
				// Leave the channel after OPT_LINGER counts
				// of the channel being idle, or when someone
				// else asks for the channel
				leave_channel = 1;
			if (m_awvalid[N] && !wrequest[N][mwindex[N]])
				// Need to leave this channel to connect
				// to any other channel
				leave_channel = 1;
		end


		initial	wgrant[N]  = 0;
		initial	mwgrant[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			wgrant[N]  <= 0;
			mwgrant[N] <= 0;
		end else if (!stay_on_channel)
		begin
			if (requested_channel_is_available)
			begin
				// Switching channels
				mwgrant[N] <= 1'b1;
				wgrant[N]  <= wrequest[N][NS:0];
			end else if (leave_channel)
			begin
				mwgrant[N] <= 1'b0;
				wgrant[N]  <= 0;
			end
		end

		always @(*)
		begin
			requested_index = 0;
			for(iM=0; iM<=NS; iM=iM+1)
			if (wrequest[N][iM])
				requested_index= requested_index | iM[LGNS-1:0];
		end

		// Now for mwindex
		initial	mwindex[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!stay_on_channel && requested_channel_is_available)
			mwindex[N] <= requested_index;

	end for (N=NM; N<NMFULL; N=N+1)
	begin

		always @(*)
			mwindex[N] = 0;

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : R3_ARBITRATE_READ_REQUESTS
		reg			stay_on_channel;
		reg			requested_channel_is_available;
		reg			leave_channel;
		reg	[LGNS-1:0]	requested_index;


		always @(*)
		begin
			stay_on_channel = |(rrequest[N][NS:0] & rgrant[N]);

			if (rgrant[N][NS] && (!rerr_none[N] || rskd_valid[N]))
				stay_on_channel = 1;
			if (mrgrant[N] && !mrempty[N])
				stay_on_channel = 1;
		end

		always @(*)
		begin
			requested_channel_is_available = 
				|(rrequest[N][NS-1:0] & ~srgrant
						& ~rrequested[N][NS-1:0]);
			if (rrequest[N][NS])
				requested_channel_is_available = 1;

			if (NM < 2)
				requested_channel_is_available = m_arvalid[N];
		end

		reg	linger;
		if (OPT_LINGER == 0)
		begin
			always @(*)
				linger = 0;
		end else begin : READ_LINGER

			reg [LGLINGER-1:0]	linger_counter;

			initial	linger = 0;
			initial	linger_counter = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN || rgrant[N][NS])
			begin
				linger <= 0;
				linger_counter <= 0;
			end else if (!mrempty[N] || rskd_valid[N])
			begin
				linger_counter <= OPT_LINGER;
				linger <= 1;
			end else if (linger_counter > 0)
			begin
				linger <= (linger_counter > 1);
				linger_counter <= linger_counter - 1;
			end else
				linger <= 0;

		end

		always @(*)
		begin
			leave_channel = 0;
			if (!m_arvalid[N]
				&& (!linger || rrequested[NM][mrindex[N]]))
				// Leave the channel after OPT_LINGER counts
				// of the channel being idle, or when someone
				// else asks for the channel
				leave_channel = 1;
			if (m_arvalid[N] && !rrequest[N][mrindex[N]])
				// Need to leave this channel to connect
				// to any other channel
				leave_channel = 1;
		end


		initial	rgrant[N]  = 0;
		initial	mrgrant[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rgrant[N]  <= 0;
			mrgrant[N] <= 0;
		end else if (!stay_on_channel)
		begin
			if (requested_channel_is_available)
			begin
				// Switching channels
				mrgrant[N] <= 1'b1;
				rgrant[N] <= rrequest[N][NS:0];
			end else if (leave_channel)
			begin
				mrgrant[N] <= 1'b0;
				rgrant[N]  <= 0;
			end
		end


		always @(*)
		begin
			requested_index = 0;
			for(iM=0; iM<=NS; iM=iM+1)
			if (rrequest[N][iM])
				requested_index = requested_index|iM[LGNS-1:0];
		end

		// Now for mrindex
		initial	mrindex[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!stay_on_channel && requested_channel_is_available)
			mrindex[N] <= requested_index;


	end for (N=NM; N<NMFULL; N=N+1)
	begin

		always @(*)
			mrindex[N] = 0;

	end endgenerate

	// Calculate swindex
	generate for (M=0; M<NS; M=M+1)
	begin : W4_SLAVE_WRITE_INDEX

		if (NM <= 1)
		begin

			always @(*)
				swindex[M] = 0;

		end else begin : MULTIPLE_MASTERS

			reg [LGNM-1:0]	reqwindex;

			always @(*)
			begin
				reqwindex = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if ((!mwgrant[iN] || mwempty[iN])
				&&(wrequest[iN][M] && !wrequested[iN][M]))
					reqwindex = reqwindex | iN[LGNM-1:0];
			end

			always @(posedge S_AXI_ACLK)
			if (!swgrant[M])
				swindex[M] <= reqwindex;
		end

	end for (M=NS; M<NSFULL; M=M+1)
	begin

		always @(*)
			swindex[M] = 0;

	end endgenerate

	// Calculate srindex
	generate for (M=0; M<NS; M=M+1)
	begin : R4_SLAVE_READ_INDEX

		if (NM <= 1)
		begin

			always @(*)
				srindex[M] = 0;

		end else begin : MULTIPLE_MASTERS

			reg [LGNM-1:0]	reqrindex;

			always @(*)
			begin
				reqrindex = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if ((!mrgrant[iN] || mrempty[iN])
				&&(rrequest[iN][M] && !rrequested[iN][M]))
					reqrindex = reqrindex | iN[LGNM-1:0];
			end

			always @(posedge S_AXI_ACLK)
			if (!srgrant[M])
				srindex[M] <= reqrindex;
		end

	end for (M=NS; M<NSFULL; M=M+1)
	begin

		always @(*)
			srindex[M] = 0;

	end endgenerate


	// Assign outputs to the various slaves
	generate for(M=0; M<NS; M=M+1)
	begin : W5_WRITE_SLAVE_OUTPUTS

		reg			axi_awvalid;
		reg	[IW-1:0]	axi_awid;
		reg	[AW-1:0]	axi_awaddr;
		reg	[7:0]		axi_awlen;
		reg	[2:0]		axi_awsize;
		reg	[1:0]		axi_awburst;
		reg			axi_awlock;
		reg	[3:0]		axi_awcache;
		reg	[2:0]		axi_awprot;
		reg	[3:0]		axi_awqos;

		reg			axi_wvalid;
		reg	[DW-1:0]	axi_wdata;
		reg	[DW/8-1:0]	axi_wstrb;
		reg			axi_wlast;
		//
		reg			axi_bready;

		reg	sawstall, swstall, mbstall;
		always @(*)
			sawstall= (M_AXI_AWVALID[M]&& !M_AXI_AWREADY[M]);
		always @(*)
			swstall = (M_AXI_WVALID[M] && !M_AXI_WREADY[M]);
		always @(*)
			mbstall = (bskd_valid[swindex[M]] && !bskd_ready[swindex[M]]);

		reg	awaccepts;
		always @(*)
		begin
			if (!swgrant[M])
				awaccepts = 1'b0;
			if (mwfull[swindex[M]])
				awaccepts = 1'b0;
			if (!wrequest[swindex[M]][M])
				awaccepts = 1'b0;
			if ((m_axi_wvalid[M] && !m_axi_wready[M]))
				awaccepts = 1'b0;
			awaccepts = slave_awaccepts[swindex[M]];
		end


		initial	axi_awvalid = 0;
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN || !swgrant[M])
			axi_awvalid <= 0;
		else if (!sawstall)
		begin
			axi_awvalid <= m_awvalid[swindex[M]] &&(awaccepts);
		end

		initial	axi_awid    = 0;
		initial	axi_awaddr  = 0;
		initial	axi_awlen   = 0;
		initial	axi_awsize  = 0;
		initial	axi_awburst = 0;
		initial	axi_awlock  = 0;
		initial	axi_awcache = 0;
		initial	axi_awprot  = 0;
		initial	axi_awqos   = 0;
		always @(posedge  S_AXI_ACLK)
		if (OPT_LOWPOWER && (!S_AXI_ARESETN || !swgrant[M]))
		begin
			axi_awid    <= 0;
			axi_awaddr  <= 0;
			axi_awlen   <= 0;
			axi_awsize  <= 0;
			axi_awburst <= 0;
			axi_awlock  <= 0;
			axi_awcache <= 0;
			axi_awprot  <= 0;
			axi_awqos   <= 0;
		end else if (!sawstall)
		begin
			if (!OPT_LOWPOWER||(m_awvalid[swindex[M]]&&awaccepts))
			begin
				// swindex[M] is defined as 0 above in the
				// case where NM <= 1
				axi_awid    <= m_awid[   swindex[M]];
				axi_awaddr  <= m_awaddr[ swindex[M]];
				axi_awlen   <= m_awlen[  swindex[M]];
				axi_awsize  <= m_awsize[ swindex[M]];
				axi_awburst <= m_awburst[swindex[M]];
				axi_awlock  <= m_awlock[ swindex[M]];
				axi_awcache <= m_awcache[swindex[M]];
				axi_awprot  <= m_awprot[ swindex[M]];
				axi_awqos   <= m_awqos[  swindex[M]];
			end else begin
				axi_awid    <= 0;
				axi_awaddr  <= 0;
				axi_awlen   <= 0;
				axi_awsize  <= 0;
				axi_awburst <= 0;
				axi_awlock  <= 0;
				axi_awcache <= 0;
				axi_awprot  <= 0;
				axi_awqos   <= 0;
			end
		end

		initial	axi_wvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || !swgrant[M])
			axi_wvalid <= 0;
		else if (!swstall)
		begin
			axi_wvalid <= (m_wvalid[swindex[M]])
					&&(slave_waccepts[swindex[M]]);
		end

		initial axi_wdata  = 0;
		initial axi_wstrb  = 0;
		initial axi_wlast  = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			axi_wdata  <= 0;
			axi_wstrb  <= 0;
			axi_wlast  <= 0;
		end else if (OPT_LOWPOWER && !swgrant[M])
		begin
			axi_wdata  <= 0;
			axi_wstrb  <= 0;
			axi_wlast  <= 0;
		end else if (!swstall)
		begin
			if (!OPT_LOWPOWER || (m_wvalid[swindex[M]]&&slave_waccepts[swindex[M]]))
			begin
				// If NM <= 1, swindex[M] is already defined
				// to be zero above
				axi_wdata  <= m_wdata[swindex[M]];
				axi_wstrb  <= m_wstrb[swindex[M]];
				axi_wlast  <= m_wlast[swindex[M]];
			end else begin
				axi_wdata  <= 0;
				axi_wstrb  <= 0;
				axi_wlast  <= 0;
			end
		end

		//
		always @(*)
		if (!swgrant[M])
			axi_bready <= 1;
		else
			axi_bready <= bskd_ready[swindex[M]];

		//
		assign	M_AXI_AWVALID[M]          = axi_awvalid;
		assign	M_AXI_AWID[   M*IW +: IW] = axi_awid;
		assign	M_AXI_AWADDR[ M*AW +: AW] = axi_awaddr;
		assign	M_AXI_AWLEN[  M* 8 +:  8] = axi_awlen;
		assign	M_AXI_AWSIZE[ M* 3 +:  3] = axi_awsize;
		assign	M_AXI_AWBURST[M* 2 +:  2] = axi_awburst;
		assign	M_AXI_AWLOCK[ M]          = axi_awlock;
		assign	M_AXI_AWCACHE[M* 4 +:  4] = axi_awcache;
		assign	M_AXI_AWPROT[ M* 3 +:  3] = axi_awprot;
		assign	M_AXI_AWQOS[  M* 4 +:  4] = axi_awqos;
		//
		//
		assign	M_AXI_WVALID[M]             = axi_wvalid;
		assign	M_AXI_WDATA[M*DW +: DW]     = axi_wdata;
		assign	M_AXI_WSTRB[M*DW/8 +: DW/8] = axi_wstrb;
		assign	M_AXI_WLAST[M]              = axi_wlast;
		//
		//
		assign	M_AXI_BREADY[M]             = axi_bready;
		//
	end endgenerate


	generate for(M=0; M<NS; M=M+1)
	begin : R5_READ_SLAVE_OUTPUTS

		reg				axi_arvalid;
		reg	[IW-1:0]		axi_arid;
		reg	[AW-1:0]		axi_araddr;
		reg	[7:0]			axi_arlen;
		reg	[2:0]			axi_arsize;
		reg	[1:0]			axi_arburst;
		reg				axi_arlock;
		reg	[3:0]			axi_arcache;
		reg	[2:0]			axi_arprot;
		reg	[3:0]			axi_arqos;
		//
		reg				axi_rready;

		reg	arstall, mrstall;
		always @(*)
			arstall= axi_arvalid && !M_AXI_ARREADY[M];
		always @(*)
			mrstall = (rskd_valid[srindex[M]]
						&& !rskd_ready[srindex[M]]);

		initial	axi_arvalid = 0;
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN || !srgrant[M])
			axi_arvalid <= 0;
		else if (!arstall)
			axi_arvalid <= m_arvalid[srindex[M]] && slave_raccepts[srindex[M]];
		else if (M_AXI_ARREADY[M])
			axi_arvalid <= 0;

		initial axi_arid    = 0;
		initial axi_araddr  = 0;
		initial axi_arlen   = 0;
		initial axi_arsize  = 0;
		initial axi_arburst = 0;
		initial axi_arlock  = 0;
		initial axi_arcache = 0;
		initial axi_arprot  = 0;
		initial axi_arqos   = 0;
		always @(posedge  S_AXI_ACLK)
		if (OPT_LOWPOWER && (!S_AXI_ARESETN || !srgrant[M]))
		begin
			axi_arid    <= 0;
			axi_araddr  <= 0;
			axi_arlen   <= 0;
			axi_arsize  <= 0;
			axi_arburst <= 0;
			axi_arlock  <= 0;
			axi_arcache <= 0;
			axi_arprot  <= 0;
			axi_arqos   <= 0;
		end else if (!arstall)
		begin
			if (!OPT_LOWPOWER || (m_arvalid[srindex[M]] && slave_raccepts[srindex[M]]))
			begin
				// If NM <=1, srindex[M] is defined to be zero
				axi_arid    <= m_arid[   srindex[M]];
				axi_araddr  <= m_araddr[ srindex[M]];
				axi_arlen   <= m_arlen[  srindex[M]];
				axi_arsize  <= m_arsize[ srindex[M]];
				axi_arburst <= m_arburst[srindex[M]];
				axi_arlock  <= m_arlock[ srindex[M]];
				axi_arcache <= m_arcache[srindex[M]];
				axi_arprot  <= m_arprot[ srindex[M]];
				axi_arqos   <= m_arqos[  srindex[M]];
			end else begin
				axi_arid    <= 0;
				axi_araddr  <= 0;
				axi_arlen   <= 0;
				axi_arsize  <= 0;
				axi_arburst <= 0;
				axi_arlock  <= 0;
				axi_arcache <= 0;
				axi_arprot  <= 0;
				axi_arqos   <= 0;
			end
		end

		initial	axi_rready = 1;
		always @(*)
		if (!srgrant[M])
			axi_rready <= 1;
		else
			axi_rready <= rskd_ready[srindex[M]];

		//
		assign	M_AXI_ARVALID[M]          = axi_arvalid;
		assign	M_AXI_ARID[   M*IW +: IW] = axi_arid;
		assign	M_AXI_ARADDR[ M*AW +: AW] = axi_araddr;
		assign	M_AXI_ARLEN[  M* 8 +:  8] = axi_arlen;
		assign	M_AXI_ARSIZE[ M* 3 +:  3] = axi_arsize;
		assign	M_AXI_ARBURST[M* 2 +:  2] = axi_arburst;
		assign	M_AXI_ARLOCK[ M]          = axi_arlock;
		assign	M_AXI_ARCACHE[M* 4 +:  4] = axi_arcache;
		assign	M_AXI_ARPROT[ M* 3 +:  3] = axi_arprot;
		assign	M_AXI_ARQOS[  M* 4 +:  4] = axi_arqos;
		//
		assign	M_AXI_RREADY[M]          = axi_rready;
		//
	end endgenerate

	// Return values
	generate for (N=0; N<NM; N=N+1)
	begin : W6_WRITE_RETURN_CHANNEL

		reg	[1:0]	i_axi_bresp;
		reg	[IW-1:0] i_axi_bid;

		initial	berr_valid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			berr_valid[N] <= 0;
		else if (wgrant[N][NS] && m_wvalid[N] && m_wlast[N]
				&& slave_waccepts[N])
			berr_valid[N] <= 1;
		else if (bskd_ready[N])
			berr_valid[N] <= 0;

		always @(*)
		if (berr_valid[N])
			bskd_valid[N] = 1;
		else
			bskd_valid[N] = mwgrant[N]&&m_axi_bvalid[mwindex[N]];

		always @(posedge S_AXI_ACLK)
		if (m_awvalid[N] && slave_awaccepts[N])
			berr_id[N] <= m_awid[N];

		always @(*)
		if (wgrant[N][NS])
		begin
			i_axi_bid   = berr_id[N];
			i_axi_bresp = INTERCONNECT_ERROR;
		end else begin
			i_axi_bid   = m_axi_bid[mwindex[N]];
			i_axi_bresp = m_axi_bresp[mwindex[N]];
		end

		skidbuffer #(.DW(IW+2),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_OUTREG(1))
		bskid(S_AXI_ACLK, !S_AXI_ARESETN,
			bskd_valid[N], bskd_ready[N],
			{ i_axi_bid, i_axi_bresp },
			S_AXI_BVALID[N], S_AXI_BREADY[N],
			{ S_AXI_BID[N*IW +: IW], S_AXI_BRESP[N*2 +: 2] });

	end endgenerate

	always @(*)
	begin
		m_axi_arvalid = 0;
		m_axi_arready = 0;
		m_axi_rvalid = 0;
		m_axi_rready = 0;
		for(iM=0; iM<NS; iM=iM+1)
		begin
			m_axi_arlen[iM] = M_AXI_ARLEN[iM* 8 +:  8];
			m_axi_arid[iM]  = M_AXI_ARID[ iM*IW +: IW];
		end
		for(iM=NS; iM<NSFULL; iM=iM+1)
		begin
			m_axi_arlen[iM] = 0;
			m_axi_arid[iM]  = 0;
		end

		m_axi_arvalid[NS-1:0] = M_AXI_ARVALID;
		m_axi_arready[NS-1:0] = M_AXI_ARREADY;
		m_axi_rvalid[NS-1:0]  = M_AXI_RVALID;
		m_axi_rready[NS-1:0]  = M_AXI_RREADY;
	end

	// Return values
	generate for (N=0; N<NM; N=N+1)
	begin : R6_READ_RETURN_CHANNEL

		reg	[DW-1:0]	i_axi_rdata;
		reg	[IW-1:0]	i_axi_rid;
		reg	[2-1:0]		i_axi_rresp;

		always @(*)
		if (rgrant[N][NS])
			rskd_valid[N] = !rerr_none[N];
		else
			rskd_valid[N] = mrgrant[N] && m_axi_rvalid[mrindex[N]];

		always @(*)
		if (rgrant[N][NS])
		begin
			i_axi_rid   = rerr_id[N];
			i_axi_rdata = 0;
			rskd_rlast[N] = rerr_last[N];
			i_axi_rresp = INTERCONNECT_ERROR;
		end else begin
			i_axi_rid   = m_axi_rid[mrindex[N]];
			i_axi_rdata = m_axi_rdata[mrindex[N]];
			rskd_rlast[N]= m_axi_rlast[mrindex[N]];
			i_axi_rresp = m_axi_rresp[mrindex[N]];
		end

		skidbuffer #(.DW(IW+DW+1+2),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_OUTREG(1))
		rskid(S_AXI_ACLK, !S_AXI_ARESETN,
			rskd_valid[N], rskd_ready[N],
			{ i_axi_rid, i_axi_rdata, rskd_rlast[N], i_axi_rresp },
			S_AXI_RVALID[N], S_AXI_RREADY[N],
			{ S_AXI_RID[N*IW +: IW], S_AXI_RDATA[N*DW +: DW],
			  S_AXI_RLAST[N], S_AXI_RRESP[N*2 +: 2] });

	end endgenerate

	// Count pending transactions
	generate for (N=0; N<NM; N=N+1)
	begin : W7_COUNT_PENDING_WRITES

		reg	[LGMAXBURST-1:0]	awpending;
		reg				r_wdata_expected;

		initial	awpending    = 0;
		initial	mwempty[N]   = 1;
		initial	mwfull[N]    = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			awpending     <= 0;
			mwempty[N]    <= 1;
			mwfull[N]     <= 0;
		end else case ({(m_awvalid[N] && slave_awaccepts[N]),
				(bskd_valid[N] && bskd_ready[N])})
		2'b01: begin
			awpending     <= awpending - 1;
			mwempty[N]    <= (awpending <= 1);
			mwfull[N]     <= 0;
			end
		2'b10: begin
			awpending <= awpending + 1;
			mwempty[N] <= 0;
			mwfull[N]     <= &awpending[LGMAXBURST-1:1];
			end
		default: begin end
		endcase

		initial	r_wdata_expected = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			r_wdata_expected <= 0;
		end else case ({(m_awvalid[N] && slave_awaccepts[N]),
				(m_wvalid[N] && slave_waccepts[N])})
		2'b01: r_wdata_expected <= !m_wlast[N];
		2'b10: r_wdata_expected <= 1;
		2'b11: r_wdata_expected <= r_wdata_expected || !m_wlast[N];
		default: begin end
		endcase

		assign	w_mawpending[N] = awpending;

		always @(*)
			wdata_expected[N] = r_wdata_expected;


	end endgenerate

	generate for (N=0; N<NM; N=N+1)
	begin : R7_COUNT_PENDING_READS

		reg	[LGMAXBURST-1:0]	rpending;

		initial	rpending     = 0;
		initial	mrempty[N]   = 1;
		initial	mrfull[N]    = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rpending  <= 0;
			mrempty[N]<= 1;
			mrfull[N] <= 0;
		end else case ({(m_arvalid[N] && slave_raccepts[N] && !rgrant[N][NS]),
				(rskd_valid[N] && rskd_ready[N]
					&& rskd_rlast[N] && !rgrant[N][NS])})
		2'b01: begin
			rpending      <= rpending - 1;
			mrempty[N]    <= (rpending == 1);
			mrfull[N]     <= 0;
			end
		2'b10: begin
			rpending      <= rpending + 1;
			mrfull[N]     <= &rpending[LGMAXBURST-1:1];
			mrempty[N]    <= 0;
			end
		default: begin end
		endcase

		initial	rerr_outstanding[N] = 0;
		initial	rerr_last[N] = 0;
		initial	rerr_none[N] = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rerr_outstanding[N] <= 0;
			rerr_last[N] <= 0;
			rerr_none[N] <= 1;
		end else if (!rerr_none[N])
		begin
			if (!rskd_valid[N] || rskd_ready[N])
			begin
				rerr_none[N] <= (rerr_outstanding[N] == 1);
				rerr_last[N] <= (rerr_outstanding[N] == 2);
				rerr_outstanding[N] <= rerr_outstanding[N] - 1;
			end
		end else if (m_arvalid[N] && rrequest[N][NS]
						&& slave_raccepts[N])
		begin
			rerr_none[N] <= 0;
			rerr_last[N] <= (m_arlen[N] == 0);
			rerr_outstanding[N] <= m_arlen[N] + 1;
		end

		initial	rerr_id[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN && OPT_LOWPOWER)
			rerr_id[N] <= 0;
		else if (m_arvalid[N] && rrequest[N][NS] && slave_raccepts[N])
		begin
			if (rrequest[N][NS] || !OPT_LOWPOWER)
				rerr_id[N] <= m_arid[N];
			else
				rerr_id[N] <= 0;
		end else if (OPT_LOWPOWER && rerr_last[N]
				&& (!rskd_valid[N] || rskd_ready[N]))
			rerr_id[N] <= 0;

		assign	w_mrpending[N]  = rpending;

`ifdef	FORMAL
		always @(*)
			assert(rerr_none[N] ==  (rerr_outstanding[N] == 0));
		always @(*)
			assert(rerr_last[N] ==  (rerr_outstanding[N] == 1));
		always @(*)
		if (OPT_LOWPOWER && rerr_none[N])
			assert(rerr_id[N] ==  0);
`endif
	end endgenerate

	initial begin
		if (NM == 0) begin
                        $display("At least one master must be defined");
                        $stop;
                end

		if (NS == 0) begin
                        $display("At least one slave must be defined");
                        $stop;
                end
        end

`ifdef	FORMAL
	localparam	F_LGDEPTH = LGMAXBURST+9;


	//
	// ...
	//

	initial	assert(NS >= 1);
	initial	assert(NM >= 1);

	generate for(N=0; N<NM; N=N+1)
	begin : F1_CHECK_MASTER_GRANTS

		// Write grants
		always @(*)
		for(iM=0; iM<=NS; iM=iM+1)
		begin
			if (wgrant[N][iM])
			begin
				assert((wgrant[N] ^ (1<<iM))==0);
				assert(mwgrant[N]);
				assert(mwindex[N] == iM);
				if (iM < NS)
				begin
					assert(swgrant[iM]);
					assert(swindex[iM] == N);
				end
			end
		end

		always @(*)
		if (mwgrant[N])
			assert(wgrant[N] != 0);

		always @(*)
		if (wrequest[N][NS])
			assert(wrequest[N][NS-1:0] == 0);


		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && f_past_valid && bskd_valid[N])
		begin
			assert($stable(wgrant[N]));
			assert($stable(mwindex[N]));
		end

		////////////////////////////////////////////////////////////////
		//
		// Read grant checking
		//
		always @(*)
		for(iM=0; iM<=NS; iM=iM+1)
		begin
			if (rgrant[N][iM])
			begin
				assert((rgrant[N] ^ (1<<iM))==0);
				assert(mrgrant[N]);
				assert(mrindex[N] == iM);
				if (iM < NS)
				begin
					assert(srgrant[iM]);
					assert(srindex[iM] == N);
				end
			end
		end

		always @(*)
		if (mrgrant[N])
			assert(rgrant[N] != 0);

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && f_past_valid && S_AXI_RVALID[N])
		begin
			assert($stable(rgrant[N]));
			assert($stable(mrindex[N]));
			if (!rgrant[N][NS])
				assert(!mrempty[N]);
		end
	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : F2_CHECK_MASTERS

		faxi_slave #(
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(DW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_ASSUME_RESET(1'b1),
			.F_AXI_MAXSTALL(0),
			.F_AXI_MAXRSTALL(2),
			.F_AXI_MAXDELAY(0),
			.F_OPT_READCHECK(0),
			.F_OPT_NO_RESET(1),
			.F_LGDEPTH(F_LGDEPTH))
		  mstri(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awid(   S_AXI_AWID[   N*IW +:IW]),
			.i_axi_awaddr( S_AXI_AWADDR[ N*AW +:AW]),
			.i_axi_awlen(  S_AXI_AWLEN[  N* 8 +: 8]),
			.i_axi_awsize( S_AXI_AWSIZE[ N* 3 +: 3]),
			.i_axi_awburst(S_AXI_AWBURST[N* 2 +: 2]),
			.i_axi_awlock( S_AXI_AWLOCK[ N]),
			.i_axi_awcache(S_AXI_AWCACHE[N* 4 +: 4]),
			.i_axi_awprot( S_AXI_AWPROT[ N* 3 +: 3]),
			.i_axi_awqos(  S_AXI_AWQOS[  N* 4 +: 4]),
			.i_axi_awvalid(S_AXI_AWVALID[N]),
			.i_axi_awready(S_AXI_AWREADY[N]),
			//
			.i_axi_wdata( S_AXI_WDATA[ N*DW   +: DW]),
			.i_axi_wstrb( S_AXI_WSTRB[ N*DW/8 +: DW/8]),
			.i_axi_wlast( S_AXI_WLAST[ N]),
			.i_axi_wvalid(S_AXI_WVALID[N]),
			.i_axi_wready(S_AXI_WREADY[N]),
			//
			.i_axi_bid(   S_AXI_BID[   N*IW +:IW]),
			.i_axi_bresp( S_AXI_BRESP[ N*2 +: 2]),
			.i_axi_bvalid(S_AXI_BVALID[N]),
			.i_axi_bready(S_AXI_BREADY[N]),
			//
			.i_axi_arid(   S_AXI_ARID[   N*IW +:IW]),
			.i_axi_arready(S_AXI_ARREADY[N]),
			.i_axi_araddr( S_AXI_ARADDR[ N*AW +:AW]),
			.i_axi_arlen(  S_AXI_ARLEN[  N* 8 +: 8]),
			.i_axi_arsize( S_AXI_ARSIZE[ N* 3 +: 3]),
			.i_axi_arburst(S_AXI_ARBURST[N* 2 +: 2]),
			.i_axi_arlock( S_AXI_ARLOCK[ N]),
			.i_axi_arcache(S_AXI_ARCACHE[N* 4 +: 4]),
			.i_axi_arprot( S_AXI_ARPROT[ N* 3 +: 3]),
			.i_axi_arqos(  S_AXI_ARQOS[  N* 4 +: 4]),
			.i_axi_arvalid(S_AXI_ARVALID[N]),
			//
			//
			.i_axi_rid(   S_AXI_RID[   N*IW +: IW]),
			.i_axi_rdata( S_AXI_RDATA[ N*DW +: DW]),
			.i_axi_rresp( S_AXI_RRESP[ N* 2 +: 2]),
			.i_axi_rlast( S_AXI_RLAST[ N]),
			.i_axi_rvalid(S_AXI_RVALID[N]),
			.i_axi_rready(S_AXI_RREADY[N]),
			//
			// ...
			//
			);

		//
		// ...
		//

		//
		// Check full/empty flags
		//

		always @(*)
		begin
			assert(mwfull[N] == &w_mawpending[N]);
			assert(mwempty[N] == (w_mawpending[N] == 0));
		end

		always @(*)
		begin
			assert(mrfull[N] == &w_mrpending[N]);
			assert(mrempty[N] == (w_mrpending[N] == 0));
		end


	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : F3_CHECK_SLAVES

		faxi_master #(
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(DW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_ASSUME_RESET(1'b1),
			.F_AXI_MAXSTALL(2),
			.F_AXI_MAXRSTALL(0),
			.F_AXI_MAXDELAY(2),
			.F_OPT_READCHECK(0),
			.F_OPT_NO_RESET(1),
			.F_LGDEPTH(F_LGDEPTH))
		  slvi(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awid(   M_AXI_AWID[   M*IW+:IW]),
			.i_axi_awaddr( M_AXI_AWADDR[ M*AW +: AW]),
			.i_axi_awlen(  M_AXI_AWLEN[  M*8 +: 8]),
			.i_axi_awsize( M_AXI_AWSIZE[ M*3 +: 3]),
			.i_axi_awburst(M_AXI_AWBURST[M*2 +: 2]),
			.i_axi_awlock( M_AXI_AWLOCK[ M]),
			.i_axi_awcache(M_AXI_AWCACHE[M*4 +: 4]),
			.i_axi_awprot( M_AXI_AWPROT[ M*3 +: 3]),
			.i_axi_awqos(  M_AXI_AWQOS[  M*4 +: 4]),
			.i_axi_awvalid(M_AXI_AWVALID[M]),
			.i_axi_awready(M_AXI_AWREADY[M]),
			//
			.i_axi_wready(M_AXI_WREADY[M]),
			.i_axi_wdata( M_AXI_WDATA[ M*DW   +: DW]),
			.i_axi_wstrb( M_AXI_WSTRB[ M*DW/8 +: DW/8]),
			.i_axi_wlast( M_AXI_WLAST[ M]),
			.i_axi_wvalid(M_AXI_WVALID[M]),
			//
			.i_axi_bid(   M_AXI_BID[   M*IW +: IW]),
			.i_axi_bresp( M_AXI_BRESP[ M*2 +: 2]),
			.i_axi_bvalid(M_AXI_BVALID[M]),
			.i_axi_bready(M_AXI_BREADY[M]),
			//
			.i_axi_arid(   M_AXI_ARID[   M*IW +:IW]),
			.i_axi_araddr( M_AXI_ARADDR[ M*AW +:AW]),
			.i_axi_arlen(  M_AXI_ARLEN[  M*8  +: 8]),
			.i_axi_arsize( M_AXI_ARSIZE[ M*3  +: 3]),
			.i_axi_arburst(M_AXI_ARBURST[M*2  +: 2]),
			.i_axi_arlock( M_AXI_ARLOCK[ M]),
			.i_axi_arcache(M_AXI_ARCACHE[M* 4 +: 4]),
			.i_axi_arprot( M_AXI_ARPROT[ M* 3 +: 3]),
			.i_axi_arqos(  M_AXI_ARQOS[  M* 4 +: 4]),
			.i_axi_arvalid(M_AXI_ARVALID[M]),
			.i_axi_arready(M_AXI_ARREADY[M]),
			//
			//
			.i_axi_rresp( M_AXI_RRESP[ M*2 +: 2]),
			.i_axi_rvalid(M_AXI_RVALID[M]),
			.i_axi_rdata( M_AXI_RDATA[ M*DW +: DW]),
			.i_axi_rready(M_AXI_RREADY[M]),
			.i_axi_rlast( M_AXI_RLAST[ M]),
			.i_axi_rid(   M_AXI_RID[   M*IW +: IW]),
			//
			// ...
			//
			);

			//
			// ...
			//

		always @(*)
		if (M_AXI_AWVALID[M])
			assert(((M_AXI_AWADDR[M*AW +:AW]^SLAVE_ADDR[M*AW +:AW])
				& SLAVE_MASK[M*AW +: AW]) == 0);

		always @(*)
		if (M_AXI_ARVALID[M])
			assert(((M_AXI_ARADDR[M*AW +:AW]^SLAVE_ADDR[M*AW +:AW])
				& SLAVE_MASK[M*AW +: AW]) == 0);

	end endgenerate


	////////////////////////////////////////////////////////////////////////
	//
	// Artificially constraining assumptions
	//
	// Ideally, this section should be empty--there should be no
	// assumptions here.  The existence of these assumptions should
	// give you an idea of where I'm at with this project.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate for(N=0; N<NM; N=N+1)
	begin : F6_LIMITING_ASSUMPTIONS

		if (!OPT_WRITES)
		begin
			always @(*)
				assume(S_AXI_AWVALID[N] == 0);
			always @(*)
				assert(wgrant[N] == 0);
			always @(*)
				assert(mwgrant[N] == 0);
			always @(*)
				assert(S_AXI_BVALID[N]== 0);
		end

		if (!OPT_READS)
		begin
			always @(*)
				assume(S_AXI_ARVALID [N]== 0);
			always @(*)
				assert(rgrant[N] == 0);
			always @(*)
				assert(S_AXI_RVALID[N] == 0);
		end

	end endgenerate

	always@(*)
		assert(OPT_READS | OPT_WRITES);
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
