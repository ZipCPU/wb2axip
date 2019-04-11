////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilxbar.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Create a full crossbar between NM AXI-lite sources (masters),
//		and NS AXI-lite slaves.  Every master can talk to any slave,
//	provided it isn't already busy.
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
module	axilxbar #(
		parameter integer C_S_AXI_DATA_WIDTH = 32,
		parameter integer C_S_AXI_ADDR_WIDTH = 32,
		parameter	NM = 4,
		parameter	NS = 8
		//
	) (
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		input	wire	[NM*C_S_AXI_ADDR_WIDTH*NM-1:0]	M_AXI_AWADDR,
		input	wire	[NM*3-1:0]			M_AXI_AWPROT,
		input	wire	[NM-1:0]			M_AXI_AWVALID,
		output	wire	[NM-1:0]			M_AXI_AWREADY,
		//
		input	wire	[NM*C_S_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		input	wire	[NM*C_S_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		input	wire	[NM-1:0]			M_AXI_WVALID,
		output	wire	[NM-1:0]			M_AXI_WREADY,
		//
		output	wire	[NM*2-1:0]			M_AXI_BRESP,
		output	wire	[NM-1:0]			M_AXI_BVALID,
		input	wire	[NM-1:0]			M_AXI_BREADY,
		//
		input	wire	[NM*C_S_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		input	wire	[NM*3-1:0]			M_AXI_ARPROT,
		input	wire	[NM-1:0]			M_AXI_ARVALID,
		output	wire	[NM-1:0]			M_AXI_ARREADY,
		//
		output	wire	[NM*C_S_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		output	wire	[NM*2-1:0]			M_AXI_RRESP,
		output	wire	[NM-1:0]			M_AXI_RVALID,
		input	wire	[NM-1:0]			M_AXI_RREADY,
		//
		//
		//
		output	wire	[NS*C_S_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		output	wire	[NS*3-1:0]			S_AXI_AWPROT,
		output	wire	[NS-1:0]			S_AXI_AWVALID,
		input	wire	[NS-1:0]			S_AXI_AWREADY,
		//
		output	wire	[NS*C_S_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		output	wire	[NS*C_S_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		output	wire	[NS-1:0]			S_AXI_WVALID,
		input	wire	[NS-1:0]			S_AXI_WREADY,
		//
		input	wire	[NS*2-1:0]			S_AXI_BRESP,
		input	wire	[NS-1:0]			S_AXI_BVALID,
		output	wire	[NS-1:0]			S_AXI_BREADY,
		//
		output	wire	[NS*C_S_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		output	wire	[NS*3-1:0]			S_AXI_ARPROT,
		output	wire	[NS-1:0]			S_AXI_ARVALID,
		input	wire	[NS-1:0]			S_AXI_ARREADY,
		//
		input	wire	[NS*C_S_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		input	wire	[NS*2-1:0]			S_AXI_RRESP,
		input	wire	[NS-1:0]			S_AXI_RVALID,
		output	wire	[NS-1:0]			S_AXI_RREADY
	);
	localparam	AW = C_S_AXI_ADDR_WIDTH;
	localparam	DW = C_S_AXI_DATA_WIDTH;
	parameter	[NS*AW-1:0]	SLAVE_ADDR = {
		3'b111,  {(AW-3){1'b0}},
		3'b110,  {(AW-3){1'b0}},
		3'b101,  {(AW-3){1'b0}},
		3'b100,  {(AW-3){1'b0}},
		3'b011,  {(AW-3){1'b0}},
		3'b010,  {(AW-3){1'b0}},
		4'b0001, {(AW-4){1'b0}},
		4'b0000, {(AW-4){1'b0}} };
	parameter	[NS*AW-1:0]	SLAVE_MASK =
		(NS <= 1) ? { 4'b1111, {(AW-4){1'b0}}}
		: { {(NS-2){ 3'b111, {(AW-3){1'b0}} }},
			{(2){ 4'b1111, {(AW-4){1'b0}}}} };
	parameter [0:0]	OPT_LOWPOWER = 1;
	parameter	OPT_LINGER = 4;
	parameter	LGMAXBURST = 5;
	localparam	LGLINGER = (OPT_LINGER>1) ? $clog2(OPT_LINGER+1) : 1;
	localparam	LGNM = (NM>1) ? $clog2(NM) : 1;
	localparam	LGNS = (NS>1) ? $clog2(NS+1) : 1;
	localparam	NMFULL = (NM>1) ? (1<<LGNM) : 1;
	localparam	NSFULL = (NS>1) ? (1<<LGNS) : 2;
	localparam [1:0] INTERCONNECT_ERROR = 2'b11;

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
	wire	[LGMAXBURST-1:0]	w_mwpending	[0:NM-1];
	wire	[LGMAXBURST-1:0]	w_mrpending	[0:NM-1];
	// verilator lint_on  UNUSED
	reg	[NM-1:0]		mwfull;
	reg	[NM-1:0]		mrfull;
	reg	[NM-1:0]		mwnearfull;
	reg	[NM-1:0]		mrnearfull;
	reg	[NM-1:0]		mwempty;
	reg	[NM-1:0]		mrempty;
	reg	[LGNS-1:0]	mwindex	[0:NMFULL-1];
	reg	[LGNS-1:0]	mrindex	[0:NMFULL-1];
	reg	[LGNM-1:0]	swindex	[0:NSFULL-1];
	reg	[LGNM-1:0]	srindex	[0:NSFULL-1];

	(* keep *) reg	[NM-1:0]		wdata_expected;

	// The skid buffers
	reg	[NMFULL-1:0]	r_awvalid, r_wvalid, r_arvalid;

	reg	[C_S_AXI_ADDR_WIDTH-1:0]	r_awaddr	[0:NMFULL-1];
	reg	[2:0]				r_awprot	[0:NMFULL-1];
	reg	[C_S_AXI_DATA_WIDTH-1:0]	r_wdata		[0:NMFULL-1];
	reg	[C_S_AXI_DATA_WIDTH/8-1:0]	r_wstrb		[0:NMFULL-1];

	reg	[C_S_AXI_ADDR_WIDTH-1:0]	r_araddr	[0:NMFULL-1];
	reg	[2:0]				r_arprot	[0:NMFULL-1];
	//

	// The shadow buffers
	reg	[NMFULL-1:0]	m_awvalid, m_wvalid, m_arvalid;

	reg	[C_S_AXI_ADDR_WIDTH-1:0]	m_awaddr	[0:NMFULL-1];
	reg	[2:0]				m_awprot	[0:NMFULL-1];
	reg	[C_S_AXI_DATA_WIDTH-1:0]	m_wdata		[0:NMFULL-1];
	reg	[C_S_AXI_DATA_WIDTH/8-1:0]	m_wstrb		[0:NMFULL-1];

	reg	[C_S_AXI_ADDR_WIDTH-1:0]	m_araddr	[0:NMFULL-1];
	reg	[2:0]				m_arprot	[0:NMFULL-1];
	//

	reg	[NSFULL-1:0]	s_axi_awvalid;
	reg	[NSFULL-1:0]	s_axi_awready;
	reg	[NSFULL-1:0]	s_axi_wvalid;
	reg	[NSFULL-1:0]	s_axi_wready;
	reg	[NSFULL-1:0]	s_axi_bvalid;
	reg	[NSFULL-1:0]	s_axi_bready;
	reg	[1:0]		s_axi_bresp	[0:NSFULL-1];

	reg	[NSFULL-1:0]	s_axi_arvalid;
	// Verilator lint_off UNUSED
	reg	[NSFULL-1:0]	s_axi_arready;
	// Verilator lint_on  UNUSED
	reg	[NSFULL-1:0]	s_axi_rvalid;
	// Verilator lint_off UNUSED
	reg	[NSFULL-1:0]	s_axi_rready;
	// Verilator lint_on  UNUSED

	reg	[DW-1:0]	s_axi_rdata	[0:NSFULL-1];
	reg	[1:0]		s_axi_rresp	[0:NSFULL-1];

	reg	[NM-1:0]	slave_awaccepts;
	reg	[NM-1:0]	slave_waccepts;
	reg	[NM-1:0]	slave_raccepts;

	always @(*)
	begin
		s_axi_awvalid = -1;
		s_axi_awready = -1;
		s_axi_wvalid = -1;
		s_axi_wready = -1;
		s_axi_bvalid = 0;
		s_axi_bready = -1;

		s_axi_awvalid[NS-1:0] = S_AXI_AWVALID;
		s_axi_awready[NS-1:0] = S_AXI_AWREADY;
		s_axi_wvalid[NS-1:0]  = S_AXI_WVALID;
		s_axi_wready[NS-1:0]  = S_AXI_WREADY;
		s_axi_bvalid[NS-1:0]  = S_AXI_BVALID;
		s_axi_bready[NS-1:0]  = S_AXI_BREADY;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			s_axi_bresp[iM] = S_AXI_BRESP[iM* 2 +:  2];

			s_axi_rdata[iM] = S_AXI_RDATA[iM*DW +: DW];
			s_axi_rresp[iM] = S_AXI_RRESP[iM* 2 +:  2];
		end
		for(iM=NS; iM<NSFULL; iM=iM+1)
		begin
			s_axi_bresp[iM] = INTERCONNECT_ERROR;

			s_axi_rdata[iM] = 0;
			s_axi_rresp[iM] = INTERCONNECT_ERROR;
		end
	end

	generate for(N=0; N<NM; N=N+1)
	begin : DECODE_WRITE_REQUEST
		reg	none_sel;

		always @(*)
		begin
			none_sel = 1'b1;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (((m_awaddr[N]^SLAVE_ADDR[iM*AW +:AW])
						& SLAVE_MASK[iM*AW +: AW])==0)
					none_sel = 1'b0;
			end
			if (!m_awvalid[N])
				none_sel = 1'b0;
		end


		always @(*)
		begin
			wrequest[N] = 0;
			for(iM=0; iM<NS; iM=iM+1)
				wrequest[N][iM] = m_awvalid[N]
					&&(((m_awaddr[N]^ SLAVE_ADDR[iM*AW+:AW])
						& SLAVE_MASK[iM*AW +: AW])==0);
			wrequest[N][NS] = m_awvalid[N] && none_sel;
		end

		always @(*)
		begin
			slave_awaccepts[N] = 1'b1;
			if (!mwgrant[N])
				slave_awaccepts[N] = 1'b0;
			if (mwnearfull[N])
				slave_awaccepts[N] = 1'b0;
			if (!wrequest[N][mwindex[N]])
				slave_awaccepts[N] = 1'b0;
			if ((mwindex[N] != NS)&&(s_axi_awvalid[mwindex[N]] && !s_axi_awready[mwindex[N]]))
				slave_awaccepts[N] = 1'b0;
			// ERRORs are always accepted
			//	back pressure is handled in the write side
		end

		always @(*)
		begin
			slave_waccepts[N] = 1'b1;
			if (!mwgrant[N])
				slave_waccepts[N] = 1'b0;
			// if ((!wdata_expected[N]) && (!slave_awaccepts[N]))
			//	slave_waccepts[N] = 1'b0;
			if (!wdata_expected[N])
				slave_waccepts[N] = 1'b0;
			if ((mwindex[N] != NS)
					&&(s_axi_wvalid[mwindex[N]]
						&& !s_axi_wready[mwindex[N]]))
				slave_waccepts[N] = 1'b0;
			if ((mwindex[N] == NS)
					&&(M_AXI_BVALID[N] && !M_AXI_BREADY[N]))
				slave_waccepts[N] = 1'b0;
		end

		initial	r_awvalid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_awvalid[N] <= 0;
		else if (r_awvalid[N])
		begin
			if (slave_awaccepts[N])
				r_awvalid[N] <= 1'b0;
		end else if (M_AXI_AWVALID[N] && M_AXI_AWREADY[N])
		begin
			if (slave_awaccepts[N])
				r_awvalid[N] <= 1'b0;
			else
				r_awvalid[N] <= 1'b1;
		end


		initial	r_wvalid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_wvalid[N] <= 0;
		else if (r_wvalid[N])
		begin
			if (slave_waccepts[N])
				r_wvalid[N] <= 1'b0;
		end else if (M_AXI_WVALID[N] && M_AXI_WREADY[N])
		begin
			if (slave_waccepts[N])
				r_wvalid[N] <= 1'b0;
			else
				r_wvalid[N] <= 1'b1;
		end


		always @(*)
		if (mwfull[N])
			m_awvalid[N] = 1'b0;
		else if (mwnearfull[N])
			m_awvalid[N] = M_AXI_AWVALID[N] && !r_awvalid[N];
		else
			m_awvalid[N] = M_AXI_AWVALID[N] || r_awvalid[N];

		always @(*)
			m_awaddr[N] = r_awvalid[N] ? r_awaddr[N] : M_AXI_AWADDR[N * AW +: AW];
		always @(*)
			m_awprot[N] = r_awvalid[N] ? r_awprot[N] : M_AXI_AWPROT[N*3 +: 3];

		always @(*)
		begin
			m_wvalid[N] = r_wvalid[N];
			if (M_AXI_WVALID[N] && M_AXI_WREADY[N])
				m_wvalid[N] = 1'b1;
			else if (!M_AXI_WREADY[N])
				m_wvalid[N] = 1'b1;
			// if ((!wdata_expected[N]) && (!slave_awaccepts[N]))
			//	m_wvalid[N] = 1'b0;
		end

		always @(*)
			m_wdata[N] = r_wvalid[N] ? r_wdata[N] : M_AXI_WDATA[N*DW+:DW];
		always @(*)
			m_wstrb[N] = r_wvalid[N] ? r_wstrb[N] : M_AXI_WSTRB[N*DW/8+:DW/8];
	end for (N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_WSKID_BUFFERS

		always @(*)
			m_awvalid[N] = 0;
		always @(*)
			m_awaddr[N] = 0;
		always @(*)
			m_awprot[N] = 0;
		always @(*)
			m_wdata[N] = 0;
		always @(*)
			m_wstrb[N] = 0;

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : DECODE_READ_REQUEST
		reg	none_sel;

		always @(*)
		begin
			none_sel = 1'b1;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (((m_araddr[N]^SLAVE_ADDR[iM*AW +:AW])
						& SLAVE_MASK[iM*AW +: AW])==0)
					none_sel = 1'b0;
			end
			if (!m_arvalid[N])
				none_sel = 1'b0;
		end


		always @(*)
		begin
			rrequest[N] = 0;
			for(iM=0; iM<NS; iM=iM+1)
				rrequest[N][iM] = m_arvalid[N]
					&&(((m_araddr[N]^ SLAVE_ADDR[iM*AW+:AW])
						& SLAVE_MASK[iM*AW +: AW])==0);
			rrequest[N][NS] = m_arvalid[N] && none_sel;
		end

		always @(*)
		begin
			slave_raccepts[N] = 1'b1;
			if (!mrgrant[N])
				slave_raccepts[N] = 1'b0;
			if (mrnearfull[N])
				slave_raccepts[N] = 1'b0;
			// verilator lint_off  WIDTH
			if (!rrequest[N][mrindex[N]])
				slave_raccepts[N] = 1'b0;
			// verilator lint_on  WIDTH
			if ((mrindex[N] != NS)&&(s_axi_arvalid[mrindex[N]] && !s_axi_arready[mrindex[N]]))
				slave_raccepts[N] = 1'b0;
			if ((mrindex[N] == NS)&&(M_AXI_RVALID[N] && !M_AXI_RREADY[N]))
				slave_raccepts[N] = 1'b0;
		end

		initial	r_arvalid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_arvalid[N] <= 0;
		else if (r_arvalid[N])
		begin
			if (slave_raccepts[N])
				r_arvalid[N] <= 1'b0;
		end else if (M_AXI_ARVALID[N] && M_AXI_ARREADY[N])
		begin
			if (slave_raccepts[N])
				r_arvalid[N] <= 1'b0;
			else
				r_arvalid[N] <= 1'b1;
		end


		always @(*)
		if (mrfull[N])
			m_arvalid[N] = 1'b0;
		else if (mrnearfull[N])
			m_arvalid[N] = M_AXI_ARVALID[N] && !r_arvalid[N];
		else
			m_arvalid[N] = M_AXI_ARVALID[N] || r_arvalid[N];

		always @(*)
			m_araddr[N] = r_arvalid[N] ? r_araddr[N] : M_AXI_ARADDR[N*AW +: AW];
		always @(*)
			m_arprot[N] = r_arvalid[N] ? r_arprot[N] : M_AXI_ARPROT[N*3 +: 3];

	end for (N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_RSKID_BUFFERS

		always @(*)
			m_arvalid[N] = 0;
		always @(*)
			m_araddr[N] = 0;
		always @(*)
			m_arprot[N] = 0;
	end endgenerate

	always @(*)
	begin : DECONFLICT_WRITE_REQUESTS

		wrequested[NM] = 0;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			wrequested[0][iM] = 0;
			for(iN=1; iN<NM ; iN=iN+1)
			wrequested[iN][iM]
				= (wrequest[iN-1][iM] || wrequested[iN-1][iM]);
			wrequested[NM][iM] = wrequest[NM-1][iM] || wrequested[NM-1][iM];
		end

		for(iM=NS; iM<NSFULL; iM=iM+1)
		begin
			for(iN=0; iN<NM+1; iN=iN+1)
				wrequested[iN][iM] = 0;
		end
	end

	always @(*)
	begin : DECONFLICT_READ_REQUESTS

		rrequested[NM] = 0;

		for(iM=0; iM<NS; iM=iM+1)
		begin
			rrequested[0][iM] = 0;
			for(iN=1; iN<NM ; iN=iN+1)
			rrequested[iN][iM]
				= (rrequest[iN-1][iM] || rrequested[iN-1][iM]);
			rrequested[NM][iM] = rrequest[NM-1][iM] || rrequested[NM-1][iM];
		end

		for(iM=NS; iM<NSFULL; iM=iM+1)
		begin
			for(iN=0; iN<NM ; iN=iN+1)
				rrequested[iN][iM] = 0;
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
	begin : ARBITRATE_WRITE_REQUESTS
		reg	stay_on_channel;

		always @(*)
		begin
			stay_on_channel = 0;
			for(iM=0; iM<=NS; iM=iM+1)
			begin
				if (wrequest[N][iM] && wgrant[N][iM])
					stay_on_channel = 1;
			end
		end

		reg	requested_channel_is_available;

		always @(*)
		begin
			requested_channel_is_available = 0;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (wrequest[N][iM] && !swgrant[iM]
					&& !wrequested[N][iM])
					requested_channel_is_available = 1;
			end
			if (wrequest[N][NS])
				requested_channel_is_available = 1;
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
			end else if (!mwempty[N] || M_AXI_BVALID[N])
			begin
				linger_counter <= OPT_LINGER;
				linger <= 1;
			end else if (linger_counter > 0)
			begin
				linger <= (linger_counter > 1);
				linger_counter <= linger_counter - 1;
			end else
				linger <= 0;

`ifdef	FORMAL
			always @(*)
				assert(linger == (linger_counter != 0));
`endif
		end

		reg	leave_channel;
		always @(*)
		begin
			leave_channel = 0;
			if (!M_AXI_AWVALID[N] && !r_awvalid[N]
				&& (!linger || wrequested[NM][mwindex[N]]))
				// Leave the channel after OPT_LINGER counts
				// of the channel being idle, or when someone
				// else asks for the channel
				leave_channel = 1;
			if (m_awvalid[N] && !wrequest[N][mwindex[N]])
				// Need to leave this channel to connect
				// to any other channel
				leave_channel = 1;

			if (!mwempty[N])
				// Can't leave this channel until we've gotten
				// all of the acknowledgments
				leave_channel = 0;
			if (!mwgrant[N])
				// Can't leave a channel we aren't a part of
				leave_channel = 0;
		end


		initial	wgrant[N]  = 0;
		initial	mwgrant[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			wgrant[N]  <= 0;
			mwgrant[N] <= 0;
		end else if (!stay_on_channel && (!mwgrant[N] || mwempty[N]))
		begin
			if (requested_channel_is_available)
			begin
				// Switching channels
				mwgrant[N] <= 1'b1;
				wgrant[N]  <= wrequest[N];
			end else if (M_AXI_AWVALID[N] || r_awvalid[N])
			begin
				// Requested channel isn't yet available
				mwgrant[N] <= 1'b0;
				wgrant[N]  <= 0;
			end else if (leave_channel)
			begin
				mwgrant[N] <= 1'b0;
				wgrant[N]  <= wrequest[N];
			end
		end

		// Now for mwindex
		initial	mwindex[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!stay_on_channel && (!mwgrant[N] || mwempty[N])
			&& requested_channel_is_available)
		begin

			for(iM=0; iM<=NS; iM=iM+1)
			begin

				if (wrequest[N][iM])
					mwindex[N] <= iM[LGNS-1:0];
			end
		end
	end for (N=NM; N<NMFULL; N=N+1)
	begin

		always @(*)
			mwindex[N] = 0;

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : ARBITRATE_READ_REQUESTS
		reg	stay_on_channel;

		always @(*)
		begin
			stay_on_channel = 0;
			for(iM=0; iM<=NS; iM=iM+1)
			begin
				if (rrequest[N][iM] && rgrant[N][iM])
					stay_on_channel = 1;
			end
		end

		reg	requested_channel_is_available;

		always @(*)
		begin
			requested_channel_is_available = 0;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (rrequest[N][iM] && !srgrant[iM]
					&& !rrequested[N][iM])
					requested_channel_is_available = 1;
			end
			if (rrequest[N][NS])
				requested_channel_is_available = 1;
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
			end else if (!mrempty[N] || M_AXI_RVALID[N])
			begin
				linger_counter <= OPT_LINGER;
				linger <= 1;
			end else if (linger_counter > 0)
			begin
				linger <= (linger_counter > 1);
				linger_counter <= linger_counter - 1;
			end else
				linger <= 0;

`ifdef	FORMAL
			always @(*)
				assert(linger == (linger_counter != 0));
`endif
		end

		reg	leave_channel;
		always @(*)
		begin
			leave_channel = 0;
			if (!M_AXI_ARVALID[N] && !r_arvalid[N]
				&& (!linger || rrequested[NM][mrindex[N]]))
				// Leave the channel after OPT_LINGER counts
				// of the channel being idle, or when someone
				// else asks for the channel
				leave_channel = 1;
			if (m_arvalid[N] && !rrequest[N][mrindex[N]])
				// Need to leave this channel to connect
				// to any other channel
				leave_channel = 1;

			if (!mrempty[N])
				// Can't leave this channel until we've gotten
				// all of the acknowledgments
				leave_channel = 0;
			if (!mrgrant[N])
				// Can't leave a channel we aren't a part of
				leave_channel = 0;
		end


		initial	rgrant[N]  = 0;
		initial	mrgrant[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rgrant[N]  <= 0;
			mrgrant[N] <= 0;
		end else if (!stay_on_channel && (!mrgrant[N] || mrempty[N]))
		begin
			if (requested_channel_is_available)
			begin
				// Switching channels
				mrgrant[N] <= 1'b1;
				rgrant[N] <= rrequest[N];
			end else if (M_AXI_ARVALID[N] || r_arvalid[N])
			begin
				// Requesting another channel, which isn't
				// (yet) available
				mrgrant[N] <= 1'b0;
				rgrant[N]  <= 0;
			end else if (leave_channel)
			begin
				mrgrant[N] <= 1'b0;
				rgrant[N]  <= 0;
			end
		end

		// Now for mrindex
		initial	mrindex[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!stay_on_channel && (!mrgrant[N] || mrempty[N])
			&& requested_channel_is_available)
		begin
			for(iM=0; iM<=NS; iM=iM+1)
			begin
				if (rrequest[N][iM])
					mrindex[N] <= iM[LGNS-1:0];
			end
		end


	end for (N=NM; N<NMFULL; N=N+1)
	begin

		always @(*)
			mrindex[N] = 0;

	end endgenerate

	generate for (N=0; N<NM; N=N+1)
	begin : INCOMING_SKID_BUFFERS

		initial r_awaddr[N] = 0;
		initial r_awprot[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			r_awaddr[N] <= 0;
			r_awprot[N] <= 0;
		end else if (M_AXI_AWREADY[N])
		begin
			if (M_AXI_AWVALID[N] || !OPT_LOWPOWER)
			begin
				r_awaddr[N] <= M_AXI_AWADDR[N*AW +: AW];
				r_awprot[N] <= M_AXI_AWPROT[N*3  +:  3];
			end else // if (OPT_LOWPOWER)
			begin
				r_awaddr[N] <= 0;
				r_awprot[N] <= 0;
			end
		end


		initial	r_wdata[N] = 0;
		initial	r_wstrb[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			r_wdata[N] <= 0;
			r_wstrb[N] <= 0;
		end else if (M_AXI_WREADY[N])
		begin
			if (M_AXI_WVALID[N] || !OPT_LOWPOWER)
			begin
				r_wdata[N] <= M_AXI_WDATA[N*DW   +: DW];
				r_wstrb[N] <= M_AXI_WSTRB[N*DW/8 +: DW/8];
			end else // if (OPT_LOWPOWER)
			begin
				r_wdata[N] <= 0;
				r_wstrb[N] <= 0;
			end
		end

		//
		//

		initial	r_araddr[N] = 0;
		initial	r_arprot[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			r_araddr[N] <= 0;
			r_arprot[N] <= 0;
		end else if (M_AXI_ARREADY[N])
		begin
			if (M_AXI_ARVALID[N] || !OPT_LOWPOWER)
			begin
				r_araddr[N] <= M_AXI_ARADDR[N*AW +: AW];
				r_arprot[N] <= M_AXI_ARPROT[N*3  +:  3];
			end else // if (OPT_LOWPOWER)
			begin
				r_araddr[N] <= 0;
				r_arprot[N] <= 0;
			end
		end


`ifdef	FORMAL
		always @(*)
		if (r_awvalid[N])
		begin
			assert(!M_AXI_AWREADY[N]);
			assert(r_awprot[N] == 0);
		end

		always @(*)
			assert(!M_AXI_AWREADY[N] == r_awvalid[N]);

		always @(*)
			assert(!M_AXI_WREADY[N] == r_wvalid[N]);

		always @(*)
		if (r_arvalid[N])
			assert(r_arprot[N] == 0);

		always @(*)
			assert(!M_AXI_ARREADY[N] == r_arvalid[N]);
`endif
	end endgenerate

	// Calculate swindex
	generate for (M=0; M<NS; M=M+1)
	begin : SLAVE_WRITE_INDEX

		if (NM <= 1)
		begin

			always @(*)
				swindex[M] = 0;

		end else begin : MULTIPLE_MASTERS

			always @(posedge S_AXI_ACLK)
			if (!swgrant[M])
			begin
				for(iN=0; iN<NM; iN=iN+1)
				begin
					if ((!mwgrant[iN] || mwempty[iN])
						&&(wrequest[iN][M]
						&& !wrequested[iN][M]))
						swindex[M] <= iN[LGNM-1:0];
				end
			end
		end

	end for (M=NS; M<NSFULL; M=M+1)
	begin

		always @(*)
			swindex[M] = 0;

	end endgenerate

	// Calculate srindex
	generate for (M=0; M<NS; M=M+1)
	begin : SLAVE_READ_INDEX

		if (NM <= 1)
		begin

			always @(*)
				srindex[M] = 0;

		end else begin : MULTIPLE_MASTERS

			always @(posedge S_AXI_ACLK)
			if (!srgrant[M])
			begin
				for(iN=0; iN<NM; iN=iN+1)
				begin
					if ((!mrgrant[iN] || mrempty[iN])
						&& (rrequest[iN][M]
						&& !rrequested[iN][M]))
						srindex[M] <= iN[LGNM-1:0];
				end
			end
		end

	end for (M=NS; M<NSFULL; M=M+1)
	begin

		always @(*)
			swindex[M] = 0;

	end endgenerate


	// Assign outputs to the various slaves
	generate for(M=0; M<NS; M=M+1)
	begin : WRITE_SLAVE_OUTPUTS

		reg			axi_awvalid;
		reg	[AW-1:0]	axi_awaddr;
		reg	[2:0]		axi_awprot;

		reg			axi_wvalid;
		reg	[DW-1:0]	axi_wdata;
		reg	[DW/8-1:0]	axi_wstrb;
		//
		reg			axi_bready;

		reg	sawstall, swstall, mbstall;
		always @(*)
			sawstall= (S_AXI_AWVALID[M]&& !S_AXI_AWREADY[M]);
		always @(*)
			swstall = (S_AXI_WVALID[M] && !S_AXI_WREADY[M]);
		always @(*)
			mbstall = (M_AXI_BVALID[swindex[M]] && !M_AXI_BREADY[swindex[M]]);

		initial	axi_awvalid = 0;
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN || !swgrant[M])
			axi_awvalid <= 0;
		else if (!sawstall)
		begin
			axi_awvalid <= m_awvalid[swindex[M]]
				&&(slave_awaccepts[swindex[M]]);
		end

		initial	axi_awaddr  = 0;
		initial	axi_awprot  = 0;
		always @(posedge  S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			axi_awaddr  <= 0;
			axi_awprot  <= 0;
		end else if (OPT_LOWPOWER && !swgrant[M])
		begin
			axi_awaddr  <= 0;
			axi_awprot  <= 0;
		end else if (!sawstall)
		begin
			if (!OPT_LOWPOWER||(m_awvalid[swindex[M]]&&slave_awaccepts[swindex[M]]))
			begin
				if (NM == 1)
				begin
					axi_awaddr  <= m_awaddr[0];
					axi_awprot  <= m_awprot[0];
				end else begin
					axi_awaddr  <= m_awaddr[swindex[M]];
					axi_awprot  <= m_awprot[swindex[M]];
				end
			end else begin
				axi_awaddr  <= 0;
				axi_awprot  <= 0;
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
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			axi_wdata  <= 0;
			axi_wstrb  <= 0;
		end else if (OPT_LOWPOWER && !swgrant[M])
		begin
			axi_wdata  <= 0;
			axi_wstrb  <= 0;
		end else if (!swstall)
		begin
			if (!OPT_LOWPOWER || (m_wvalid[swindex[M]]&&slave_waccepts[swindex[M]]))
			begin
				if (NM == 1)
				begin
					axi_wdata <= m_wdata[0];
					axi_wstrb <= m_wstrb[0];
				end else begin
					axi_wdata  <= m_wdata[swindex[M]];
					axi_wstrb  <= m_wstrb[swindex[M]];
				end
			end else begin
				axi_wdata  <= 0;
				axi_wstrb  <= 0;
			end
		end

		//
		initial	axi_bready = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || !swgrant[M])
			axi_bready <= 1;
		else if (!mbstall)
			axi_bready <= 1;
		else if (S_AXI_BVALID[M]) // && mbstall
			axi_bready <= 0;

		//
		assign	S_AXI_AWVALID[M]         = axi_awvalid;
		assign	S_AXI_AWADDR[M*AW +: AW] = axi_awaddr;
		assign	S_AXI_AWPROT[M*3 +: 3]   = axi_awprot;
		//
		//
		assign	S_AXI_WVALID[M]             = axi_wvalid;
		assign	S_AXI_WDATA[M*DW +: DW]     = axi_wdata;
		assign	S_AXI_WSTRB[M*DW/8 +: DW/8] = axi_wstrb;
		//
		//
		assign	S_AXI_BREADY[M]             = axi_bready;
		//
`ifdef	FORMAL
		if (OPT_LOWPOWER)
		begin
			always @(*)
			if (!axi_awvalid)
			begin
				assert(axi_awaddr == 0);
				assert(axi_awprot == 0);
			end

			always @(*)
			if (!axi_wvalid)
			begin
				assert(axi_wdata == 0);
				assert(axi_wstrb == 0);
			end
		end
`endif
	end endgenerate


	generate for(M=0; M<NS; M=M+1)
	begin : READ_SLAVE_OUTPUTS

		reg					axi_arvalid;
		reg	[C_S_AXI_ADDR_WIDTH-1:0]	axi_araddr;
		reg	[2:0]				axi_arprot;
		//
		reg					axi_rready;

		reg	arstall, mrstall;
		always @(*)
			arstall= (S_AXI_ARVALID[M]&& !S_AXI_ARREADY[M]);
		always @(*)
			mrstall = (M_AXI_RVALID[srindex[M]]
						&& !M_AXI_RREADY[srindex[M]]);

		initial	axi_arvalid = 0;
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN || !srgrant[M])
			axi_arvalid <= 0;
		else if (!arstall)
		begin
			axi_arvalid <= m_arvalid[srindex[M]] && slave_raccepts[srindex[M]];
		end

		initial	axi_araddr  = 0;
		initial	axi_arprot  = 0;
		always @(posedge  S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			axi_araddr  <= 0;
			axi_arprot  <= 0;
		end else if (OPT_LOWPOWER && !srgrant[M])
		begin
			axi_araddr  <= 0;
			axi_arprot  <= 0;
		end else if (!arstall)
		begin
			if (!OPT_LOWPOWER || (m_arvalid[srindex[M]] && slave_raccepts[srindex[M]]))
			begin
				if (NM == 1)
				begin
					axi_araddr  <= m_araddr[0];
					axi_arprot  <= m_arprot[0];
				end else begin
					axi_araddr  <= m_araddr[srindex[M]];
					axi_arprot  <= m_arprot[srindex[M]];
				end
			end else begin
				axi_araddr  <= 0;
				axi_arprot  <= 0;
			end
		end

		initial	axi_rready = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || !srgrant[M])
			axi_rready <= 1;
		else if (!mrstall)
			axi_rready <= 1;
		else if (S_AXI_RVALID[M] && S_AXI_RREADY[M]) // && mrstall
			axi_rready <= 0;

		//
		assign	S_AXI_ARVALID[M]         = axi_arvalid;
		assign	S_AXI_ARADDR[M*AW +: AW] = axi_araddr;
		assign	S_AXI_ARPROT[M*3 +: 3]   = axi_arprot;
		//
		assign	S_AXI_RREADY[M]          = axi_rready;
		//
`ifdef	FORMAL
		if (OPT_LOWPOWER)
		begin
			always @(*)
			if (!axi_arvalid)
			begin
				assert(axi_araddr == 0);
				assert(axi_arprot == 0);
			end
		end
`endif
	end endgenerate

	reg		r_bvalid	[0:NM-1];
	reg	[1:0]	r_bresp		[0:NM-1];

	// Return values
	generate for (N=0; N<NM; N=N+1)
	begin : WRITE_RETURN_CHANNEL

		reg		axi_awready, axi_wready;
		reg		axi_bvalid;
		reg	[1:0]	axi_bresp;
		reg		i_axi_bvalid;
		reg	[1:0]	i_axi_bresp;

		// reg	[((NS>1)?$clog2(NS)-1:0):0]	windex;
		// always @(*)
			// windex = mwindex[N];

		always @(*)
		if (mwindex[N] == NS)
			i_axi_bvalid = m_wvalid[N] && slave_waccepts[N];
		else
			i_axi_bvalid = s_axi_bvalid[mwindex[N]];

		always @(*)
			i_axi_bresp = s_axi_bresp[mwindex[N]];

		reg	mbstall;
		always @(*)
			mbstall = M_AXI_BVALID[N] && !M_AXI_BREADY[N];

		initial	axi_awready = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axi_awready <= 1;
		else begin
			if (M_AXI_AWVALID[N] && axi_awready)
			begin
				if (!slave_awaccepts[N])
					axi_awready <= 1'b0;
			end else if (!axi_awready && slave_awaccepts[N])
				axi_awready <= 1'b1;
		end

		initial	axi_wready = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axi_wready <= 1;
		else begin

			if (M_AXI_WVALID[N] && axi_wready)
			begin
				if (!slave_waccepts[N])
					axi_wready <= 1'b0;
			end else if (!axi_wready && slave_waccepts[N])
				axi_wready <= 1'b1;
		end

		initial	r_bvalid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_bvalid[N] <= 0;
		else if (mbstall && !r_bvalid[N] && (mwindex[N] != NS))
			r_bvalid[N] <= mwgrant[N] && (mwindex[N]<NS)&&i_axi_bvalid;
		else if (!mbstall)
			r_bvalid[N] <= 1'b0;

		initial	r_bresp[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			r_bresp[N] <= 0;
		else if (OPT_LOWPOWER && (!mwgrant[N] || M_AXI_BREADY[N]))
			r_bresp[N] <= 0;
		else if (!r_bvalid[N])
		begin
			if (!OPT_LOWPOWER ||(i_axi_bvalid && (mwindex[N] < NS) && mbstall))
			begin
				if (NS==1)
					r_bresp[N] <= S_AXI_BRESP[1:0];
				else
					r_bresp[N] <= i_axi_bresp;
			end else
				r_bresp[N] <= 0;
		end

		initial	axi_bvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axi_bvalid <= 0;
		else if (!mbstall)
			axi_bvalid <= mwgrant[N] && (r_bvalid[N] || i_axi_bvalid);

		initial	axi_bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			axi_bresp <= 0;
		else if (OPT_LOWPOWER && !mwgrant[N])
			axi_bresp <= 0;
		else if (!mbstall)
		begin
			if (r_bvalid[N])
				axi_bresp <= r_bresp[N];
			else if (!OPT_LOWPOWER || i_axi_bvalid)
				axi_bresp <= i_axi_bresp;
			else
				axi_bresp <= 0;

			if (mwindex[N] == NS && (!OPT_LOWPOWER || i_axi_bvalid))
				axi_bresp <= INTERCONNECT_ERROR;
		end

		assign	M_AXI_AWREADY[N]      = axi_awready;
		assign	M_AXI_WREADY[N]       = axi_wready;
		//
		assign	M_AXI_BVALID[N]       = axi_bvalid;
		assign	M_AXI_BRESP[N*2 +: 2] = axi_bresp;
`ifdef	FORMAL
		always @(*)
		if (r_bvalid[N])
			assert(r_bresp[N] != 2'b01);
		always @(*)
		if (mwgrant[N])
			assert(s_axi_bready[mwindex[N]] == !r_bvalid[N]);
		else
			assert(!r_bvalid[N]);
		always @(*)
		if (OPT_LOWPOWER && !r_bvalid[N])
			assert(r_bresp[N]  == 0);

		always @(*)
		if (OPT_LOWPOWER && !axi_bvalid)
			assert(axi_bresp  == 0);
`endif
	end endgenerate

	always @(*)
	begin
		s_axi_arvalid = 0;
		s_axi_arready = 0;
		s_axi_rvalid = 0;
		s_axi_rready = 0;

		s_axi_arvalid[NS-1:0] = S_AXI_ARVALID;
		s_axi_arready[NS-1:0] = S_AXI_ARREADY;
		s_axi_rvalid[NS-1:0]  = S_AXI_RVALID;
		s_axi_rready[NS-1:0]  = S_AXI_RREADY;
	end

	reg			r_rvalid	[0:NM-1];
	reg	[1:0]		r_rresp		[0:NM-1];
	reg	[DW-1:0]	r_rdata		[0:NM-1];
	// Return values
	generate for (N=0; N<NM; N=N+1)
	begin : READ_RETURN_CHANNEL

		reg			axi_rvalid;
		reg	[1:0]		axi_rresp;
		reg	[DW-1:0]	axi_rdata;
		reg			axi_arready;
		// reg	[((NM>1)?($clog2(NM)-1):0):0]		rindex;

		reg	mrstall;
		reg	i_axi_rvalid;
		always @(*)
		if (mrindex[N] == NS)
			i_axi_rvalid = m_arvalid[N] && slave_raccepts[N];
		else
			i_axi_rvalid = s_axi_rvalid[mrindex[N]];

		always @(*)
			mrstall = M_AXI_RVALID[N] && !M_AXI_RREADY[N];



		initial	axi_arready = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axi_arready <= 1'b1;
		else begin
			if (M_AXI_ARVALID[N] && axi_arready)
			begin
				if (!slave_raccepts[N])
					axi_arready <= 1'b0;
			end else if (!axi_arready && slave_raccepts[N])
				axi_arready <= 1'b1;
		end

		initial	r_rvalid[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_rvalid[N] <= 0;
		else if (mrstall && !r_rvalid[N])
			r_rvalid[N] <= mrgrant[N] && (mrindex[N]<NS)&&i_axi_rvalid;
		else if (!mrstall)
			r_rvalid[N] <= 0;

		initial	r_rresp[N] = 0;
		initial	r_rdata[N] = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			r_rresp[N] <= 0;
			r_rdata[N] <= 0;
		end else if (OPT_LOWPOWER && (!mrgrant[N] || M_AXI_RREADY[N]))
		begin
			r_rresp[N] <= 0;
			r_rdata[N] <= 0;
		end else if (!r_rvalid[N])
		begin
			if (!OPT_LOWPOWER || (i_axi_rvalid && (mrindex[N] < NS)&& mrstall))
			begin
				if (NS == 1)
				begin
					r_rresp[N] <= s_axi_rresp[0];
					r_rdata[N] <= s_axi_rdata[0];
				end else begin
					r_rresp[N] <= s_axi_rresp[mrindex[N]];
					r_rdata[N] <= s_axi_rdata[mrindex[N]];
				end
			end else begin
				r_rresp[N] <= 0;
				r_rdata[N] <= 0;
			end
		end

		initial	axi_rvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axi_rvalid <= 0;
		else if (!mrstall)
			axi_rvalid <= mrgrant[N] && (r_rvalid[N] || i_axi_rvalid);

		initial	axi_rresp = 0;
		initial	axi_rdata = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			axi_rresp <= 0;
			axi_rdata <= 0;
		end else if (OPT_LOWPOWER && !mrgrant[N])
		begin
			axi_rresp <= 0;
			axi_rdata <= 0;
		end else if (!mrstall)
		begin
			if (r_rvalid[N])
			begin
				axi_rresp <= r_rresp[N];
				axi_rdata <= r_rdata[N];
			end else if (!OPT_LOWPOWER || i_axi_rvalid)
			begin
				if (NS == 1)
				begin
					axi_rresp <= s_axi_rresp[0];
					axi_rdata <= s_axi_rdata[0];
				end else begin
					axi_rresp <= s_axi_rresp[mrindex[N]];
					axi_rdata <= s_axi_rdata[mrindex[N]];
				end

				if (mrindex[N] >= NS)
					axi_rresp <= INTERCONNECT_ERROR;
			end else begin
				axi_rresp <= 0;
				axi_rdata <= 0;
			end
		end

		assign	M_AXI_ARREADY[N]       = axi_arready && !r_arvalid[N];
		//
		assign	M_AXI_RVALID[N]        = axi_rvalid;
		assign	M_AXI_RRESP[N*2  +: 2] = axi_rresp;
		assign	M_AXI_RDATA[N*DW +: DW]= axi_rdata;
`ifdef	FORMAL
		always @(*)
		if (r_rvalid[N])
			assert(r_rresp[N] != 2'b01);
		always @(*)
		if (mrgrant[N] && (mrindex[N] < NS))
			assert(s_axi_rready[mrindex[N]] == !r_rvalid[N]);
		else
			assert(!r_rvalid[N]);
		always @(*)
		if (OPT_LOWPOWER && !r_rvalid[N])
		begin
			assert(r_rresp[N]  == 0);
			assert(r_rdata[N] == 0);
		end

		always @(*)
		if (OPT_LOWPOWER && !axi_rvalid)
		begin
			assert(axi_rresp  == 0);
			assert(axi_rdata == 0);
		end
`endif
	end endgenerate

	// Count pending transactions
	generate for (N=0; N<NM; N=N+1)
	begin : COUNT_PENDING

		reg	[LGMAXBURST-1:0]	wpending, awpending, rpending,
						missing_wdata;
		//reg				rempty, awempty; // wempty;
		(* keep *) reg	r_wdata_expected;

		initial	awpending    = 0;
		initial	mwempty[N]   = 1;
		initial	mwfull[N]    = 0;
		initial	mwnearfull[N]= 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			awpending     <= 0;
			mwempty[N]    <= 1;
			mwfull[N]     <= 0;
			mwnearfull[N] <= 0;
		end else case ({(m_awvalid[N] && slave_awaccepts[N]),
				(M_AXI_BVALID[N] && M_AXI_BREADY[N])})
		2'b01: begin
			awpending     <= awpending - 1;
			mwempty[N]    <= (awpending <= 1);
			mwfull[N]     <= 0;
			mwnearfull[N] <= (&awpending[LGMAXBURST-1:0]);
			end
		2'b10: begin
			awpending <= awpending + 1;
			mwempty[N] <= 0;
			mwfull[N]     <= &awpending[LGMAXBURST-1:1];
			mwnearfull[N] <= (&awpending[LGMAXBURST-1:2])
					&&(awpending[1:0] > 2'b00);
			end
		default: begin end
		endcase

		initial	wpending = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			wpending <= 0;
		else case ({(m_wvalid[N] && slave_waccepts[N]),
				(M_AXI_BVALID[N] && M_AXI_BREADY[N])})
		2'b01: wpending <= wpending - 1;
		2'b10: wpending <= wpending + 1;
		default: begin end
		endcase

		initial	missing_wdata = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			missing_wdata <= 0;
		else begin
			missing_wdata <= missing_wdata
				+((m_awvalid[N] && slave_awaccepts[N])? 1:0)
				-((m_wvalid[N] && slave_waccepts[N])? 1:0);
		end

		always @(*)
			r_wdata_expected = (missing_wdata > 0);

		initial	rpending     = 0;
		initial	mrempty[N]   = 1;
		initial	mrfull[N]    = 0;
		initial	mrnearfull[N]= 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			rpending  <= 0;
			mrempty[N]<= 1;
			mrfull[N] <= 0;
			mrnearfull[N] <= 0;
		end else case ({(m_arvalid[N] && slave_raccepts[N]),
				(M_AXI_RVALID[N] && M_AXI_RREADY[N])})
		2'b01: begin
			rpending      <= rpending - 1;
			mrempty[N]    <= (rpending == 1);
			mrfull[N]     <= 0;
			mrnearfull[N] <= (&rpending[LGMAXBURST-1:0]);
			end
		2'b10: begin
			rpending      <= rpending + 1;
			mrfull[N]     <= &rpending[LGMAXBURST-1:1];
			mrnearfull[N] <= (&rpending[LGMAXBURST-1:2])
					&&(rpending[1:0] > 2'b00);
			mrempty[N]    <= 0;
			end
		default: begin end
		endcase

		assign	w_mawpending[N] = awpending;
		assign	w_mwpending[N]  = wpending;
		assign	w_mrpending[N]  = rpending;

		always @(*)
			wdata_expected[N] = r_wdata_expected;

`ifdef	FORMAL
	reg	[LGMAXBURST-1:0]	f_missing_wdata;

	always @(*)
		assert(missing_wdata == awpending - wpending);
`endif
	end endgenerate

`ifdef	FORMAL
	localparam	F_LGDEPTH = LGMAXBURST+1;
	wire	[F_LGDEPTH-1:0]	fm_rd_outstanding	[0:NM-1];
	wire	[F_LGDEPTH-1:0]	fm_wr_outstanding	[0:NM-1];
	wire	[F_LGDEPTH-1:0]	fm_awr_outstanding	[0:NM-1];

	wire	[F_LGDEPTH-1:0]	fs_rd_outstanding	[0:NS-1];
	wire	[F_LGDEPTH-1:0]	fs_wr_outstanding	[0:NS-1];
	wire	[F_LGDEPTH-1:0]	fs_awr_outstanding	[0:NS-1];

	initial	assert(NS >= 1);
	initial	assert(NM >= 1);

	generate for(N=0; N<NM; N=N+1)
	begin : CHECK_MASTER_GRANTS

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


		// Read grants
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

		always @(*)
		if (rrequest[N][NS])
			assert(rrequest[N][NS-1:0] == 0);

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : CHECK_MASTERS

		faxil_slave #(
			.C_AXI_DATA_WIDTH(DW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_HAS_CACHE(1'b0),
			.F_OPT_ASSUME_RESET(1'b1),
			.F_AXI_MAXWAIT(0),
			.F_AXI_MAXDELAY(0),
			.F_LGDEPTH(F_LGDEPTH))
		  mstri(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awready(M_AXI_AWREADY[N]),
			.i_axi_awaddr(M_AXI_AWADDR[N*AW +: AW]),
			.i_axi_awcache(0),
			.i_axi_awprot(M_AXI_AWPROT[N*3 +: 3]),
			.i_axi_awvalid(M_AXI_AWVALID[N]),
			//
			.i_axi_wready(M_AXI_WREADY[N]),
			.i_axi_wdata( M_AXI_WDATA[N*DW +: DW]),
			.i_axi_wstrb( M_AXI_WSTRB[N*DW/8 +: DW/8]),
			.i_axi_wvalid(M_AXI_WVALID[N]),
			//
			.i_axi_bresp( M_AXI_BRESP[N*2 +: 2]),
			.i_axi_bvalid(M_AXI_BVALID[N]),
			.i_axi_bready(M_AXI_BREADY[N]),
			//
			.i_axi_arready(M_AXI_ARREADY[N]),
			.i_axi_araddr( M_AXI_ARADDR[N*AW +: AW]),
			.i_axi_arcache(4'b0),
			.i_axi_arprot( M_AXI_ARPROT[N*3 +: 3]),
			.i_axi_arvalid(M_AXI_ARVALID[N]),
			//
			//
			.i_axi_rresp( M_AXI_RRESP[N*2 +: 2]),
			.i_axi_rvalid(M_AXI_RVALID[N]),
			.i_axi_rdata( M_AXI_RDATA[N*DW +: DW]),
			.i_axi_rready(M_AXI_RREADY[N]),
			//
			.f_axi_rd_outstanding( fm_rd_outstanding[N]),
			.f_axi_wr_outstanding( fm_wr_outstanding[N]),
			.f_axi_awr_outstanding(fm_awr_outstanding[N]));

		//
		// Check write counters
		//
		always @(*)
		assert(fm_awr_outstanding[N] == { 1'b0, w_mawpending[N] }
				+ (M_AXI_AWREADY[N] ? 0:1));

		always @(*)
		assert(fm_wr_outstanding[N] == { 1'b0, w_mwpending[N] }
				+ (M_AXI_WREADY[N] ? 0:1));

		always @(*)
		if (S_AXI_ARESETN)
			assert(fm_awr_outstanding[N] >=
				(M_AXI_AWREADY[N] ? 0:1)
				+ (M_AXI_BVALID[N]  ? 1:0));

		always @(*)
		if (S_AXI_ARESETN)
			assert(fm_wr_outstanding[N] >= 
				(M_AXI_WREADY[N] ? 0:1)
				+ (M_AXI_BVALID[N]? 1:0));

		always @(*)
		assert(fm_wr_outstanding[N]-(M_AXI_WREADY[N] ? 0:1)
			<= fm_awr_outstanding[N]-(M_AXI_AWREADY[N] ? 0:1));

		always @(*)
		if (S_AXI_ARESETN && wgrant[N][NS])
			assert(fm_wr_outstanding[N] == (M_AXI_WREADY[N] ? 0:1)
				+ (M_AXI_BVALID[N] ? 1:0));

		always @(*)
		if (!mwgrant[N])
		begin
			assert(!M_AXI_BVALID[N]);

			assert(fm_awr_outstanding[N]==(M_AXI_AWREADY[N] ? 0:1));
			assert(fm_wr_outstanding[N] == (M_AXI_WREADY[N] ? 0:1));
			assert(w_mawpending[N] == 0);
			assert(w_mwpending[N] == 0);
		end


		//
		// Check read counters
		//
		always @(*)
		if (S_AXI_ARESETN)
			assert(fm_rd_outstanding[N] >= 
				(M_AXI_ARREADY[N] ? 0:1)
				+(M_AXI_RVALID[N] ? 1:0));

		always @(*)
		if (!mrgrant[N] || rgrant[N][NS])
			assert(fm_rd_outstanding[N] == 
				(M_AXI_ARREADY[N] ? 0:1)
				+(M_AXI_RVALID[N] ? 1:0));

		always @(*)
			assert(fm_rd_outstanding[N] == { 1'b0, w_mrpending[N] }
				+ (M_AXI_ARREADY[N] ? 0:1));

		always @(*)
		if (S_AXI_ARESETN && rgrant[N][NS])
			assert(fm_rd_outstanding[N] == (M_AXI_ARREADY[N] ? 0:1)
				+(M_AXI_RVALID[N] ? 1:0));

		always @(*)
		if (!mrgrant[N])
		begin
			assert(!M_AXI_RVALID[N]);
			assert(fm_rd_outstanding[N]== (M_AXI_ARREADY[N] ? 0:1));
			assert(w_mrpending[N] == 0);
		end

		//
		// Check full/empty flags
		//
		localparam	[LGMAXBURST-1:0] NEAR_THRESHOLD = -2;

		always @(*)
		begin
			assert(mwfull[N] == &w_mawpending[N]);
			assert(mwnearfull[N]==(w_mawpending[N] >= NEAR_THRESHOLD));
			assert(mwempty[N] == (w_mawpending[N] == 0));
		end

		always @(*)
		begin
			assert(mrfull[N] == &w_mrpending[N]);
			assert(mrnearfull[N]==(w_mrpending[N] >= NEAR_THRESHOLD));
			assert(mrempty[N] == (w_mrpending[N] == 0));
		end


	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : CHECK_SLAVES

		faxil_master #(
			.C_AXI_DATA_WIDTH(DW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_HAS_CACHE(1'b0),
			.F_OPT_ASSUME_RESET(1'b1),
			.F_AXI_MAXRSTALL(0),
			.F_LGDEPTH(F_LGDEPTH))
		  slvi(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awready(S_AXI_AWREADY[M]),
			.i_axi_awaddr(S_AXI_AWADDR[M*AW +: AW]),
			.i_axi_awcache(0),
			.i_axi_awprot(S_AXI_AWPROT[M*3 +: 3]),
			.i_axi_awvalid(S_AXI_AWVALID[M]),
			//
			.i_axi_wready(S_AXI_WREADY[M]),
			.i_axi_wdata( S_AXI_WDATA[M*DW +: DW]),
			.i_axi_wstrb( S_AXI_WSTRB[M*DW/8 +: DW/8]),
			.i_axi_wvalid(S_AXI_WVALID[M]),
			//
			.i_axi_bresp( S_AXI_BRESP[M*2 +: 2]),
			.i_axi_bvalid(S_AXI_BVALID[M]),
			.i_axi_bready(S_AXI_BREADY[M]),
			//
			.i_axi_arready(S_AXI_ARREADY[M]),
			.i_axi_araddr( S_AXI_ARADDR[M*AW +: AW]),
			.i_axi_arcache(4'b0),
			.i_axi_arprot( S_AXI_ARPROT[M*3 +: 3]),
			.i_axi_arvalid(S_AXI_ARVALID[M]),
			//
			//
			.i_axi_rresp( S_AXI_RRESP[M*2 +: 2]),
			.i_axi_rvalid(S_AXI_RVALID[M]),
			.i_axi_rdata( S_AXI_RDATA[M*DW +: DW]),
			.i_axi_rready(S_AXI_RREADY[M]),
			//
			.f_axi_rd_outstanding( fs_rd_outstanding[M]),
			.f_axi_wr_outstanding( fs_wr_outstanding[M]),
			.f_axi_awr_outstanding(fs_awr_outstanding[M]));

		always @(*)
		assert(fs_wr_outstanding[M] + (S_AXI_WVALID[M] ? 1:0) 
			<= fs_awr_outstanding[M] + (S_AXI_AWVALID[M]? 1:0));

		always @(*)
		if (!swgrant[M])
		begin
			assert(fs_awr_outstanding[M] == 0);
			assert(fs_wr_outstanding[M] == 0);
		end

		always @(*)
		if (!srgrant[M])
			assert(fs_rd_outstanding[M] == 0);

		always @(*)
			assert(fs_awr_outstanding[M] < { 1'b1, {(F_LGDEPTH-1){1'b0}}});
		always @(*)
			assert(fs_wr_outstanding[M] < { 1'b1, {(F_LGDEPTH-1){1'b0}}});
		always @(*)
			assert(fs_rd_outstanding[M] < { 1'b1, {(F_LGDEPTH-1){1'b0}}});

		always @(*)
		if (S_AXI_AWVALID[M])
			assert(((S_AXI_AWADDR[M*AW +: AW]
				^ SLAVE_ADDR[M*AW +: AW])
				& SLAVE_MASK[M*AW +: AW]) == 0);

		always @(*)
		if (S_AXI_ARVALID[M])
			assert(((S_AXI_ARADDR[M*AW +: AW]
				^ SLAVE_ADDR[M*AW +: AW])
				& SLAVE_MASK[M*AW +: AW]) == 0);

	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : CORRELATE_OUTSTANDING

		always @(*)
		if (mwgrant[N] && (mwindex[N] < NS))
		begin
			assert((fm_awr_outstanding[N]
				- (M_AXI_AWREADY[N] ? 0:1)
				- (M_AXI_BVALID[N]  ? 1:0))
				== (fs_awr_outstanding[mwindex[N]]
					+ (s_axi_awvalid[mwindex[N]] ? 1:0)
					+ (s_axi_bready[mwindex[N]] ? 0:1)));

			assert((fm_wr_outstanding[N]
				- (M_AXI_WREADY[N] ? 0:1)
				- (M_AXI_BVALID[N] ? 1:0))
				== (fs_wr_outstanding[mwindex[N]]
					+ (s_axi_wvalid[mwindex[N]] ? 1:0)
					+ (s_axi_bready[mwindex[N]] ? 0:1)));

		end else if (!mwgrant[N] || (mwindex[N]==NS))
		begin
			if (!mwgrant[N])
				assert(fm_awr_outstanding[N] ==
						(M_AXI_AWREADY[N] ? 0:1)
						+(M_AXI_BVALID[N]  ? 1:0));
			else
				assert(fm_awr_outstanding[N] >=
						(M_AXI_AWREADY[N] ? 0:1)
						+(M_AXI_BVALID[N]  ? 1:0));

			assert(fm_wr_outstanding[N]  ==
					(M_AXI_WREADY[N]  ? 0:1)
					+(M_AXI_BVALID[N]  ? 1:0));
		end

		always @(*)
		if (mrgrant[N] && (mrindex[N] < NS))
		begin
			assert((fm_rd_outstanding[N]//17
				- (M_AXI_ARREADY[N] ? 0:1)//1
				- (M_AXI_RVALID[N] ? 1:0))//0
				== (fs_rd_outstanding[mrindex[N]]//16
					+ (s_axi_arvalid[mrindex[N]] ? 1:0)//0
					+ (s_axi_rready[mrindex[N]] ? 0:1)));//0
		end

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Can every master reach every slave?
	// Can things transition without dropping the request line(s)?
	generate for(N=0; N<NM; N=N+1)
	begin : COVER_CONNECTIVITY_FROM_MASTER
		reg [3:0]	w_returns, r_returns;
		reg		err_wr_return, err_rd_return;
		reg [NS-1:0]	w_every, r_every;
		reg		was_wevery, was_revery, whsreturn, rhsreturn;

		// w_returns is a speed check: Can we return one write
		// acknowledgement per clock cycle?
		initial	w_returns = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			w_returns = 0;
		else begin
			w_returns <= { w_returns[2:0], 1'b0 };
			if (M_AXI_BVALID[N] && M_AXI_BREADY[N] && !wgrant[N][NS])
				w_returns[0] <= 1'b1;
		end

		initial	whsreturn = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			whsreturn <= 0;
		else
			whsreturn <= whsreturn || (&w_returns);

		// w_every is a connectivity test: Can we get a return from
		// every slave?
		initial	w_every = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			w_every <= 0;
		else if (!M_AXI_AWVALID[N])
			w_every <= 0;
		else begin
			if (M_AXI_BVALID[N] && M_AXI_BREADY[N] && !wgrant[N][NS])
				w_every[mwindex[N]] <= 1'b1;
		end

		always @(posedge S_AXI_ACLK)
		if (M_AXI_BVALID[N])
			assert($stable(mwindex[N]));

		initial	was_wevery = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			was_wevery <= 0;
		else
			was_wevery <= was_wevery || (&w_every);

		always @(*)
			cover(!mwgrant[N] && whsreturn);	// @27
		always @(*)
			cover(!mwgrant[N] && was_wevery);	// @27

		// err_wr_return is a test to make certain we can return a
		// bus error on the write channel.
		initial	err_wr_return = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			err_wr_return = 0;
		else if (wgrant[N][NS] && M_AXI_BVALID[N]
				&& (M_AXI_BRESP[2*N+:2]==INTERCONNECT_ERROR))
			err_wr_return = 1;

		always @(*) // @!
			cover(err_wr_return);
		always @(*) // @!
			cover(!mwgrant[N] && err_wr_return);

		always @(*)
		if (M_AXI_BVALID[N])
			assert(mwgrant[N]);

		// r_returns is a speed check: Can we return one read
		// acknowledgment per clock cycle?
		initial	r_returns = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_returns = 0;
		else begin
			r_returns <= { r_returns[2:0], 1'b0 };
			if (M_AXI_RVALID[N] && M_AXI_RREADY[N])
				r_returns[0] <= 1'b1;
		end

		initial	rhsreturn = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			rhsreturn <= 0;
		else
			rhsreturn <= rhsreturn || (&r_returns);


		// r_every is a connectivity test: Can we get a read return from
		// every slave?
		initial	r_every = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_every = 0;
		else if (!M_AXI_ARVALID[N])
			r_every = 0;
		else begin
			if (M_AXI_RVALID[N] && M_AXI_RREADY[N])
				r_every[mrindex[N]] <= 1'b1;
		end

		// was_revery is a return to idle check following the
		// connectivity test.  Since the connectivity test is cleared
		// if there's ever a drop in the valid line, we need a separate
		// wire to check that this master can return to idle again.
		initial	was_revery = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			was_revery <= 0;
		else
			was_revery <= was_revery || (&r_every);

		always @(posedge S_AXI_ACLK)
		if (M_AXI_RVALID[N])
			assert($stable(mrindex[N]));

		always @(*)
			cover(!mrgrant[N] && rhsreturn);	// @26
		always @(*)
			cover(!mrgrant[N] && was_revery);	// @26

		initial	err_rd_return = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			err_rd_return = 0;
		else if (rgrant[N][NS] && M_AXI_RVALID[N]
				&& (M_AXI_RRESP[2*N+:2]==INTERCONNECT_ERROR))
			err_rd_return = 1;

		always @(*)
			cover(M_AXI_ARVALID[N] && rrequest[N][NS]);
		always @(*)
			cover(rgrant[N][NS]);
		always @(*)
			cover(err_rd_return);
		always @(*)
			cover(!mrgrant[N] && err_rd_return); //@!

		always @(*)
		if (M_AXI_BVALID[N] && wgrant[N][NS])
			assert(M_AXI_BRESP[2*N+:2]==INTERCONNECT_ERROR);
		always @(*)
		if (M_AXI_RVALID[N] && rgrant[N][NS])
			assert(M_AXI_RRESP[2*N+:2]==INTERCONNECT_ERROR);
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Negation check
	//
	// Pick a particular value.  Assume the value doesn't show up on the
	// input.  Prove it doesn't show up on the output.  This will check for
	// ...
	// 1. Stuck bits on the output channel
	// 2. Cross-talk between channels
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[LGNM-1:0]	f_const_source;
	(* anyconst *)	reg	[AW-1:0]	f_const_addr;
	(* anyconst *)	reg	[AW-1:0]	f_const_addr_n;
	(* anyconst *)	reg	[DW-1:0]	f_const_data_n;
	(* anyconst *)	reg	[DW/8-1:0]	f_const_strb_n;
	(* anyconst *)	reg	[3-1:0]		f_const_prot_n;
	(* anyconst *)	reg	[2-1:0]		f_const_resp_n;
			reg	[LGNS-1:0]	f_const_slave;

	always @(*)
		assume(f_const_source < NM);
	always @(*)
	begin
		f_const_slave = NS;
		for(iM=0; iM<NS; iM=iM+1)
		begin
			if (((f_const_addr ^ SLAVE_ADDR[iM*AW+:AW])
					&SLAVE_MASK[iM*AW+:AW])==0)
				f_const_slave = iM;
		end

		assume(f_const_slave < NS);
	end

	reg	[AW-1:0]	f_awaddr;
	reg	[AW-1:0]	f_araddr;
	always @(*)
		f_awaddr = M_AXI_AWADDR[f_const_source * AW +: AW];
	always @(*)
		f_araddr = M_AXI_ARADDR[f_const_source * AW +: AW];

	// The assumption check: assume our negated values are not found on
	// the inputs
	always @(*)
	begin
		if (M_AXI_AWVALID[f_const_source])
		begin
			assume(f_awaddr != f_const_addr_n);
			assume(M_AXI_AWPROT[f_const_source*3+:3] != f_const_prot_n);
		end
		if (m_wvalid)
		begin
			assume(m_wdata[f_const_source] != f_const_data_n);
			assume(m_wstrb[f_const_source] != f_const_strb_n);
		end
		if (M_AXI_ARVALID[f_const_source])
		begin
			assume(f_araddr != f_const_addr_n);
			assume(M_AXI_ARPROT[f_const_source*3+:3] != f_const_prot_n);
		end

		if (S_AXI_BVALID[f_const_slave] && wgrant[f_const_source][f_const_slave])
		begin
			assume(s_axi_bresp[f_const_slave] != f_const_resp_n);
		end

		if (S_AXI_RVALID[f_const_slave] && rgrant[f_const_source][f_const_slave])
		begin
			assume(s_axi_rdata[f_const_slave] != f_const_data_n);
			assume(s_axi_rresp[f_const_slave] != f_const_resp_n);
		end
	end

	// Proof check: Prove these values are not found on our outputs
	always @(*)
	begin
		if (r_awvalid[f_const_source])
		begin
			assert(r_awaddr[f_const_source] != f_const_addr_n);
			assert(r_awprot[f_const_source]  != f_const_prot_n);
		end
		if (S_AXI_AWVALID[f_const_slave] && wgrant[f_const_source][f_const_slave])
		begin
			assert(S_AXI_AWADDR[f_const_slave*AW+:AW] != f_const_addr_n);
			assert(S_AXI_AWPROT[f_const_slave*3+:3] != f_const_prot_n);
		end
		if (S_AXI_WVALID[f_const_slave] && wgrant[f_const_source][f_const_slave])
		begin
			assert(S_AXI_WDATA[f_const_slave*DW+:DW] != f_const_data_n);
			assert(S_AXI_WSTRB[f_const_slave*(DW/8)+:(DW/8)] != f_const_strb_n);
		end
		if (r_arvalid[f_const_source])
		begin
			assert(r_araddr[f_const_source] != f_const_addr_n);
			assert(r_arprot[f_const_source] != f_const_prot_n);
		end
		if (S_AXI_ARVALID[f_const_slave] && rgrant[f_const_source][f_const_slave])
		begin
			assert(S_AXI_ARADDR[f_const_slave*AW+:AW] != f_const_addr_n);
			assert(S_AXI_ARPROT[f_const_slave*3+:3] != f_const_prot_n);
		end
		//
		if (r_bvalid[f_const_source] && wgrant[f_const_source][f_const_slave])
			assert(r_bresp[f_const_source] != f_const_resp_n);
		if (M_AXI_BVALID[f_const_source] && wgrant[f_const_source][f_const_slave])
			assert(M_AXI_BRESP[f_const_source*2+:2] != f_const_resp_n);
		if (r_rvalid[f_const_source] && rgrant[f_const_source][f_const_slave])
		begin
			assert(r_rresp[f_const_source] != f_const_resp_n);
			assert(r_rdata[f_const_source] != f_const_data_n);
		end
		if (M_AXI_RVALID[f_const_source] && rgrant[f_const_source][f_const_slave])
		begin
			assert(M_AXI_RRESP[f_const_source*2+:2]!=f_const_resp_n);
			assert(M_AXI_RDATA[f_const_source*DW+:DW]!=f_const_data_n);
		end
	end

	////////////////////////////////////////////////////////////////////////
	//
	// (Careless) constraining assumptions
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate for(N=0; N<NM; N=N+1)
	begin

//		always @(*)
//			assume(!wgrant[N][NS]);

//		always @(*)
//			assume(!rgrant[N][NS]);
	end endgenerate

`endif
endmodule
