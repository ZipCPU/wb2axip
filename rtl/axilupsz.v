////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilupsz.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Converts AXI4-lite traffic of one data width to a similar
//		AXI4-lite interface with a larger data path.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	axilupsz #(
		// {{{
		parameter	C_S_AXIL_DATA_WIDTH = 32,
		parameter	C_M_AXIL_DATA_WIDTH = 64,
		parameter	C_AXIL_ADDR_WIDTH = 32,
		parameter	LGFIFO = 5,
		parameter [0:0]	OPT_LOWPOWER = 1,
		localparam	SDW = C_S_AXIL_DATA_WIDTH,
		localparam	MDW = C_M_AXIL_DATA_WIDTH,
		localparam	AW = C_AXIL_ADDR_WIDTH
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
				S_AXI_ARESETN,
		// The slave interface
		// {{{
		input	wire			S_AXIL_AWVALID,
		output	wire			S_AXIL_AWREADY,
		input	wire	[AW-1:0]	S_AXIL_AWADDR,
		input	wire	[2:0]		S_AXIL_AWPROT,
		//
		input	wire			S_AXIL_WVALID,
		output	wire			S_AXIL_WREADY,
		input	wire	[SDW-1:0]	S_AXIL_WDATA,
		input	wire	[SDW/8-1:0]	S_AXIL_WSTRB,
		//
		output	wire			S_AXIL_BVALID,
		input	wire			S_AXIL_BREADY,
		output	wire	[1:0]		S_AXIL_BRESP,
		//
		input	wire			S_AXIL_ARVALID,
		output	wire			S_AXIL_ARREADY,
		input	wire	[AW-1:0]	S_AXIL_ARADDR,
		input	wire	[2:0]		S_AXIL_ARPROT,
		//
		output	wire			S_AXIL_RVALID,
		input	wire			S_AXIL_RREADY,
		output	wire	[SDW-1:0]	S_AXIL_RDATA,
		output	wire	[1:0]		S_AXIL_RRESP,
		// }}}
		// The master interface
		// {{{
		output	wire			M_AXIL_AWVALID,
		input	wire			M_AXIL_AWREADY,
		output	wire	[AW-1:0]	M_AXIL_AWADDR,
		output	wire	[2:0]		M_AXIL_AWPROT,
		//
		output	wire			M_AXIL_WVALID,
		input	wire			M_AXIL_WREADY,
		output	wire	[MDW-1:0]	M_AXIL_WDATA,
		output	wire	[MDW/8-1:0]	M_AXIL_WSTRB,
		//
		input	wire			M_AXIL_BVALID,
		output	wire			M_AXIL_BREADY,
		input	wire	[1:0]		M_AXIL_BRESP,
		//
		output	wire			M_AXIL_ARVALID,
		input	wire			M_AXIL_ARREADY,
		output	wire	[AW-1:0]	M_AXIL_ARADDR,
		output	wire	[2:0]		M_AXIL_ARPROT,
		//
		input	wire			M_AXIL_RVALID,
		output	wire			M_AXIL_RREADY,
		input	wire	[MDW-1:0]	M_AXIL_RDATA,
		input	wire	[1:0]		M_AXIL_RRESP
		// }}}
		// }}}
	);

	localparam	MLSB = $clog2(C_M_AXIL_DATA_WIDTH/8);
	localparam	SLSB = $clog2(C_S_AXIL_DATA_WIDTH/8);
	localparam	RPTS = MDW/SDW;

	generate if (SDW == MDW)
	begin : NO_CHANGE
		// {{{
		assign	M_AXIL_AWVALID = S_AXIL_AWVALID;
		assign	S_AXIL_AWREADY = M_AXIL_AWREADY;
		assign	M_AXIL_AWADDR  = S_AXIL_AWADDR;
		assign	M_AXIL_AWPROT  = S_AXIL_AWPROT;

		assign	M_AXIL_WVALID = S_AXIL_WVALID;
		assign	S_AXIL_WREADY = M_AXIL_WREADY;
		assign	M_AXIL_WDATA  = S_AXIL_WDATA;
		assign	M_AXIL_WSTRB  = S_AXIL_WSTRB;

		assign	S_AXIL_BVALID = M_AXIL_BVALID;
		assign	M_AXIL_BREADY = S_AXIL_BREADY;
		assign	S_AXIL_BRESP  = M_AXIL_BRESP;

		assign	M_AXIL_ARVALID = S_AXIL_ARVALID;
		assign	S_AXIL_ARREADY = M_AXIL_ARREADY;
		assign	M_AXIL_ARADDR  = S_AXIL_ARADDR;
		assign	M_AXIL_ARPROT  = S_AXIL_ARPROT;

		assign	S_AXIL_RVALID = M_AXIL_RVALID;
		assign	M_AXIL_RREADY = S_AXIL_RREADY;
		assign	S_AXIL_RDATA  = M_AXIL_RDATA;
		assign	S_AXIL_RRESP  = M_AXIL_RRESP;
		// }}}
	end else begin : UPSIZE_BUS_DATA_WIDTH
		// {{{
		// Signal declarations
		// {{{
		wire			awskd_valid, wskd_valid, wskd_ready;
		wire	[AW-1:0]	awskd_addr;
		wire	[2:0]		awskd_prot;

		wire	[SDW-1:0]	wskd_data;
		wire	[SDW/8-1:0]	wskd_strb;

		reg			awvalid, wvalid;
		reg	[AW-1:0]	awaddr;
		reg	[2:0]		awprot;
		reg	[MDW-1:0]	wdata;
		reg	[MDW/8-1:0]	wstrb;

		reg			rvalid;
		reg	[SDW-1:0]	rdata;
		reg	[1:0]		rresp;
		wire			rfifo_full, rfifo_empty;
		wire	[LGFIFO:0]	rfifo_fill;
		wire	[MLSB-SLSB-1:0]	rfifo_data;
		wire	[MDW-1:0]	shift_rdata;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Write channel(s)
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// AW* skid bufer
		// {{{
		skidbuffer #(
			// {{{
			.OPT_OUTREG(0),
			.DW(AW+3)
			// }}}
		) awskd (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
			.i_data({ S_AXIL_AWADDR, S_AXIL_AWPROT }),
			.o_valid(awskd_valid), .i_ready(wskd_ready),
			.o_data({ awskd_addr, awskd_prot })
			// }}}
		);
		// }}}

		skidbuffer #(
			// {{{
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0),
			.DW(SDW+SDW/8)
			// }}}
		) wskd (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
			.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
			.o_valid(wskd_valid), .i_ready(wskd_ready),
			.o_data({ wskd_data, wskd_strb })
			// }}}
		);

		// wskd_ready
		// {{{
		// We *need* to synchronize the two channels here.  We need the
		// address informatiuon to know how to set the W* channel
		// downstream
		assign	wskd_ready = (awskd_valid && wskd_valid)
				&& (!M_AXIL_AWVALID || M_AXIL_AWREADY)
				&& (!M_AXIL_WVALID || M_AXIL_WREADY);
		// }}}

		// awvalid
		// {{{
		initial	awvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			awvalid <= 0;
		else if (!M_AXIL_AWVALID || M_AXIL_AWREADY)
			awvalid <= wskd_ready;
		// }}}

		// awaddr, awprot
		// {{{
		initial	{ awaddr, awprot } = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			{ awaddr, awprot } <= 0;
		else if (!M_AXIL_AWVALID || M_AXIL_AWREADY)
		begin
			{ awaddr, awprot } <= 0;
			if (awskd_valid || !OPT_LOWPOWER)
				{awaddr, awprot } <= { awskd_addr, awskd_prot };
		end
		// }}}

		// wvalid
		// {{{
		initial	wvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			wvalid <= 0;
		else if (!M_AXIL_WVALID || M_AXIL_WREADY)
			wvalid <= wskd_ready;
		// }}}

		// wdata, wstrb
		// {{{
		initial	{ wdata, wstrb } = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN && OPT_LOWPOWER)
			{ wdata, wstrb } <= 0;
		else if (!M_AXIL_WVALID || M_AXIL_WREADY)
		begin
			// Default values
			wstrb <= 0;
			wdata <= {(RPTS){ wskd_data }};

			// Verilator lint_off WIDTH
			if (OPT_LOWPOWER)
			begin
				wdata <= 0;
				wdata <= (wskd_data)
					<< (awskd_addr[MLSB-1:SLSB] *  SDW);
			end

			if (!OPT_LOWPOWER || wskd_valid)
				wstrb <= (wskd_strb)
					<< (awskd_addr[MLSB-1:SLSB] *  SDW);
			// Verilator lint_on WIDTH
		end
		// }}}
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Read channel
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		wire			rskd_valid, rskd_ready;
		wire	[MDW-1:0]	rskd_data;
		wire	[1:0]		rskd_resp;

		// Read LSB address FIFO
		// {{{
		sfifo #(
			// {{{
			.BW(MLSB-SLSB),
			.LGFLEN(LGFIFO)
			// }}}
		) rfifo (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(S_AXIL_ARVALID && S_AXIL_ARREADY),
				.i_data(M_AXIL_ARADDR[MLSB-1:SLSB]),
			.o_full(rfifo_full), .o_fill(rfifo_fill),
			.i_rd(M_AXIL_RVALID && M_AXIL_RREADY),
			.o_data(rfifo_data),
			.o_empty(rfifo_empty)
			// }}}
		);
		// }}}

		// Read return skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0),
			.DW(MDW+2)
			// }}}
		) rskd (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(M_AXIL_RVALID), .o_ready(M_AXIL_RREADY),
			.i_data({ M_AXIL_RDATA, M_AXIL_RRESP }),
			.o_valid(rskd_valid), .i_ready(rskd_ready),
			.o_data({ rskd_data, rskd_resp })
			// }}}
		);

		assign	rskd_ready = !S_AXIL_RVALID || S_AXIL_RREADY;
		// }}}

		assign	shift_rdata = rskd_data
			>> ({ {(MDW-(MLSB-SLSB)){1'b0}}, rfifo_data} * SDW);


		// rvalid
		// {{{
		initial	rvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			rvalid <= 0;
		else if (!S_AXIL_RVALID || S_AXIL_RREADY)
			rvalid <= rskd_valid;
		// }}}

		// rresp
		// {{{
		initial	rresp = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			rresp <= 0;
		else if (!S_AXIL_RVALID || S_AXIL_RREADY)
		begin
			rresp <= rskd_resp;
			if (OPT_LOWPOWER && !rskd_valid)
				rresp <= 0;
		end
		// }}}

		// rdata
		// {{{
		initial	rdata = 0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			rdata <= 0;
		else if (!S_AXIL_RVALID || S_AXIL_RREADY)
		begin
			rdata <= shift_rdata[SDW-1:0];

			if (OPT_LOWPOWER && !rskd_valid)
				rdata <= 0;
		end
`ifdef	FORMAL
		// Low power check
		// {{{
		always @(*)
		if (S_AXI_ARESETN && OPT_LOWPOWER && !S_AXIL_RVALID)
		begin
			assert(rdata == 0);
			assert(rresp == 0);
		end
		// }}}
`endif
		// }}}

		// }}}

		// M_* values, S_B*
		// {{{
		assign	M_AXIL_AWVALID = awvalid;
		assign	M_AXIL_AWADDR  = awaddr;
		assign	M_AXIL_AWPROT  = awprot;
		assign	M_AXIL_WVALID  = wvalid;
		assign	M_AXIL_WDATA   = wdata;
		assign	M_AXIL_WSTRB   = wstrb;

		assign	M_AXIL_ARVALID = S_AXIL_ARVALID  && !rfifo_full;
		assign	S_AXIL_ARREADY = M_AXIL_ARREADY  && !rfifo_full;
		assign	M_AXIL_ARADDR  = S_AXIL_ARADDR;
		assign	M_AXIL_ARPROT  = S_AXIL_ARPROT;

		assign	S_AXIL_RVALID  = rvalid;
		assign	S_AXIL_RDATA   = rdata;
		assign	S_AXIL_RRESP   = rresp;

		assign	S_AXIL_BVALID = M_AXIL_BVALID;
		assign	M_AXIL_BREADY = S_AXIL_BREADY;
		assign	S_AXIL_BRESP  = M_AXIL_BRESP;
		// }}}

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, shift_rdata[MDW-1:SDW],
				rfifo_empty, rfifo_fill };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	// Formal properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		localparam	F_LGDEPTH = LGFIFO+2;
		wire	[F_LGDEPTH-1:0]	fslv_rd_outstanding,
					fmst_rd_outstanding,
					fslv_wr_outstanding,
					fmst_wr_outstanding,
					fslv_awr_outstanding,
					fmst_awr_outstanding;
		////////////////////////////////////////////////////////////////
		//
		// Interface properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		faxil_slave #(
			// {{{
			.C_AXI_DATA_WIDTH(SDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_COVER_BURST(4),
			.F_LGDEPTH(F_LGDEPTH),
			.F_AXI_MAXWAIT(8),
			.F_AXI_MAXRSTALL(3),
			.F_AXI_MAXDELAY(16)
			// }}}
		) axil_slave (
			// {{{
			.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awvalid(S_AXIL_AWVALID),
			.i_axi_awready(S_AXIL_AWREADY),
			.i_axi_awaddr( S_AXIL_AWADDR),
			.i_axi_awprot( S_AXIL_AWPROT),
			//
			.i_axi_wvalid(S_AXIL_WVALID),
			.i_axi_wready(S_AXIL_WREADY),
			.i_axi_wdata( S_AXIL_WDATA),
			.i_axi_wstrb( S_AXIL_WSTRB),
			//
			.i_axi_bvalid(S_AXIL_BVALID),
			.i_axi_bready(S_AXIL_BREADY),
			.i_axi_bresp( S_AXIL_BRESP),
			//
			.i_axi_arvalid(S_AXIL_ARVALID),
			.i_axi_arready(S_AXIL_ARREADY),
			.i_axi_araddr( S_AXIL_ARADDR),
			.i_axi_arprot( S_AXIL_ARPROT),
			//
			.i_axi_rvalid(S_AXIL_RVALID),
			.i_axi_rready(S_AXIL_RREADY),
			.i_axi_rdata( S_AXIL_RDATA),
			.i_axi_rresp( S_AXIL_RRESP),
			//
			.f_axi_rd_outstanding(fslv_rd_outstanding),
			.f_axi_wr_outstanding(fslv_wr_outstanding),
			.f_axi_awr_outstanding(fslv_awr_outstanding)
			// }}}
		);

		faxil_master #(
			// {{{
			.C_AXI_DATA_WIDTH(MDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_COVER_BURST(1),
			.F_LGDEPTH(F_LGDEPTH),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXRSTALL(3),
			.F_AXI_MAXDELAY(5)
			// }}}
		) axil_master (
			// {{{
			.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awvalid(M_AXIL_AWVALID),
			.i_axi_awready(M_AXIL_AWREADY),
			.i_axi_awaddr( M_AXIL_AWADDR),
			.i_axi_awprot( M_AXIL_AWPROT),
			//
			.i_axi_wvalid(M_AXIL_WVALID),
			.i_axi_wready(M_AXIL_WREADY),
			.i_axi_wdata( M_AXIL_WDATA),
			.i_axi_wstrb( M_AXIL_WSTRB),
			//
			.i_axi_bvalid(M_AXIL_BVALID),
			.i_axi_bready(M_AXIL_BREADY),
			.i_axi_bresp( M_AXIL_BRESP),
			//
			.i_axi_arvalid(M_AXIL_ARVALID),
			.i_axi_arready(M_AXIL_ARREADY),
			.i_axi_araddr( M_AXIL_ARADDR),
			.i_axi_arprot( M_AXIL_ARPROT),
			//
			.i_axi_rvalid(M_AXIL_RVALID),
			.i_axi_rready(M_AXIL_RREADY),
			.i_axi_rdata( M_AXIL_RDATA),
			.i_axi_rresp( M_AXIL_RRESP),
			//
			.f_axi_rd_outstanding(fmst_rd_outstanding),
			.f_axi_wr_outstanding(fmst_wr_outstanding),
			.f_axi_awr_outstanding(fmst_awr_outstanding)
			// }}}
		);

		// Correlate slave and master write outstanding counters
		// {{{
		always @(*)
		begin
			assume(fslv_awr_outstanding <= (1<<LGFIFO));
			assume(fslv_wr_outstanding  <= (1<<LGFIFO));

			assert(fslv_awr_outstanding + (S_AXIL_WREADY ? 0:1)
				== fslv_wr_outstanding +(S_AXIL_AWREADY ? 0:1));

			assert(fmst_awr_outstanding + (M_AXIL_AWVALID ? 1:0)
				== fmst_wr_outstanding + (M_AXIL_WVALID ? 1:0));

			assert(fslv_awr_outstanding == fmst_awr_outstanding
				+(M_AXIL_AWVALID ? 1:0)+(S_AXIL_AWREADY ? 0:1));
			assert(fslv_wr_outstanding == fmst_wr_outstanding
				+(M_AXIL_WVALID ? 1:0) + (S_AXIL_WREADY ? 0:1));
		end
		// }}}

		// Correlate the slave and master read outstanding counters
		// w/ FIFO fill
		// {{{
		always @(*)
		begin
			assert(fslv_rd_outstanding == fmst_rd_outstanding
				+(S_AXIL_RVALID ? 1:0) + (M_AXIL_RREADY ? 0:1));
			assert(rfifo_fill == fmst_rd_outstanding);

			if (M_AXIL_RVALID)
				assert(!rfifo_empty);
		end
		// }}}

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Contract checks
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// Not implemented yet

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Cover checks
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// (Currently) captured by the interface properties
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// "Careless" assumptions
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// None

		// }}}
`endif
	// }}}
	end endgenerate

	// Parameter checking
	// {{{
	initial if (SDW > MDW) $stop;
	// }}}
endmodule
