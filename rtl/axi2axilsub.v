///////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi2axilsub.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Convert from AXI to AXI-lite with no performance loss, and to
//		a potentially smaller bus width.
//
// Performance:	The goal of this converter is to convert from AXI to an AXI-lite
//		bus of a smaller width, while still maintaining the one-clock
//	per transaction speed of AXI.  It currently achieves this goal.  The
//	design needs very little configuration to be useful, but you might
//	wish to resize the FIFOs within depending upon the length of your
//	slave's data path.  The current FIFO length, LGFIFO=4, is sufficient to
//	maintain full speed.  If the slave, however, can maintain full speed but
//	requires a longer processing cycle, then you may need longer FIFOs.
//
//	The AXI specification does require an additional 2 clocks per
//	transaction when using this core, so your latency will go up.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2021, Gisselquist Technology, LLC
// {{{
// This digital logic component is the proprietary property of Gisselquist
// Technology, LLC.  It may only be distributed and/or re-distributed by the
// express permission of Gisselquist Technology.
//
// Permission has been granted to the Patreon sponsors of the ZipCPU blog
// to use this logic component as they see fit, but not to redistribute it
// beyond their individual personal or commercial use.
//
// This component is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.
//
// Please feel free to contact me should you have any questions, or even if you
// just want to ask about what you find within here.
//
// Yours,
//
// Dan Gisselquist
// Owner
// Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
`ifdef	FORMAL
`ifdef	BMC
`define	BMC_ASSERT	assert
`else
`define	BMC_ASSERT	assume
`endif
`endif
//
// }}}
module axi2axilsub #(
		// {{{
		parameter integer C_AXI_ID_WIDTH	= 2,
		parameter integer C_S_AXI_DATA_WIDTH	= 64,
		parameter integer C_M_AXI_DATA_WIDTH	= 32,
		parameter integer C_AXI_ADDR_WIDTH	= 6,
		parameter	 [0:0]	OPT_LOWPOWER	= 1,
		parameter	 [0:0]	OPT_WRITES	= 1,
		parameter	 [0:0]	OPT_READS	= 0,
		parameter		SLVSZ = $clog2(C_S_AXI_DATA_WIDTH/8),
		parameter		MSTSZ = $clog2(C_M_AXI_DATA_WIDTH/8),
		parameter		LENB = 8+SLVSZ-MSTSZ,
		// Log (based two) of the maximum number of outstanding AXI
		// (not AXI-lite) transactions.  If you multiply 2^LGFIFO * 256,
		// you'll get the maximum number of outstanding AXI-lite
		// transactions
		parameter	LGFIFO			= 4
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// AXI4 slave interface
		// {{{
		// Write address channel
		// {{{
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[7:0]			S_AXI_AWLEN,
		input	wire	[2:0]			S_AXI_AWSIZE,
		input	wire	[1:0]			S_AXI_AWBURST,
		input	wire				S_AXI_AWLOCK,
		input	wire	[3:0]			S_AXI_AWCACHE,
		input	wire	[2:0]			S_AXI_AWPROT,
		input	wire	[3:0]			S_AXI_AWQOS,
		// }}}
		// Write data channel
		// {{{
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire [C_S_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire [(C_S_AXI_DATA_WIDTH/8)-1:0] S_AXI_WSTRB,
		input	wire				S_AXI_WLAST,
		// }}}
		// Write return channel
		// {{{
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_BID,
		output	wire	[1:0]			S_AXI_BRESP,
		// }}}
		// Read address channel
		// {{{
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[7:0]			S_AXI_ARLEN,
		input	wire	[2:0]			S_AXI_ARSIZE,
		input	wire	[1:0]			S_AXI_ARBURST,
		input	wire				S_AXI_ARLOCK,
		input	wire	[3:0]			S_AXI_ARCACHE,
		input	wire	[2:0]			S_AXI_ARPROT,
		input	wire	[3:0]			S_AXI_ARQOS,
		// }}}
		// Read data channel
		// {{{
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_RID,
		output	wire [C_S_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire	[1:0]			S_AXI_RRESP,
		output	wire				S_AXI_RLAST,
		// }}}
		// }}}
		// AXI-lite master interface
		// {{{
		// AXI-lite Write interface
		// {{{
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[2 : 0]			M_AXI_AWPROT,
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire [C_M_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [(C_M_AXI_DATA_WIDTH/8)-1:0] M_AXI_WSTRB,
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		input	wire	[1 : 0]			M_AXI_BRESP,
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		// }}}
		// AXI-lite read interface
		// {{{
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_M_AXI_DATA_WIDTH-1 : 0] M_AXI_RDATA,
		input	wire	[1 : 0]			M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Local parameters, register, and net declarations
	// {{{
	// Verilator lint_off UNUSED
	localparam [1:0]	OKAY   = 2'b00,
				EXOKAY = 2'b01,
				SLVERR = 2'b10;
	// localparam [1:0]	DECERR = 2'b10;

	// Verilator lint_on UNUSED
	localparam	AW = C_AXI_ADDR_WIDTH;
	localparam	SLVDW = C_S_AXI_DATA_WIDTH;
	localparam	MSTDW = C_M_AXI_DATA_WIDTH;
	localparam	IW = C_AXI_ID_WIDTH;
	// localparam	LSB = $clog2(C_AXI_DATA_WIDTH)-3;
	// }}}
	// Register declarations
	// {{{
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_WRITES && SLVDW == MSTDW)
	begin : IMPLEMENT_AXI2AXILITE_WRITES
		// {{{

		// (Unused) signal declarations
		// {{{
		// Verilator lint_off UNUSED
		wire				ign_arready, ign_rvalid,
						ign_rlast,
						ign_arvalid, ign_rready;
		wire	[IW-1:0]		ign_rid;
		wire [SLVDW-1:0]	ign_rdata;
		wire	[1:0]			ign_rresp;
		wire	[AW-1:0]	ign_araddr;
		wire	[2:0]			ign_arprot;
		// Verilator lint_on  UNUSED
		// }}}

		axi2axilite #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_WRITES(1),
			.OPT_READS(0),
			.LGFIFO(LGFIFO)
			// }}}
		) axilwrite (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			// AXI4 slave interface
			// {{{
			// Write address channel
			// {{{
			.S_AXI_AWVALID(S_AXI_AWVALID),
			.S_AXI_AWREADY(S_AXI_AWREADY),
			.S_AXI_AWID(   S_AXI_AWID),
			.S_AXI_AWADDR( S_AXI_AWADDR),
			.S_AXI_AWLEN(  S_AXI_AWLEN),
			.S_AXI_AWSIZE( S_AXI_AWSIZE),
			.S_AXI_AWBURST(S_AXI_AWBURST),
			.S_AXI_AWLOCK( S_AXI_AWLOCK),
			.S_AXI_AWCACHE(S_AXI_AWCACHE),
			.S_AXI_AWPROT( S_AXI_AWPROT),
			.S_AXI_AWQOS(  S_AXI_AWQOS),
			// }}}
			// Write data channel
			// {{{
			.S_AXI_WVALID(S_AXI_WVALID),
			.S_AXI_WREADY(S_AXI_WREADY),
			.S_AXI_WDATA( S_AXI_WDATA),
			.S_AXI_WSTRB( S_AXI_WSTRB),
			.S_AXI_WLAST( S_AXI_WLAST),
			// }}}
			// Write return channel
			// {{{
			.S_AXI_BVALID(S_AXI_BVALID),
			.S_AXI_BREADY(S_AXI_BREADY),
			.S_AXI_BID(   S_AXI_BID),
			.S_AXI_BRESP( S_AXI_BRESP),
			// }}}
			// Read address channel
			// {{{
			.S_AXI_ARVALID(1'b0),
			.S_AXI_ARREADY(ign_arready),
			.S_AXI_ARID(   {(IW){1'b0}}),
			.S_AXI_ARADDR( {(AW){1'b0}}),
			.S_AXI_ARLEN(  8'h0),
			.S_AXI_ARSIZE( 3'h0),
			.S_AXI_ARBURST(2'h0),
			.S_AXI_ARLOCK( 1'b0),
			.S_AXI_ARCACHE(4'h0),
			.S_AXI_ARPROT( 3'h0),
			.S_AXI_ARQOS(  4'h0),
			// }}}
			// Read data channel
			// {{{
			.S_AXI_RVALID(ign_rvalid),
			.S_AXI_RREADY(1'b1),
			.S_AXI_RID(   ign_rid),
			.S_AXI_RDATA( ign_rdata),
			.S_AXI_RRESP( ign_rresp),
			.S_AXI_RLAST( ign_rlast),
			// }}}
			// }}}
			// AXI-lite master interface
			// {{{
			// AXI-lite Write interface
			// {{{
			.M_AXI_AWVALID(M_AXI_AWVALID),
			.M_AXI_AWREADY(M_AXI_AWREADY),
			.M_AXI_AWADDR(M_AXI_AWADDR),
			.M_AXI_AWPROT(M_AXI_AWPROT),
			//
			.M_AXI_WVALID(M_AXI_WVALID),
			.M_AXI_WREADY(M_AXI_WREADY),
			.M_AXI_WDATA(M_AXI_WDATA),
			.M_AXI_WSTRB(M_AXI_WSTRB),
			//
			.M_AXI_BVALID(M_AXI_BVALID),
			.M_AXI_BREADY(M_AXI_BREADY),
			.M_AXI_BRESP(M_AXI_BRESP),
			// }}}
			// AXI-lite read interface
			// {{{
			.M_AXI_ARVALID(ign_arvalid),
			.M_AXI_ARREADY(1'b1),
			.M_AXI_ARADDR(ign_araddr),
			.M_AXI_ARPROT(ign_arprot),
			//
			.M_AXI_RVALID(1'b0),
			.M_AXI_RREADY(ign_rready),
			.M_AXI_RDATA({(MSTDW){1'b0}}),
			.M_AXI_RRESP(2'b00)
			// }}}
			// }}}
			// }}}
		);

		// }}}		
	end else if (OPT_WRITES)
	begin : IMPLEMENT_WRITES
		// {{{

		// Register declarations
		// {{{

		//
		// S_AXI_AW* skid buffer
		wire			skids_awvalid;
		reg			skids_awready;
		wire	[IW-1:0]	skids_awid;
		wire	[AW-1:0]	skids_awaddr;
		wire	[7:0]		skids_awlen;
		wire	[2:0]		skids_awsize;
		wire	[1:0]		skids_awburst;
		wire	[2:0]		skids_awprot;
		//
		// S_AXI_W* skid buffer
		wire			skids_wvalid, skids_wready;
		wire	[SLVDW-1:0]	skids_wdata;
		wire	[SLVDW/8-1:0]	skids_wstrb;

		wire					slv_awvalid,slv_awready;
		reg	[SLVDW-1:0]	slv_wdata;
		reg	[SLVDW/8-1:0]	slv_wstrb;

		reg	[IW-1:0]			slv_awid;
		reg	[AW-1:0]			slv_awaddr,
							slv_next_awaddr;
		reg	[2:0]				slv_awsize;
		reg	[1:0]				slv_awburst;
		reg	[2:0]				slv_awprot;
		reg	[7:0]				slv_awlen;
		reg	[8:0]				slv_wlen;
		reg					slv_awlast;

		// Write registers
		reg				m_axi_awvalid;
		reg				bfifo_write, wfifo_wlast;
		reg	[IW+1+SLVSZ-MSTSZ:0]	bfifo_wdata;
		wire	[LGFIFO:0]		wfifo_count;
		wire				wfifo_full;
		wire				wfifo_empty;
		wire	[SLVSZ-MSTSZ:0]		wfifo_subcount;
		wire	[IW-1:0]		wfifo_bid;
		reg	[SLVSZ-MSTSZ:0]		bcounts;
		reg	[IW-1:0]	s_axi_bid, bid;
		reg				blast;
		reg	[1:0]			s_axi_bresp, bresp;
		reg				s_axi_bvalid;
		wire				read_from_wrfifo;
		//
		// S_AXI_B* skid buffer isn't needed
		//
		// M_AXI_AW* skid buffer isn't needed
		//
		// M_AXI_W* skid buffer isn't needed
		//
		// M_AXI_B* skid buffer
		wire			skidm_bvalid, skidm_bready;
		wire	[1:0]		skidm_bresp;

		reg				m_axi_wvalid;
		reg	[AW-1:0]		mst_awaddr;
		reg	[2:0]			mst_awprot;
		reg	[SLVSZ-MSTSZ:0]		slv_awbeats, mst_awbeats,
						mst_wbeats;

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Incoming write address / data handling
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// The write address channel's skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2+3),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) awskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
				S_AXI_AWSIZE, S_AXI_AWBURST, S_AXI_AWPROT }),
			.o_valid(skids_awvalid), .i_ready(skids_awready),
			.o_data({ skids_awid, skids_awaddr, skids_awlen,
				skids_awsize, skids_awburst, skids_awprot })
			// }}}
		);
		// }}}
		//
		// The write data channel's skid buffer (S_AXI_W*)
		// {{{
		skidbuffer #(
			// {{{
			.DW(SLVDW+SLVDW/8),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) wskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
			.o_valid(skids_wvalid), .i_ready(skids_wready),
			.o_data({ skids_wdata, skids_wstrb })
			// }}}
		);
		// }}}

		assign	skids_awready = (slv_wlen >= (slv_awready ? 1:0));
		assign	slv_awvalid = (slv_wlen > 0);
		assign	slv_awready = (!M_AXI_AWVALID || M_AXI_AWREADY)
					&& (mst_wbeats <= (M_AXI_WREADY ? 1:0))
					&& (!bfifo_write || !wfifo_full);

		// slv_aw*
		// {{{
		always @(posedge S_AXI_ACLK)
		if (skids_awvalid && skids_awready)
		begin
			slv_awid    <= skids_awid;
			slv_awaddr  <= skids_awaddr;
			slv_awlen   <= skids_awlen;
			slv_awsize  <= skids_awsize;
			slv_awburst <= skids_awburst;
			slv_awprot  <= skids_awprot;
			slv_wlen    <= skids_awlen + 1;
			slv_awlast  <= (skids_awlen == 0);
		end else if (slv_awready && slv_wlen > 0)
		begin
			slv_wlen   <= slv_wlen - 1;
			slv_awaddr <= slv_next_awaddr;
			slv_awlast <= (slv_wlen <= 2);
		end
`ifdef	FORMAL
		always @(*)
			assert(slv_awlast == (slv_wlen <= 1));
		always @(*)
			assert(slv_wlen <= (slv_awlen + 1));
`endif
		// }}}

		// slv_next_awaddr
		// {{{
		axi_addr #(
			// {{{
			.AW(AW),
			.DW(SLVDW)
			// }}}
		) get_next_slave_addr (
			// {{{
			.i_last_addr(slv_awaddr),
			.i_size(slv_awsize),
			.i_burst(slv_awburst),
			.i_len(slv_awlen),
			.o_next_addr(slv_next_awaddr)
			// }}}
		);
		// }}}

		// slv_awbeats
		// {{{
		always @(*)
		if (slv_awvalid)
		begin
			// Master beats to turn this slave beat into
			if (slv_awsize >= MSTSZ[2:0])
				slv_awbeats = (1<<(slv_awsize-MSTSZ[2:0]))
					- (slv_awaddr[MSTSZ-1:0] >> slv_awsize);
			else
				slv_awbeats = 1;
		end else
			slv_awbeats = 0;
		// }}}

		// mst_awaddr, mst_awprot, mst_awbeats
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (slv_awready)
			begin
				// {{{
				mst_awaddr  <= slv_awaddr;
				mst_awprot  <= slv_awprot;

				// Beats to turn this beat into
				mst_awbeats <= slv_awbeats;

				if (OPT_LOWPOWER && !slv_awvalid)
				begin
					mst_awaddr <= 0;
					mst_awprot <= 0;
				end
				// }}}
			end else if (mst_awbeats > 0)
			begin
				// {{{
				mst_awaddr <= mst_awaddr + (1<<SLVSZ);
				mst_awaddr[SLVSZ-1:0] <= 0;
				mst_awbeats <= mst_awbeats - 1;
				// }}}
			end

			if (!S_AXI_ARESETN)
			begin
				// {{{
				mst_awbeats <= 0;
				if (OPT_LOWPOWER)
				begin
					mst_awaddr  <= 0;
					mst_awprot  <= 0;
				end
				// }}}
			end
		end
`ifdef	FORMAL
		always @(*)
		if(OPT_LOWPOWER && mst_awbeats == 0)
		begin
			assert(mst_awaddr == 0);
			assert(mst_awprot == 0);
		end
`endif
		// }}}

		// skids_wready
		// {{{
		assign	skids_wready = (mst_wbeats <= (M_AXI_WREADY ? 1:0))
					&&((slv_awbeats > 0) || slv_awready);
		// }}}

		// m_axi_awvalid
		// {{{
		initial	m_axi_awvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_awvalid <= 0;
		else if (skids_awvalid && skids_awready)
			m_axi_awvalid <= 1;
		else if (!M_AXI_AWVALID || M_AXI_AWREADY)
			m_axi_awvalid <= (mst_awbeats > 1);

		assign	M_AXI_AWVALID = m_axi_awvalid;
		// }}}

		// M_AXI_WVALID, mst_wbeats
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			m_axi_wvalid <= 0;
			mst_wbeats   <= 0;
		end else if (skids_wready)
		begin
			m_axi_wvalid <= skids_wvalid;
			mst_wbeats   <= slv_awbeats;
		end else if (M_AXI_WVALID && M_AXI_WREADY)
		begin
			m_axi_wvalid <= (mst_wbeats > 1);
			if (mst_wbeats > 0)
				mst_wbeats   <= mst_wbeats - 1;
		end
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN)
			assert(M_AXI_WVALID == (mst_wbeats > 0));
`endif
		// }}}

		// slv_wstrb, slv_wdata
		// {{{
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			{ slv_wstrb, slv_wdata } <= 0;
		else if (skids_wready)
		begin
			slv_wstrb <= skids_wstrb >> (slv_awaddr[SLVSZ-1:MSTSZ]);
			slv_wdata <= skids_wdata >> (slv_awaddr[SLVSZ-1:MSTSZ]*8);
			if (OPT_LOWPOWER && !skids_wvalid)
			begin
				slv_wstrb <= 0;
				slv_wdata <= 0;
			end
		end else if (M_AXI_WVALID && M_AXI_WREADY)
		begin
			slv_wstrb <= slv_wstrb >> (MSTDW/8);
			slv_wdata <= slv_wdata >> (MSTDW);
		end
`ifdef	FORMAL
		always @(*)
		if (OPT_LOWPOWER && S_AXI_ARESETN && !M_AXI_WVALID)
		begin
			assert(slv_wstrb == 0);
			assert(slv_wdata == 0);
		end
`endif
		// }}}

		assign	M_AXI_WVALID = m_axi_wvalid;
		assign	M_AXI_WDATA  = slv_wdata[MSTDW-1:0];
		assign	M_AXI_WSTRB  = slv_wstrb[MSTDW/8-1:0];

		// read_from_wrfifo
		// {{{
		assign	read_from_wrfifo = (bcounts <= 1)&&(!wfifo_empty)
			    &&(skidm_bvalid && skidm_bready);
		// }}}

		//
		// The downstream AXI-lite response (M_AXI_B*) skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(2),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) bskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(M_AXI_BVALID), .o_ready(M_AXI_BREADY),
				.i_data({ M_AXI_BRESP }),
			.o_valid(skidm_bvalid), .i_ready(skidm_bready),
				.o_data({ skidm_bresp })
			// }}}
		);
		// }}}

		// bfifo_write
		// {{{
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bfifo_write <= 0;
		else
			bfifo_write <= slv_awready && slv_wlen != 0;
		// }}}

		// bfifo_wdata
		// {{{
		always @(posedge  S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bfifo_wdata <= 0;
		else
			bfifo_wdata <= { slv_awid, slv_awlast, slv_awbeats };
		// }}}

		// BFIFO
		// {{{
		sfifo	#(
			// {{{
			.BW(IW+1+(SLVSZ-MSTSZ+1)),
			.LGFLEN(LGFIFO)
			// }}}
		) bidlnfifo(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			bfifo_write, bfifo_wdata, wfifo_full, wfifo_count,
			read_from_wrfifo,
			{ wfifo_bid, wfifo_wlast,wfifo_subcount }, wfifo_empty);
			// }}}
		// }}}

		// bcounts
		// {{{
		// Return counts
		initial	bcounts = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bcounts <= 0;
		else if (read_from_wrfifo)
			bcounts <= wfifo_subcount + bcounts;
		else if (skidm_bvalid && skidm_bready)
			bcounts <= bcounts - 1;
		// }}}

		// blast
		// {{{
		always @(posedge S_AXI_ACLK)
		if (read_from_wrfifo)
			blast <= wfifo_wlast;
		// }}}

		// bid
		// {{{
		always @(posedge S_AXI_ACLK)
		if (read_from_wrfifo)
			bid <= wfifo_bid;
		// }}}

		// bresp
		// {{{
		initial	bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bresp <= OKAY;
		else if (!S_AXI_BVALID || S_AXI_BREADY)
			bresp <= OKAY;
		else if (skidm_bvalid && skidm_bready)
		begin
			if (skidm_bvalid && skidm_bready)
			begin
				// Let SLVERR take priority over DECERR
				casez({ bresp, skidm_bresp })
				4'b??0?: bresp <= bresp;
				4'b0?1?: bresp <= skidm_bresp;
				4'b1?10: bresp <= SLVERR;
				4'b1011: bresp <= SLVERR;
				4'b1111: bresp <= skidm_bresp;
				endcase
			end

			if (blast)
				bresp <= OKAY;
		end
		// }}}

		// s_axi_bid
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (!skidm_bvalid || skidm_bready)
				s_axi_bid <= (read_from_wrfifo && bcounts==0) ? wfifo_bid : bid;
			if (OPT_LOWPOWER && !S_AXI_ARESETN)
				s_axi_bid <= 0;
		end
		// }}}

		// s_axi_bvalid
		// {{{
		initial	s_axi_bvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_bvalid <= 0;
		else if (skidm_bvalid && skidm_bready)
			s_axi_bvalid <= ((bcounts == 1)&& blast)
				||((bcounts == 0) && (!wfifo_empty)
					&& (wfifo_subcount == 0) && wfifo_wlast);
		else if (S_AXI_BREADY)
			s_axi_bvalid <= 0;
		// }}}

		// s_axi_bresp
		// {{{
		initial	s_axi_bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_bresp <= 0;
		else if (!S_AXI_BVALID || S_AXI_BREADY)
		begin
			if (skidm_bvalid && skidm_bready)
			begin
				// Let SLVERR take priority over DECERR
				casez({ bresp, skidm_bresp[1] })
				3'b??0: s_axi_bresp <= s_axi_bresp;
				3'b0?1: s_axi_bresp <= skidm_bresp;
				3'b101: s_axi_bresp <= SLVERR;
				3'b111: s_axi_bresp <= skidm_bresp;
				endcase
			end else
				s_axi_bresp <= bresp;
		end
`ifdef	FORMAL
		(* anyconst *) reg	[1:0]	f_max_bresp;

		always @(*)
		begin
			assume(skidm_bresp <= f_max_bresp);
			assume(skidm_bresp != EXOKAY);

			assert(bresp <= f_max_bresp);
			assert(bresp != EXOKAY);
			if (S_AXI_BVALID)
			begin
				assert(S_AXI_BRESP <= f_max_bresp);
				assert(S_AXI_BRESP != EXOKAY);
			end
		end
`endif
		// }}}

		// M_AXI_AW*
		// {{{
		assign	M_AXI_AWVALID= m_axi_awvalid;
		assign	M_AXI_AWADDR = mst_awaddr;
		assign	M_AXI_AWPROT = mst_awprot;
		// }}}

		// skidm_bready, S_AXI_B*
		// {{{
		assign	skidm_bready = ((bcounts > 0)||(!wfifo_empty))
				&& (!S_AXI_BVALID || S_AXI_BREADY || !blast);
		assign	S_AXI_BID    = s_axi_bid;
		assign	S_AXI_BRESP  = s_axi_bresp;
		assign	S_AXI_BVALID = s_axi_bvalid;
		// }}}
		// }}}
		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_write;
		assign	unused_write = &{ 1'b0, wfifo_count, S_AXI_WLAST };
		// Verilator lint_on  UNUSED
		// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties, write half
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		// These are only a subset of the formal properties used to
		// verify this design.  While I will warrant that the full
		// property set will work, I don't really expect the below
		// properties to be sufficient or for that matter even
		// syntactically correct.
		//
		// Register declarations
		// {{{
		localparam	F_LGDEPTH = LGFIFO+1+8;

		wire	[F_LGDEPTH-1:0]		faxi_awr_nbursts;
		wire	[9-1:0]			faxi_wr_pending;
		wire	[F_LGDEPTH-1:0]		faxi_rd_nbursts;
		wire	[F_LGDEPTH-1:0]		faxi_rd_outstanding;

		//
		// ...
		//
	
		localparam	F_AXIL_LGDEPTH = F_LGDEPTH;
		wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
						faxil_wr_outstanding,
						faxil_awr_outstanding;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI channel properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxi_slave #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_LGDEPTH(F_AXIL_LGDEPTH),
			.OPT_EXCLUSIVE(0)
			// ...
			// }}}
		) faxi(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address
			// {{{
			.i_axi_awready(skids_awready),
			.i_axi_awid(   skids_awid),
			.i_axi_awaddr( skids_awaddr),
			.i_axi_awlen(  skids_awlen),
			.i_axi_awsize( skids_awsize),
			.i_axi_awburst(skids_awburst),
			.i_axi_awlock( 0),
			.i_axi_awcache(0),
			.i_axi_awprot( 0),
			.i_axi_awqos(  0),
			.i_axi_awvalid(skids_awvalid),
			// }}}
			// Write data
			// {{{
			.i_axi_wready( skids_wready),
			.i_axi_wdata(  skids_wdata),
			.i_axi_wstrb(  skids_wstrb),
			.i_axi_wlast(  S_AXI_WLAST),
			.i_axi_wvalid( skids_wvalid),
			// }}}
			// Write return response
			// {{{
			.i_axi_bid(    S_AXI_BID),
			.i_axi_bresp(  S_AXI_BRESP),
			.i_axi_bvalid( S_AXI_BVALID),
			.i_axi_bready( S_AXI_BREADY),
			// }}}
			// Read address
			// {{{
			.i_axi_arready(skids_arready),
			.i_axi_arid(   skids_arid),
			.i_axi_araddr( skids_araddr),
			.i_axi_arlen(  skids_arlen),
			.i_axi_arsize( skids_arsize),
			.i_axi_arburst(skids_arburst),
			.i_axi_arlock( 0),
			.i_axi_arcache(0),
			.i_axi_arprot( 0),
			.i_axi_arqos(  0),
			.i_axi_arvalid(skids_arvalid),
			// }}}
			// Read response
			// {{{
			.i_axi_rid(    S_AXI_RID),
			.i_axi_rresp(  S_AXI_RRESP),
			.i_axi_rvalid( S_AXI_RVALID),
			.i_axi_rdata(  S_AXI_RDATA),
			.i_axi_rlast(  S_AXI_RLAST),
			.i_axi_rready( S_AXI_RREADY),
			// }}}
			// Formal property data
			// {{{
			.f_axi_awr_nbursts(   faxi_awr_nbursts),
			.f_axi_wr_pending(    faxi_wr_pending),
			.f_axi_rd_nbursts(    faxi_rd_nbursts),
			.f_axi_rd_outstanding(faxi_rd_outstanding)
			//
			// ...
			//
			// }}}
			// }}}
		);

		always @(*)
		begin
			// ...
			assert(faxi_rd_nbursts == 0);
		end

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI-lite properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxil_master #(
			// {{{
			.C_AXI_DATA_WIDTH(MSTDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXDELAY(4),
			.F_AXI_MAXRSTALL(0),
			.F_OPT_WRITE_ONLY(OPT_WRITES && !OPT_READS),
			.F_OPT_READ_ONLY(!OPT_WRITES &&  OPT_READS),
			.F_LGDEPTH(F_AXIL_LGDEPTH)
			// }}}
		) faxil(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address channel
			// {{{
			.i_axi_awready(M_AXI_AWREADY),
			.i_axi_awaddr( M_AXI_AWADDR),
			.i_axi_awcache(4'h0),
			.i_axi_awprot( M_AXI_AWPROT),
			.i_axi_awvalid(M_AXI_AWVALID),
			// }}}
			// Write data
			// {{{
			.i_axi_wready( M_AXI_WREADY),
			.i_axi_wdata(  M_AXI_WDATA),
			.i_axi_wstrb(  M_AXI_WSTRB),
			.i_axi_wvalid( M_AXI_WVALID),
			// }}}
			// Write response
			// {{{
			.i_axi_bresp(  skidm_bresp),
			.i_axi_bvalid( skidm_bvalid),
			.i_axi_bready( skidm_bready),
			// }}}
			// Read address
			// {{{
			.i_axi_arready(M_AXI_ARREADY),
			.i_axi_araddr( M_AXI_ARADDR),
			.i_axi_arcache(4'h0),
			.i_axi_arprot( M_AXI_ARPROT),
			.i_axi_arvalid(M_AXI_ARVALID),
			// }}}
			// Read data return
			// {{{
			.i_axi_rresp(  skidm_rresp),
			.i_axi_rvalid( skidm_rvalid),
			.i_axi_rdata(  skidm_rdata),
			.i_axi_rready( skidm_rready),
			// }}}
			// Formal check variables
			// {{{
			.f_axi_rd_outstanding(faxil_rd_outstanding),
			.f_axi_wr_outstanding(faxil_wr_outstanding),
			.f_axi_awr_outstanding(faxil_awr_outstanding)
			// }}}
			// }}}
		);

		always @(*)
			assert(faxil_rd_outstanding == 0);
		always @(*)
			assert(faxil_awr_outstanding == wfifo_count - (M_AXI_AWVALID&&!bfifo_write) ? 1:0));
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// BFIFO property checking
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		//
		// ...
		//

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN)
		begin
			assert(faxi_awr_nbursts == f_bfifo_packets
				+ (slv_awvalid ? 1:0));
			assert(f_bfifo_packets <= wfifo_count);

			// ...
		end

		//
		// ...
		//

		// }}}
`endif
		// }}}
	end else begin : NO_WRITE_SUPPORT
		// {{{
		assign	S_AXI_AWREADY = 0;
		assign	S_AXI_WREADY  = 0;
		assign	S_AXI_BID     = 0;
		assign	S_AXI_BRESP   = 2'b11;
		assign	S_AXI_BVALID  = 0;
		assign	S_AXI_BID     = 0;

		//
		assign	M_AXI_AWVALID = 0;
		assign	M_AXI_AWADDR  = 0;
		assign	M_AXI_AWPROT  = 0;
		//
		assign	M_AXI_WVALID  = 0;
		assign	M_AXI_WDATA   = 0;
		assign	M_AXI_WSTRB   = 0;
		//
		assign	M_AXI_BREADY  = 0;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_READS && SLVDW == MSTDW)
	begin : IMPLEMENT_AXI2AXILITE_READS
		// {{{

		// (Unused) signal declarations
		// {{{
		// Verilator lint_off UNUSED
		wire				ign_awready, ign_wready,
						ign_bvalid;
		wire	[IW-1:0]	ign_bid;
		wire	[1:0]			ign_bresp;

		wire				ign_awvalid, ign_wvalid,
						ign_bready;
		wire	[AW-1:0]	ign_awaddr;
		wire	[2:0]			ign_awprot;
		wire	[MSTDW-1:0]	ign_wdata;
		wire	[MSTDW/8-1:0]	ign_wstrb;
		// Verilator lint_on  UNUSED
		// }}}

		axi2axilite #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_WRITES(0),
			.OPT_READS(1),
			.LGFIFO(LGFIFO)
			// }}}
		) axilread (
		// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			// AXI4 slave interface
			// {{{
			// Write address channel
			// {{{
			.S_AXI_AWVALID(1'b0),
			.S_AXI_AWREADY(ign_awready),
			.S_AXI_AWID(   {(IW){1'b0}} ),
			.S_AXI_AWADDR( {(AW){1'b0}} ),
			.S_AXI_AWLEN(  8'h0),
			.S_AXI_AWSIZE( 3'h0),
			.S_AXI_AWBURST(2'h0),
			.S_AXI_AWLOCK( 1'b0),
			.S_AXI_AWCACHE(4'h0),
			.S_AXI_AWPROT( 3'h0),
			.S_AXI_AWQOS(  4'h0),
			// }}}
			// Write data channel
			// {{{
			.S_AXI_WVALID(1'b0),
			.S_AXI_WREADY(ign_wready),
			.S_AXI_WDATA( {(SLVDW){1'b0}}),
			.S_AXI_WSTRB( {(SLVDW/8){1'b0}}),
			.S_AXI_WLAST( 1'b0),
			// }}}
			// Write return channel
			// {{{
			.S_AXI_BVALID(ign_bvalid),
			.S_AXI_BREADY(1'b1),
			.S_AXI_BID(   ign_bid),
			.S_AXI_BRESP( ign_bresp),
			// }}}
			// Read address channel
			// {{{
			.S_AXI_ARVALID(S_AXI_ARVALID),
			.S_AXI_ARREADY(S_AXI_ARREADY),
			.S_AXI_ARID(   S_AXI_ARID),
			.S_AXI_ARADDR( S_AXI_ARADDR),
			.S_AXI_ARLEN(  S_AXI_ARLEN),
			.S_AXI_ARSIZE( S_AXI_ARSIZE),
			.S_AXI_ARBURST(S_AXI_ARBURST),
			.S_AXI_ARLOCK( S_AXI_ARLOCK),
			.S_AXI_ARCACHE(S_AXI_ARCACHE),
			.S_AXI_ARPROT( S_AXI_ARPROT),
			.S_AXI_ARQOS(  S_AXI_ARQOS),
			// }}}
			// Read data channel
			// {{{
			.S_AXI_RVALID(S_AXI_RVALID),
			.S_AXI_RREADY(S_AXI_RREADY),
			.S_AXI_RID(   S_AXI_RID),
			.S_AXI_RDATA( S_AXI_RDATA),
			.S_AXI_RRESP( S_AXI_RRESP),
			.S_AXI_RLAST( S_AXI_RLAST),
			// }}}
			// }}}
			// AXI-lite master interface
			// {{{
			// AXI-lite Write interface
			// {{{
			.M_AXI_AWVALID(ign_awvalid),
			.M_AXI_AWREADY(1'b1),
			.M_AXI_AWADDR(ign_awaddr),
			.M_AXI_AWPROT(ign_awprot),
			//
			.M_AXI_WVALID(ign_wvalid),
			.M_AXI_WREADY(1'b1),
			.M_AXI_WDATA(ign_wdata),
			.M_AXI_WSTRB(ign_wstrb),
			//
			.M_AXI_BVALID(1'b0),
			.M_AXI_BREADY(ign_bready),
			.M_AXI_BRESP(2'b00),
			// }}}
			// AXI-lite read interface
			// {{{
			.M_AXI_ARVALID(M_AXI_ARVALID),
			.M_AXI_ARREADY(M_AXI_ARREADY),
			.M_AXI_ARADDR(M_AXI_ARADDR),
			.M_AXI_ARPROT(M_AXI_ARPROT),
			//
			.M_AXI_RVALID(M_AXI_RVALID),
			.M_AXI_RREADY(M_AXI_RREADY),
			.M_AXI_RDATA(M_AXI_RDATA),
			.M_AXI_RRESP(M_AXI_RRESP)
			// }}}
			// }}}
			// }}}
		);

		// }}}		
	end else if (OPT_READS)
	begin : IMPLEMENT_READS
		// {{{

		// Declarations
		// {{{
		wire				slv_arready;
		reg	[IW-1:0]	slv_arid, mst_arid;
		reg	[AW-1:0]		slv_araddr, mst_araddr;
		wire	[AW-1:0]		slv_next_araddr;
		reg	[7:0]			slv_arlen;
		reg				slv_arlast, mst_arlast,
						mst_arsublast;
		reg	[2:0]			slv_arprot, mst_arprot;
		reg	[2:0]			slv_arsize;
		reg	[1:0]			slv_arburst;
		reg	[SLVSZ-MSTSZ:0]		slv_arbeats, mst_arbeats;
		reg	[8:0]			slv_rlen;

		wire	[SLVSZ-MSTSZ-1:0]	rfifo_addr;
		wire				rfifo_end_of_beat,
						rfifo_rlast;
		wire	[4:0]			rfifo_count;
		//
		reg				m_axi_arvalid;
		wire				rfifo_full;
		wire				rfifo_empty;
		reg				s_axi_rvalid;
		reg	[1:0]			s_axi_rresp;
		reg	[IW-1:0]	s_axi_rid;
		wire	[IW-1:0]	rfifo_rid;
		reg [SLVDW-1:0]	s_axi_rdata, next_rdata;
		reg				s_axi_rlast;
		reg	[IW-1:0]		rid;
		wire				read_from_rdfifo;

		//
		//
		// S_AXI_AR* skid buffer
		wire			skids_arvalid, skids_arready;
		wire	[IW-1:0]	skids_arid;
		wire	[AW-1:0]	skids_araddr;
		wire	[7:0]		skids_arlen;
		wire	[2:0]		skids_arsize, skids_arprot;
		wire	[1:0]		skids_arburst;
		//
		// S_AXI_R* skid buffer isn't needed
		//
		// M_AXI_AR* skid buffer isn't needed
		// M_AXI_R* skid buffer
		wire			skidm_rvalid, skidm_rready;
		wire	[MSTDW-1:0]	skidm_rdata;
		wire	[1:0]		skidm_rresp;
		// }}}

		// S_AXI_AR* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2+3),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) arskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data({ S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN,
				S_AXI_ARSIZE, S_AXI_ARBURST, S_AXI_ARPROT }),
			.o_valid(skids_arvalid), .i_ready(skids_arready),
			.o_data({ skids_arid, skids_araddr, skids_arlen,
				skids_arsize, skids_arburst, skids_arprot })
			// }}}
		);
		// }}}
		// M_AXI_R* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(MSTDW+2),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) rskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(M_AXI_RVALID), .o_ready(M_AXI_RREADY),
				.i_data({ M_AXI_RDATA, M_AXI_RRESP }),
			.o_valid(skidm_rvalid), .i_ready(skidm_rready),
				.o_data({ skidm_rdata, skidm_rresp })
			// }}}
		);
		// }}}
		// m_axi_arvalid
		// {{{
		initial	m_axi_arvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_arvalid <= 0;
		else if (skids_arvalid && skids_arready)
			m_axi_arvalid <= 1;
		else if (M_AXI_ARREADY && slv_rlen == 0)
			m_axi_arvalid <= 0;
		// }}}

		// slv_*
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (OPT_LOWPOWER && (slv_rlen <= (slv_arready ? 1:0)))
			begin
				// {{{
				slv_arid    <= 0;
				slv_araddr  <= 0;
				slv_arlen   <= 0;
				slv_arsize  <= 0;
				slv_arburst <= 0;
				slv_arprot  <= 0;

				slv_rlen    <= 0;
				// }}}
			end

			if (skids_arvalid && skids_arready)
			begin
				// {{{
				slv_arid    <= skids_arid;
				slv_araddr  <= skids_araddr;
				slv_arlen   <= skids_arlen;
				slv_arsize  <= skids_arsize;
				slv_arburst <= skids_arburst;
				slv_arlast  <= (skids_arlen == 0);
				slv_arprot  <= skids_arprot;

				slv_rlen    <= skids_arlen+1;
				// }}}
			end else if (slv_arready && slv_rlen > 0)
			begin
				// {{{
				slv_araddr  <= (!OPT_LOWPOWER || slv_rlen > 1)
							? slv_next_araddr : 0;
				slv_rlen    <= slv_rlen - 1;
				slv_arlast  <= (slv_rlen <= 2);
				// }}}
			end

			if (OPT_LOWPOWER && !S_AXI_ARESETN)
			begin
				// {{{
				slv_arid    <= 0;
				slv_araddr  <= 0;
				slv_arlen   <= 0;
				slv_arsize  <= 0;
				slv_arburst <= 0;
				slv_arprot  <= 0;

				slv_rlen    <= 0;
				// }}}
			end
		end
`ifdef	FORMAL
		always @(*)
			assert(slv_arlast == (skids_rlen <= 1));
		always @(*)
			assert(slv_rlen <= (skids_arlen + 1));
`endif
		// }}}

		// slv_next_araddr
		// {{{
		axi_addr #(
			// {{{
			.AW(AW),
			.DW(SLVDW)
			// }}}
		) get_next_slave_addr (
			// {{{
			.i_last_addr(slv_araddr),
			.i_size(slv_arsize),
			.i_burst(slv_arburst),
			.i_len(slv_arlen),
			.o_next_addr(slv_next_araddr)
			// }}}
		);
		// }}}


		// slv_arbeats
		// {{{
		always @(*)
		if (slv_rlen > 0)
		begin
			// Master beats to turn this slave beat into
			if (slv_arsize >= MSTSZ[2:0])
				slv_arbeats = (1<<(slv_arsize-MSTSZ[2:0]))
					- (slv_araddr[MSTSZ-1:0] >> slv_arsize);
			else
				slv_arbeats = 1;
		end else
			slv_arbeats = 0;
		// }}}

		// mst_araddr, mst_arprot, mst_arbeats
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (slv_arready)
			begin
				// {{{
				mst_arid    <= slv_arid;
				mst_araddr  <= slv_araddr;
				mst_arprot  <= slv_arprot;

				// Beats to turn this beat into
				mst_arbeats <= slv_arbeats;
				mst_arlast  <= slv_arlast;
				mst_arsublast <= (slv_arbeats <= 1);

				if (OPT_LOWPOWER && slv_rlen == 0)
				begin
					mst_arid   <= 0;
					mst_araddr <= 0;
					mst_arprot <= 0;
				end
				// }}}
			end else if (mst_arbeats > 0)
			begin
				// {{{
				mst_araddr <= mst_araddr + (1<<SLVSZ);
				mst_araddr[SLVSZ-1:0] <= 0;
				mst_arbeats <= mst_arbeats - 1;

				mst_arsublast <= (mst_arbeats <= 2);
				// }}}
			end

			if (!S_AXI_ARESETN)
			begin
				// {{{
				mst_arbeats <= 0;
				if (OPT_LOWPOWER)
				begin
					mst_arid    <= 0;
					mst_araddr  <= 0;
					mst_arprot  <= 0;
				end
				// }}}
			end
		end
`ifdef	FORMAL
		always @(*)
		if(OPT_LOWPOWER && mst_arbeats == 0)
		begin
			assert(mst_arid   == 0);
			assert(mst_araddr == 0);
			assert(mst_arprot == 0);
		end
`endif
		// }}}

		// m_axi_arvalid
		// {{{
		initial	m_axi_arvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_arvalid <= 0;
		else if (skids_arvalid && skids_arready)
			m_axi_arvalid <= 1;
		else if (!M_AXI_ARVALID || M_AXI_ARREADY)
			m_axi_arvalid <= (mst_arbeats > 1);

		assign	M_AXI_ARVALID = m_axi_arvalid;
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN)
			assert(M_AXI_ARVALID == (mst_arbeats > 1));
`endif
		// }}}

		assign	skids_arready = (slv_rlen >= (slv_arready ? 1:0))
					&&(mst_arbeats >=(M_AXI_ARREADY ? 1:0));
		assign	slv_arready = (mst_arbeats <= (M_AXI_ARREADY ? 1:0));
		assign	read_from_rdfifo = skidm_rvalid && skidm_rready
					&& (rfifo_rlast && rfifo_end_of_beat) && !rfifo_empty;

		// Read ID FIFO
		// {{{
		sfifo	#(
			// {{{
			.BW(IW+2+SLVSZ-MSTSZ),
			.LGFLEN(LGFIFO)
			// }}}
		) ridlnfifo(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			//
			.i_wr(M_AXI_ARVALID && M_AXI_ARREADY),
			.i_data({ mst_arid, mst_arlast, mst_arsublast,
				M_AXI_ARADDR[SLVSZ-1:MSTSZ] }),
			.o_full(rfifo_full), .o_fill(rfifo_count),
			//
			.i_rd(read_from_rdfifo),
			.o_data({ rfifo_rid, rfifo_rlast, rfifo_end_of_beat,
				rfifo_addr }),
			.o_empty(rfifo_empty)
			// }}}
		);
		// }}}

		assign	skidm_rready = (!S_AXI_RVALID || S_AXI_RREADY);

		// s_axi_rvalid
		// {{{
		initial	s_axi_rvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_rvalid <= 0;
		else if (skidm_rvalid && skidm_rready && rfifo_end_of_beat)
			s_axi_rvalid <= 1;
		else if (S_AXI_RREADY)
			s_axi_rvalid <= 0;
		// }}}

		// s_axi_rresp, s_axi_rdata
		// {{{
		always @(*)
		begin
			next_rdata = s_axi_rdata;
			if (S_AXI_RVALID)
				next_rdata = 0;
			if (skidm_rvalid)
				next_rdata = next_rdata | ({ {(SLVDW-MSTDW){1'b0}}, skidm_rdata } << (rfifo_addr * MSTDW));
		end

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_RVALID || S_AXI_RREADY)
			s_axi_rdata <= next_rdata;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_RVALID || S_AXI_RREADY)
		begin
			if (S_AXI_RVALID)
				s_axi_rresp <= (skidm_rvalid) ? skidm_rresp : OKAY;
			else if (skidm_rvalid)
			casez({ s_axi_rresp, skidm_rresp[1] })
			// Let SLVERR take priority over DECERR
			3'b??0: s_axi_rresp <= s_axi_rresp;
			3'b0?1: s_axi_rresp <= skidm_rresp;
			3'b101: s_axi_rresp <= SLVERR;
			3'b111: s_axi_rresp <= skidm_rresp;
			endcase
		end
		// }}}

		// rid
		// {{{
		initial	rid = 0;
		always @(posedge S_AXI_ACLK)
		if (read_from_rdfifo)
			rid <= rfifo_rid;
		// }}}

		// s_axi_rlast
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_RVALID || S_AXI_RREADY)
		begin
			if (read_from_rdfifo)
				s_axi_rlast <= rfifo_rlast && rfifo_end_of_beat;
			else
				s_axi_rlast <= 0;
		end
		// }}}

		// s_axi_rid
		// {{{
		initial	s_axi_rid = 0;
		always @(posedge S_AXI_ACLK)
		if ((S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST)
				||(!S_AXI_RVALID && rfifo_rlast && rfifo_end_of_beat))
			s_axi_rid <= (read_from_rdfifo && rfifo_rlast && rfifo_end_of_beat)?rfifo_rid : rid;
		// }}}

		// M_AXI_AR*
		// {{{
		assign	M_AXI_ARVALID= m_axi_arvalid;
		assign	M_AXI_ARADDR = mst_araddr;
		assign	M_AXI_ARPROT = mst_arprot;
		// }}}
		// S_AXI_R*
		// {{{
		assign	S_AXI_RVALID = s_axi_rvalid;
		assign	S_AXI_RDATA  = s_axi_rdata;
		assign	S_AXI_RRESP  = s_axi_rresp;
		assign	S_AXI_RLAST  = s_axi_rlast;
		assign	S_AXI_RID    = s_axi_rid;
		// }}}
		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_read;
		assign	unused_read = &{ 1'b0,
				/*
				S_AXI_AWID, S_AXI_AWVALID,
				S_AXI_AWLEN, S_AXI_AWBURST, S_AXI_AWSIZE,
				S_AXI_AWADDR,
				S_AXI_WVALID, S_AXI_WDATA, S_AXI_WSTRB,
				S_AXI_WLAST, S_AXI_BREADY,
				M_AXI_AWREADY, M_AXI_WREADY,
				M_AXI_BRESP, M_AXI_BVALID,
				*/
				rfifo_count, rfifo_full
				};
		// Verilator lint_on  UNUSED
		// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties, read half
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		// As with the write half, the following is a subset of the
		// formal properties used to verify this section of the core.
		// It may, or may not, be syntactically correct.  I don't
		// warrant this version of the design.
		//
		// Register declarations
		// {{{
		localparam	F_LGDEPTH = LGFIFO+1+8;

		wire	[F_LGDEPTH-1:0]		faxi_awr_nbursts;
		wire	[9-1:0]			faxi_wr_pending;
		wire	[F_LGDEPTH-1:0]		faxi_rd_nbursts;
		wire	[F_LGDEPTH-1:0]		faxi_rd_outstanding;

		//
		// ...
		//
	
		localparam	F_AXIL_LGDEPTH = F_LGDEPTH;
		wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
						faxil_wr_outstanding,
						faxil_awr_outstanding;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI channel properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxi_slave #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_EXCLUSIVE(0)
			// ...
			// }}}
		) faxi(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address
			// {{{
			.i_axi_awready(skids_awready),
			.i_axi_awid(   skids_awid),
			.i_axi_awaddr( skids_awaddr),
			.i_axi_awlen(  skids_awlen),
			.i_axi_awsize( skids_awsize),
			.i_axi_awburst(skids_awburst),
			.i_axi_awlock( 0),
			.i_axi_awcache(0),
			.i_axi_awprot( 0),
			.i_axi_awqos(  0),
			.i_axi_awvalid(skids_awvalid),
			// }}}
			// Write data
			// {{{
			.i_axi_wready( skids_wready),
			.i_axi_wdata(  skids_wdata),
			.i_axi_wstrb(  skids_wstrb),
			.i_axi_wlast(  skids_wlast),
			.i_axi_wvalid( skids_wvalid),
			// }}}
			// Write return response
			// {{{
			.i_axi_bid(    S_AXI_BID),
			.i_axi_bresp(  S_AXI_BRESP),
			.i_axi_bvalid( S_AXI_BVALID),
			.i_axi_bready( S_AXI_BREADY),
			// }}}
			// Read address
			// {{{
			.i_axi_arready(skids_arready),
			.i_axi_arid(   skids_arid),
			.i_axi_araddr( skids_araddr),
			.i_axi_arlen(  skids_arlen),
			.i_axi_arsize( skids_arsize),
			.i_axi_arburst(skids_arburst),
			.i_axi_arlock( 0),
			.i_axi_arcache(0),
			.i_axi_arprot( 0),
			.i_axi_arqos(  0),
			.i_axi_arvalid(skids_arvalid),
			// }}}
			// Read response
			// {{{
			.i_axi_rid(    S_AXI_RID),
			.i_axi_rresp(  S_AXI_RRESP),
			.i_axi_rvalid( S_AXI_RVALID),
			.i_axi_rdata(  S_AXI_RDATA),
			.i_axi_rlast(  S_AXI_RLAST),
			.i_axi_rready( S_AXI_RREADY),
			// }}}
			// Formal property data
			// {{{
			.f_axi_awr_nbursts(   faxi_awr_nbursts),
			.f_axi_wr_pending(    faxi_wr_pending),
			.f_axi_rd_nbursts(    faxi_rd_nbursts),
			.f_axi_rd_outstanding(faxi_rd_outstanding),
			//
			// ...
			//
			// }}}
			// }}}
		);

		always @(*)
		begin
			assert(faxi_awr_nbursts == 0);
			assert(faxi_wr_pending == 0);
			assert(faxi_wr_ckvalid == 0);
		end
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI-lite properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxil_master #(
			// {{{
			.C_AXI_DATA_WIDTH(MSTDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXDELAY(4),
			.F_AXI_MAXRSTALL(0),
			.F_OPT_WRITE_ONLY(OPT_WRITES && !OPT_READS),
			.F_OPT_READ_ONLY(!OPT_WRITES &&  OPT_READS),
			.F_LGDEPTH(F_AXIL_LGDEPTH)
			// }}}
		) faxil(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address channel
			// {{{
			.i_axi_awready(M_AXI_AWREADY),
			.i_axi_awaddr( M_AXI_AWADDR),
			.i_axi_awcache(4'h0),
			.i_axi_awprot( M_AXI_AWPROT),
			.i_axi_awvalid(M_AXI_AWVALID),
			// }}}
			// Write data
			// {{{
			.i_axi_wready( skidm_wready),
			.i_axi_wdata(  skidm_wdata),
			.i_axi_wstrb(  skidm_wstrb),
			.i_axi_wvalid( skidm_wvalid),
			// }}}
			// Write response
			// {{{
			.i_axi_bresp(  skidm_bresp),
			.i_axi_bvalid( skidm_bvalid),
			.i_axi_bready( skidm_bready),
			// }}}
			// Read address
			// {{{
			.i_axi_arready(M_AXI_ARREADY),
			.i_axi_araddr( M_AXI_ARADDR),
			.i_axi_arcache(4'h0),
			.i_axi_arprot( M_AXI_ARPROT),
			.i_axi_arvalid(M_AXI_ARVALID),
			// }}}
			// Read data return
			// {{{
			.i_axi_rresp(  skidm_rresp),
			.i_axi_rvalid( skidm_rvalid),
			.i_axi_rdata(  skidm_rdata),
			.i_axi_rready( skidm_rready),
			// }}}
			// Formal check variables
			// {{{
			.f_axi_rd_outstanding(faxil_rd_outstanding),
			.f_axi_wr_outstanding(faxil_wr_outstanding),
			.f_axi_awr_outstanding(faxil_awr_outstanding)
			// }}}
			// }}}
		);

		always @(*)
		begin
			assert(faxil_awr_outstanding == 0);
			assert(faxil_wr_outstanding == 0);
		end
		// }}}
`endif
		// }}}
		// }}}
	end else begin : NO_READ_SUPPORT // if (!OPT_READS)
		// {{{
		assign	M_AXI_ARVALID= 0;
		assign	M_AXI_ARADDR = 0;
		assign	M_AXI_ARPROT = 0;
		assign	M_AXI_RREADY = 0;
		//
		assign	S_AXI_ARREADY= 0;
		assign	S_AXI_RVALID = 0;
		assign	S_AXI_RDATA  = 0;
		assign	S_AXI_RRESP  = 0;
		assign	S_AXI_RLAST  = 0;
		assign	S_AXI_RID    = 0;

		// Make Verilator happy
		// Verilator lint_off UNUSED
		wire	unused_read;
		assign	unused_read = &{ 1'b0, M_AXI_ARREADY, M_AXI_RVALID,
				M_AXI_RDATA, M_AXI_RRESP, S_AXI_RREADY,
				S_AXI_ARLEN, S_AXI_ARSIZE, S_AXI_ARBURST,
				S_AXI_ARADDR, S_AXI_ARVALID, S_AXI_ARID
				};
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}
	// Minimal parameter validation
	// {{{
	initial begin
		if (SLVDW < MSTDW)
		begin
			$fatal;		// Fatal elaboration error
			$stop;		// Stop any simulation
		end
	end
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
		S_AXI_AWLOCK, S_AXI_AWCACHE, S_AXI_AWPROT, S_AXI_AWQOS,
		// skids_wlast, wfifo_count, rfifo_count
		S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT, S_AXI_ARQOS
		};
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// Assume that the two write channels stay within an appropriate
	// distance of each other.  This is to make certain that the property
	// file features are not violated, although not necessary true for
	// actual operation
	//
	always @(*)
		assert(s_axi_wready == (OPT_WRITES && faxi_wr_pending > 0));

	////////////////////////////////////////////////////////////////////////
	//
	// Write induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// These are extra properties necessary to pass write induction
	//

	always @(*)
	if ((bcounts == 0)&&(!read_from_wrfifo))
		assert(!skidm_bvalid || !skidm_bready);

	always @(*)
	if (axi_awlen > 0)
	begin
		assert(m_axi_awvalid);
		if (axi_awlen > 1)
			assert(!skids_awready);
		else if (wfifo_full)
			assert(!skids_awready);
		else if (M_AXI_AWVALID && !M_AXI_AWREADY)
			assert(!skids_awready);
	end


	always @(*)
		assert(axi_bresp != EXOKAY);

	reg	[F_LGDEPTH-1:0]	f_wfifo_bursts, f_wfifo_bursts_minus_one,
				f_wfifo_within, f_wfifo_within_minus_burst,
				f_wfiid_bursts, f_wfiid_bursts_minus_one;
	reg	[IW-1:0]	f_awid;
	always @(posedge S_AXI_ACLK)
	if (skids_awvalid && skids_awready)
		f_awid = skids_awid;

	initial f_wfifo_bursts = 0;
	initial f_wfifo_within = 0;
	initial f_wfiid_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_WRITES)
	begin
		f_wfifo_bursts <= 0;
		f_wfifo_within <= 0;
		// ...
	end else case({ skids_awvalid && skids_awready, read_from_wrfifo })
	2'b00: begin end
	2'b01: begin
		f_wfifo_bursts <= f_wfifo_bursts - 1;
		f_wfifo_within <= f_wfifo_within - wfifo_subcount - 1;;
		// ...
		end
	2'b10: begin
		f_wfifo_bursts <= f_wfifo_bursts + 1;
		f_wfifo_within <= f_wfifo_within + skids_awlen + 1;
		// ...
		end
	2'b11: begin
		f_wfifo_bursts <= f_wfifo_bursts;
		f_wfifo_within <= f_wfifo_within + skids_awlen - wfifo_subcount;
		// ...
		end
	endcase

	always @(*)
		assert(f_wfifo_bursts == wfifo_count);
	always @(*)
		assert(f_wfifo_bursts <= f_wfifo_within);
	// ...
	always @(*)
		assert(f_wfifo_within <= { f_wfifo_bursts, 8'h00 });

	always @(*)
		assert(faxi_awr_nbursts == f_wfifo_bursts
			+ ((bcounts > 0) ? 1:0)
			+  (S_AXI_BVALID ? 1:0));

	//
	// ...
	//

	always @(*)
		assert(faxil_awr_outstanding
			== f_wfifo_within + bcounts - axi_awlen
				-(M_AXI_AWVALID ? 1:0));

	always @(*)
		assert(faxil_wr_outstanding
			== f_wfifo_within + bcounts - faxi_wr_pending);

	always @(*)
		assert(f_wfifo_within + bcounts >= faxi_wr_pending);

	//
	// ...
	//

	always @(*)
		f_wfifo_bursts_minus_one = f_wfifo_bursts - 1;

	always @(*)
		f_wfifo_within_minus_burst = f_wfifo_within - wfifo_subcount - 1;

	//
	// ...
	//


`ifdef	BMC
`define	BMC_ASSERT	assert
`else
`define	BMC_ASSERT	assume
`endif

	always @(*)
		assert(faxil_awr_outstanding <= { 1'b1, {(LGFIFO+8){1'b0}} } + bcounts);
	always @(*)
		assert(faxil_wr_outstanding  <= { 1'b1, {(LGFIFO+8){1'b0}} } + bcounts);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write FIFO assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// ...
	//

	always @(*)
	if (f_wfifo_bursts == 0)
		`BMC_ASSERT(wfifo_empty);
	else if (f_wfifo_bursts == f_wfifo_within)
		`BMC_ASSERT(wfifo_subcount == 0);
	else if ({f_wfifo_bursts, 8'h00 } == f_wfifo_within)
		`BMC_ASSERT(wfifo_subcount == 8'hff);

	always @(*)
	if (!wfifo_empty)
	begin
		`BMC_ASSERT({ f_wfifo_bursts_minus_one, 8'h00 }
			>= f_wfifo_within - wfifo_subcount - 1);

		`BMC_ASSERT(wfifo_subcount <= f_wfifo_within-f_wfifo_bursts);
	end

	//
	// ...
	//

	always @(*)
	if (!wfifo_empty)
		`BMC_ASSERT(wfifo_subcount <= (f_wfifo_within-f_wfifo_bursts));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (S_AXI_RVALID && !S_AXI_RLAST)
		assert(rid == S_AXI_RID);

	always @(*)
	if ((rcounts == 0)&&(!read_from_rdfifo))
		assert(!skidm_rvalid || !skidm_rready);

	always @(*)
	if (axi_arlen > 0)
	begin
		assert(m_axi_arvalid);
		assert(!skids_arready);
	end

	reg	[F_LGDEPTH-1:0]	f_rfifo_bursts, f_rfifo_bursts_minus_one,
				f_rfifo_within,
				f_rfiid_bursts, f_rfiid_bursts_minus_one,
				f_rfiid_within,
				f_rfino_bursts, f_rfino_bursts_minus_one,
				f_rfino_within;
	reg	[F_LGDEPTH-1:0]	f_rdpip_bursts, f_rdpip_outs,
				f_rfign_bursts, f_rfign_outs;



	reg	[IW-1:0]	f_arid;
	always @(posedge S_AXI_ACLK)
	if (skids_arvalid && skids_arready)
		f_arid = skids_arid;

	initial f_rfifo_bursts = 0;
	initial f_rfifo_within = 0;
	initial f_rfiid_bursts = 0;
	initial f_rfiid_within = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_READS)
	begin
		f_rfifo_bursts <= 0;
		f_rfifo_within <= 0;
		f_rfiid_bursts <= 0;
		f_rfiid_within <= 0;
	end else case({ skids_arvalid && skids_arready, read_from_rdfifo })
	2'b00: begin end
	2'b01: begin
		f_rfifo_bursts <= f_rfifo_bursts - 1;
		f_rfifo_within <= f_rfifo_within - rfifo_rcount - 1;
		// ...
		end
	2'b10: begin
		f_rfifo_bursts <= f_rfifo_bursts + 1;
		f_rfifo_within <= f_rfifo_within + skids_arlen + 1;
		// ...
		end
	2'b11: begin
		f_rfifo_bursts <= f_rfifo_bursts;
		f_rfifo_within <= f_rfifo_within + skids_arlen - rfifo_rcount;
		// ...
		end
	endcase

	//
	// ...
	//


	always @(*)
		assert(f_rfifo_bursts == rfifo_count);

	//
	// ...
	//


	//
	// Correlate faxi_rd*_bursts with f_rfifo*bursts
	always @(*)
		assert(faxi_rd_nbursts == f_rfifo_bursts
			+ ((rcounts > 0) ? 1:0)
			+  (S_AXI_RVALID&&S_AXI_RLAST ? 1:0));

	//
	// ...
	//

	always @(*)
		assert(faxil_rd_outstanding
			== f_rfifo_within + rcounts - axi_arlen
				-(M_AXI_ARVALID ? 1:0));

	always @(*)
		assert(faxi_rd_outstanding
			== f_rfifo_within + rcounts + (S_AXI_RVALID ? 1:0));


	//
	// ...
	//

	always @(*)
		f_rfifo_bursts_minus_one = f_rfifo_bursts - 1;

	//
	// ...
	//

	always @(*)
		assert(rcounts <= 256);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read FIFO "assumptions"
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// ...
	//

	always @(*)
	if (rcounts == 0 && S_AXI_RVALID)
		assert(S_AXI_RLAST);

	//
	// ...
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Select only write or only read operation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (!OPT_WRITES)
	begin
		always @(*)
		begin
			assume(!skids_awvalid);
			assume(!skids_wvalid);
			assert(M_AXI_AWVALID == 0);
			assert(faxil_awr_outstanding == 0);
			assert(faxil_wr_outstanding == 0);
			assert(!skidm_bvalid);
			assert(!S_AXI_BVALID);
		end
	end endgenerate

	generate if (!OPT_READS)
	begin

		always @(*)
		begin
			assume(!S_AXI_ARVALID);
			assert(M_AXI_ARVALID == 0);
			assert(faxil_rd_outstanding == 0);
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover statements, to show performance
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_WRITES)
	begin
		// {{{
		reg	[3:0]	cvr_write_count, cvr_write_count_simple;

		initial	cvr_write_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_write_count_simple <= 0;
		else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN == 0)
			cvr_write_count_simple <= cvr_write_count_simple + 1;

		initial	cvr_write_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_write_count <= 0;
		else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN > 2)
			cvr_write_count <= cvr_write_count + 1;

		always @(*)
			cover(cvr_write_count_simple > 6 && faxi_awr_nbursts == 0 && !S_AXI_BVALID);
		always @(*)
			cover(cvr_write_count > 2 && faxi_awr_nbursts == 0 && !S_AXI_BVALID);
		// }}}
	end endgenerate

	generate if (OPT_READS)
	begin
		// {{{
		reg	[3:0]	cvr_read_count, cvr_read_count_simple;

		initial	cvr_read_count_simple = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_read_count_simple <= 0;
		else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN == 0)
			cvr_read_count_simple <= cvr_read_count_simple + 1;

		initial	cvr_read_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_read_count <= 0;
		else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN > 2)
			cvr_read_count <= cvr_read_count + 1;

		always @(*)
			cover(cvr_read_count_simple > 6 && faxi_rd_nbursts == 0 && !S_AXI_RVALID);
		always @(*)
			cover(cvr_read_count > 2 && faxi_rd_nbursts == 0 && !S_AXI_RVALID);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	reg	[4:0]	f_count_awwait;
	initial	f_count_awwait = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || S_AXI_BVALID ||(faxi_wr_pending > 0))
		f_count_awwait <= 0;
	else if (skids_awvalid && !skids_awready && (!(&f_count_awwait)))
		f_count_awwait <= f_count_awwait+1;

	always @(*)
	if (wfifo_full)
		assume(f_count_awwait < 3);
	// }}}
`undef	BMC_ASSERT
`endif
// }}}
endmodule
