////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisgdma.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Scripts an AXI DMA via in-memory tables: reads from the tables,
//		commands the DMA.
//
// Registers:
//
//	0. Control
//		8b	KEY
//			3'b PROT
//			4'b QOS
//		1b	Abort: Either aborting or aborted
//		1b	Err: Ended on an error
//		1b	Busy
//		1b	Interrupt Enable
//		1b	Interrupt Set
//		1b	Start
//	1. Reserved
//	2-3. First table entry address
//		(Current) table entry address on read, if in progress
// (Optional)
//	4-5. Current read address
//	6-7. Current write address
//	1.   Remaining amount to be written (this entry)
//
// Table entries (must be 32-bit aligned):
//	If (address_width > 30)
//		64b: { 2'bflags, 62'b SOURCE ADDRESS (bytes) }
//			00: Continue after this to next
//			01: Skip this address
//			10: Jump to new address
//			11: Last item in chain
//		64b: { int_en, 1'b0,  DESTINATION ADDRESS (bytes) }
//		32b LENGTH (in bytes)
//	else
//		32b: { 2'bflags, 30'b SOURCE ADDRESS (bytes) }
//		32b: { int_en, 1'b0, 30'b DESTINATION ADDRESS (bytes) }
//		32b LENGTH (in bytes)
//
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
// `define			AXI3
// }}}
module	axisgdma #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 64,
		//
		localparam	C_AXIL_ADDR_WIDTH = 4,
		localparam	C_AXIL_DATA_WIDTH = 32,
		//
		// OPT_UNALIGNED turns on support for unaligned addresses,
		// whether source, destination, or length parameters.
		parameter [0:0]	OPT_UNALIGNED = 1'b1,
		//
		// OPT_WRAPMEM controls what happens if the transfer runs off
		// of the end of memory.  If set, the transfer will continue
		// again from the beginning of memory.  If clear, the transfer
		// will be aborted with an error if either read or write
		// address ever get this far.
		parameter [0:0]	OPT_WRAPMEM = 1'b1,
		//
		// LGMAXBURST controls the size of the maximum burst produced
		// by this core.  Specifically, its the log (based 2) of that
		// maximum size.  Hence, for AXI4, this size must be 8
		// (i.e. 2^8 or 256 beats) or less.  For AXI3, the size must
		// be 4 or less.  Tests have verified performance for
		// LGMAXBURST as low as 2.  While I expect it to fail at
		// LGMAXBURST=0, I haven't verified at what value this burst
		// parameter is too small.
`ifdef	AXI3
		parameter	LGMAXBURST=4,	// 16 beats max
`else
		parameter	LGMAXBURST=8,	// 256 beats
`endif
		//
		// LGFIFO: This is the (log-based-2) size of the internal FIFO.
		// Hence if LGFIFO=8, the internal FIFO will have 256 elements
		// (words) in it.  High throughput transfers are accomplished
		// by first storing data into a FIFO, then once a full burst
		// size is available bursting that data over the bus.  In
		// order to be able to keep receiving data while bursting it
		// out, the FIFO size must be at least twice the size of the
		// maximum burst size.  Larger sizes are possible as well.
		parameter	LGFIFO = LGMAXBURST+1,	// 512 element FIFO
		//
		// LGLEN: specifies the number of bits in the transfer length
		// register.  If a transfer cannot be specified in LGLEN bits,
		// it won't happen.  LGLEN must be less than or equal to the
		// address width.
		parameter	LGLEN = C_AXI_ADDR_WIDTH,
		//
		// AXI uses ID's to transfer information.  This core rather
		// ignores them.  Instead, it uses a constant ID for all
		// transfers.  The following two parameters control that ID.
		parameter	[C_AXI_ID_WIDTH-1:0]	DMA_READ_ID = 0,
		parameter	[C_AXI_ID_WIDTH-1:0]	DMA_WRITE_ID = 0,
		parameter	[C_AXI_ID_WIDTH-1:0] PF_READ_ID = DMA_READ_ID+1,
		//
		// The "ABORT_KEY" is a byte that, if written to the control
		// word while the core is running, will cause the data transfer
		// to be aborted.
		parameter	[7:0]			ABORT_KEY  = 8'h6d,
		//
		// OPT_LOWPOWER
		parameter	[0:0]			OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// The AXI4-lite control interface
		input	wire				S_AXIL_AWVALID,
		output	wire				S_AXIL_AWREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_AWADDR,
		input	wire 	[2:0]			S_AXIL_AWPROT,
		//
		input	wire				S_AXIL_WVALID,
		output	wire				S_AXIL_WREADY,
		input	wire [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_WDATA,
		input	wire [C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	reg				S_AXIL_BVALID,
		input	wire				S_AXIL_BREADY,
		output	wire	[1:0]			S_AXIL_BRESP,
		//
		input	wire				S_AXIL_ARVALID,
		output	wire				S_AXIL_ARREADY,
		input	wire [C_AXIL_ADDR_WIDTH-1:0]	S_AXIL_ARADDR,
		input	wire 	[2:0]			S_AXIL_ARPROT,
		//
		output	reg				S_AXIL_RVALID,
		input	wire				S_AXIL_RREADY,
		output	reg [C_AXIL_DATA_WIDTH-1:0]	S_AXIL_RDATA,
		output	wire	[1:0]			S_AXIL_RRESP,
		//
		//
		// The AXI Master (DMA) interface
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
`ifdef	AXI3
		output	wire	[3:0]			M_AXI_AWLEN,
`else
		output	wire	[7:0]			M_AXI_AWLEN,
`endif
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
`ifdef	AXI3
		output	wire	[1:0]			M_AXI_AWLOCK,
`else
		output	wire				M_AXI_AWLOCK,
`endif
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
`ifdef	AXI3
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_WID,
`endif
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		output	reg				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		//
		//
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
`ifdef	AXI3
		output	wire	[3:0]			M_AXI_ARLEN,
`else
		output	wire	[7:0]			M_AXI_ARLEN,
`endif
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
`ifdef	AXI3
		output	wire	[1:0]			M_AXI_ARLOCK,
`else
		output	wire				M_AXI_ARLOCK,
`endif
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP,
		//
		output	reg				o_int
		// }}}
	);

	// Local parameter definitions
	// {{{
	// The number of beats in this maximum burst size is
	// automatically determined from LGMAXBURST, and so its
	// forced to be a power of two this way.
	// localparam	MAXBURST=(1<<LGMAXBURST);
	//
	localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3;
	localparam	AXILLSB= $clog2(C_AXIL_DATA_WIDTH)-3;
	// localparam	LGLENW= LGLEN-ADDRLSB;

	localparam	[1:0]	CTRL_ADDR   = 2'b00,
				// UNUSED_ADDR = 2'b01,
				TBLLO_ADDR  = 2'b10,
				TBLHI_ADDR  = 2'b11;
	localparam		CTRL_START_BIT = 0,
				CTRL_BUSY_BIT  = 0,
				CTRL_INT_BIT   = 1,
				CTRL_INTEN_BIT = 2,
				CTRL_ABORT_BIT = 3,
				CTRL_ERR_BIT   = 4;
				// CTRL_INTERIM_BIT= 5;
	localparam	[1:0]	AXI_INCR = 2'b01, AXI_OKAY = 2'b00;

`ifdef	AXI3
	localparam	LENWIDTH = 4;
`else
	localparam	LENWIDTH = 8;
`endif

	// DMA device internal addresses
	// {{{
	localparam [4:0]	DMA_CONTROL= 5'b00000;
	// }}}

	// localparam [C_AXI_ADDR_WIDTH-1:0] TBL_SIZE
	//			= (C_AXI_ADDR_WIDTH < 30) ? (4*5) : (4*7);

	// }}}

	// Register/net declarations
	// {{{
	reg				axil_write_ready, axil_read_ready;
	reg	[2*C_AXIL_DATA_WIDTH-1:0] wide_tbl, new_widetbl;
	reg	[C_AXI_ADDR_WIDTH-1:0]	tbl_addr, r_tbl_addr;
	reg				r_int_enable, r_int, r_err, r_abort;
	wire				w_int, fsm_err;

	reg	[3:0]		r_qos;
	reg	[2:0]		r_prot;
	reg			r_start;
	wire			r_done, r_busy;

	wire				awskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	awskd_addr;
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;

	wire				arskd_valid;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	arskd_addr;

	// Prefetch interface registers
	// {{{
	wire				new_pc, pf_ready, pf_clear_cache;
	wire	[C_AXI_ADDR_WIDTH-1:0]	ipc;
	wire	[31:0]			pf_insn;
	wire				pf_valid, pf_illegal;
	wire				pf_axi_arvalid;
	reg				pf_axi_arready;
	wire	[C_AXI_ADDR_WIDTH-1:0]	pf_axi_araddr, pf_pc;
	wire				pf_axi_rready_ignored;
	wire	[C_AXI_ID_WIDTH-1:0]	pf_axi_arid;
	wire	[LENWIDTH-1:0]		pf_axi_arlen;
	wire	[2:0]			pf_axi_arsize;
	wire	[1:0]			pf_axi_arburst;
	wire	[3:0]			pf_axi_arcache;
	wire	[2:0]			pf_axi_arprot;
	wire	[3:0]			pf_axi_arqos;
	// }}}

	// DMA control registers/AXI-lite interface
	// {{{
	wire		dmac_awready_ignored;
	reg	[4:0]	dmac_waddr;
	//
	reg		dmac_wvalid;
	wire		dmac_wready;
	reg	[31:0]	dmac_wdata;
	reg	[3:0]	dmac_wstrb;
	//
	wire		dmac_bvalid;
	wire	[1:0]	dmac_bresp;
	//
	wire		dmac_arready;
	wire		dmac_rvalid;
	wire	[31:0]	dmac_rdata;
	wire	[1:0]	dmac_rresp;
	// }}}

	// DMA AXI nets
	// {{{
	wire				sdma_arvalid;
	wire	[C_AXI_ID_WIDTH-1:0]	sdma_arid;
	wire	[C_AXI_ADDR_WIDTH-1:0]	sdma_araddr;
	wire	[LENWIDTH-1:0]		sdma_arlen;
	wire	[2:0]			sdma_arsize;
	wire	[1:0]			sdma_arburst;
	wire	[0:0]			sdma_arlock;
	wire	[3:0]			sdma_arcache;
	wire	[2:0]			sdma_arprot;
	wire	[3:0]			sdma_arqos;
	reg				sdma_arready;
	wire				sdma_rready_ignored;
	wire				dma_complete;

	wire				unused_dma_lock;
	// }}}

	// Combined AXI nets
	// {{{
	reg				m_axi_arvalid;
	reg	[C_AXI_ID_WIDTH-1:0]	m_axi_arid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	m_axi_araddr;
	reg	[LENWIDTH-1:0]		m_axi_arlen;
	reg	[2:0]			m_axi_arsize;
	reg	[1:0]			m_axi_arburst;
	reg	[3:0]			m_axi_arcache;
	reg	[2:0]			m_axi_arprot;
	reg	[3:0]			m_axi_arqos;
	// }}}

	reg	pf_wins_arbitration;
	wire	m_axi_arready;

	// }}}

	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-Lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	//


	////////////////////////////////////////////////////////////////////////
	//
	// Write control logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// axil AW skid buffer
	// {{{
	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB)
		// }}}
	) axilawskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr)
		// }}}
	);
	// }}}

	// axil W skid buffer
	// {{{
	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8)
		// }}}
	) axilwskid (
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WSTRB, S_AXIL_WDATA }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_strb, wskd_data })
		// }}}
	);
	// }}}

	// axil_write_ready
	// {{{
	always  @(*)
	begin
		axil_write_ready = !S_AXIL_BVALID || S_AXIL_BREADY;
		if (!awskd_valid || !wskd_valid)
			axil_write_ready = 0;
	end
	// }}}

	// S_AXIL_BVALID
	// {{{
	initial	S_AXIL_BVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXIL_BVALID <= 1'b0;
	else if (!S_AXIL_BVALID || S_AXIL_BREADY)
		S_AXIL_BVALID <= axil_write_ready;
	// }}}

	// S_AXIL_BRESP
	// {{{
	assign	S_AXIL_BRESP = AXI_OKAY;
	// }}}

	// r_start
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_start <= 1'b0;
	else begin
		r_start <= !r_busy && axil_write_ready && wskd_strb[0]
				&& wskd_data[CTRL_START_BIT]
				&& (awskd_addr == CTRL_ADDR);
		if (r_err && !wskd_data[CTRL_ERR_BIT])
			r_start <= 0;
		if (r_abort && !wskd_data[CTRL_ABORT_BIT])
			r_start <= 0;
	end
	// }}}

	// r_err
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_err <= 1'b0;
	else if (!r_busy)
	begin
		if (axil_write_ready)
			r_err <= (r_err) && (!wskd_strb[0]
						|| !wskd_data[CTRL_ERR_BIT]);
	end else begin
		r_err <= r_err || fsm_err;
	end
	// }}}

	// o_int
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !r_int_enable || !r_busy)
		o_int <= 0;
	else if (w_int)
		o_int <= 1'b1;
	// }}}

	// r_int
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_int <= 0;
	else if (!r_busy)
	begin
		if (axil_write_ready && awskd_addr == CTRL_ADDR
			&& wskd_strb[0])
		begin
			if (wskd_data[CTRL_START_BIT])
				r_int <= 0;
			else if (wskd_data[CTRL_INT_BIT])
				r_int <= 0;
		end
	end else if (w_int)
		r_int <= 1'b1;
	// }}}

	// r_abort
	// {{{
	initial	r_abort = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_abort <= 1'b0;
	else if (!r_busy)
	begin
		if (axil_write_ready && awskd_addr == CTRL_ADDR && wskd_strb[0])
		begin
			if(wskd_data[CTRL_START_BIT]
				||wskd_data[CTRL_ABORT_BIT]
				||wskd_data[CTRL_ERR_BIT])
			r_abort <= 0;
		end
	end else if (!r_abort)
		r_abort <= (axil_write_ready && awskd_addr == CTRL_ADDR)
			&&(wskd_strb[3] && wskd_data[31:24] == ABORT_KEY);
	// }}}

	// wide_tbl, new_widetbl
	// {{{
	always @(*)
	begin
		wide_tbl = 0;
		wide_tbl[C_AXI_ADDR_WIDTH-1:0] = r_tbl_addr;

		new_widetbl = wide_tbl;
		if (awskd_addr == TBLLO_ADDR)
			new_widetbl[31:0] = apply_wstrb(wide_tbl[31:0],
							wskd_data, wskd_strb);
		if (awskd_addr == TBLHI_ADDR)
			new_widetbl[63:32] = apply_wstrb(wide_tbl[63:32],
					wskd_data, wskd_strb);
	end
	// }}}

	// r_prot, r_qos, r_int_enable, r_tbl_addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		r_prot <= 0;
		r_qos  <= 0;
		r_int_enable <= 0;
	end else if (!r_busy && axil_write_ready)
	begin
		case(awskd_addr)
		CTRL_ADDR: begin
				if (wskd_strb[2])
				begin
					r_prot <= wskd_data[22:20];
					r_qos  <= wskd_data[19:16];
				end
			if (wskd_strb[0])
			begin
				r_int_enable <= wskd_data[CTRL_INTEN_BIT];
			end end
		TBLLO_ADDR: begin
			r_tbl_addr <= new_widetbl[C_AXI_ADDR_WIDTH-1:0];
			end
		TBLHI_ADDR: if (C_AXI_ADDR_WIDTH > C_AXIL_DATA_WIDTH) begin
			r_tbl_addr <= new_widetbl[C_AXI_ADDR_WIDTH-1:0];
			end
		default: begin end
		endcase
	end else if (r_busy)
	begin
		r_tbl_addr <= tbl_addr;
	end
	// }}}

	// apply_wstrb function
	// {{{
	function [C_AXIL_DATA_WIDTH-1:0]	apply_wstrb;
		input [C_AXIL_DATA_WIDTH-1:0]	prior_data;
		input [C_AXIL_DATA_WIDTH-1:0]	new_data;
		input [C_AXIL_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXIL_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8] = wstrb[k] ? new_data[k*8 +: 8]
				: prior_data[k*8 +: 8];
		end
	endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite control read interface
	// {{{

	// AXI-lite AR skid buffer
	// {{{
	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB)
		// }}}
	) axilarskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr)
		// }}}
	);
	// }}}

	// axil_read_ready
	// {{{
	always @(*)
	begin
		axil_read_ready = !S_AXIL_RVALID || S_AXIL_RREADY;
		if (!arskd_valid)
			axil_read_ready = 1'b0;
	end
	// }}}

	// S_AXIL_RVALID
	// {{{
	initial	S_AXIL_RVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXIL_RVALID <= 1'b0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
		S_AXIL_RVALID <= axil_read_ready;
	// }}}

	// S_AXIL_RDATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		S_AXIL_RDATA <= 0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		S_AXIL_RDATA <= 0;
		case(arskd_addr)
		CTRL_ADDR: begin
			S_AXIL_RDATA[CTRL_ERR_BIT]     <= r_err;
			S_AXIL_RDATA[CTRL_ABORT_BIT]   <= r_abort;
			S_AXIL_RDATA[CTRL_INTEN_BIT]   <= r_int_enable;
			S_AXIL_RDATA[CTRL_INT_BIT]     <= r_int;
			S_AXIL_RDATA[CTRL_BUSY_BIT]    <= r_busy;
			end
		// Unused:
		TBLLO_ADDR:
			S_AXIL_RDATA <= wide_tbl[C_AXIL_DATA_WIDTH-1:0];
		TBLHI_ADDR:
			S_AXIL_RDATA <= wide_tbl[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
		default: begin end
		endcase

		if (OPT_LOWPOWER && (!axil_read_ready || !arskd_valid))
			S_AXIL_RDATA <= 0;
	end
	// }}}

	// S_AXIL_RRESP
	// {{{
	assign	S_AXIL_RRESP = AXI_OKAY;
	// }}}
	// }}} // AXI-lite read
	// }}} // AXI-lite (all)
	////////////////////////////////////////////////////////////////////////
	//
	// DMA wrapper
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Prefix: dmac for the sub DMA control interface
	// Prefix: sdma for the sub DMA master  interface
	axidma #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_UNALIGNED(OPT_UNALIGNED),
		.OPT_WRAPMEM(OPT_WRAPMEM),
		.LGMAXBURST(LGMAXBURST),
		.LGFIFO(LGFIFO),
		.LGLEN(LGLEN),
		.AXI_READ_ID(DMA_READ_ID),
		.AXI_WRITE_ID(DMA_WRITE_ID),
		.ABORT_KEY(ABORT_KEY)
		// }}}
	) subdma(
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		//
		// The AXI4-lite control interface
		// {{{
		.S_AXIL_AWVALID(dmac_wvalid), // Merge AW & W channels:DMA ok w/
		.S_AXIL_AWREADY(dmac_awready_ignored),
		.S_AXIL_AWADDR( dmac_waddr),
		.S_AXIL_AWPROT( 3'h0),	// Internally ignored
		//
		.S_AXIL_WVALID(dmac_wvalid),
		.S_AXIL_WREADY(dmac_wready),
		.S_AXIL_WDATA( dmac_wdata),
		.S_AXIL_WSTRB( dmac_wstrb),
		//
		.S_AXIL_BVALID(dmac_bvalid),
		.S_AXIL_BREADY(1'b1),
		.S_AXIL_BRESP( dmac_bresp),
		//
		.S_AXIL_ARVALID(!S_AXI_ARESETN),
		.S_AXIL_ARREADY(dmac_arready),
		.S_AXIL_ARADDR( DMA_CONTROL),
		.S_AXIL_ARPROT( 3'h0),	// Internally ignored
		//
		.S_AXIL_RVALID(dmac_rvalid),
		.S_AXIL_RREADY(1'b1),
		.S_AXIL_RDATA( dmac_rdata),
		.S_AXIL_RRESP( dmac_rresp),
		// }}}
		//
		// The AXI Master (DMA) interface
		// {{{
		.M_AXI_AWVALID(M_AXI_AWVALID),
		.M_AXI_AWREADY(M_AXI_AWREADY),
		.M_AXI_AWID(   M_AXI_AWID),
		.M_AXI_AWADDR( M_AXI_AWADDR),
		.M_AXI_AWLEN(  M_AXI_AWLEN),
		.M_AXI_AWSIZE( M_AXI_AWSIZE),
		.M_AXI_AWBURST(M_AXI_AWBURST),
		.M_AXI_AWLOCK( unused_dma_lock),
		.M_AXI_AWCACHE(M_AXI_AWCACHE),
		.M_AXI_AWPROT( M_AXI_AWPROT),
		.M_AXI_AWQOS(  M_AXI_AWQOS),
		//
		//
		.M_AXI_WVALID(M_AXI_WVALID),
		.M_AXI_WREADY(M_AXI_WREADY),
`ifdef	AXI3
		.M_AXI_WID(M_AXI_WID),
`endif
		.M_AXI_WDATA(M_AXI_WDATA),
		.M_AXI_WSTRB(M_AXI_WSTRB),
		.M_AXI_WLAST(M_AXI_WLAST),
		//
		//
		.M_AXI_BVALID(M_AXI_BVALID),
		.M_AXI_BREADY(M_AXI_BREADY),
		.M_AXI_BID(   M_AXI_BID),
		.M_AXI_BRESP( M_AXI_BRESP),
		// }}}
		// AXI master read interface
		// {{{
		// The read channel needs to be arbitrated
		.M_AXI_ARVALID(sdma_arvalid),
		.M_AXI_ARREADY(sdma_arready),
		.M_AXI_ARID(sdma_arid),
		.M_AXI_ARADDR(sdma_araddr),
		.M_AXI_ARLEN(sdma_arlen),
		.M_AXI_ARSIZE(sdma_arsize),
		.M_AXI_ARBURST(sdma_arburst),
		.M_AXI_ARLOCK(sdma_arlock),
		.M_AXI_ARCACHE(sdma_arcache),
		.M_AXI_ARPROT(sdma_arprot),
		.M_AXI_ARQOS(sdma_arqos),
		//
		.M_AXI_RVALID(M_AXI_RVALID && M_AXI_RID == DMA_READ_ID),
		.M_AXI_RREADY(sdma_rready_ignored),	// Known to be one
		.M_AXI_RID(  DMA_READ_ID),
		.M_AXI_RDATA(M_AXI_RDATA),
		.M_AXI_RLAST(M_AXI_RLAST),
		.M_AXI_RRESP(M_AXI_RRESP),
		// }}}
		.o_int(dma_complete)
		// }}}
	);

	assign	M_AXI_AWLOCK = 0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-Lite prefetch
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The AXI_lite fetch submodule
	// {{{
	axilfetch #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.FETCH_LIMIT(4)
		// }}}
	) pf (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		//
		// "CPU" interface
		// {{{
		.i_cpu_reset(!S_AXI_ARESETN),
		.i_new_pc(new_pc),
		.i_clear_cache(pf_clear_cache),
		.i_ready(pf_ready),
		.i_pc(ipc),
		.o_insn(pf_insn),
		.o_valid(pf_valid),
		.o_pc(pf_pc),
		.o_illegal(pf_illegal),
		// }}}
		// AXI-lite interface
		// {{{
		.M_AXI_ARVALID(pf_axi_arvalid),
		.M_AXI_ARREADY(pf_axi_arready),
		.M_AXI_ARADDR( pf_axi_araddr),
		.M_AXI_ARPROT( pf_axi_arprot),
		//
		.M_AXI_RVALID( M_AXI_RVALID && M_AXI_RID == PF_READ_ID),
		.M_AXI_RREADY( pf_axi_rready_ignored), // Always 1'b1
		.M_AXI_RDATA(  M_AXI_RDATA),
		.M_AXI_RRESP(  M_AXI_RRESP)
		// }}}
		// }}}
	);
	// }}}

	assign	pf_axi_arid    = PF_READ_ID;
	assign	pf_axi_arlen   = 0; // Only read singletons
	assign	pf_axi_arsize  = ADDRLSB[2:0];
	assign	pf_axi_arburst = AXI_INCR;
	assign	pf_axi_arcache = 4'b0011;
	// assign	pf_axi_arprot  = 3'b100;
	assign	pf_axi_arqos   = 4'h0;

	assign	M_AXI_RREADY = 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PF vs DMA arbiter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// pf_wins_arbitration
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!m_axi_arvalid || m_axi_arready)
	begin
		if (pf_axi_arvalid && !sdma_arvalid)
			pf_wins_arbitration <= 1'b1;
		else
			pf_wins_arbitration <= 1'b0;
	end
	// }}}

	// m_axi_*
	// {{{
	always @(*)
	begin
		if (pf_wins_arbitration)
		begin
			m_axi_arvalid = pf_axi_arvalid;
			m_axi_arid    = pf_axi_arid;
			m_axi_araddr  = pf_axi_araddr;
			m_axi_arlen   = pf_axi_arlen;
			m_axi_arsize  = pf_axi_arsize;
			m_axi_arburst = pf_axi_arburst;
			m_axi_arcache = pf_axi_arcache;
			m_axi_arprot  = pf_axi_arprot;
			m_axi_arqos   = pf_axi_arqos;
		end else begin
			m_axi_arvalid = sdma_arvalid;
			m_axi_arid    = sdma_arid;
			m_axi_araddr  = sdma_araddr;
			m_axi_arlen   = sdma_arlen;
			m_axi_arsize  = sdma_arsize;
			m_axi_arburst = sdma_arburst;
			m_axi_arcache = sdma_arcache;
			m_axi_arprot  = sdma_arprot;
			m_axi_arqos   = sdma_arqos;
		end
	end
	// }}}

	// *_arready
	// {{{
	always @(*)
	begin
		sdma_arready   = m_axi_arready && !pf_wins_arbitration;
		pf_axi_arready = m_axi_arready &&  pf_wins_arbitration;
	end
	// }}}

	// Outgoing AR skid buffer
	// {{{
	skidbuffer #(
		// {{{
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_OUTREG(1'b1),
		.DW(C_AXI_ID_WIDTH + C_AXI_ADDR_WIDTH + LENWIDTH
				+ 3 + 2 + 4  +3 + 4)
		// }}}
	) marskd(
		// {{{
		S_AXI_ACLK, !S_AXI_ARESETN, m_axi_arvalid, m_axi_arready,
		{ m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize,
			m_axi_arburst, m_axi_arcache,
			m_axi_arprot, m_axi_arqos },
		M_AXI_ARVALID, M_AXI_ARREADY,
		{ M_AXI_ARID, M_AXI_ARADDR, M_AXI_ARLEN, M_AXI_ARSIZE,
			M_AXI_ARBURST, M_AXI_ARCACHE,
			M_AXI_ARPROT, M_AXI_ARQOS }
		// }}}
	);

`ifdef	AXI3
	assign	M_AXI_ARLOCK = 2'b00;	// We don't use lock anyway
`else
	assign	M_AXI_ARLOCK = 1'b0;
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FSM Control states
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axisgfsm #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.ABORT_KEY(ABORT_KEY)
		// }}}
	) fsm (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		// Control interface
		// {{{
		.i_start(r_start),
		.i_abort(r_abort),
		.i_tbl_addr(r_tbl_addr),
		.i_qos(r_qos),
		.i_prot(r_prot),
		.o_done(r_done),
		.o_busy(r_busy),
		.o_int(w_int),
		.o_err(fsm_err),
		.o_tbl_addr(tbl_addr),
		// }}}
		// Prefetch interface
		// {{{
		.o_new_pc(new_pc),
		.o_pf_clear_cache(pf_clear_cache),
		.o_pf_ready(pf_ready),
		.o_pf_pc(ipc),
		.i_pf_valid(pf_valid),
		.i_pf_insn(pf_insn),
		.i_pf_pc(pf_pc),
		.i_pf_illegal(pf_illegal),
		// }}}
		// DMA AXI-lite control interface
		// {{{
		.o_dmac_wvalid(dmac_wvalid),
		.i_dmac_wready(dmac_wready),
		.o_dmac_waddr(dmac_waddr),
		.o_dmac_wdata(dmac_wdata),
		.o_dmac_wstrb(dmac_wstrb),
		.i_dmac_rdata(dmac_rdata),
		.i_dma_complete(dma_complete)
		// }}}

		// }}}
	);

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dmac_awready_ignored, dmac_bvalid,
			dmac_bresp, dmac_rvalid, dmac_rresp,
			S_AXIL_AWADDR[AXILLSB-1:0], S_AXIL_AWPROT,
			S_AXIL_ARADDR[AXILLSB-1:0], S_AXIL_ARPROT,
			M_AXI_RREADY, r_done,
			new_widetbl[63:C_AXI_ADDR_WIDTH],
			unused_dma_lock,
			sdma_arlock, sdma_rready_ignored,
			pf_axi_rready_ignored, dmac_arready };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties (neither written, nor tested)
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// The full formal verification of this core has not been completed.
	//
	////////////////////////////////////////////////////////////////////////
	//
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxil_slave #(
		.C_AXI_DATA_WIDTH(C_AXIL_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXIL_ADDR_WIDTH)
		//
		// ...
		//
		)
	faxil(
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXIL_AWVALID),
		.i_axi_awready(S_AXIL_AWREADY),
		.i_axi_awaddr(S_AXIL_AWADDR),
		.i_axi_awprot(S_AXIL_AWPROT),
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
		.i_axi_rresp( S_AXIL_RRESP)
		//
		// ...
		//
		);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The main AXI data interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions (i.e. constraints)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// None (currently)

	// }}}
`endif
// }}}
endmodule
