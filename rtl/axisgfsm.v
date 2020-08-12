////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisgfsm.v
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
// Copyright (C) 2020, Gisselquist Technology, LLC
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
module	axisgfsm #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		localparam DMAC_ADDR_WIDTH = 5,
		localparam DMAC_DATA_WIDTH = 32,
		//
		// The "ABORT_KEY" is a byte that, if written to the control
		// word while the core is running, will cause the data transfer
		// to be aborted.
		parameter	[7:0]			ABORT_KEY  = 8'h6d
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// The control interface
		// {{{
		input	wire				i_start, i_abort,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_tbl_addr,
		input	reg	[3:0]			i_qos,
		input	reg	[2:0]			i_prot,
		output	reg				o_busy,
		output	reg				o_done,
		output	reg				o_int,
		output	reg				o_err,
		output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_tbl_addr,
		// }}}
		//
		// The prefetch interface
		// {{{
		output	reg				o_new_pc,
		output	reg				o_pf_clear_cache,
		output	reg				o_pf_ready,
		output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_pf_pc,
		input	reg				i_pf_valid,
		input	reg	[31:0]			i_pf_insn,
		input	reg	[C_AXI_ADDR_WIDTH-1:0]	i_pf_pc,
		input	reg				i_pf_illegal,
		// }}}
		//
		// The DMA submodule's AXI4-lite control interface
		// {{{
		output	reg				o_dmac_wvalid,
		input	wire				i_dmac_wready,
		output	reg [DMAC_ADDR_WIDTH-1:0]	o_dmac_waddr,
		output	reg [DMAC_DATA_WIDTH-1:0]	o_dmac_wdata,
		output	reg [DMAC_DATA_WIDTH/8-1:0]	o_dmac_wstrb,
		input	wire [DMAC_DATA_WIDTH-1:0]	i_dmac_rdata,
		input	wire				i_dma_complete
		// }}}
		// }}}
	);

	// Local parameter definitions
	// {{{

	// Scatter gather state machine states
	// {{{
	// States:
	// - 0. IDLE (nothing going on, waiting for a new program counter)
	//	Enter on completion, reset, or (abort and DMA complete)
	// - 1. READ_LOSRC -> DMA
	// - 2. READ_HISRC -> DMA (Optional)
	//	((Skip || JUMP) ->READ_LOSRC)
	// - 3. READ_LODST -> DMA
	// - 4. READ_HIDST -> DMA (Optional)
	// - 5. READ_LEN   -> DMA
	// - 6. READ_FLAGS -> SETS -> START DMA
	// - 7. Wait on DMA
	//	(Set interrupt if INT complete)
	//	(If last, go to idle, else jump to #1)
	//	(Set LAST on abort)
	//
	localparam [2:0]	SG_IDLE    = 3'h0,
				SG_SRCHALF = 3'h1,
				SG_SRCADDR = 3'h2,
				SG_DSTHALF = 3'h3,
				SG_DSTADDR = 3'h4,
				SG_LENGTH  = 3'h5,
				SG_CONTROL = 3'h6,
				SG_WAIT    = 3'h7;
	// }}}

	// DMA device internal addresses
	// {{{
	localparam [4:0]	DMA_CONTROL= 5'b00000,
				DMA_UNUSED = 5'b00100,
				DMA_SRCLO  = 5'b01000,
				DMA_SRCHI  = 5'b01100,
				DMA_DSTLO  = 5'b10000,
				DMA_DSTHI  = 5'b10100,
				DMA_LENLO  = 5'b11000,
				DMA_LENHI  = 5'b11100;
	// }}}

	localparam [C_AXI_ADDR_WIDTH-1:0] TBL_SIZE
				= (C_AXI_ADDR_WIDTH < 30) ? (4*5) : (4*7);

	// }}}

	// Register/net declarations
	// {{{
	reg		tbl_last, tbl_int_enable;
	reg	[2:0]	sgstate;
	reg		dma_err, dma_abort, dma_done, dma_busy;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// FSM Control states
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_pf_ready
	// {{{
	always @(*)
	begin
		case(sgstate)
		SG_IDLE:	o_pf_ready = 1'b0;
		SG_SRCHALF:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_SRCADDR:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_DSTHALF:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_DSTADDR:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_LENGTH:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_CONTROL:	o_pf_ready = (!o_dmac_wvalid || i_dmac_wready);
		SG_WAIT:	o_pf_ready = 1'b0;
		endcase

		if (!o_busy || o_pf_clear_cache)
			o_pf_ready = 0;
	end
	// }}}

	// w_int
	// {{{
	always @(*)
	begin
		o_int = 1'b0;

		if (sgstate == SG_WAIT && i_dma_complete
					&& (tbl_last || tbl_int_enable))
			o_int = 1'b1;
		if (i_pf_valid && o_pf_ready && i_pf_illegal)
			o_int = 1'b1;
	end
	// }}}

	always @(*)
	begin
		dma_err   = i_dmac_rdata[4];
		dma_abort = i_dmac_rdata[3];
		dma_done  = i_dmac_rdata[1];
		dma_busy  = i_dmac_rdata[0];
	end

	// The GIANT FSM itself
	// new_pc, pf_clear_cache, dmac_wvalid, dmac_waddr, dmac_wdata,
	// dmac_wstrb, ipc,
	// {{{
	always @(posedge S_AXI_ACLK)
	begin
		// Auto-cleared values
		// {{{
		o_new_pc <= 1'b0;
		o_pf_clear_cache <= 1'b0;
		if (i_dmac_wready)
			o_dmac_wvalid <= 1'b0;
		if (!o_dmac_wvalid || i_dmac_wready)
			o_dmac_wstrb <= 4'hf;
		o_done <= 1'b0;
		o_err  <= 1'b0;
		// }}}

		case(sgstate)
		SG_IDLE: // IDLE -- waiting for start
			// {{{
			begin
			o_pf_pc <= i_tbl_addr;
			if (i_start)
			begin
				o_new_pc <= 1'b1;
				if (C_AXI_ADDR_WIDTH > 30)
					sgstate <= SG_SRCHALF;
				else
					sgstate <= SG_SRCADDR;
				o_busy <= 1'b1;
			end else begin
				o_new_pc <= 1'b0;
				o_pf_clear_cache <= 1'b1;
				o_busy <= 1'b0;
			end end
			// }}}
		SG_SRCHALF: // Get the first source address
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid <= 1'b1;
			o_dmac_waddr  <= DMA_SRCLO;
			o_dmac_wdata  <= i_pf_insn;
			sgstate <= SG_SRCADDR;
			o_pf_pc[31:0] <= i_pf_insn;
			o_tbl_addr <= i_pf_pc;
			end
			// }}}
		SG_SRCADDR: // Second half of the source address
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid <= 1'b1;
			o_dmac_waddr  <= (C_AXI_ADDR_WIDTH<30)
						? DMA_SRCLO : DMA_SRCHI;
			o_dmac_wdata  <= i_pf_insn;
			sgstate <= SG_DSTHALF;
			o_pf_pc[31:0] <= i_pf_insn;
			if (C_AXI_ADDR_WIDTH < 30)
				o_tbl_addr <= i_pf_pc;

			tbl_last <= 1'b0;

			case(i_pf_insn[31:30])
			2'b00: // Other items still to follow
				tbl_last <= 1'b0;
			2'b01: // Last item in the chain
				tbl_last <= 1'b1;
			2'b10: begin // Skip
				tbl_last <= 1'b0;
				if (C_AXI_ADDR_WIDTH > 30)
					sgstate <= SG_SRCHALF;
				else
					sgstate <= SG_SRCADDR;
				o_new_pc <= 1'b1;
				o_pf_pc <= o_tbl_addr + TBL_SIZE;
				end
			2'b11: begin // Jump
				o_new_pc <= 1'b1;
				// ipc <= // already set from above
				end
			endcase
			end
			// }}}
		SG_DSTHALF: // Get the first half of the destination address
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid<= 1'b1;
			o_dmac_waddr <= DMA_DSTLO;
			o_dmac_wdata <= i_pf_insn;
			sgstate    <= SG_DSTADDR;
			end
			// }}}
		SG_DSTADDR: // Second half of the destination address
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid <= 1'b1;
			o_dmac_waddr  <= (C_AXI_ADDR_WIDTH<30)
						? DMA_DSTLO : DMA_DSTHI;
			o_dmac_wdata <= { 1'b0, i_pf_insn[30:0] };
			sgstate    <= SG_LENGTH;
			tbl_int_enable <= i_pf_insn[31];
			end
			// }}}
		SG_LENGTH: // The length word
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid <= 1'b1;
			o_dmac_waddr  <= DMA_LENLO;
			o_dmac_wdata <= i_pf_insn;
			sgstate    <= SG_CONTROL;
			end
			// }}}
		SG_CONTROL: // The control word to get us started
			// {{{
			if (i_pf_valid && (!o_dmac_wvalid || i_dmac_wready))
			begin
			o_dmac_wvalid <= 1'b1;
			o_dmac_waddr  <= DMA_CONTROL;
			o_dmac_wdata <= { 9'h0, i_prot, i_qos,
					11'h0,
					1'h1, // Clear any errors
					1'b1, // Clr abort flag
					1'b1, // Set int enable, int
					1'b1, // Clr any prior interrupt
					1'b1 };
			sgstate    <= SG_WAIT;
			o_tbl_addr <= o_tbl_addr + TBL_SIZE;
			end
			// }}}
		SG_WAIT: // Wait for the DMA transfer to complete
			// {{{
			if (i_dma_complete && !o_dmac_wvalid)
			begin
				// o_int <= int_enable;
				if (tbl_last || dma_err || i_pf_illegal)
				begin
					o_pf_clear_cache <= 1'b1;
					sgstate <= SG_IDLE;
					o_busy <= 1'b0;
					o_done <= 1'b1;
					o_err  <= dma_err || dma_abort;
					if (!i_pf_illegal)
						// Halt at the beginning
						// of the TBL
						o_pf_pc <= o_tbl_addr;
					else
						o_pf_pc <= i_pf_pc;
				end else if (C_AXI_ADDR_WIDTH > 30)
					sgstate <= SG_SRCHALF;
				else
					sgstate <= SG_SRCADDR;
			end
			// }}}
		endcase

		if (i_pf_valid && i_pf_illegal && sgstate != SG_WAIT
			&& !o_new_pc && !o_pf_clear_cache)
		begin
			// {{{
			sgstate <= SG_IDLE;
			o_pf_clear_cache <= 1'b1;
			o_done <= 1'b1;
			o_busy <= 1'b0;
			o_err  <= 1'b1;
			// }}}
		end

		if (i_abort && (!o_dmac_wvalid || i_dmac_wready))
		begin
			// {{{
			o_dmac_wstrb <= 4'h8;
			o_dmac_wdata[31:24] <= ABORT_KEY;
			o_dmac_wvalid <= !dma_abort && (sgstate == SG_WAIT);
			// }}}
			if (!dma_busy)
				sgstate <= SG_IDLE;
		end

		if (!S_AXI_ARESETN)
		begin
			// {{{
			sgstate <= SG_IDLE;
			o_pf_clear_cache <= 1'b1;
			o_dmac_wvalid <= 1'b0;
			o_pf_pc <= 0;
			// }}}
		end
	end
	// }}}

	// }}}

	// Make Verilator happy
	// {{{
	// Verilatar lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dma_done, i_dmac_rdata[31:5],
				i_dmac_rdata[2] };
	// Verilatar lint_on  UNUSED
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
