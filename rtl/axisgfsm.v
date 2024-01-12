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
// Table format:
//	Table entries either consist of five 32-bit words, or three 32-bit
//	words, depending upon the size of the address bus.
//
//	Address bus > 30 bits: five 32-bit words
//	0-1:	64b: { 2'bflags, 62'b SOURCE ADDRESS (bytes) }
//			00: Continue after this to next
//			01: Last item in chain
//			10: Skip this address
//			11: Jump to new address
//	2-3:	64b: { int_en, 1'b0,  DESTINATION ADDRESS (bytes) }
//	4:	32b Transfer length (in bytes)
//
//	Address bus <= 30 bits: three 32-bit words
//	0:	32b: { 2'bflags, 30'b SOURCE ADDRESS (bytes) }
//	1:	32b: { int_en, 1'b0, 30'b DESTINATION ADDRESS (bytes) }
//	2:	32b LENGTH (in bytes)
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
module	axisgfsm #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 30,
		// Verilator lint_off UNUSED
		parameter	C_AXI_DATA_WIDTH = 32,
		// Verilator lint_on  UNUSED
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
		input	wire	[3:0]			i_qos,
		input	wire	[2:0]			i_prot,
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
		input	wire				i_pf_valid,
		input	wire	[31:0]			i_pf_insn,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_pf_pc,
		input	wire				i_pf_illegal,
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
	// Verilator lint_off UNUSED
	localparam [4:0]	DMA_CONTROL= 5'b00000,
				DMA_UNUSED = 5'b00100,
				DMA_SRCLO  = 5'b01000,
				DMA_SRCHI  = 5'b01100,
				DMA_DSTLO  = 5'b10000,
				DMA_DSTHI  = 5'b10100,
				DMA_LENLO  = 5'b11000,
				DMA_LENHI  = 5'b11100;
	// Verilator lint_on  UNUSED
	// }}}

	localparam [C_AXI_ADDR_WIDTH-1:0] TBL_SIZE
				= (C_AXI_ADDR_WIDTH <= 30) ? (4*3) : (4*5);

	// }}}

	// Register/net declarations
	// {{{
	reg		tbl_last, tbl_int_enable;
	reg	[2:0]	sgstate;
	reg		dma_err, dma_abort, dma_done, dma_busy, dma_starting,
			dma_aborting;
	reg	[59:0]	r_pf_pc;
	reg		dma_op_complete, dma_terminate;

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
		SG_CONTROL:	o_pf_ready = 1'b0;
		SG_WAIT:	o_pf_ready = 1'b0;
		endcase

		if (!o_busy || o_pf_clear_cache || o_new_pc)
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

	// Returns from the DMA controller (one clock later)
	// {{{
	always @(*)
	begin
		dma_err   = i_dmac_rdata[4];
		dma_abort = i_dmac_rdata[3];
		dma_done  = i_dmac_rdata[1];
		dma_busy  = i_dmac_rdata[0];
	end
	// }}}

	// dma_op_complete
	// {{{
	always @(*)
	if (dma_busy || dma_starting || (o_dmac_wvalid && !i_dmac_wready))
		dma_op_complete = 0;
	else
		dma_op_complete = (!o_dmac_wvalid || !o_dmac_wstrb[0]);
	// }}}

	// dma_terminate
	// {{{
	always @(*)
	begin
		dma_terminate = 0;
		if (i_abort || tbl_last || dma_aborting)
			dma_terminate = 1;
		if (dma_err || i_pf_illegal)
			dma_terminate = 1;
	end
	// }}}

	// The GIANT FSM itself
	// new_pc, pf_clear_cache, dmac_wvalid, dmac_waddr, dmac_wdata,
	// dmac_wstrb, ipc,
	// {{{
	initial	r_pf_pc  = 0;
	initial	sgstate  = SG_IDLE;
	initial	o_new_pc = 1'b0;
	initial	o_busy   = 1'b0;
	initial	o_done   = 1'b0;
	initial	o_err    = 1'b0;
	initial	o_dmac_wvalid = 1'b0;
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
			r_pf_pc[C_AXI_ADDR_WIDTH-1:0] <= i_tbl_addr;
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
			// r_pf_pc[31:0] <= i_pf_insn;
			o_tbl_addr <= i_pf_pc;
			end
			// }}}
		SG_SRCADDR: // Second half of the source address
			// {{{
			if (i_pf_valid && o_pf_ready)
			begin
			o_dmac_wvalid <= !i_pf_insn[31];
			o_dmac_waddr  <= (C_AXI_ADDR_WIDTH<=30)
						? DMA_SRCLO : DMA_SRCHI;
			o_dmac_wdata  <= i_pf_insn;
			// r_pf_pc[31:0] <= i_pf_insn;
			if (C_AXI_ADDR_WIDTH <= 30)
			begin
				sgstate <= SG_DSTADDR;
				o_tbl_addr <= i_pf_pc;
				// // r_pf_pc[30-1:0] <= i_pf_insn[30-1:0];
			end else begin
				sgstate <= SG_DSTHALF;
				// r_pf_pc[60-1:30] <= i_pf_insn[30-1:0];
			end

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
				r_pf_pc[C_AXI_ADDR_WIDTH-1:0]
						<= r_pf_pc[C_AXI_ADDR_WIDTH-1:0] + TBL_SIZE;
				end
			2'b11: begin // Jump
				o_new_pc <= 1'b1;
				// ipc <= // already set from above
				if (C_AXI_ADDR_WIDTH > 30)
					sgstate <= SG_SRCHALF;
				else
					sgstate <= SG_SRCADDR;
				r_pf_pc[C_AXI_ADDR_WIDTH-1:0] <= i_pf_insn[C_AXI_ADDR_WIDTH-1:0];
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
			o_dmac_waddr  <= (C_AXI_ADDR_WIDTH<=30)
						? DMA_DSTLO : DMA_DSTHI;
			o_dmac_wdata <= { 2'b0, i_pf_insn[29:0] };
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
			if (i_pf_insn <= 0)
			begin
				o_dmac_wvalid <= 1'b0;
				if (tbl_last)
				begin
					sgstate    <= SG_IDLE;
					o_new_pc   <= 1'b0;
					o_busy     <= 1'b0;
					o_done     <= 1'b1;
					o_pf_clear_cache <= 1'b1;
				end else begin
					sgstate    <= SG_SRCADDR;
					o_new_pc   <= 1'b1;
				end
			end
			end
			// }}}
		SG_CONTROL: // The control word to get us started
			// {{{
			if (!o_dmac_wvalid || i_dmac_wready)
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
			if (dma_op_complete)
			begin
				// o_int <= int_enable;
				r_pf_pc[C_AXI_ADDR_WIDTH-1:0] <= o_tbl_addr;
				if (dma_terminate)
				begin
					o_pf_clear_cache <= 1'b1;
					sgstate <= SG_IDLE;
					o_busy <= 1'b0;
					o_done <= 1'b1;
					o_err  <= dma_err || dma_abort;
					if (i_pf_illegal)
						r_pf_pc[C_AXI_ADDR_WIDTH-1:0] <= i_pf_pc;
				end else if (C_AXI_ADDR_WIDTH > 30)
					sgstate <= SG_SRCHALF;
				else
					sgstate <= SG_SRCADDR;
			end
			// }}}
		endcase

		if (i_pf_valid && i_pf_illegal
			&& sgstate != SG_CONTROL && sgstate != SG_WAIT
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
			o_dmac_wvalid <= o_dmac_wstrb[0] && dma_busy
					&& !dma_err && (sgstate == SG_WAIT);
			// }}}
			if (!dma_busy && (sgstate != SG_WAIT))
			begin
				sgstate <= SG_IDLE;
				o_done  <= 1'b1;
				o_new_pc<= 1'b0;
				o_busy  <= 1'b0;
				o_dmac_wvalid <= 1'b0;
				o_pf_clear_cache  <= 1'b1;
			end
		end

		if (!S_AXI_ARESETN)
		begin
			// {{{
			sgstate <= SG_IDLE;
			o_pf_clear_cache <= 1'b1;
			o_new_pc <= 1'b0;
			o_dmac_wvalid <= 1'b0;
			r_pf_pc <= 0;
			o_busy <= 1'b0;
			o_done <= 1'b0;
			o_err  <= 1'b0;
			// }}}
		end

		r_pf_pc[60-1:C_AXI_ADDR_WIDTH] <= 0;
	end
	// }}}

	// dma_starting
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		dma_starting <= 0;
	else if (sgstate != SG_WAIT)
		dma_starting <= 0;
	else if (!o_dmac_wvalid || o_dmac_waddr != DMA_CONTROL)
		dma_starting <= 0;
	else
		dma_starting <= o_dmac_wdata[0] && o_dmac_wstrb[0];

	always @(*)
		o_pf_pc = { r_pf_pc[C_AXI_ADDR_WIDTH-1:2], 2'b00 };
	// }}}

	// dma_aborting
	// {{{
	initial	dma_aborting = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		dma_aborting <= 0;
	else if (sgstate != SG_WAIT)
		dma_aborting <= 0;
	else if (!dma_aborting)
	begin
		if (i_abort)
			dma_aborting <= 1;
	end else if (!dma_busy && !dma_starting && (!o_dmac_wvalid
					|| (i_dmac_wready && !o_dmac_wstrb[0])))
		dma_aborting <= 0;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (o_dmac_wvalid && !o_dmac_wstrb[0])
			assert(dma_aborting);
		if (sgstate != SG_WAIT && sgstate != SG_IDLE)
			assert(!dma_aborting);
	end
`endif
	// }}}
	// }}}

	// Make Verilator happy
	// {{{
	// Verilatar lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dma_done, i_dmac_rdata[31:5],
				i_dmac_rdata[2],
				r_pf_pc[59:C_AXI_ADDR_WIDTH] };
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
	localparam	F_LGDEPTH = 4;
	// Verilator lint_off UNDRIVEN
	(* anyseq *) reg [TBL_SIZE*8-1:0] f_tblentry;
	(* anyconst *) reg		f_never_abort;
	(* anyseq *)	reg	f_dma_complete;
	// Verilator lint_on  UNDRIVEN
	reg	f_past_valid;
	reg	[C_AXI_ADDR_WIDTH-1 :0]	f_tbladdr, f_pc;
	reg				f_tbl_last, f_tbl_skip, f_tbl_jump,
					f_tbl_int_enable;
	// reg	[C_AXI_ADDR_WIDTH-1:0]	f_tbl_src;
	reg				f_dma_arvalid, f_dma_arready;
			reg	f_dma_busy;



	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(*)
	if (i_start)
	begin
		assume(!i_abort);
		assume(i_tbl_addr[1:0] == 2'b00);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Prefetch interface property checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Prefetch properties

	assume property (@(posedge S_AXI_ACLK)
		S_AXI_ARESETN && i_pf_valid && !o_pf_ready
			&& !o_pf_clear_cache && !o_new_pc
		|=> i_pf_valid && $stable({
				i_pf_insn, i_pf_pc, i_pf_illegal }));

	always @(*)
	if (o_new_pc)
		assert(o_pf_pc[1:0] == 2'b00);

	always @(posedge S_AXI_ACLK)
	if (o_new_pc)
		f_pc <= o_pf_pc;
	else if (i_pf_valid && o_pf_ready)
		f_pc <= f_pc + 4;

	always @(*)
	if (i_pf_valid)
		assume(i_pf_pc == f_pc);

	always @(*)
	if (S_AXI_ARESETN && !o_new_pc && !o_pf_clear_cache)
		assert(f_pc[1:0] == 2'b00);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN || o_new_pc
				|| o_pf_clear_cache))
	begin
		assume(!i_pf_illegal);
	end else if (!$rose(i_pf_valid))
	begin
		assume(!$rose(i_pf_illegal));
	end else
		assume($stable(i_pf_illegal));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite interface property checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[F_LGDEPTH-1:0]	fdma_rd_outstanding, fdma_wr_outstanding,
				fdma_awr_outstanding;
	reg			f_dma_bvalid, f_dma_rvalid;

	faxil_master #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(DMAC_ADDR_WIDTH),
		.F_OPT_BRESP(1'b1),
		.F_OPT_RRESP(1'b0),
		.F_OPT_NO_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(o_dmac_wvalid),
		.i_axi_awready(i_dmac_wready),
		.i_axi_awaddr(o_dmac_waddr),
		.i_axi_awprot( 3'h0),
		//
		.i_axi_wvalid(o_dmac_wvalid),
		.i_axi_wready(i_dmac_wready),
		.i_axi_wdata( o_dmac_wdata),
		.i_axi_wstrb( o_dmac_wstrb),
		//
		.i_axi_bvalid(f_dma_bvalid),
		.i_axi_bready(1'b1),
		.i_axi_bresp( 2'b00),
		//
		.i_axi_arvalid(f_dma_arvalid),
		.i_axi_arready(f_dma_arready),
		.i_axi_araddr(DMA_CONTROL),
		.i_axi_arprot(3'h0),
		//
		.i_axi_rvalid(f_dma_rvalid),
		.i_axi_rready(1'b1),
		.i_axi_rdata(i_dmac_rdata),
		.i_axi_rresp(2'b00),
		//
		.f_axi_rd_outstanding(fdma_rd_outstanding),
		.f_axi_wr_outstanding(fdma_wr_outstanding),
		.f_axi_awr_outstanding(fdma_awr_outstanding)
		// }}}
	);

	initial	f_dma_arvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dma_arvalid <= 1'b0;
	else
		f_dma_arvalid <= 1'b1;

	always @(*)
		f_dma_arready = 1'b1;

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(fdma_awr_outstanding == fdma_wr_outstanding);
		assert(fdma_wr_outstanding == (f_dma_bvalid ? 1:0));
		assert(fdma_rd_outstanding <= 1);
	end

	assert property (@(posedge S_AXI_ACLK)
		!S_AXI_ARESETN
		|=> sgstate == SG_IDLE && !o_dmac_wvalid);


	assert property (@(posedge S_AXI_ACLK)
		S_AXI_ARESETN && o_dmac_wvalid && !i_dmac_wready
		|=> o_dmac_wvalid && $stable({
			o_dmac_waddr, o_dmac_wdata, o_dmac_wstrb }));

	assert property (@(posedge S_AXI_ACLK)
		fdma_wr_outstanding == fdma_awr_outstanding);

	assert property (@(posedge S_AXI_ACLK)
		fdma_wr_outstanding == (f_dma_bvalid ? 1:0));

	initial	f_dma_bvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dma_bvalid <= 0;
	else if (o_dmac_wvalid && i_dmac_wready)
		f_dma_bvalid <= 1;
	else
		f_dma_bvalid <= 0;

	initial	f_dma_rvalid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dma_rvalid <= 0;
	else if (f_dma_arvalid)
		f_dma_rvalid <= 1;
	else
		f_dma_rvalid <= 0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DMA busy and read interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_dma_busy = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dma_busy <= 0;
	else if (o_dmac_wvalid && i_dmac_wready && o_dmac_waddr == 0
			&& o_dmac_wstrb[0] && o_dmac_wdata[0])
		f_dma_busy <= 1'b1;
	else if (f_dma_busy)
		f_dma_busy <= !f_dma_complete;

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (sgstate != SG_WAIT)
			assert(!f_dma_busy);
		else if (o_dmac_wvalid && !dma_aborting)
			assert(!f_dma_busy);
	end

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && S_AXI_ARESETN && $past(f_dma_busy))
		assert(!dma_starting);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid)
	begin
		assume(dma_busy == $past(f_dma_busy));
		assume(i_dma_complete == $past(f_dma_complete));
	end

	always @(*)
	if (!f_dma_busy)
		assume(!f_dma_complete);

	assume property (@(posedge S_AXI_ACLK)
		disable iff (!S_AXI_ARESETN)
		!dma_busy ##1 !dma_busy |-> !$rose(dma_err)
	);

	assume property (@(posedge S_AXI_ACLK)
		disable iff (!S_AXI_ARESETN)
		$rose(dma_busy) |=> !dma_err);

	assume property (@(posedge S_AXI_ACLK)
		disable iff (!S_AXI_ARESETN)
		o_dmac_wvalid && i_dmac_wready && o_dmac_wstrb[0]
				&& o_dmac_wdata[4]
		|=> ##1 !dma_err);

	assume property (@(posedge S_AXI_ACLK)
		disable iff (!S_AXI_ARESETN)
		!o_dmac_wvalid || !i_dmac_wready || !o_dmac_wstrb[0]
				|| !o_dmac_wdata[4]
		|=> ##1 !$fell(dma_err));


//	assume property (@(posedge S_AXI_ACLK)
//		dma_busy |=> dma_busy [*0:$]
//		##1 dma_busy && i_dma_complete
//		##1 !dma_busy);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// State machine checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	always @(*)
	if (o_new_pc)
	begin
		if (C_AXI_ADDR_WIDTH <= 30)
		begin
			assert(sgstate == SG_SRCADDR);
		end else
			assert(sgstate == SG_SRCHALF);
	end

	generate if (C_AXI_ADDR_WIDTH > 30)
	begin
		always @(*)
		begin
			f_tbl_last = (f_tblentry[63:62] == 2'b01);
			f_tbl_skip = (f_tblentry[63:62] == 2'b10);
			f_tbl_jump = (f_tblentry[63:62] == 2'b11);
			f_tbl_int_enable = f_tblentry[127];
		end
	end else begin
		always @(*)
		begin
			f_tbl_last = (f_tblentry[31:30] == 2'b01);
			f_tbl_skip = (f_tblentry[31:30] == 2'b10);
			f_tbl_jump = (f_tblentry[31:30] == 2'b11);
			f_tbl_int_enable = f_tblentry[63];
		end
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && (sgstate != SG_IDLE))
	begin
		if ($stable(sgstate))
		begin
			assume($stable(f_tblentry));
		end else if ((C_AXI_ADDR_WIDTH > 30)&&(sgstate != SG_SRCHALF))
		begin
			assume($stable(f_tblentry));
		end else if ((C_AXI_ADDR_WIDTH <= 30)&&(sgstate != SG_SRCADDR))
			assume($stable(f_tblentry));
	end

	always @(posedge S_AXI_ACLK)
	if (o_new_pc)
		f_tbladdr <= o_pf_pc;
	else if (sgstate == SG_WAIT && dma_op_complete && !dma_terminate)
		f_tbladdr <= f_tbladdr + TBL_SIZE;

	assert property (@(posedge S_AXI_ACLK)
		disable iff (!S_AXI_ARESETN)
		sgstate == SG_IDLE && !i_start
		|=> sgstate == SG_IDLE && o_pf_clear_cache);

	generate if (C_AXI_ADDR_WIDTH <= 30)
	begin : SMALL_ADDRESS_SPACE
		// {{{
		reg	[5:0]	f_dma_seq;

		always @(*)
		begin
			assert(sgstate != SG_SRCHALF);
			assert(sgstate != SG_DSTHALF);
		end

		always @(*)
		if (i_pf_valid)
		case(sgstate)
		// SG_IDLE:	begin end
		// SG_SRCHALF:	begin end
		// SG_DSTHALF:	begin end
		// SG_LENGTH:	begin end
		// SG_CONTROL:	begin end
		// SG_WAIT:	begin end
		SG_SRCADDR: begin
			assume(i_pf_insn == f_tblentry[31:0]
				&&(i_pf_pc == f_tbladdr));
			end
		SG_DSTADDR: begin
			assume(i_pf_insn == f_tblentry[63:32]
				&&(i_pf_pc == f_tbladdr + 4));
			end
		SG_LENGTH: begin
			assume(i_pf_insn == f_tblentry[95:64]
				&&(i_pf_pc == f_tbladdr + 8));
			end
		default: begin end
		endcase

		assert property (@(posedge S_AXI_ACLK)
			disable iff (!S_AXI_ARESETN)
			sgstate == SG_IDLE && i_start
			|=> o_new_pc && !o_pf_clear_cache
				&& sgstate == SG_SRCADDR
				&& r_pf_pc[C_AXI_ADDR_WIDTH-1:0]
					== $past(i_tbl_addr));

		initial	f_dma_seq = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			f_dma_seq <= 0;
		else begin

			// SG_SRCADDR, or entering SG_SRCADDR
			// {{{
			if ((f_dma_seq == 0)&&(i_start))
				f_dma_seq <= 1;

			if (f_dma_seq[0] || o_new_pc)
			begin
				assert(sgstate == SG_SRCADDR);
				assert(!o_dmac_wvalid);
				assert(!dma_busy);
				f_dma_seq <= 1;
				if (i_pf_valid && o_pf_ready)
				begin
					f_dma_seq <= 2;

					if (f_tbl_jump || f_tbl_skip)
						f_dma_seq <= 1;
				end

				if (!o_new_pc)
				begin
					assert(o_pf_pc == f_tbladdr);
					assert(f_pc == o_pf_pc);
				end

				if ($past(sgstate == SG_SRCADDR
					&& i_pf_valid && o_pf_ready))
				begin
					// Jump or skip

					assert(o_new_pc);
					// Check the jump address
					// if ($past(i_pf_insn[31:30] == 2'b11))
					if ($past(f_tbl_jump))
					begin
						assert(o_pf_pc == { $past(i_pf_insn[C_AXI_ADDR_WIDTH-1:2]), 2'b00 });
					end else // Skip
						assert(o_pf_pc == $past(f_tbladdr + TBL_SIZE));
				end
			end
			// }}}

			// SG_DSTADDR
			// {{{
			if (f_dma_seq[1])
			begin
				assert(sgstate == SG_DSTADDR);
				assert(tbl_last == f_tbl_last);
				assert(o_tbl_addr == f_tbladdr);
				if ($rose(f_dma_seq[1]))
					assert(o_dmac_wvalid);
				assert(o_dmac_waddr == DMA_SRCLO);
				assert(o_dmac_wdata == f_tblentry[31:0]);
				assert(&o_dmac_wstrb);
				assert(!dma_busy);
				assert(o_pf_pc == f_tbladdr);
				// assert(f_pc == o_pf_pc + 4);
				f_dma_seq <= 2;
				if (i_pf_valid && o_pf_ready)
					f_dma_seq <= 4;
			end
			// }}}

			// SG_LENGTH
			// {{{
			if (f_dma_seq[2])
			begin
				assert(sgstate == SG_LENGTH);
				assert(tbl_last == f_tbl_last);
				assert(tbl_int_enable == f_tbl_int_enable);
				assert(o_tbl_addr == f_tbladdr);
				if ($rose(f_dma_seq[2]))
					assert(o_dmac_wvalid);
				assert(o_dmac_waddr == DMA_DSTLO);
				assert(o_dmac_wdata == { 2'b00, f_tblentry[61:32] });
				assert(&o_dmac_wstrb);
				assert(!dma_busy);
				assert(o_pf_pc == f_tbladdr);
				// assert(f_pc == o_pf_pc + 8);
				f_dma_seq <= 4;
				if (i_pf_valid && o_pf_ready)
				begin
					if (i_pf_insn == 0)
					begin
						if (tbl_last)
							f_dma_seq <= 0;
						else
							f_dma_seq <= 1;
					end else
						f_dma_seq <= 8;
				end
			end
			// }}}

			// SG_CONTROL
			// {{{
			if (f_dma_seq[3])
			begin
				assert(sgstate == SG_CONTROL);
				assert(tbl_last == f_tbl_last);
				assert(o_tbl_addr == f_tbladdr);
				assert(o_dmac_wvalid);
				assert(o_dmac_waddr == DMA_LENLO);
				assert(o_dmac_wdata == f_tblentry[95:64]);
				assert(&o_dmac_wstrb);
				assert(!dma_busy);
				assert(o_pf_pc == f_tbladdr);
				assert(f_pc == f_tbladdr + TBL_SIZE);
				// assert(f_pc == o_pf_pc);
				f_dma_seq <= 8;
				if (i_dmac_wready)
					f_dma_seq <= 16;
			end
			// }}}

			// SG_WAIT && o_dmac_wvalid
			// {{{
			if (f_dma_seq[4])
			begin
				assert(sgstate == SG_WAIT);
				assert(tbl_last == f_tbl_last);
				assert(o_tbl_addr == f_tbladdr + TBL_SIZE);
				assert(o_dmac_wvalid);
				assert(o_dmac_waddr == DMA_CONTROL);
				assert(o_dmac_wdata[15:0] == 16'h1f);
				assert(&o_dmac_wstrb);
				assert(!dma_busy);
				assert(o_pf_pc == f_tbladdr);
				assert(f_pc == f_tbladdr + TBL_SIZE);
				// assert(f_pc == o_pf_pc);
				f_dma_seq <= 16;
				if (o_dmac_wvalid && i_dmac_wready)
					f_dma_seq <= 32;
			end
			// }}}

			// SG_WAIT && !o_dmac_wvalid
			// {{{
			if (f_dma_seq[5])
			begin
				assert(sgstate == SG_WAIT);
				assert(tbl_last == f_tbl_last);
				assert(o_tbl_addr == f_tbladdr + TBL_SIZE);
				assert(o_dmac_waddr == DMA_CONTROL);
				// assert(o_dmac_wdata == f_tblentry[95:64]);
				if (f_never_abort)
				begin
					assert(&o_dmac_wstrb);
					assert(!o_dmac_wvalid);
				end else
					assert(o_dmac_wstrb == 4'h8
						|| o_dmac_wstrb == 4'hf);
				if (o_dmac_wvalid)
					assert(!o_dmac_wstrb[0]);
				f_dma_seq <= 32;
				assert(o_pf_pc == f_tbladdr);
				assert(f_pc == f_tbladdr + TBL_SIZE);
				// assert(f_pc == o_pf_pc);
				// if (tbl_last || (dma_err && !o_busy)
				//			|| i_pf_illegal)
				if (dma_op_complete)
				begin
					if (dma_terminate)
							// (dma_err && !o_busy))
						f_dma_seq <= 0;
					else
						f_dma_seq <= 1;
				end
			end
			// }}}

			// pf_illegal
			// {{{
			if ((|f_dma_seq[2:0]) && i_pf_illegal)
				f_dma_seq <= 0;
			// }}}

			// i_abort
			if ((|f_dma_seq[3:0]) && i_abort
					&& (!o_dmac_wvalid || i_dmac_wready))
				f_dma_seq <= 0;
		end

		always @(*)
		if (f_dma_seq == 0)
		begin
			assert(sgstate == SG_IDLE);
			assert(!o_new_pc);
			assert(!o_dmac_wvalid);
		end

		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || $past(!S_AXI_ARESETN))
		begin end
		else if (sgstate == 0)
		begin
			assert(o_pf_clear_cache);
			assert(!dma_busy);
		end

		cover property (@(posedge S_AXI_ACLK) S_AXI_ARESETN); // !!!
		cover property (@(posedge S_AXI_ACLK) f_dma_seq == 0 && S_AXI_ARESETN); // !!!
		cover property (@(posedge S_AXI_ACLK) f_dma_seq == 0 && S_AXI_ARESETN && !i_abort); // !!!
		cover property (@(posedge S_AXI_ACLK) f_dma_seq == 0 && S_AXI_ARESETN && !i_abort && i_start); // !!!
		cover property (@(posedge S_AXI_ACLK) f_dma_seq[1]);
		cover property (@(posedge S_AXI_ACLK) f_dma_seq[2]);
		cover property (@(posedge S_AXI_ACLK) f_dma_seq[3]);
		cover property (@(posedge S_AXI_ACLK) f_dma_seq[4]);	// !!!
		cover property (@(posedge S_AXI_ACLK) f_dma_seq[5]);	// !!!

//		cover property (@(posedge S_AXI_ACLK)
//			disable iff (!S_AXI_ARESETN || i_abort || i_pf_illegal
//				|| dma_err)
//			f_dma_seq[0] ##1 1[*0:$] ##1 f_dma_seq[5]
//			##1 f_dma_seq == 0);	// !!!

		cover property (@(posedge S_AXI_ACLK)	// !!!
			f_dma_seq[5] && !tbl_last && f_dma_busy && dma_busy);

		cover property (@(posedge S_AXI_ACLK)	// !!!
			f_dma_seq[5] && tbl_last && f_dma_busy && dma_busy);

		cover property (@(posedge S_AXI_ACLK)
			f_dma_seq[5] ##2 f_dma_seq[0]);	// !!!

		cover property (@(posedge S_AXI_ACLK)
			f_dma_seq[5] && tbl_last && i_dma_complete);	// !!!

		cover property (@(posedge S_AXI_ACLK)
			f_dma_seq[5] && i_dma_complete);	// !!!
		// }}}
	end else begin : BIG_ADDR
	end endgenerate

	always @(*)
		assert(o_busy == (sgstate != SG_IDLE));

	always @(*)
	if (o_busy)
	begin
		assert(!o_done);
		assert(!o_err);
	end

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN) && $past(o_busy) && !o_busy)
		assert(o_done);

//	assert property (@(posedge S_AXI_ACLK)
//		!o_done |-> !o_int);

	assert property (@(posedge S_AXI_ACLK)
		!o_done && !o_busy |-> !o_err);

	always @(*)
	if (o_pf_ready)
		assert(!o_dmac_wvalid || i_dmac_wready);

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

	always @(*)
	if (f_never_abort)
		assume(!i_abort);

	// }}}
`endif
// }}}
endmodule
