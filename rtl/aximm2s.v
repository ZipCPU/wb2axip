////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximm2s
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Converts an AXI (full) memory port to an AXI-stream
//		interface.
// // {{{
//	While I am aware that other vendors sell similar components, if you
//	look under the hood you'll find no relation to anything but my own
//	work here.
//
// Registers:
//
//  0:	CMD_CONTROL
//		Controls the transaction via either starting or aborting an
//		ongoing transaction, provides feedback regarding the current
//		status.
//
//	[31]	r_busy
//		True if the core is in the middle of a transaction
//
//	[30]	r_err
//		True if the core has detected an error, a bus error
//		while the FIFO is reading.
//
//		Writing a '1' to this bit while the core is idle will clear it.
//		New transfers will not start until this bit is cleared.
//
//	[29]	r_complete
//		True if the transaction has completed, whether normally or
//		abnormally (error or abort).
//
//		Any write to the CMD_CONTROL register will clear this flag.
//
//	[28]	r_continuous
//		Normally the FIFO gets cleared and reset between operations.
//		However, if you set r_continuous, the core will then expect
//		a second operation to take place following the first one.
//		In this case, the operation will complete but the FIFO won't
//		get cleared.  During this time, the FIFO will not fill further.
//
//		Any write to the CMD_CONTROL register while the core is not
//		busy will adjust this bit.
//
//	[27]	!r_increment
//
//		If clear, the core reads from subsequent and incrementing
//		addresses.  If set, the core reads from the same address
//		throughout a transaction.
//
//		Writes to CMD_CONTROL while the core is idle will adjust this
//		bit.
//
//	[20:16]	LGFIFO
//		These are read-only bits, returning the size of the FIFO.
//
//	ABORT
//		If the core is busy, and ABORT_KEY (currently set to 8'h6d
//		below) is written to the top 8-bits of this register,
//		the current transfer will be aborted.  Any pending reads
//		will be completed, but nothing more will be written to the
//		stream.
//
//		Alternatively, the core will enter into an abort state
//		following any returned bus error indications.
//
//  4:	CMD_ADDR
//	[C_AXI_ADDR_WIDTH-1:($clog2(C_AXI_DATA_WIDTH)-3)]
//		If idle, the address the core will read from when it starts.
//		If busy, the address the core is currently reading from.
//		Upon completion, the address either returns to the starting
//		address (if r_continuous is clear), or otherwise becomes the
//		address where the core left off.  In the case of an abort or an
//		error, this will be (near) the address that was last read.
//
//		Why "near"?  Because this address records the reads that have
//		been issued while no error is pending.  If a bus error return
//		comes back, there may have been several more reads issued before
//		that error address.
//
//  8:  CMD_LEN
//	[LGLEN-1:0]
//		The size of the transfer in bytes.  Only accepts aligned
//		addresses, therefore bits [($clog2(C_AXI_DATA_WIDTH)-3):0]
//		will always be forced to zero.  To find out what size bus
//		this core is conencted to, or the maximum transfer length,
//		write a -1 to this value and read the returning result.
//		Only the active bits will be set.
//
//		While the core is busy, reads from this address will return
//		the number of items still to be read from the bus.
//
//		I hope to eventually add support for unaligned bursts.  Such
//		support is not currently part of this core.
//
// 12:	(Unused and reserved)
//
// }}}
//
// Status:
// {{{
//	1. The core passes both cover checks and formal property (assertion)
//		based checks.  It has not (yet) been tested in real hardware.
//
//	2. I'd like to support unaligned addresses and lengths.  This will
//		require aligning the data coming out of the FIFO as well.
//		As written, the core doesn't yet support these.
//
// }}}
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
// {{{
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
module	aximm2s #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		//
		// We support three 32-bit AXI-lite registers, requiring 2-bits
		// of AXI-lite addressing
		localparam	C_AXIL_ADDR_WIDTH = 2,
		localparam	C_AXIL_DATA_WIDTH = 32,
		//
		// The bottom ADDRLSB bits of any AXI address are subword bits
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3,
		//
		// OPT_REALIGN: Allow unaligned accesses, address requests
		// and sizes which may or may not match the underlying data
		// width.  If set, the core will quietly align these requests.
		parameter [0:0]	OPT_REALIGN = 1'b0,
		//
		// OPT_TKEEP [Future]: If set, will also add TKEEP signals to
		// the outgoing slave interface.  This is necessary if ever you
		// wish to output partial stream words, such as might happen if
		// the length were ever something other than a full number of
		// words.  (Not yet implemented)
		// parameter [0:0]	OPT_TKEEP = 1'b0,
		//
		// OPT_TLAST: If enabled, will embed TLAST=1 at the end of every
		// commanded burst.  If  disabled, TLAST will be set to a
		// constant 1'b1.
		parameter [0:0]	OPT_TLAST = 1'b0,
		//
		// ABORT_KEY is the value that, when written to the top 8-bits
		// of the control word, will abort any ongoing operation.
		parameter [7:0]	ABORT_KEY = 8'h6d,
		//
		// The size of the FIFO
		parameter	LGFIFO = 9,
		//
		// Maximum number of bytes that can ever be transferred, in
		// log-base 2
		parameter	LGLEN  = 20,
		//
		// AXI_ID is the ID we will use for all of our AXI transactions
		parameter	AXI_ID = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		// The stream interface
		// {{{
		output	wire					S_AXIS_TVALID,
		input	wire					S_AXIS_TREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXIS_TDATA,
		output	wire					S_AXIS_TLAST,
		// }}}
		//
		// The control interface
		// {{{
		input	wire					S_AXIL_AWVALID,
		output	wire					S_AXIL_AWREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_AWADDR,
		input	wire	[3:0]				S_AXIL_AWPROT,
		//
		input	wire					S_AXIL_WVALID,
		output	wire					S_AXIL_WREADY,
		input	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_WDATA,
		input	wire	[C_AXIL_DATA_WIDTH/8-1:0]	S_AXIL_WSTRB,
		//
		output	wire					S_AXIL_BVALID,
		input	wire					S_AXIL_BREADY,
		output	wire	[1:0]				S_AXIL_BRESP,
		//
		input	wire					S_AXIL_ARVALID,
		output	wire					S_AXIL_ARREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_ARADDR,
		input	wire	[3:0]				S_AXIL_ARPROT,
		//
		output	wire					S_AXIL_RVALID,
		input	wire					S_AXIL_RREADY,
		output	wire	[C_AXIL_DATA_WIDTH-1:0]		S_AXIL_RDATA,
		output	wire	[1:0]				S_AXIL_RRESP,
		// }}}
		//

		//
		// The AXI (full) read interface
		// {{{
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[7:0]			M_AXI_ARLEN,
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
		output	wire				M_AXI_ARLOCK,
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[1:0]			M_AXI_RRESP,
		// }}}
		//
		//
		// Create an output signal to indicate that we've finished
		output	reg				o_int
		// }}}
	);
	// Local parameter declarations
	// {{{
	localparam [1:0]	CMD_CONTROL   = 2'b00,
				CMD_ADDR      = 2'b01,
				CMD_LEN       = 2'b10,
				CMD_UNUSED    = 2'b11;
	localparam		CBIT_BUSY	= 31,
				CBIT_ERR	= 30,
				CBIT_COMPLETE	= 29,
				CBIT_CONTINUOUS	= 28,
				CBIT_INCREMENT	= 27;
	localparam	LGMAXBURST=(LGFIFO > 8) ? 8 : LGFIFO-1;
	localparam	LGLENW  = LGLEN  - ($clog2(C_AXI_DATA_WIDTH)-3),
			LGLENWA = LGLENW + (OPT_REALIGN ? 1:0);
	localparam	LGFIFOB = LGFIFO + ($clog2(C_AXI_DATA_WIDTH)-3);
	localparam [ADDRLSB-1:0] LSBZEROS = 0;
	// }}}

	wire	i_clk   =  S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	// Signal declarations
	// {{{
	reg	r_busy, r_err, r_complete, r_continuous, r_increment,
		cmd_abort, zero_length,
		w_cmd_start, w_complete, w_cmd_abort;
	// reg	cmd_start;
	reg				axi_abort_pending;

	reg	[LGLENWA-1:0]		ar_requests_remaining,
					ar_bursts_outstanding;
	reg	[LGMAXBURST:0]		r_max_burst;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_raddr;

	reg	[C_AXI_ADDR_WIDTH-1:0]	cmd_addr;
	reg	[LGLEN-1:0]		cmd_length_b;
	reg	[LGLENW-1:0]		cmd_length_w;
	reg	[LGLENWA-1:0]		cmd_length_aligned_w;
	reg				unaligned_cmd_addr;

	// FIFO signals
	wire				reset_fifo, write_to_fifo,
					read_from_fifo;
	wire	[C_AXI_DATA_WIDTH-1:0]	write_data;
	wire	[LGFIFO:0]		fifo_fill;
	wire				fifo_full, fifo_empty;

	wire				awskd_valid, axil_write_ready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	awskd_addr;
	//
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				arskd_valid, axil_read_ready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	arskd_addr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;
	reg	[C_AXIL_DATA_WIDTH-1:0]	w_status_word,
					w_addr_word,
					w_len_word;


	reg				axi_arvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_araddr;
	reg	[7:0]			axi_arlen;
	reg	[1:0]			axi_arburst;

	// Speed up checking for zeros
	reg				ar_none_remaining,
					ar_none_outstanding,
					phantom_start, start_burst;
	reg				partial_burst_requested;
	reg	[LGMAXBURST-1:0]	addralign;
	reg	[LGFIFO:0]		rd_uncommitted;
	reg				w_increment;
	reg	[LGMAXBURST:0]		initial_burstlen;
	reg	[LGLENWA-1:0]		rd_reads_remaining;
	reg				rd_none_remaining,
					rd_last_remaining;

	wire				realign_last_valid;
/*
					wr_none_pending, r_none_remaining;

	reg				w_phantom_start, phantom_start;
	reg	[LGFIFO:0]	next_fill;
*/

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	//
	////////////////////////////////////////////////////////////////////////
	//
	// This is mostly the skidbuffer logic, and handling of the VALID
	// and READY signals for the AXI-lite control logic in the next
	// section.
	// {{{

	//
	// Write signaling
	//
	// {{{

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXIL_BVALID || S_AXIL_BREADY);

	initial	axil_bvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXIL_BREADY)
		axil_bvalid <= 0;

	assign	S_AXIL_BVALID = axil_bvalid;
	assign	S_AXIL_BRESP = 2'b00;
	// }}}

	//
	// Read signaling
	//
	// {{{

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	assign	axil_read_ready = arskd_valid
				&& (!axil_read_valid || S_AXIL_RREADY);

	initial	axil_read_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (S_AXIL_RREADY)
		axil_read_valid <= 1'b0;

	assign	S_AXIL_RVALID = axil_read_valid;
	assign	S_AXIL_RDATA  = axil_read_data;
	assign	S_AXIL_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite controlled logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// Abort transaction
	//
	always @(*)
	begin
		w_cmd_abort = 0;
		w_cmd_abort = (axil_write_ready && awskd_addr == CMD_CONTROL)
			&& (wskd_strb[3] && wskd_data[31:24] == ABORT_KEY);
		if (!r_busy)
			w_cmd_abort = 0;
	end

	initial	cmd_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_abort <= 0;
	else
		cmd_abort <= (cmd_abort && r_busy)||w_cmd_abort;

	//
	// Start command
	//
	always @(*)
	if (r_busy)
		w_cmd_start = 0;
	else begin
		w_cmd_start = 0;
		if ((axil_write_ready && awskd_addr == CMD_CONTROL)
			&& (wskd_strb[3] && wskd_data[CBIT_BUSY]))
			w_cmd_start = 1;
		if (r_err && !wskd_data[CBIT_ERR])
			w_cmd_start = 0;
		if (zero_length)
			w_cmd_start = 0;
		if (OPT_REALIGN && unaligned_cmd_addr
				&& wskd_data[CBIT_INCREMENT])
			w_cmd_start = 0;
	end

	//
	// Calculate busy or complete flags
	//
	initial	r_busy     = 0;
	initial	r_complete = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_busy     <= 0;
		r_complete <= 0;
	end else if (!r_busy)
	begin
		if (w_cmd_start)
			r_busy <= 1'b1;
		if (axil_write_ready && awskd_addr == CMD_CONTROL)
			// Any write to the control register will clear the
			// completion flag
			r_complete <= 1'b0;
	end else if (r_busy)
	begin
		if (w_complete)
		begin
			r_complete <= 1;
			r_busy <= 1'b0;
		end
	end

	//
	// Interrupts
	//
	initial	o_int = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_int <= 0;
	else
		o_int <= (r_busy && w_complete);

	//
	// Error conditions
	//
	always @(posedge i_clk)
	if (i_reset)
		r_err <= 0;
	else if (!r_busy)
	begin
		if (axil_write_ready && awskd_addr == CMD_CONTROL)
		begin
			if (!w_cmd_abort)
				r_err <= r_err && (!wskd_strb[3] || !wskd_data[CBIT_ERR]);
			// On any request to start a transfer with an unaligned
			// address, that's not incrementing--declare an
			// immediate error
			if (wskd_strb[3] && wskd_data[CBIT_BUSY]
				&& wskd_data[CBIT_INCREMENT]
				&& (OPT_REALIGN && unaligned_cmd_addr))
				r_err <= 1'b1;
		end
	end else // if (r_busy)
	begin
		if (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RRESP[1])
			r_err <= 1'b1;
	end

	initial	r_continuous = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_continuous <= 0;
	else begin
		if (!r_busy && axil_write_ready && awskd_addr == CMD_CONTROL
			&& !w_cmd_abort)
			r_continuous <= wskd_strb[3] && wskd_data[CBIT_CONTINUOUS];
	end

	initial	r_increment   = 1'b1;
	initial	cmd_addr      = 0;
	initial	cmd_length_w  = 0;	// Counts in bytes
	initial	zero_length   = 1;
	initial	cmd_length_aligned_w = 0;
	initial	unaligned_cmd_addr = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_increment <= 1'b1;
		cmd_addr      <= 0;
		cmd_length_w  <= 0;
		cmd_length_aligned_w  <= 0;
		zero_length   <= 1;
		unaligned_cmd_addr <= 1'b0;
	end else if (axil_write_ready && !r_busy)
	begin
		case(awskd_addr)
		CMD_CONTROL:
			r_increment <= !wskd_data[CBIT_INCREMENT];
		CMD_ADDR: begin
			cmd_addr <= wskd_data;
			unaligned_cmd_addr <= |wskd_data[ADDRLSB-1:0];
			if (!OPT_REALIGN)
			begin
				cmd_addr[ADDRLSB-1:0] <= 0;
				unaligned_cmd_addr <= 1'b0;
			end else
				cmd_length_aligned_w <= cmd_length_w
					+ (|wskd_data[ADDRLSB-1:0] ? 1:0);
			// ERR: What if !r_increment?  In that case, we can't
			//   support unaligned addressing
			end
		CMD_LEN: begin
			cmd_length_w <= wskd_data[ADDRLSB +: LGLENW];
			zero_length <= (wskd_data[ADDRLSB +: LGLENW] == 0);
			cmd_length_aligned_w <= wskd_data[ADDRLSB +: LGLENW]
				+ (unaligned_cmd_addr ? 1:0);
			end
		default: begin end
		endcase
	end else if(r_busy && r_continuous && !axi_abort_pending && r_increment)
		cmd_addr <= axi_raddr
			+ ((M_AXI_RVALID && !M_AXI_RRESP[1]
				&& (!unaligned_cmd_addr || realign_last_valid))
				? (1<<ADDRLSB) : 0);

	always @(*)
		cmd_length_b    = { cmd_length_w,    {(ADDRLSB){1'b0}} };

	always @(*)
	begin
		w_status_word = 0;
		w_status_word[CBIT_BUSY]	= r_busy;
		w_status_word[CBIT_ERR]		= r_err;
		w_status_word[CBIT_COMPLETE]	= r_complete;
		w_status_word[CBIT_CONTINUOUS]	= r_continuous;
		w_status_word[CBIT_INCREMENT]	= !r_increment;
		w_status_word[20:16] = LGFIFO;

		w_addr_word = 0;
		if (r_busy)
			w_addr_word = axi_raddr;
		else
			w_addr_word = cmd_addr;

		w_len_word = 0;
		if (r_busy)
			w_len_word[LGLEN-1:0] = { rd_reads_remaining, LSBZEROS};
		else
			w_len_word[LGLEN-1:0] = cmd_length_b;

	end

	always @(posedge i_clk)
	if (!axil_read_valid || S_AXIL_RREADY)
	begin
		case(arskd_addr)
		CMD_CONTROL:	axil_read_data <= w_status_word;
		CMD_ADDR:	axil_read_data <= w_addr_word;
		CMD_LEN:	axil_read_data <= w_len_word;
		default		axil_read_data <= 0;
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The data FIFO section
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	assign	reset_fifo = i_reset || (!r_busy && (!r_continuous || r_err));

	// Realign the data (if OPT_REALIGN) before sending it to the FIFO
	// {{{
	// This allows us to handle unaligned addresses.
	generate if (OPT_REALIGN)
	begin : REALIGN_DATA

		reg				r_write_to_fifo;
		reg	[C_AXI_DATA_WIDTH-1:0]	last_data,
						r_write_data;
		reg	[ADDRLSB-1:0]		corollary_shift;
		reg				last_valid;
		reg	[ADDRLSB-1:0]		realignment;

		always @(*)
			realignment = cmd_addr[ADDRLSB-1:0];

		initial	last_data = 0;
		always @(posedge S_AXI_ACLK)
		if (reset_fifo || !unaligned_cmd_addr)
			last_data <= 0;
		else if (M_AXI_RVALID && M_AXI_RREADY)
			last_data <= M_AXI_RDATA >> (realignment * 8);

		initial	last_valid = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (reset_fifo)
			last_valid <= 0;
		else if (M_AXI_RVALID && M_AXI_RREADY)
			last_valid <= 1'b1;
		else if (!r_busy)
			last_valid <= 1'b0;

		assign	realign_last_valid = last_valid;

		always @(*)
			corollary_shift = -realignment*8;

		always @(posedge S_AXI_ACLK)
		if (M_AXI_RVALID && M_AXI_RREADY)
			r_write_data <= (M_AXI_RDATA << corollary_shift)
					| last_data;
		else if (!fifo_full)
			r_write_data <= last_data;

		initial	r_write_to_fifo = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (reset_fifo)
			r_write_to_fifo <= 1'b0;
		else if (M_AXI_RVALID && M_AXI_RREADY)
			r_write_to_fifo <= last_valid || !unaligned_cmd_addr;
		else if (!fifo_full)
			r_write_to_fifo <= 1'b0;

		assign	write_to_fifo = r_write_to_fifo;
		assign	write_data = r_write_data;

	end else begin : ALIGNED_DATA

		assign	write_to_fifo  = M_AXI_RVALID && M_AXI_RREADY;
		assign	write_data = M_AXI_RDATA;
		assign	realign_last_valid = 0;

	end endgenerate
	// }}}

	assign	read_from_fifo = S_AXIS_TVALID && S_AXIS_TREADY;
	assign	S_AXIS_TVALID  = !fifo_empty;

	// Write the results to the FIFO
	// {{{
	generate if (OPT_TLAST)
	begin : FIFO_W_TLAST
		// FIFO section--used if we have to add a TLAST signal to the
		// data stream
		// {{{
		reg	pre_tlast;
		wire	tlast;

		// tlast will be set on the last data word of any commanded
		// burst.

		// Appropriately, pre_tlast = (something) && M_AXI_RVALID
		//			&& M_AXI_RREADY && M_AXI_RLAST
		// We can simplify this greatly, since any time M_AXI_RVALID is
		// true, we also know that M_AXI_RREADY will be true.  This
		// allows us to get rid of the RREADY condition.  Next, we can
		// simplify the RVALID condition since we'll never write to the
		// FIFO if RVALID isn't also true.  Finally, we can get rid of
		// M_AXI_RLAST since this is captured by rd_last_remaining.
		always @(*)
			pre_tlast = rd_last_remaining;

		if (OPT_REALIGN)
		begin
			reg	r_tlast;

			// REALIGN delays the data by one clock period.  We'll
			// also need to delay the last as well.
			// Note that no one cares what tlast is if write_to_fifo
			// is zero, allowing us to massively simplify this.
			always @(posedge i_clk)
				r_tlast <= pre_tlast;

			assign	tlast = r_tlast;

		end else begin

			assign	tlast = pre_tlast;
		end


		sfifo #(.BW(C_AXI_DATA_WIDTH+1), .LGFLEN(LGFIFO))
		sfifo(i_clk, reset_fifo,
			write_to_fifo, { tlast, write_data }, fifo_full, fifo_fill,
			read_from_fifo, { S_AXIS_TLAST, S_AXIS_TDATA }, fifo_empty);
		// }}}
	end else begin : NO_TLAST_FIFO

		// FIFO section, where TLAST is held at 1'b1
		// {{{
		sfifo #(.BW(C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO))
		sfifo(i_clk, reset_fifo,
			write_to_fifo, write_data, fifo_full, fifo_fill,
			read_from_fifo, S_AXIS_TDATA, fifo_empty);

		assign	S_AXIS_TLAST = 1'b1;
		// }}}
	end endgenerate
	// }}}



	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The incoming AXI (full) protocol section
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// {{{

	// Some counters to keep track of our state
	// {{{


	// Count the number of word writes left to be requested, starting
	// with the overall command length and then reduced by M_AWLEN on
	// each address write
	// {{{
	initial	ar_none_remaining = 1;
	initial	ar_requests_remaining = 0;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		ar_requests_remaining <= cmd_length_aligned_w;
		ar_none_remaining     <= zero_length;
	end else if (cmd_abort || axi_abort_pending)
	begin
		ar_requests_remaining <= 0;
		ar_none_remaining <= 1;
	end else if (phantom_start)
	begin
		// Verilator lint_off WIDTH
		ar_requests_remaining
			<= ar_requests_remaining - (M_AXI_ARLEN + 1);
		ar_none_remaining <= (ar_requests_remaining == (M_AXI_ARLEN+1));
		// Verilator lint_on WIDTH
	end
	// }}}

	// Calculate the maximum possible burst length, ignoring 4kB boundaries
	// {{{
	always @(*)
		addralign = 1+(~cmd_addr[ADDRLSB +: LGMAXBURST]);
	always @(*)
		w_increment = !wskd_data[CBIT_INCREMENT];

	always @(*)
	begin
		initial_burstlen = (1<<LGMAXBURST);
		if (cmd_length_aligned_w >= (1<<LGMAXBURST))
		begin
			// initial_burstlen = (1<<LGMAXBURST);
			if (w_increment && (|cmd_addr[ADDRLSB +: LGMAXBURST])
				&&(addralign < (1<<LGMAXBURST)))
				initial_burstlen = { 1'b0, addralign };
		end else begin
			initial_burstlen = cmd_length_aligned_w[LGMAXBURST:0];
			if (w_increment && (|cmd_addr[ADDRLSB +: LGMAXBURST])
				&&({{(LGLENW-LGMAXBURST){1'b0}}, addralign } < cmd_length_aligned_w))
				initial_burstlen = { 1'b0, addralign };
		end
	end

	initial	r_max_burst = 0;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		// Force us to align ourself early
		//   That way we don't need to check for
		//   alignment (again) later
		r_max_burst <= initial_burstlen;
	end else if (phantom_start)
	begin
		// Verilator lint_off WIDTH
		if (ar_requests_remaining < (1<<LGMAXBURST) + (M_AXI_ARLEN+1))
			r_max_burst <= ar_requests_remaining[8:0] - (M_AXI_ARLEN+1);
		else
			r_max_burst <= (1<<LGMAXBURST);
		// Verilator lint_on WIDTH
	end
	// }}}

	// Count the number of bursts outstanding--these are the number of
	// AWVALIDs that have been accepted, but for which the BVALID has not
	// (yet) been returned.
	// {{{
	initial	ar_none_outstanding   = 1;
	initial	ar_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ar_bursts_outstanding <= 0;
		ar_none_outstanding <= 1;
	end else case ({ phantom_start,
				M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST })
	2'b01:	begin
			ar_bursts_outstanding <=  ar_bursts_outstanding - 1;
			ar_none_outstanding   <= (ar_bursts_outstanding == 1);
		end
	2'b10:	begin
		ar_bursts_outstanding <= ar_bursts_outstanding + 1;
		ar_none_outstanding <= 0;
		end
	default: begin end
	endcase
	// }}}

	// Are we there yet?
	// {{{
	initial	rd_reads_remaining = 0;
	initial	rd_none_remaining = 1;
	initial	rd_last_remaining = 0;
	always @(posedge  i_clk)
	if (!r_busy)
	begin
		rd_reads_remaining <= cmd_length_aligned_w;
		rd_last_remaining  <= (cmd_length_aligned_w == 1);
		rd_none_remaining  <= (cmd_length_aligned_w == 0);
	end else if (M_AXI_RVALID && M_AXI_RREADY)
	begin
		rd_reads_remaining <= rd_reads_remaining - 1;
		rd_last_remaining  <= (rd_reads_remaining == 2);
		rd_none_remaining  <= (rd_reads_remaining == 1);
	end

	always @(*)
	if (!r_busy)
		w_complete = 0;
	else if (axi_abort_pending && ar_none_outstanding && !M_AXI_ARVALID)
		w_complete = 1;
	else if (r_continuous)
		w_complete = (rd_none_remaining)||((rd_last_remaining) && M_AXI_RVALID && M_AXI_RREADY);
	else // if !r_continuous
		w_complete = (rd_none_remaining && fifo_empty);

	// }}}

	// Are we stopping early?  Aborting something ongoing?
	// {{{
	initial	axi_abort_pending = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		axi_abort_pending <= 0;
	else begin
		if (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RRESP[1])
			axi_abort_pending <= 1;
		if (cmd_abort)
			axi_abort_pending <= 1;
	end
	// }}}

	// Count the number of uncommited spaces in the FIFO
	// {{{
	generate if (OPT_REALIGN)
	begin
		initial	partial_burst_requested <= 1'b1;
		always @(posedge i_clk)
		if (!r_busy)
			partial_burst_requested <= !unaligned_cmd_addr;
		else if (phantom_start)
			partial_burst_requested <= 1'b1;
	end else begin

		always @(*)
			partial_burst_requested = 1'b1;
	end endgenerate

	initial	rd_uncommitted = (1<<LGFIFO);
	always @(posedge i_clk)
	if (reset_fifo)
	begin
		rd_uncommitted <= (1<<LGFIFO);
	end else case ({ phantom_start,
			S_AXIS_TVALID && S_AXIS_TREADY })
	2'b00: begin end
	2'b01: begin
		rd_uncommitted <= rd_uncommitted + 1;
		end
	2'b10: begin
		// Verilator lint_off WIDTH
		rd_uncommitted <= rd_uncommitted - (M_AXI_ARLEN + 1)
			+ (partial_burst_requested ? 0 :1);
		end
	2'b11: begin
		rd_uncommitted <= rd_uncommitted - (M_AXI_ARLEN)
			+ (partial_burst_requested ? 0 :1);
		// Verilator lint_on WIDTH
		end
	endcase
	// }}}

	// So that we can monitor where we are at, and perhaps restart it
	// later, keep track of the current address used by the R-channel
	// {{{

	initial	axi_raddr = 0;
	always @(posedge i_clk)
	begin
		if (!r_busy)
			axi_raddr <= cmd_addr;
		else if (axi_abort_pending || !r_increment)
			// Stop incrementing tthe address following an abort
			axi_raddr <= axi_raddr;
		else begin
			if (M_AXI_RVALID && M_AXI_RREADY && !M_AXI_RRESP[1]
				&& (!unaligned_cmd_addr || realign_last_valid))
				axi_raddr <= axi_raddr + (1<<ADDRLSB);
		end

		if (!OPT_REALIGN)
			axi_raddr[ADDRLSB-1:0] <= 0;
	end

	// }}}

	// Count the number of words remaining to be written on the W channel
	// {{{
	// }}}

	//
	// }}}

	always @(*)
	begin
		start_burst = !ar_none_remaining;
		if (rd_uncommitted< {{(LGFIFO-LGMAXBURST){1'b0}}, r_max_burst})
			start_burst = 0;
		if (phantom_start)
			// Insist on a minimum of one clock between burst
			// starts, so we can get our lengths right
			start_burst = 0;
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			start_burst = 0;
		if (!r_busy || cmd_abort || axi_abort_pending)
			start_burst  = 0;
	end

	initial	phantom_start = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_start <= 0;
	else
		phantom_start <= start_burst;
	// }}}


	// Calculate ARLEN and ARADDR for the next ARVALID
	// {{{
	initial	axi_araddr = 0;
	always @(posedge i_clk)
	if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		if (!r_busy)
			axi_araddr <= cmd_addr;
		else if (M_AXI_ARVALID && r_increment)
		begin
			axi_araddr <= axi_araddr+((M_AXI_ARLEN + 1)<<(ADDRLSB));
			axi_araddr[ADDRLSB-1:0] <= 0;
		end
		axi_arlen  <= r_max_burst[7:0] - 8'd1;

		if (!OPT_REALIGN)
			axi_araddr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// ARVALID
	// {{{
	initial	axi_arvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_arvalid <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		axi_arvalid <= start_burst;
	// }}}

	always @(posedge i_clk)
	if (!r_busy)
		axi_arburst <= (w_increment) ? 2'b01 : 2'b00;

	// Set the constant M_AXI_* signals
	// {{{
	assign	M_AXI_ARVALID= axi_arvalid;
	assign	M_AXI_ARID   = AXI_ID;
	assign	M_AXI_ARADDR = axi_araddr;
	assign	M_AXI_ARLEN  = axi_arlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_ARSIZE = $clog2(C_AXI_DATA_WIDTH)-3;
	// Verilator lint_on  WIDTH
	assign	M_AXI_ARBURST= axi_arburst;
	assign	M_AXI_ARLOCK = 0;
	assign	M_AXI_ARCACHE= 0;
	assign	M_AXI_ARPROT = 0;
	assign	M_AXI_ARQOS  = 0;

	assign	M_AXI_RREADY = 1;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_RID,
			M_AXI_RRESP[0], fifo_full, wskd_strb[2:0], fifo_fill,
			ar_none_outstanding };
	// Verilator lint_on  UNUSED
	// }}}
`ifdef	FORMAL
	//
	// The formal properties for this unit are maintained elsewhere.
	// This core does, however, pass a full prove (w/ induction) for all
	// bus properties.
	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Properties of the AXI-stream data interface
	// {{{
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// (These are captured by the FIFO within)

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXIL_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXIL_ADDR_WIDTH),
		//
		// ...
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXIL_AWVALID),
		.i_axi_awready(S_AXIL_AWREADY),
		.i_axi_awaddr( S_AXIL_AWADDR),
		.i_axi_awcache(4'h0),
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
		.i_axi_arcache(4'h0),
		.i_axi_arprot( S_AXIL_ARPROT),
		//
		.i_axi_rvalid(S_AXIL_RVALID),
		.i_axi_rready(S_AXIL_RREADY),
		.i_axi_rdata( S_AXIL_RDATA),
		.i_axi_rresp( S_AXIL_RRESP));
		//
		// ...
		// }}}
		);

	//
	// ...
	//

	always @(posedge i_clk)
	if (f_past_valid && $past(S_AXI_ARESETN))
	begin
		if ($past(r_busy)||$past(w_cmd_start))
		begin
			assert($stable(cmd_length_b));
			assert($stable(cmd_length_w));
			assert($stable(cmd_length_aligned_w));
		end
		if ($past(r_busy))
		begin
			assert($stable(r_increment));
			assert($stable(r_continuous));
		end
		if ($past(r_busy) && $past(r_busy,2))
			assert($stable(fv_start_addr));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI master memory interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// ...
	//

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		//
		.OPT_EXCLUSIVE(1'b0),
		.OPT_NARROW_BURST(1'b0),
		//
		// ...
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(1'b0),
		.i_axi_awready(1'b0),
		.i_axi_awid(   AXI_ID),
		.i_axi_awaddr( 0),
		.i_axi_awlen(  0),
		.i_axi_awsize( 0),
		.i_axi_awburst(0),
		.i_axi_awlock( 0),
		.i_axi_awcache(0),
		.i_axi_awprot( 0),
		.i_axi_awqos(  0),
		//
		.i_axi_wvalid(0),
		.i_axi_wready(0),
		.i_axi_wdata( 0),
		.i_axi_wstrb( 0),
		.i_axi_wlast( 0),
		//
		.i_axi_bvalid(1'b0),
		.i_axi_bready(1'b0),
		.i_axi_bid(   AXI_ID),
		.i_axi_bresp( 2'b00),
		//
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_arid(   M_AXI_ARID),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arlen(  M_AXI_ARLEN),
		.i_axi_arsize( M_AXI_ARSIZE),
		.i_axi_arburst(M_AXI_ARBURST),
		.i_axi_arlock( M_AXI_ARLOCK),
		.i_axi_arcache(M_AXI_ARCACHE),
		.i_axi_arprot( M_AXI_ARPROT),
		.i_axi_arqos(  M_AXI_ARQOS),
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rlast( M_AXI_RLAST),
		.i_axi_rresp( M_AXI_RRESP));
		//
		// ...
		//
		// }}}
	);


	//
	// ...
	//

	always @(*)
	if (r_busy)
		assert(axi_arburst == (r_increment ? 2'b01 : 2'b00));

	//
	// ...
	//

	always @(*)
	if (r_busy)
	begin
		//
		// ...
		//
	end else begin
		//
		// ...
		//

		assert(rd_uncommitted
			+ ((OPT_REALIGN && write_to_fifo) ? 1:0)
			+ fifo_fill == (1<<LGFIFO));
		if (!r_continuous)
			assert(fifo_fill == 0 || reset_fifo);
	end

	//
	// ...
	//

	always @(*)
	if (r_busy)
	begin
		if (!OPT_REALIGN)
			assert(M_AXI_ARADDR[ADDRLSB-1:0] == 0);
		else
			assert((M_AXI_ARADDR[ADDRLSB-1:0] == 0)
				||(M_AXI_ARADDR == fv_start_addr));
	end

	always @(*)
	if (!OPT_REALIGN || (r_busy && !r_increment))
	begin
		assert(cmd_addr[ADDRLSB-1:0] == 0);
		assert(fv_start_addr[ADDRLSB-1:0] == 0);
		assert(axi_araddr[ADDRLSB-1:0] == 0);
		assert(axi_raddr[ADDRLSB-1:0] == 0);
	end

	//
	// f_last_addr is the (aligned) address one following the last valid
	// address read.  Once all reading is done, all (aligned) address
	// pointers should point there.
	always @(*)
	begin
		f_last_addr = { fv_start_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB],
				{(ADDRLSB){1'b0}} };

		if (r_increment)
			f_last_addr = f_last_addr + cmd_length_b;
		if (unaligned_cmd_addr)	// Only true if r_increment as well
			f_last_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				= f_last_addr[C_AXI_ADDR_WIDTH-1:ADDRLSB]+1;

		f_last_addr[ADDRLSB-1:0] = 0;

		f_next_start = fv_start_addr;
		if (r_increment)
			f_next_start = f_next_start + cmd_length_b;
		if (!OPT_REALIGN)
			assert(f_next_start == f_last_addr);
	end


	//
	// ...
	//


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Other formal properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// Define some helper metrics
	//
	initial	fv_start_addr = 0;
	always @(posedge i_clk)
	if (!r_busy)
		fv_start_addr <= cmd_addr;

	always @(*)
	begin
		// Metrics defining M_AXI_ARADDR
		f_araddr_is_aligned = (M_AXI_ARADDR[ADDRLSB+LGMAXBURST-1:0]==0);
		f_araddr_is_initial = (M_AXI_ARADDR == fv_start_addr);
		f_araddr_is_final   = (M_AXI_ARADDR == f_last_addr);

		//
		// Metrics to check ARADDR, assuming it had been accepted
		//

		//
		// ...
		//
	end

	//
	// fv_ar_requests_remaining ... shadows ar_requests_remaining
	//
	// Since ar_requests_remaining drops to zero suddenly on any
	// axi_abort_pending, we need another counter that we can use
	// which doesn't have this feature, but which can also be used
	// to check assertions and intermediate logic against until the
	// abort takes effect.
	initial	fv_ar_requests_remaining = 0;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		fv_ar_requests_remaining <= cmd_length_aligned_w;
	end else if (phantom_start)
	begin
		// Verilator lint_off WIDTH
		fv_ar_requests_remaining
			<= fv_ar_requests_remaining - (M_AXI_ARLEN + 1);
		// Verilator lint_on WIDTH
	end

	always @(*)
	if (r_busy)
	begin
		if (!axi_abort_pending)
			assert(fv_ar_requests_remaining == ar_requests_remaining);
		else
			assert((ar_requests_remaining == 0)
				||(fv_ar_requests_remaining
					== ar_requests_remaining));
	end

	always @(*)
	if(r_busy)
	begin
		assert(fv_ar_requests_remaining <= cmd_length_aligned_w);
		//
		// ...
		//
	end

	//
	// fv_axi_raddr ... shadows axi_raddr
	//
	// The low order bits will match the low order bits of the initial
	// cmd_addr
	//
	initial	fv_axi_raddr = 0;
	always @(posedge i_clk)
	if (!r_busy)
		fv_axi_raddr <= cmd_addr;
	else if (!r_increment)
		fv_axi_raddr <= fv_start_addr;
	else begin
		if (M_AXI_RVALID && M_AXI_RREADY
				&& (!unaligned_cmd_addr || realign_last_valid))
			fv_axi_raddr <= fv_axi_raddr + (1<<ADDRLSB);
		if (!OPT_REALIGN)
			fv_axi_raddr[ADDRLSB-1:0] <= 0;
	end

	// Constrain start <= axi_raddr <= fv_axi_raddr <= f_last_addr
	//	in spite of any address wrapping
	always @(*)
	if (r_busy)
	begin
		assert(axi_raddr[ADDRLSB-1:0] == cmd_addr[ADDRLSB-1:0]);
		assert(axi_abort_pending || fv_axi_raddr == axi_raddr);
		if (!r_increment)
		begin
			assert(fv_axi_raddr == fv_start_addr);
			assert(axi_raddr == fv_start_addr);
		end if (!axi_abort_pending)
		begin
			if (fv_start_addr <= f_last_addr)
			begin
				// Natural order: start < f_raddr < last
				assert(fv_axi_raddr <= f_last_addr);
				assert(fv_axi_raddr >= fv_start_addr);
			end else begin
				// Reverse order
				//	Either: last < start <= f_raddr
				//	    or: f_raddr < last < start
				assert((fv_axi_raddr >= fv_start_addr)
					||(fv_axi_raddr <= f_last_addr));
			end

			if (fv_start_addr <= fv_axi_raddr)
			begin
				// Natural order: start < rad < f_rad < last
				//   or even: last < start < rad < f_rad
				assert(axi_raddr <= fv_axi_raddr);
				assert(fv_start_addr <= axi_raddr);
			end else if (fv_axi_raddr <= f_last_addr)
			begin
				// Reverse order: f_raddr < last < start
				//   so either: last < start < raddr
				//          or: raddr < f_raddr < last < start
				//
				assert((axi_raddr >= fv_start_addr)
					|| (axi_raddr <= fv_axi_raddr));
			end
		end
	end

	always @(*)
	if (!r_busy)
	begin
		assert(!M_AXI_ARVALID);
		assert(!M_AXI_RVALID);
		//
		// ...
		//
	end

	always @(*)
		assert(zero_length == (cmd_length_w == 0));

	always @(*)
	if (phantom_start)
		assert(rd_uncommitted >= (M_AXI_ARLEN + 1));

	always @(*)
	if (zero_length)
		assert(!r_busy);
	always @(*)
	if (r_busy)
		assert(ar_none_remaining   == (ar_requests_remaining == 0));
	always @(*)
		assert(ar_none_outstanding == (ar_bursts_outstanding == 0));
	always @(*)
		assert(rd_none_remaining   == (rd_reads_remaining == 0));
	always @(*)
		assert(rd_last_remaining   == (rd_reads_remaining == 1));

	always @(*)
	if (r_complete)
		assert(!r_busy);

	//
	// ...
	//

	//
	// fifo_availability is a measure of (1<<LGFIFO) minus the current
	// fifo fill.  This does not include what's in the pre-FIFO
	// logic when OPT_REALIGN is true.
	always @(*)
		f_fifo_availability = rd_uncommitted;

	always @(*)
		assert(f_fifo_committed <= (1<<LGFIFO));

	always @(*)
		assert(f_fifo_availability <= (1<<LGFIFO));

	//
	// ...
	//

	always @(*)
	if (!reset_fifo)
		assert(f_fifo_committed + f_fifo_availability + fifo_fill
			== (1<<LGFIFO));

	//
	// ...
	//

	always @(*)
	if (r_busy)
		assert(r_max_burst <= (1<<LGMAXBURST));

	always @(*)
	if (r_busy)
		assert((r_max_burst > 0) || (ar_requests_remaining == 0));


	always @(*)
	if (phantom_start)
		assert(M_AXI_ARVALID);

	always @(posedge i_clk)
	if (phantom_start)
	begin
		assert(r_max_burst > 0);
		assert(M_AXI_ARLEN == $past(r_max_burst)-1);
	end

	always @(*)
	if (r_busy)
		assert(initial_burstlen > 0);


	//
	// Address checking
	//

	// Check cmd_addr
	always @(*)
	if (r_busy)
	begin
		if (r_increment && r_continuous)
			assert(cmd_addr == axi_raddr);
		else
			assert(cmd_addr == fv_start_addr);
	end

	// Check M_AXI_ARADDR
	//
	// ...
	//

	//
	// Check M_AXI_ARLEN
	//
	// ...
	//

	//
	// Constrain the r_maxburst
	//
	// ...
	//

	always @(*)
	if (r_busy)
	begin
		assert(r_max_burst <= (1<<LGMAXBURST));
		//
		// ...
		//
	end

	//
	// Constrain the length
	//
	// ...
	//

	always @(posedge i_clk)
	if (phantom_start)
	begin
		assert(axi_arlen == $past(r_max_burst[7:0]) - 8'd1);
		if (!r_increment)
			assert(M_AXI_ARADDR == fv_start_addr);
	end

	// Constrain rd_reads_remaining
	//
	// ...
	//
	always @(*)
	if (r_busy)
	begin
		assert(rd_reads_remaining <= cmd_length_w);
		//
		// ...
		//
		assert(ar_bursts_outstanding <= rd_reads_remaining);
		//
		// ...
		//
	end

	//
	// Constrain the number of requests remaining
	//
	// ...
	//

	//
	// Make sure our aw_bursts_outstanding counter never overflows
	// (Given that the counter is as long as the length register, it cannot)
	//
	always @(*)
	begin
		if (&ar_bursts_outstanding[LGLENWA-1:1])
			assert(!M_AXI_ARVALID);
		//
		// ...
		//
	end

	// }}}

	//
	// Match axi_raddr to the faxi_ values
	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// 1. All data values must get read and placed into the FIFO, with
	//	none skipped
	//	Captured in logic above(?)
	//
	// 2. No addresses skipped.  Check the write address against the 
	//	write address we are expecting
	//
	// ...
	//

	// 3. If we aren't incrementing addresses, then our current address
	//	should always be the axi address
	//
	// ...

	//
	// 4. Whenever we go from busy to idle, we should raise o_int for one
	// (and only one) cycle
	always @(posedge i_clk)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!o_int);
	else
		assert(o_int == $fell(r_busy));

	//
	// ...
	//


	// 5. Pick an incoming data value.  Choose whether or not to restrict
	// incoming data not to be that value.  If the incoming data is so restricted
	// then assert that the stream output will contain that value.
	(* anyconst *)	reg	f_restrict_data;
	(* anyconst *)	reg	[C_AXI_DATA_WIDTH-1:0]	f_restricted;

	always @(*)
	if (f_restrict_data && M_AXI_RVALID
			&& (!OPT_REALIGN || !unaligned_cmd_addr))
		assume(M_AXI_RDATA != f_restricted);

	always @(*)
	if (f_restrict_data && S_AXIS_TVALID
			&& (!OPT_REALIGN || !unaligned_cmd_addr))
		assert(S_AXIS_TDATA != f_restricted);

	//
	// ...
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg		cvr_aborted, cvr_buserr;
	reg	[2:0]	cvr_continued;

	initial	{ cvr_aborted, cvr_buserr } = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		{ cvr_aborted, cvr_buserr } <= 0;
	else if (r_busy && !axi_abort_pending)
	begin
		if (cmd_abort && ar_requests_remaining > 0)
			cvr_aborted <= 1;
		if (M_AXI_RVALID && M_AXI_RRESP[1] && M_AXI_RLAST)
			cvr_buserr <= 1;
	end

	initial	cvr_continued = 0;
	always @(posedge i_clk)
	if (i_reset || r_err || cmd_abort)
		cvr_continued <= 0;
	else begin
		// Cover a continued transaction across two separate bursts
		if (r_busy && r_continuous)
			cvr_continued[0] <= 1;
		if (!r_busy && cvr_continued[0])
			cvr_continued[1] <= 1;
		if (r_busy && cvr_continued[1])
			cvr_continued[2] <= 1;
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !i_reset && $fell(r_busy))
	begin
		cover( r_err && cvr_aborted);
		cover( r_err && cvr_buserr);
		cover(!r_err);
		if (!r_err && !axi_abort_pending && !cvr_aborted && !cvr_buserr)
		begin
			cover(cmd_length_w > 5);
			cover(cmd_length_w > 8);
			//
			// ...
			//
			cover(&cvr_continued);
			cover(&cvr_continued && (cmd_length_w > 2));
			cover(&cvr_continued && (cmd_length_w > 5));
		end
	end

	always @(*)
	if (!i_reset)
		cover(!r_err && fifo_fill > 8 && !r_busy);

	always @(*)
		cover(r_busy);

	always @(*)
		cover(start_burst);

	always @(*)
		cover(M_AXI_ARVALID && M_AXI_ARREADY);

	always @(*)
		cover(M_AXI_RVALID);

	always @(*)
		cover(M_AXI_RVALID & M_AXI_RLAST);
	always @(*)
	if (r_busy)
	begin
		cover(!ar_none_remaining);
		if(!ar_none_remaining)
		begin
			cover(1);
			cover(rd_uncommitted>= {{(LGFIFO-LGMAXBURST){1'b0}}, r_max_burst});
			if(rd_uncommitted>= {{(LGFIFO-LGMAXBURST){1'b0}}, r_max_burst})
			begin
				cover(!phantom_start);
				cover(phantom_start);
			end
		end
	end

	//
	// Unaligned cover properties
	generate if (OPT_TLAST)
	begin
		reg	[3:0]	cvr_lastcount;
		always @(posedge i_clk)
		if (i_reset || (r_busy && cmd_length_w <= 2))
			cvr_lastcount <= 0;
		else if (S_AXIS_TVALID && S_AXIS_TREADY && S_AXIS_TLAST
				&& !cvr_lastcount[3])
			cvr_lastcount <= cvr_lastcount + 1;

		always @(*)
			cover(S_AXIS_TVALID && S_AXIS_TREADY && S_AXIS_TLAST);

		always @(posedge i_clk)
			cover(o_int && cvr_lastcount > 2);

	end endgenerate

	generate if (OPT_REALIGN)
	begin
		//
		// ...
		//
		always @(posedge i_clk)
		if (f_past_valid && !$past(i_reset) && !i_reset &&$fell(r_busy))
		begin
			cover(r_err);
			cover(!r_err);
			cover(axi_abort_pending);
			cover(!axi_abort_pending);
			cover(cvr_aborted);
			cover(!cvr_aborted);
			cover(cvr_buserr);
			cover(!cvr_buserr);
			cover(!cvr_buserr && !axi_abort_pending);
			cover(!cvr_buserr && !axi_abort_pending
				&& (cmd_length_w > 2));
			cover(!r_err && !cvr_aborted && !cvr_buserr
				&& !axi_abort_pending
				&& (cmd_length_w > 2));
		end
	end endgenerate


	// }}}
	// }}}
`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
