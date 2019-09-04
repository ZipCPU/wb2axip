////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axis2mm
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Converts an AXI-stream (input) to an AXI (full) memory
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
//	[31]	r_busy
//		True if the core is in the middle of a transaction
//
//	[30]	r_err
//		True if the core has detected an error, such as FIFO
//		overflow while writing, or FIFO overflow in continuous mode.
//
//		Writing a '1' to this bit while the core is idle will clear it.
//		New transfers will not start until this bit is cleared.
//
//	[29]	r_complete
//		True if the transaction has completed normally.
//
//		Any write to the CMD_CONTROL register will clear this flag.
//
//	[28]	r_continuous
//		Normally the FIFO gets cleared and reset between operations.
//		However, if you set r_continuous, the core will then expectt
//		a second operation to take place following the first one.
//		In this case, the FIFO doesn't get cleared.  However, if the
//		FIFO fills and the incoming data is both valid and changing,
//		the r_err flag will be set.
//
//		Any write to the CMD_CONTROL register while the core is not
//		busy will adjust this bit.
//
//	[27]	!r_increment
//
//		If clear, the core writes to subsequent and incrementing
//		addresses.  If set, the core writes to the same address
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
//		the current transfer will be aborted.  Any pending writes
//		will be completed, but nothing more will be written.
//
//		Alternatively, the core will enter into an abort state
//		following any returned bus error indications.
//
//  4:	CMD_ADDR
//	[C_AXI_ADDR_WIDTH-1:($clog2(C_AXI_DATA_WIDTH)-3)]
//		If idle, the address the core will write to when it starts.
//		If busy, the address the core is currently writing to.
//		Upon completion, the address either returns to the starting
//		address (if r_continuous is clear), or otherwise becomes the
//		address where the core left off.  In the case of an abort or an
//		error, this will be (near) the address that was last written.
//
//		Why "near"?  Because this address records the writes that have
//		been issued while no error is pending.  If a bus error return
//		comes back, there may have been several writes issued before
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
//		the number of items still to be written to the bus.
//
//		I hope to eventually add support for unaligned bursts.  Such
//		support is not currently part of this core.
//
// 12:	CMD_THRESHOLD
//	[ADDRLSB +: LGFIFO]
//		This is the fill level the FIFO must have before the core will
//		attempt a burst.  Ideally, you'd want to set this high in order
//		to avoid sending a large number of small bursts across the bus.
//		That said, if you set it too high there is a possibility that
//		the bus won't accept the data requests before the incoming FIFO
//		overflows.
//
//		As with CMD_LENGTH, this is also given in bytes, although the
//		core only accepts aligned values.  Hence the bottom
//		[$clog2(C_AXI_DATA_WIDTH)-3:0] bits will always be set to zero.
// }}}
//
// Status:
// {{{
//	1. While the core passes a formal property check, that formal check
//		doesn't (yet) include any cover checks.  These need to be
//		added in order to be complete.
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
module	axis2mm #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		localparam	C_AXIL_ADDR_WIDTH = 2,
		localparam	C_AXIL_DATA_WIDTH = 32,
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3,
		parameter [7:0]	ABORT_KEY = 8'h6d,
		//
		// The size of the FIFO
		parameter	LGFIFO = 12,
		//
		// Maximum number of bytes that can ever be transferred, in
		// log-base 2
		parameter	LGLEN  = 20,
		parameter	AXI_ID = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		// The stream interface
		// {{{
		input	wire					S_AXIS_TVALID,
		output	wire					S_AXIS_TREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXIS_TDATA,
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
		// The AXI (full) write interface
		// {{{
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[7:0]			M_AXI_AWLEN,
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
		output	wire				M_AXI_AWLOCK,
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire	[C_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		// }}}
		//
		//
		// Create an output signal to indicate that we've finished
		output	reg				o_int
		// }}}
	);
	localparam [1:0]	CMD_CONTROL   = 2'b00,
				CMD_ADDR      = 2'b01,
				CMD_LEN       = 2'b10,
				CMD_THRESHOLD = 2'b11;
	localparam	LGMAXBURST=8;
	localparam	LGLENW  = LGLEN  - ($clog2(C_AXI_DATA_WIDTH)-3);
	localparam	LGFIFOB = LGFIFO + ($clog2(C_AXI_DATA_WIDTH)-3);
	localparam [ADDRLSB-1:0] LSBZEROS = 0;

	wire	i_clk   =  S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	// Signal declarations
	// {{{
	reg	r_busy, r_err, r_complete, r_continuous, r_increment,
		cmd_abort, zero_length, zero_threshold,
		w_cmd_start, w_complete, w_cmd_abort;
	// reg	cmd_start;
	reg			axi_abort_pending;
	reg	[LGLEN-1:0]	aw_requests_remaining,
				aw_bursts_outstanding;
	reg	[LGMAXBURST:0]	wr_writes_pending;
	reg	[8:0]		w_next_len;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_addr;
	reg	[C_AXI_ADDR_WIDTH-1:0]	next_awaddr;

	reg	[C_AXI_ADDR_WIDTH-1:0]	cmd_addr;
	reg	[LGLEN-1:0]		cmd_length_b;
	reg	[LGLENW-1:0]		cmd_length_w;
	reg	[LGFIFO-1:0]		cmd_threshold_w;
	reg	[LGFIFOB-1:0]		cmd_threshold_b;

	// FIFO signals
	wire				reset_fifo, write_to_fifo,
					read_from_fifo;
	wire	[C_AXI_DATA_WIDTH-1:0]	fifo_data;
	wire	[LGFIFO:0]		fifo_fill;
	wire				fifo_full, fifo_empty,
					fifo_threshold_trigger;

	wire				awskd_valid, axil_write_ready;
	reg				axil_write_valid;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	awskd_addr;
	//
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;
	//
	wire				bskd_ready, ignore_bzero;
	wire	arskd_valid, axil_read_ready, rskd_ready;
	wire	[C_AXIL_ADDR_WIDTH-1:0]	arskd_addr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;
	reg				last_stalled, overflow;
	reg	[C_AXI_DATA_WIDTH-1:0]	last_tdata;
	reg	[C_AXIL_DATA_WIDTH-1:0]	w_status_word,
					w_addr_word,
					w_len_word,
					w_threshold_word;

	reg	[LGLEN-1:0]		r_remaining_b;
	reg	[LGLENW-1:0]		r_remaining_w;

	reg				axi_awvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	reg	[7:0]			axi_awlen;
	reg				axi_wvalid;
	reg	[C_AXI_DATA_WIDTH-1:0]	axi_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	axi_wstrb;
	reg	[1:0]			awburst;

	// Speed up checking for zeros
	reg	aw_none_remaining, aw_none_outstanding, wr_none_pending,
		r_none_remaining;
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

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8),
		.OPT_PASSTHROUGH(SKID_PASSTHROUGH))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!axil_write_valid || bskd_ready);

	initial	axil_write_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axil_write_valid <= 0;
	else if (axil_write_ready)
		axil_write_valid <= 1;
	else if (bskd_ready)
		axil_write_valid <= 0;

	skidbuffer #(.OPT_OUTREG(1), .DW(1))
	axilbskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(axil_write_valid), .o_ready(bskd_ready),
		.i_data(1'b0),
		.o_valid(S_AXIL_BVALID), .i_ready(S_AXIL_BREADY),
		.o_data(ignore_bzero));

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
				&& (!axil_read_valid || rskd_ready);

	initial	axil_read_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (rskd_ready)
		axil_read_valid <= 1'b0;

	skidbuffer #(.OPT_OUTREG(1), .DW(C_AXIL_DATA_WIDTH))
	axilrskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(axil_read_valid), .o_ready(rskd_ready),
		.i_data(axil_read_data),
		.o_valid(S_AXIL_RVALID), .i_ready(S_AXIL_RREADY),
		.o_data(S_AXIL_RDATA));

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

	initial	last_stalled = 1'b0;
	always @(posedge i_clk)
		last_stalled <= (!i_reset) && (S_AXIS_TVALID && !S_AXIS_TREADY);
	always @(posedge i_clk)
		last_tdata <= S_AXIS_TDATA;


	initial	overflow = 0;
	always @(posedge i_clk)
	if (i_reset)
		overflow <= 0;
	else
		overflow <= (S_AXIS_TVALID && !S_AXIS_TREADY
				&& last_stalled && S_AXIS_TDATA != last_tdata);

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
	else if (r_busy && w_cmd_abort)
		cmd_abort <= 1;

	//
	// Start command
	//
	always @(*)
	if (r_busy)
		w_cmd_start = 0;
	else begin
		w_cmd_start = 0;
		if ((axil_write_ready && awskd_addr == CMD_CONTROL)
			&& (wskd_strb[3] && wskd_data[31]))
			w_cmd_start = 1;
		if (r_err && !wskd_data[30])
			w_cmd_start = 0;
		if (zero_length)
			w_cmd_start = 0;
		if (zero_threshold)
			w_cmd_start = 0;
	end

	// initial	cmd_start = 0;
	// always @(posedge i_clk)
	//	cmd_start <= (!i_reset)&&(w_cmd_start);

	//
	// Recognize the last ack
	//
	// assign	w_complete = something
					
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
		if (!w_cmd_abort
			&& (!axil_write_ready || awskd_addr != CMD_CONTROL))
			r_complete <= 1'b0;
	end else if (r_busy)
	begin
		if (w_complete)
		begin
			r_complete <= (r_none_remaining);
			r_busy <= 1'b0;
		end
	end	

	//
	// Interrupts
	//
	initial	o_int = 0;
	always @(posedge i_clk)
	if (i_reset || cmd_abort)
		o_int <= 0;
	else
		o_int <= (r_busy && w_complete)
			|| (r_continuous && overflow);

	//
	// Error conditions
	//
	always @(posedge i_clk)
	if (i_reset)
		r_err <= 0;
	else if (!r_busy)
	begin
		if (r_continuous && overflow)
			r_err <= 1;
		if (axil_write_ready && awskd_addr == CMD_CONTROL
			&& !w_cmd_abort)
			r_err <= wskd_strb[3] && wskd_data[30];
	end else if (r_busy)
	begin
		if (M_AXI_BVALID && M_AXI_BREADY && M_AXI_BRESP[1])
			r_err <= 1'b1;
		else if (overflow)
			r_err <= 1'b1;
	end

	initial	r_continuous = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_continuous <= 0;
	else begin
		if (r_continuous && overflow)
			r_continuous <= 1'b0;
		if (!r_busy && axil_write_ready && awskd_addr == CMD_CONTROL
			&& !w_cmd_abort)
			r_continuous <= wskd_strb[3] && wskd_data[28];
	end

	initial	r_increment   = 1'b1;
	initial	cmd_addr      = 0;
	initial	cmd_length_w  = 0;	// Counts in bytes
	initial	zero_length   = 1;
	initial	cmd_threshold_w = 0;
	initial	zero_threshold= 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_increment <= 1'b1;
		cmd_addr      <= 0;
		cmd_length_w  <= 0;
		zero_length   <= 1;
		cmd_threshold_w <= 0;
		zero_threshold<= 1;
	end else if (axil_write_ready && !r_busy)
	begin
		case(awskd_addr)
		CMD_CONTROL:
			r_increment <= !wskd_data[27];
		CMD_ADDR: begin
			cmd_addr <= wskd_data;
			cmd_addr[ADDRLSB-1:0] <= 0;
			end
		CMD_LEN: begin
			cmd_length_w <= wskd_data[ADDRLSB +: LGLENW];
			zero_length <= (wskd_data[ADDRLSB +: LGLENW] == 0);
			end
		CMD_THRESHOLD: begin
			cmd_threshold_w <= wskd_data[ADDRLSB +: LGFIFO];
			zero_threshold <= (wskd_data[ADDRLSB +: LGFIFO]==0);
			end
		default: begin end
		endcase
	end else if (r_busy && r_continuous)
		cmd_addr <= axi_addr;

	always @(*)
	begin
		cmd_length_b    = { cmd_length_w,    {(ADDRLSB){1'b0}} };
		cmd_threshold_b = { cmd_threshold_w, {(ADDRLSB){1'b0}} };
	end

	always @(*)
	begin
		w_status_word = 0;
		w_status_word[31] = r_busy;
		w_status_word[30] = r_err;
		w_status_word[29] = r_complete;
		w_status_word[28] = r_continuous;
		w_status_word[27] = !r_increment;
		w_status_word[20:16] = LGFIFO;

		w_addr_word = 0;
		if (r_busy)
			w_addr_word = axi_addr;
		else
			w_addr_word = cmd_addr;

		w_len_word = 0;
		if (r_busy)
			w_len_word[LGLEN-1:0] = r_remaining_b;
		else
			w_len_word[LGLEN-1:0] = cmd_length_b;

		w_threshold_word = 0;
		w_threshold_word[LGFIFOB-1:0] = cmd_threshold_b;
	end

	always @(posedge i_clk)
	if (!axil_read_valid || rskd_ready)
	begin
		case(arskd_addr)
		CMD_CONTROL:   axil_read_data = w_status_word;
		CMD_ADDR:      axil_read_data = w_addr_word;
		CMD_LEN:       axil_read_data = w_len_word;
		CMD_THRESHOLD: axil_read_data = w_threshold_word;
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
	assign	write_to_fifo  = S_AXIS_TVALID && S_AXIS_TREADY;
	assign	read_from_fifo = M_AXI_WVALID  && M_AXI_WREADY;
	assign	S_AXIS_TREADY  = !fifo_full;

	sfifothresh #(.BW(C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO))
	sfifothreshi(i_clk, reset_fifo,
		write_to_fifo, S_AXIS_TDATA, fifo_full, fifo_fill,
		read_from_fifo, fifo_data, fifo_empty,
		{ 1'b0, cmd_threshold_w }, fifo_threshold_trigger);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The outgoing AXI (full) protocol section
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
	initial	aw_none_remaining = 1;
	initial	aw_requests_remaining = 0;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		aw_requests_remaining <= cmd_length_w;
		aw_none_remaining <= zero_length;
	end else if (axi_abort_pending)
	begin
		aw_requests_remaining <= 0;
		aw_none_remaining <= 1;
	end else if (M_AXI_AWVALID && M_AXI_AWREADY)
	begin
		// Verilator lint_off WIDTH
		aw_requests_remaining
			<= aw_requests_remaining - (M_AXI_AWLEN + 1);
		// Verilator lint_on WIDTH
		aw_none_remaining <= (aw_requests_remaining == (M_AXI_AWLEN+1));
	end
	// }}}

	// Count the number of bursts outstanding--these are the number of
	// AWVALIDs that have been accepted, but for which the BVALID has not
	// (yet) been returned.
	// {{{
	initial	aw_none_outstanding   = 1;
	initial	aw_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		aw_bursts_outstanding <= 0;
		aw_none_outstanding <= 1;
	end else case ({M_AXI_AWVALID && M_AXI_AWREADY,
				M_AXI_BVALID && M_AXI_BREADY })
	2'b01:	begin
			aw_bursts_outstanding <= aw_bursts_outstanding - 1;
			aw_none_outstanding <= (aw_bursts_outstanding == 1);
		end
	2'b10:	begin
		aw_bursts_outstanding <= aw_bursts_outstanding + 1;
		aw_none_outstanding <= 0;
		end
	default: begin end
	endcase
	// }}}

	always @(*)
	if (!r_busy)
		w_complete = 0;
	else
		w_complete = !M_AXI_AWVALID && (aw_none_remaining)&&(aw_none_outstanding);

	initial	axi_abort_pending = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		axi_abort_pending <= 0;
	else begin
		if (M_AXI_BVALID && M_AXI_BREADY && M_AXI_BRESP[1])
			axi_abort_pending <= 1;
		if (cmd_abort)
			axi_abort_pending <= 1;
	end

	// Count the number of WVALIDs yet to be sent on the write channel
	// {{{
	initial	wr_none_pending = 1;
	initial	wr_writes_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		wr_writes_pending <= 0;
		wr_none_pending = 1;
	end else case ({M_AXI_AWVALID && M_AXI_AWREADY,
			M_AXI_WVALID && M_AXI_WREADY })
	2'b00: begin end
	2'b01: begin
		wr_writes_pending <= wr_writes_pending - 1;
		wr_none_pending <= (wr_writes_pending == 1);
		end
	2'b10: begin
		wr_writes_pending <= wr_writes_pending + (M_AXI_AWLEN + 1);
		wr_none_pending <= 0;
		end
	2'b11: begin
		wr_writes_pending <= wr_writes_pending + (M_AXI_AWLEN);
		wr_none_pending <= 0;
		end
	endcase
	// }}}

	// So that we can monitor where we are at, and perhaps restart it
	// later, keep track of the current address used by the W-channel
	// {{{
	initial	axi_addr = 0;
	always @(posedge i_clk)
	if (!r_busy)
		axi_addr <= cmd_addr;
	else if (axi_abort_pending)
		// Stop incrementing tthe address following an abort
		axi_addr <= axi_addr;
	else begin
		case({M_AXI_AWVALID && M_AXI_AWREADY,
			M_AXI_WVALID && M_AXI_WREADY })
		2'b00: begin end
		2'b01: axi_addr <= axi_addr + (r_increment ? (1<<ADDRLSB):0);
		2'b10: axi_addr <= M_AXI_AWADDR;
		2'b11: axi_addr <= M_AXI_AWADDR + (r_increment ? (1<<ADDRLSB):0);
		endcase
		axi_addr[ADDRLSB-1:0] = 0;
	end
	// }}}

	// Count the number of words remaining to be written on the W channel
	// {{{
	initial	r_none_remaining = 1;
	initial	r_remaining_w = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_remaining_w <= 0;
		r_none_remaining <= 1;
	end else if (!r_busy)
	begin
		r_remaining_w<= cmd_length_w;
		r_none_remaining <= zero_length;
	end else if (M_AXI_WVALID && M_AXI_WREADY)
	begin
		r_remaining_w <= r_remaining_w - 1;
		r_none_remaining <= (r_remaining_w == 1);
	end

	always @(*)
		r_remaining_b = { r_remaining_w, {(ADDRLSB){1'b0}} };
	// }}}

	//
	// }}}

	//
	// Determine WLAST
	//
	reg	axi_wlast;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		axi_wlast <= (cmd_length_w == 1);
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (M_AXI_AWVALID && M_AXI_AWREADY)
			axi_wlast <= (M_AXI_AWLEN == 0);
		else
			axi_wlast <= (wr_writes_pending == 1 + (M_AXI_WVALID ? 1:0));
	end

	// Calculate AWLEN and AWADDR for the next AWVALID
	// {{{
	//
	// Determine next_awlen, for AWLEN in a bit
	//
	always @(*)
	begin
		if (fifo_fill < (1<<LGMAXBURST))
			w_next_len <= fifo_fill;
		else
			w_next_len = (1<<(LGMAXBURST));

		// Verilator lint_off WIDTH
		if (w_next_len > aw_requests_remaining)
			w_next_len = aw_requests_remaining;
		if ({ w_next_len,{(ADDRLSB){1'b0}} }
			+ { next_awaddr[11:ADDRLSB], LSBZEROS } > 13'h1_000)
			w_next_len = (13'h1_000
				- { next_awaddr[11:ADDRLSB], LSBZEROS })
				>> ADDRLSB;
		w_next_len = w_next_len - 1;
		// Verilator lint_on  WIDTH
	end

	always @(posedge i_clk)
	if (!r_busy)
		next_awaddr <= cmd_addr;
	else if (M_AXI_AWVALID && M_AXI_AWREADY)
	begin
		// Verilator lint_off WIDTH
		next_awaddr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
		<= M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]+M_AXI_AWLEN+1'b1;
		// Verilator lint_on WIDTH
		next_awaddr[ADDRLSB-1:0] <= 0;
	end

	always @(posedge i_clk)
	if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		axi_awlen  <= w_next_len[7:0];
		axi_awaddr <= next_awaddr;
	end
	// }}}

	// AWVALID
	// {{{
	initial	axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_awvalid <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		axi_awvalid <= 0;
		if (fifo_threshold_trigger && !aw_none_remaining)
			axi_awvalid <= !M_AXI_WVALID
					|| (M_AXI_WLAST && M_AXI_WREADY);
		if (!r_busy || cmd_abort || axi_abort_pending)
			axi_awvalid <= 0;
		if ((!wr_none_pending)
			// ||(M_AXI_WVALID && !M_AXI_WLAST)
					||(M_AXI_AWVALID))
			axi_awvalid <= 0;
		if (r_none_remaining || fifo_empty)
			axi_awvalid <= 0;
	end
	// }}}

	// WVALID
	// {{{
	initial	axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_wvalid <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		axi_wvalid <= ((M_AXI_AWVALID && M_AXI_AWREADY)
			||(!wr_none_pending));

		if (fifo_empty || (wr_writes_pending <= (axi_wvalid ? 1:0)))
			axi_wvalid <= 0;
	end
	// }}}

	always @(posedge i_clk)
	if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wdata <= fifo_data;


	always @(posedge i_clk)
	if (!r_busy)
		axi_wstrb <= -1;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wstrb <= (axi_abort_pending) ? 0:-1;

	always @(posedge i_clk)
	if (r_increment)
		awburst <= 2'b01;
	else
		awburst <= 2'b00;

	// }}}

	// {{{
	assign	M_AXI_AWVALID= axi_awvalid;
	assign	M_AXI_AWID   = AXI_ID;
	assign	M_AXI_AWADDR = axi_awaddr;
	assign	M_AXI_AWLEN  = axi_awlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_AWSIZE = $clog2(C_AXI_DATA_WIDTH)-3;
	// Verilator lint_on  WIDTH
	assign	M_AXI_AWBURST= awburst;
	assign	M_AXI_AWLOCK = 0;
	assign	M_AXI_AWCACHE= 0;
	assign	M_AXI_AWPROT = 0;
	assign	M_AXI_AWQOS  = 0;

	assign	M_AXI_WVALID = axi_wvalid;
	assign	M_AXI_WDATA  = axi_wdata;
	assign	M_AXI_WSTRB  = axi_wstrb;
	assign	M_AXI_WLAST  = axi_wlast;
	// M_AXI_WLAST = ??

	assign	M_AXI_BREADY = 1;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_BID,
			M_AXI_BRESP[0], fifo_fill, wskd_strb[2:0],
			ignore_bzero };
	// Verilator lint_on  UNUSED
	// }}}
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-stream data interface
	// {{{
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
			faxil_wr_outstanding, faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXIL_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXIL_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3)
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
		.i_axi_arcache(4'h0),
		.i_axi_arprot( S_AXIL_ARPROT),
		//
		.i_axi_rvalid(S_AXIL_RVALID),
		.i_axi_rready(S_AXIL_RREADY),
		.i_axi_rdata( S_AXIL_RDATA),
		.i_axi_rresp( S_AXIL_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	// {{{
	generate if (SKID_PASSTHROUGH)
	begin
		always @(*)
		begin
			assert(faxil_rd_outstanding == (S_AXIL_RVALID ? 1:0));
			assert(faxil_wr_outstanding == (S_AXIL_BVALID ? 1:0));
			assert(faxil_awr_outstanding== (S_AXIL_BVALID ? 1:0));
		end

	end endgenerate

	// }}}
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
		.F_LGDEPTH(F_AXI_LGDEPTH),
		.F_AXI_MAXSTALL(3),
		.F_AXI_MAXRSTALL(2),
		.F_AXI_MAXDELAY(3),
		.F_AXI_MAXDELAY(3)
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(M_AXI_AWVALID),
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awid(   M_AXI_AWID),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awlen(  M_AXI_AWLEN),
		.i_axi_awsize( M_AXI_AWSIZE),
		.i_axi_awburst(M_AXI_AWBURST),
		.i_axi_awlock( M_AXI_AWLOCK),
		.i_axi_awcache(M_AXI_AWCACHE),
		.i_axi_awprot( M_AXI_AWPROT),
		.i_axi_awqos(  M_AXI_AWQOS),
		//
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		//
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(   M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		//
		.i_axi_arvalid(1'b0),
		.i_axi_arready(1'b0),
		.i_axi_arid(   M_AXI_AWID),
		.i_axi_araddr( M_AXI_AWADDR),
		.i_axi_arlen(  M_AXI_AWLEN),
		.i_axi_arsize( M_AXI_AWSIZE),
		.i_axi_arburst(M_AXI_AWBURST),
		.i_axi_arlock( M_AXI_AWLOCK),
		.i_axi_arcache(M_AXI_AWCACHE),
		.i_axi_arprot( M_AXI_AWPROT),
		.i_axi_arqos(  M_AXI_AWQOS),
		//
		.i_axi_rvalid(1'b0),
		.i_axi_rready(1'b0),
		.i_axi_rdata({(C_AXI_DATA_WIDTH){1'b0}}),
		.i_axi_rlast(1'b0),
		.i_axi_rresp(2'b00)
		//
		//
		// }}}
	);

	//
	// ...
	//

	always @(*)
	if (r_busy)
		assert(M_AXI_AWADDR[ADDRLSB-1:0] == 0);

	always @(*)
		assert(cmd_addr[ADDRLSB-1:0] == 0);

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

	always @(*)
	if (!r_busy)
	begin
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(!M_AXI_BVALID);
		//
		// ...
		//
	end

	always @(*)
		assert(zero_threshold == (cmd_threshold_w == 0));
	always @(*)
		assert(zero_length == (cmd_length_w == 0));

	always @(*)
	if (M_AXI_AWVALID)
		assert(fifo_fill >= wr_writes_pending + (M_AXI_AWLEN+1));
	else
		assert(fifo_fill >= wr_writes_pending);

	always @(*)
	if (r_busy)
	begin
		if (!aw_none_remaining)
		begin
			assert(aw_requests_remaining
				+ wr_writes_pending == r_remaining_w);

			// Make sure we don't wrap
			assert(wr_writes_pending <= r_remaining_w);
		end
	end else
		assert(!M_AXI_WVALID);

	always @(*)
		assert(aw_none_remaining == (aw_requests_remaining == 0));
	always @(*)
		assert(aw_none_outstanding == (aw_bursts_outstanding == 0));
	always @(*)
		assert(wr_none_pending == (wr_writes_pending == 0));
	always @(*)
		assert(r_none_remaining == (r_remaining_w == 0));
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// These still need to be written
`endif
endmodule
