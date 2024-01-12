////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axis2mm
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Converts an AXI-stream (input) to an AXI (full) memory
//		interface.
//
// {{{
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
//		True if the core is in the middle of a transaction.  Set this
//		bit to one to begin a transaction.
//
//	[30]	r_err
//		True if the core has detected an error, such as FIFO
//		overflow while writing, or FIFO overflow in continuous mode.
//
//		Writing a '1' to this bit while the core is idle will clear it.
//		New transfers will not start until this bit is cleared.  For
//		this reason, I often start a new transfer by writing to bits
//		31 and 30 of this register.
//
//		_s2mm->a_control = 0xc0000000;
//
//		Other bits may be appropriate as well, as discussed below,
//		depending on your application.
//
//	[29]	r_complete
//		True if the transaction has completed, whether normally or
//		abnormally (error or abort).
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
//		addresses--the normal copy to memory case.  If !r_increment is
//		set, the core writes to the same address throughout the
//		transaction.  This is useful if you want to copy data to a
//		FIFO or other device living at a single address in the memory
//		map.
//
//		Writes to CMD_CONTROL while the core is idle will adjust this
//		bit.
//
//	[26]	!tlast_syncd
//
//		Read only status indicator.  Reads 0 if OPT_TLAST_SYNC isn't
//		set.  If OPT_TLAST_SYNC is set, then this bit indicates whether
//		or not the memory transfer is currently aligned with any stream
//		packets, or whether it is out of synchronization and waiting to
//		sync with the incoming stream.  If the IP is out of alignment
//		and OPT_TLAST_SYNC is set, then the core will synchronize
//		itself automatically by holding TREADY high and ignoring data
//		until the first sample after TLAST.
//
//	[25]	Error code, decode error
//
//		Read only bit.  True following any AXI decode error.  This will
//		also set the error bit.  When the error bit is cleared, this
//		bit will be automatically cleared as well.
//
//	[24]	Error code, slave error
//
//		Read only bit.  True following any AXI slave error.  This will
//		also set the error bit.  When the error bit is cleared, this bit
//		will be automatically cleared as well.
//
//	[23]	Error code, overflow error
//
//		Read only bit.  True following any AXI stream overflow.  As with
//		the other two error code bits, this one will also set the error
//		bit.  It will also be cleared whenever the error bit is cleared.
//
//		A "proper" AXI stream will never nor can it ever overflow.  This
//		overflow check therefore looks for AXI stream protocol
//		violations.  Such a violation might be not maintaining TVALID
//		when !TREADY, or changing TDATA when TVALID && !TREADY.
//		Likewise, if TLAST changes while TVALID && !TREADY an overflow
//		condition will be generated--but in this case only if the
//		OPT_TLAST_SYNC option is set.
//
//	[22]	Abort in progress
//
//		Read only bit.  This bit will be true following any abort until
//		the bus transactions complete.  Self-clearing.
//
//	[20:16]	LGFIFO
//		These are read-only bits, returning the size of the FIFO.
//
//	ABORT
//		If the core is busy, and the ABORT_KEY (currently set to 8'h26
//		below) is written to the top 8-bits ([31:24]) of this command
//		register, then the current transfer will be aborted.  Yes, this
//		does repurpose the other bits written above.  Any pending writes
//		will be completed, but nothing more will be written.
//
//		Alternatively, the core will enter into an abort state
//		following any returned bus error indications.
//
//  x4-c:	(Unused and reserved)
//
//  x10-14:	CMD_ADDR
//	[C_AXI_ADDR_WIDTH-1:($clog2(C_AXI_DATA_WIDTH)-3)]
//
//		If idle, this is address the core will write to when it starts.
//
//		If busy, this is the address of either the current or next
//		address the core will request writing to.
//
//		Upon completion, the address either returns to the starting
//		address (if r_continuous is clear), or otherwise becomes the
//		address where the core left off.  In the case of an abort or an
//		error, this will be (near) the address that was last written.
//
//		Why "near"?  Because this address records the writes that have
//		been issued while no error is pending.  If a bus error return
//		comes back, there may have been several writes issued before
//		that error address.  Likewise if an overflow is detected, the
//		data associated with the overflow may have already been
//		somewhat written--the AXI bus doesn't stop on a dime.
//
//		I hope to eventually add support for unaligned bursts.  Such
//		support is not currently part of this core.
//
//  x18-1c:  CMD_LEN
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
// }}}
//
// Status:
// {{{
//	1. The core passes both cover checks and formal property (assertion)
//		based checks.  It has not (yet) been tested in real hardware.
//
//	2. I'd also like to support unaligned addresses (not lengths).  This
//		will require aligning the data coming out of the FIFO as well.
//		As written, the core doesn't yet support these features.
//
// }}}
//
// Updates:
// {{{
//	20210426 - Fix.  Upon reading, the current AXI write address and length
//		will (now) be returned.  These are word address and lengths, not
//		packet address and lengths, and may (or may not) be aligned with
//		packet boundaries.
//
//		In a similar fashion, the cmd_addr and cmd_length registers will
//		be adjusted on any error to (approximate) the address and length
//		remaining upon any discovered error.
// }}}
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	axis2mm #(
		// {{{
		//
		// Downstream AXI (MM) address width.  Remember, this is *byte*
		// oriented, so an address width of 32 means this core can
		// interact with a full 2^(C_AXI_ADDR_WIDTH) *bytes*.
		parameter	C_AXI_ADDR_WIDTH = 32,
		// ... and the downstream AXI (MM) data width.  High speed can
		// be achieved by increasing this data width.
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXIS_TUSER_WIDTH = 0,
		//
		// OPT_AXIS_SKIDBUFFER will place a buffer between the incoming
		// AXI stream interface and the outgoing AXI stream ready.  This
		// is technically necessary, and probably good practice too,
		// when dealing with high speed networks.
		parameter [0:0]	OPT_AXIS_SKIDBUFFER = 1,
		//
		// OPT_AXIS_SKIDREGISTER will force the outputs of the skid
		// buffer to be registered.  This is something you would
		// do primarily if you are trying to hit high speeds through
		// this core.
		parameter [0:0]	OPT_AXIS_SKIDREGISTER = 0,
		//
		// OPT_TLAST_SYNC will synchronize the write with any incoming
		// packets.  Packets are assumed to be synchronized initially
		// after any reset, or on the TVALID following any TLAST
		parameter [0:0]	OPT_TLAST_SYNC = 1,
		//
		// OPT_TREADY_WHILE_IDLE controls how the stream idle is set
		// when the memory copy isn't running.  If 1, then TREADY will
		// be 1 and the core will ignore/throw out data when the core
		// isn't busy.  Otherwise, if this is set to 0, the core will
		// force the stream to stall if ever no data is being copied.
		parameter [0:0]	OPT_TREADY_WHILE_IDLE = 1,
		//
		// If the ABORT_KEY is written to the upper 8-bits of the
		// control/status word, the current operation will be halted.
		// Any currently active (AxVALID through xVALID & xREADY)
		// requests will continue to completion, and the core will then
		// come to a halt.
		parameter [7:0]	ABORT_KEY = 8'h26,
		//
		// The size of the FIFO, log-based two.  Hence LGFIFO=9 gives
		// you a FIFO of size 2^(LGFIFO) or 512 elements.  This is about
		// as big as the FIFO should ever need to be, since AXI bursts
		// can be 256 in length.
		parameter	LGFIFO = 9,
		//
		// Maximum number of bytes that can ever be transferred, in
		// log-base 2.  Hence LGLEN=20 will transfer 1MB of data.
		parameter	LGLEN  = C_AXI_ADDR_WIDTH-1,
		//
		// We only ever use one AXI ID for all of our transactions.
		// Here it is given as 0.  Feel free to change it as necessary.
		parameter [C_AXI_ID_WIDTH-1:0]	AXI_ID = 0,
		//
		// Set OPT_UNALIGNED to be able to transfer from unaligned
		// addresses.  Only applies to non fixed addresses and
		// (possibly) non-continuous bursts.  (THIS IS A PLACEHOLDER.
		// UNALIGNED ADDRESSING IS NOT CURRENTLY SUPPORTED.)
		localparam [0:0]	OPT_UNALIGNED = 0,
		//
		parameter	[0:0]	OPT_LOWPOWER  = 1'b0,
		parameter	[0:0]	OPT_CLKGATE   = OPT_LOWPOWER,
		//
		// OPT_ASYNCMEM.  The default FIFO implementation uses an
		// asynchronous memory read, which will return the result in
		// the same clock it is requested within.  This forces the
		// FIFO to use distributed RAM.  For those architectures that
		// don't have distributed RAM, or those designs that need to
		// use block RAM, this flag should be set to zero.
		parameter	[0:0]	OPT_ASYNCMEM  = 1'b1,
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		localparam	C_AXIL_ADDR_WIDTH = 5,
		localparam	C_AXIL_DATA_WIDTH = 32
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
		input	wire					S_AXIS_TLAST,
		input wire [((C_AXIS_TUSER_WIDTH>0) ? C_AXIS_TUSER_WIDTH-1:0):0]
								S_AXIS_TUSER,
		// }}}
		//
		// The control interface
		// {{{
		input	wire					S_AXIL_AWVALID,
		output	wire					S_AXIL_AWREADY,
		input	wire	[C_AXIL_ADDR_WIDTH-1:0]		S_AXIL_AWADDR,
		input	wire	[2:0]				S_AXIL_AWPROT,
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
		input	wire	[2:0]				S_AXIL_ARPROT,
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
		output wire [(C_AXIS_TUSER_WIDTH>0 ? C_AXIS_TUSER_WIDTH-1:0):0]
							M_AXI_WUSER,
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

	// Local parameters
	// {{{
	localparam	AXILLSB = $clog2(C_AXIL_DATA_WIDTH)-3;
	localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3;
	localparam [2:0]	CMD_CONTROL   = 3'b000,
				// CMD_UNUSED_1  = 3'b001,
				// CMD_UNUSED_2  = 3'b010,
				// CMD_UNUSED_3  = 3'b011,
				CMD_ADDRLO    = 3'b100,
				CMD_ADDRHI    = 3'b101,
				CMD_LENLO     = 3'b110,
				CMD_LENHI     = 3'b111;
				// CMD_RESERVED = 2'b11;

	// The maximum burst size is either 256, or half the FIFO size,
	// whichever is smaller.
	localparam	TMP_LGMAXBURST=(LGFIFO > 8) ? 8 : LGFIFO-1;
	// Of course, if this busts our 4kB packet size, it's an error.
	// Let's clip to that size, then, if the LGMAXBURST would otherwise
	// break it.  So .. if 4kB is larger than our maximum burst size, then
	// no change is required.
	localparam	LGMAXBURST = ((4096 / (C_AXI_DATA_WIDTH / 8))
						> (1<<TMP_LGMAXBURST))
			? TMP_LGMAXBURST : $clog2(4096 * 8 / C_AXI_DATA_WIDTH);
	localparam	LGMAX_FIXED_BURST = (LGMAXBURST > 4) ? 4 : LGMAXBURST;
	localparam	MAX_FIXED_BURST = (1<<LGMAX_FIXED_BURST);
	localparam	LGLENW  = LGLEN  - ADDRLSB;
	// localparam	LGFIFOB = LGFIFO + ADDRLSB;
	localparam	ERRCODE_NOERR    = 0,
			ERRCODE_OVERFLOW = 0,
			ERRCODE_SLVERR   = 1,
			ERRCODE_DECERR   = 2;
	// }}}

	// Signal declarations
	// {{{
	wire	clk_active, gated_clk;
	wire	i_clk   =  gated_clk;
	wire	i_reset = !S_AXI_ARESETN;

	// Incoming stream buffer
	wire		sskd_valid, sskd_ready, sskd_last;
	wire	[C_AXI_DATA_WIDTH-1:0]	sskd_data;
	wire	[((C_AXIS_TUSER_WIDTH>0) ? C_AXIS_TUSER_WIDTH : 1)-1:0] sskd_user;

	reg	r_busy, r_err, r_complete, r_continuous, r_increment,
		cmd_abort, zero_length, r_pre_start,
		w_cmd_start, w_complete, w_cmd_abort;
	reg	[2:0]		r_errcode;
	// reg	cmd_start;
	reg			axi_abort_pending;

	reg	[LGLENW-1:0]	aw_requests_remaining,
				aw_bursts_outstanding,
				aw_next_remaining;
	reg	[LGMAXBURST:0]	wr_writes_pending;
	reg	[LGMAXBURST:0]		r_max_burst;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_addr;

	reg	[C_AXI_ADDR_WIDTH-1:0]	cmd_addr;
	reg	[LGLENW-1:0]		cmd_length_w;

	reg	[2*C_AXIL_DATA_WIDTH-1:0]	wide_address, wide_length,
					new_wideaddr, new_widelen,
					wide_len_remaining,wide_current_address;
	wire	[C_AXIL_DATA_WIDTH-1:0]	new_cmdaddrlo, new_cmdaddrhi,
					new_lengthlo,  new_lengthhi;

	// FIFO signals
	wire				reset_fifo, write_to_fifo,
					read_from_fifo;
	wire [C_AXIS_TUSER_WIDTH+C_AXI_DATA_WIDTH-1:0]	fifo_data;
	wire	[LGFIFO:0]		fifo_fill;
	wire				fifo_full, fifo_empty;

	wire				awskd_valid, axil_write_ready;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	awskd_addr;
	//
	wire				wskd_valid;
	wire	[C_AXIL_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXIL_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				arskd_valid, axil_read_ready;
	wire	[C_AXIL_ADDR_WIDTH-AXILLSB-1:0]	arskd_addr;
	reg	[C_AXIL_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;
	reg				last_stalled, overflow, last_tlast;
	reg	[C_AXI_DATA_WIDTH-1:0]	last_tdata;
	reg	[C_AXIL_DATA_WIDTH-1:0]	w_status_word;

	reg	[LGLENW-1:0]		r_remaining_w;

	reg				axi_awvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	reg	[7:0]			axi_awlen;
	reg				axi_wvalid, axi_wlast;
	reg [C_AXI_DATA_WIDTH/8-1:0]	axi_wstrb;

	// Speed up checking for zeros
	reg				aw_none_remaining,
					aw_none_outstanding,
					aw_last_outstanding,
					wr_none_pending; // r_none_remaining;

	reg				w_phantom_start, phantom_start;
	reg	[LGMAXBURST:0]	initial_burstlen;
	reg	[LGMAXBURST-1:0] addralign;

	//
	// Option processing
	wire			tlast_syncd;

	reg			aw_multiple_full_bursts,
				aw_multiple_fixed_bursts,
				aw_multiple_bursts_remaining,
				aw_needs_alignment;
	reg	[LGFIFO:0]	data_available;
	reg			sufficiently_filled;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream skidbuffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		// {{{
		.OPT_OUTREG(OPT_AXIS_SKIDREGISTER),
		.DW(C_AXI_DATA_WIDTH + 1
			+ ((C_AXIS_TUSER_WIDTH > 0) ? C_AXIS_TUSER_WIDTH:1)),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_PASSTHROUGH(!OPT_AXIS_SKIDBUFFER)
		// }}}
	) skd_stream(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(reset_fifo),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
		.i_data({ S_AXIS_TUSER, S_AXIS_TDATA, S_AXIS_TLAST }),
		.o_valid(sskd_valid), .i_ready(sskd_ready),
			.o_data({ sskd_user, sskd_data, sskd_last })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// This is mostly the skidbuffer logic, and handling of the VALID
	// and READY signals for the AXI-lite control logic in the next
	// section.

	//
	// Write signaling
	//
	// {{{

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) axilawskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr)
		// }}}
	);

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_DATA_WIDTH+C_AXIL_DATA_WIDTH/8),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) axilwskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
		.i_data({ S_AXIL_WDATA, S_AXIL_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb })
		// }}}
	);

	assign	axil_write_ready = clk_active && awskd_valid && wskd_valid
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

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) axilarskid(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr)
		// }}}
	);

	assign	axil_read_ready = clk_active && arskd_valid
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
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// last_stalled -- used in overflow checking
	// {{{
	initial	last_stalled = 1'b0;
	always @(posedge i_clk)
		last_stalled <= (!i_reset) && (S_AXIS_TVALID && !S_AXIS_TREADY);
	// }}}

	// last_tlast -- used to check for protocol violations in overflow next
	// {{{
	always @(posedge i_clk)
	if (!OPT_TLAST_SYNC)
		last_tlast <= 0;
	else
		last_tlast <= S_AXIS_TLAST;
	// }}}

	// last_tdata -- used for overflow checking
	// {{{
	always @(posedge i_clk)
		last_tdata <= S_AXIS_TDATA;
	// }}}

	// overflow
	// {{{
	// Capture and check whether or not the incoming data stream overflowed
	// This is primarily a check for AXI-stream protocol violations, since
	// you can't really overflow an AXI stream when following protocol.  The
	// problem is that many stream sources--such as ADCs for example--can't
	// handle back-pressure.  Hence, checking for stream violations can
	// be used in those cases to check for overflows.  The check is only
	// so good, however, since an overflow condition might take place if
	// an ADC produces two consecutive (identical) values, one of which gets
	// skipped--and this check will not capture that.
	initial	overflow = 0;
	always @(posedge i_clk)
	if (i_reset)
		overflow <= 0;
	else if (last_stalled)
	begin
		// The overflow pulse is only one clock period long
		overflow <= 0;
		if (!sskd_valid)
			overflow <= 1;
		if (S_AXIS_TDATA != last_tdata)
			overflow <= 1;
		if (OPT_TLAST_SYNC && S_AXIS_TLAST != last_tlast)
			overflow <= 1;

		// This will be caught by r_err and r_continuous
	end
	// }}}

	// w_cmd_abort, cmd_abort -- Abort transaction on user request
	// {{{

	// w_cmd_abort is a combinational value capturing a user abort request
	// {{{
	always @(*)
	begin
		w_cmd_abort = 0;
		w_cmd_abort = (axil_write_ready && awskd_addr == CMD_CONTROL)
			&& (wskd_strb[3] && wskd_data[31:24] == ABORT_KEY);
		if (!r_busy)
			w_cmd_abort = 0;
	end
	// }}}

	// cmd_abort latches the user request until the abort is complete
	// {{{
	initial	cmd_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_abort <= 0;
	else if (!r_busy)
		cmd_abort <= 0;
	else
		cmd_abort <= cmd_abort || w_cmd_abort;
	// }}}
	// }}}

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
	end

	// r_busy, r_complete -- Calculate busy or complete flags
	// {{{
	initial	r_busy     = 0;
	initial	r_complete = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_busy     <= 0;
		r_complete <= 0;
	end else if (!r_busy)
	begin
		// Core is idle, waiting for a command to start
		if (w_cmd_start)
			r_busy <= 1'b1;

		// Any write to the control register will clear the
		// completion flag
		if (axil_write_ready && awskd_addr == CMD_CONTROL)
			r_complete <= 1'b0;
	end else if (w_complete)
	begin
		// Clear busy once the transaction is complete
		//  This includes clearing busy on any error
		r_complete <= 1;
		r_busy <= 1'b0;
	end
	// }}}

	// o_int -- interrupt generation
	// {{{
	initial	o_int = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_int <= 0;
	else
		o_int <= (r_busy && w_complete)
			|| (r_continuous && overflow);
	// }}}

	// r_err, r_errcode: Error conditions checking
	// {{{
	initial	r_err = 0;
	initial	r_errcode = ERRCODE_NOERR;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_err <= 0;
		r_errcode <= ERRCODE_NOERR;
	end else if (!r_busy)
	begin
		if (r_continuous && overflow)
		begin
			r_err <= 1;
			r_errcode[ERRCODE_OVERFLOW] <= 1'b1;
		end

		if (axil_write_ready && awskd_addr == CMD_CONTROL
			&& wskd_strb[3] && wskd_data[30])
		begin
			r_err     <= 0;
			r_errcode <= ERRCODE_NOERR;
		end
	end else if (r_busy)
	begin
		if (M_AXI_BVALID && M_AXI_BREADY && M_AXI_BRESP[1])
		begin
			r_err <= 1'b1;
			if (M_AXI_BRESP[0])
				r_errcode[ERRCODE_DECERR] <= 1'b1;
			else
				r_errcode[ERRCODE_SLVERR] <= 1'b1;
		end

		if (overflow)
		begin
			r_err <= 1'b1;
			r_errcode[ERRCODE_OVERFLOW] <= 1'b1;
		end
	end
	// }}}

	// r_continuous
	// {{{
	initial	r_continuous = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_continuous <= 0;
	else begin
		if (r_continuous && overflow)
			r_continuous <= 1'b0;
		if (!r_busy && axil_write_ready && awskd_addr == CMD_CONTROL)
			r_continuous <= wskd_strb[3] && wskd_data[28];
	end
	// }}}

	// wide_*
	// {{{
	always @(*)
	begin
		wide_address = 0;
		wide_address[C_AXI_ADDR_WIDTH-1:0] = cmd_addr;

		wide_current_address = 0;
		wide_current_address[C_AXI_ADDR_WIDTH-1:0] = axi_addr;

		wide_length = 0;
		wide_length[ADDRLSB +: LGLENW] = cmd_length_w;

		wide_len_remaining = 0;
		wide_len_remaining[ADDRLSB +: LGLENW] = r_remaining_w;
	end
	// }}}

	// new_* wires created via apply_wstrb
	// {{{
	assign	new_cmdaddrlo= apply_wstrb(
			wide_address[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);
	assign	new_cmdaddrhi=apply_wstrb(
			wide_address[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);
	assign	new_lengthlo= apply_wstrb(
			wide_length[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);
	assign	new_lengthhi= apply_wstrb(
			wide_length[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);
	// }}}

	// new_wideaddr, new_widelen
	// {{{
	// These are the wide_* adjusted for any write, and then adjusted again
	// to make sure they are within the correct number of bits for the
	// interface.
	always @(*)
	begin
		new_wideaddr = wide_address;
		if (awskd_addr == CMD_ADDRLO)
			new_wideaddr[C_AXIL_DATA_WIDTH-1:0]
				= new_cmdaddrlo;
		if (awskd_addr == CMD_ADDRHI)
			new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH]
				= new_cmdaddrhi;
		if (!OPT_UNALIGNED)
			new_wideaddr[ADDRLSB-1:0] = 0;

		// We only support C_AXI_ADDR_WIDTH address bits
		new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH] = 0;

		//
		///////////////
		//

		new_widelen = wide_length;
		if (awskd_addr == CMD_LENLO)
			new_widelen[C_AXIL_DATA_WIDTH-1:0] = new_lengthlo;
		if (awskd_addr == CMD_LENHI)
			new_widelen[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH]
				= new_lengthhi;

		// We only support integer numbers of words--even if unaligned
		new_widelen[ADDRLSB-1:0] = 0;

		// We only support LGLEN length bits
		new_widelen[2*C_AXIL_DATA_WIDTH-1:LGLEN] = 0;
	end
	// }}}

	// cmd_addr, cmd_length_w, r_increment, zero_length, aw_multiple_*
	// {{{
	initial	r_increment   = 1'b1;
	initial	cmd_addr      = 0;
	initial	cmd_length_w  = 0;	// Counts in bytes
	initial	zero_length   = 1;
	initial aw_multiple_full_bursts  = 0;
	initial aw_multiple_fixed_bursts = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		r_increment <= 1'b1;
		cmd_addr      <= 0;
		cmd_length_w  <= 0;
		zero_length   <= 1;
		aw_multiple_full_bursts  <= 0;
		aw_multiple_fixed_bursts <= 0;
		// }}}
	end else if (axil_write_ready && !r_busy)
	begin // Set the command, address, and length prior to operation
		// {{{
		case(awskd_addr)
		CMD_CONTROL:
			r_increment <= !wskd_data[27];
		CMD_ADDRLO:
			cmd_addr <= new_wideaddr[C_AXI_ADDR_WIDTH-1:0];
		CMD_ADDRHI: if (C_AXI_ADDR_WIDTH > C_AXIL_DATA_WIDTH)
			begin
			cmd_addr <= new_wideaddr[C_AXI_ADDR_WIDTH-1:0];
			end
		CMD_LENLO: begin
			cmd_length_w <= new_widelen[ADDRLSB +: LGLENW];
			zero_length <= (new_widelen[ADDRLSB +: LGLENW] == 0);
			aw_multiple_full_bursts  <= |new_widelen[LGLEN-1:(ADDRLSB+LGMAXBURST)];
			aw_multiple_fixed_bursts <= |new_widelen[LGLEN-1:(ADDRLSB+LGMAX_FIXED_BURST)];

			end
		CMD_LENHI: if (LGLEN > C_AXIL_DATA_WIDTH)
			begin
			cmd_length_w <= new_widelen[ADDRLSB +: LGLENW];
			zero_length <= (new_widelen[ADDRLSB +: LGLENW] == 0);
			aw_multiple_full_bursts  <= |new_widelen[LGLEN-1:(ADDRLSB+LGMAXBURST)];
			aw_multiple_fixed_bursts <= |new_widelen[LGLEN-1:(ADDRLSB+LGMAX_FIXED_BURST)];
			end
		default: begin end
		endcase
		// }}}
	end else if (r_busy)
	begin // Updated cmd_addr && cmd_length during operation
		// {{{
		// Capture the last address written to in case of r_continuous
		// (where we'll want to start again from this address),
		// cmd_abort (where we'll want to know how far we got), or
		// a bus error (where again we'll want to know how far we got)
		if (r_continuous||axi_abort_pending)
			cmd_addr <= axi_addr;

		// Capture the number of remaining requests on either an error
		// or an abort.  Need to be careful here that we don't capture
		// this address twice--hence the check for
		// w_cmd_abort && !cmd_abort, and again for BVALID && !r_err
		//
		// Note that we can't check for axi_abort_pending here, since
		// as soon as axi_abort_pending becomes true then cmd_length_w
		// will get set to zero.  Hence we need to capture this before
		// axi_abort_pending gets set.
		//
		// Note that this is only an *approximate* length--especially
		// in the case of either a bus error or an overflow, in which
		// cases we won't really know what writes have been accomplished
		// only that the last one failed.  In that case, this will
		// indicate the amount of writes we haven't requested
		// (yet)--knowing that at least one (or more) of those prior
		// must've failed.  In the case of an overflow error, the
		// overflow error may (or may not) have been written to memory
		// by this time.
		if (!axi_abort_pending && (cmd_abort || r_err
				|| (M_AXI_BVALID && M_AXI_BRESP[1])))
		begin
			cmd_length_w <= aw_requests_remaining;
			zero_length  <= (aw_requests_remaining == 0);
			aw_multiple_full_bursts  <= |aw_requests_remaining[LGLENW-1:LGMAXBURST];
			aw_multiple_fixed_bursts <= |aw_requests_remaining[LGLENW-1:LGMAX_FIXED_BURST];
		end

		// Note that, because cmd_addr and cmd_length_w here aren't set
		// on the same conditions that it is possible, on an error,
		// that the two will not match.
		// }}}
	end
	// }}}

	// w_status_word
	// {{{
	always @(*)
	begin
		w_status_word = 0;

		// The ABORT_KEY needs to be chosen so as not to look
		// like these bits, lest someone read from the register
		// and write back to it accidentally aborting any transaction
		w_status_word[31] = r_busy;
		w_status_word[30] = r_err;
		w_status_word[29] = r_complete;
		w_status_word[28] = r_continuous;
		w_status_word[27] = !r_increment;
		w_status_word[26] = !tlast_syncd;
		w_status_word[25:23] = r_errcode;
		w_status_word[22] = cmd_abort;
		w_status_word[20:16] = LGFIFO;
	end
	// }}}

	// axil_read_data
	// {{{
	always @(posedge i_clk)
	if (!axil_read_valid || S_AXIL_RREADY)
	begin
		case(arskd_addr)
		CMD_CONTROL: axil_read_data <= w_status_word;
		CMD_ADDRLO: begin
			if (!r_busy)
				axil_read_data <= wide_address[C_AXIL_DATA_WIDTH-1:0];
			else
				axil_read_data <= wide_current_address[C_AXIL_DATA_WIDTH-1:0];
			end
		CMD_ADDRHI: begin
			if (!r_busy)
				axil_read_data <= wide_address[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
			else
				axil_read_data <= wide_current_address[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
			end
		CMD_LENLO: begin
			if (!r_busy)
				axil_read_data <= wide_length[C_AXIL_DATA_WIDTH-1:0];
			else
				axil_read_data <= wide_len_remaining[C_AXIL_DATA_WIDTH-1:0];
			end
		CMD_LENHI: begin
			if (!r_busy)
				axil_read_data <= wide_length[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
			else
				axil_read_data <= wide_len_remaining[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
			end
		default:     axil_read_data <= 0;
		endcase
	end
	// }}}

	function [C_AXIL_DATA_WIDTH-1:0] apply_wstrb;
	// {{{
		input   [C_AXIL_DATA_WIDTH-1:0]  prior_data;
		input   [C_AXIL_DATA_WIDTH-1:0]  new_data;
		input   [C_AXIL_DATA_WIDTH/8-1:0]   wstrb;

		integer k;
		for(k=0; k<C_AXIL_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The data FIFO section
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Reset the FIFO between bursts, as long as r_continuous isn't set
	assign	reset_fifo = i_reset || (!r_busy && (!r_continuous || r_err));
	assign	write_to_fifo  = sskd_valid && sskd_ready && tlast_syncd;
	assign	read_from_fifo = M_AXI_WVALID  && M_AXI_WREADY
					&& !axi_abort_pending;

	// We are ready if the FIFO isn't full and ...
	//	if OPT_TREADY_WHILE_IDLE is true
	//		at which point we ignore incoming data when we aren't
	//		busy, or
	//	if we aren't resetting the FIFO--that is, if data is actually
	//		going into the FIFO, or
	// 	if we are ever out of synchronization--then we can ignore data
	//		until the next TLAST comes, where we must realign
	//		ourselves
	assign	sskd_ready  = clk_active && !fifo_full
			&& (OPT_TREADY_WHILE_IDLE
				|| !reset_fifo || !tlast_syncd);

	generate if (OPT_TLAST_SYNC)
	begin : GEN_TLAST_SYNC
		reg	r_tlast_syncd;
		// If the user has set OPT_TLAST_SYNC, then he wants to make
		// certain that we don't start writing until the first stream
		// value after the TLAST packet indicating an end of packet.
		// For this cause, we'll maintain an r_tlast_syncd value
		// indicating that the last value was a TLAST.  If, at any
		// time afterwards, a value is accepted into the stream but not
		// into the FIFO, then the stream is now out of sync and
		// r_tlast_syncd will drop.
		//
		// Note, this doesn't catch the case where the FIFO can't keep
		// up.  Lost data (might be) caught by overflow below.
		initial	r_tlast_syncd = 1;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_tlast_syncd <= 1;
		else if (sskd_valid && sskd_ready)
		begin
			if (sskd_last)
				r_tlast_syncd <= 1;
			else if (reset_fifo)
				r_tlast_syncd <= 0;
		end

		assign	tlast_syncd = r_tlast_syncd;
	end else begin : NO_TLAST_SYNC

		//
		// If the option isn't set, then we are always synchronized.
		//
		assign	tlast_syncd = 1;

		// Verilator lint_off UNUSED
		wire unused_tlast_sync;
		assign	unused_tlast_sync = &{ 1'b0, sskd_last };
		// Verilator lint_on  UNUSED
	end endgenerate

	// Incoming FIFO
	// {{{
	generate if (C_AXIS_TUSER_WIDTH > 0)
	begin : FIFO_WITH_USER_DATA

		sfifo #(
			// {{{
			.BW(C_AXIS_TUSER_WIDTH + C_AXI_DATA_WIDTH),
			.LGFLEN(LGFIFO), .OPT_ASYNC_READ(OPT_ASYNCMEM)
			// }}}
		) u_sfifo (
			// {{{
			.i_clk(i_clk), .i_reset(reset_fifo),
			.i_wr(write_to_fifo),
				.i_data({ sskd_user, sskd_data }),
				.o_full(fifo_full), .o_fill(fifo_fill),
			.i_rd(read_from_fifo), .o_data(fifo_data),
				.o_empty(fifo_empty)
			// }}}
		);

		assign	{ M_AXI_WUSER, M_AXI_WDATA }  = fifo_data;

	end else begin : NO_USER_DATA

		sfifo #(
			// {{{
			.BW(C_AXI_DATA_WIDTH),
			.LGFLEN(LGFIFO), .OPT_ASYNC_READ(OPT_ASYNCMEM)
			// }}}
		) u_sfifo (
			// {{{
			.i_clk(i_clk), .i_reset(reset_fifo),
			.i_wr(write_to_fifo), .i_data(sskd_data),
				.o_full(fifo_full), .o_fill(fifo_fill),
			.i_rd(read_from_fifo), .o_data(fifo_data),
				.o_empty(fifo_empty)
			// }}}
		);

		assign	M_AXI_WDATA = fifo_data;
		assign	M_AXI_WUSER = 0;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_tuser;
		assign	unused_tuser = &{ 1'b0, sskd_user };
		// Verilator lint_on UNUSED
		// }}}
	end endgenerate

	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The outgoing AXI (full) protocol section
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//

	// Some counters to keep track of our state
	// {{{


	// Count the number of word writes left to be requested, starting
	// with the overall command length and then reduced by M_AWLEN on
	// each address write
	// {{{
	always @(*)
	begin
		// aw_next_remaining = aw_requests_remaining;
		// if (phantom_start)
		//	aw_next_remaining = aw_requests_remaining
		//		+  (~{{ (LGLENW-8){1'b0}}, M_AXI_AWLEN });
		//		// - (M_AXI_AWLEN+1)
		//		// + (~M_AXI_AWLEN+1) - 1
		//		// + ~M_AXI_AWLEN
		aw_next_remaining = aw_requests_remaining
			+ { {(LGLENW-8){phantom_start}},
					(phantom_start) ? ~M_AXI_AWLEN : 8'h00};
	end

	initial	r_pre_start = 1;
	always @(posedge i_clk)
	if (!r_busy)
		r_pre_start <= 1;
	else
		r_pre_start <= 0;

	always @(posedge i_clk)
	if (!r_busy)
	begin
		aw_needs_alignment <= 0;

		if (|new_wideaddr[ADDRLSB +: LGMAXBURST])
		begin
			if (|new_widelen[LGLEN-1:(LGMAXBURST+ADDRLSB)])
				aw_needs_alignment <= 1;
			if (~new_wideaddr[ADDRLSB +: LGMAXBURST]
					< new_widelen[ADDRLSB +: LGMAXBURST])
				aw_needs_alignment <= 1;
		end
	end

	initial	aw_none_remaining = 1;
	initial	aw_requests_remaining = 0;
	always @(posedge i_clk)
	if (!r_busy)
	begin
		aw_requests_remaining <= cmd_length_w;
		aw_none_remaining     <= zero_length;
		aw_multiple_bursts_remaining <= |cmd_length_w[LGLENW-1:LGMAXBURST+1];
	end else if (cmd_abort || axi_abort_pending)
	begin
		aw_requests_remaining <= 0;
		aw_none_remaining <= 1;
		aw_multiple_bursts_remaining <= 0;
	end else if (phantom_start)
	begin
		aw_requests_remaining <= aw_next_remaining;
		aw_none_remaining<= !aw_multiple_bursts_remaining
			&&(aw_next_remaining[LGMAXBURST:0] == 0);
		aw_multiple_bursts_remaining
				<= |aw_next_remaining[LGLENW-1:LGMAXBURST+1];
	end
	// }}}

	// Calculate the maximum possible burst length, ignoring 4kB boundaries
	// {{{
	always @(*)
		addralign = 1+(~cmd_addr[ADDRLSB +: LGMAXBURST]);

	always @(*)
	begin
		initial_burstlen = (1<<LGMAXBURST);
		if (!r_increment)
		begin
			initial_burstlen = MAX_FIXED_BURST;
			if (!aw_multiple_fixed_bursts)
				initial_burstlen = { 1'b0, cmd_length_w[LGMAXBURST-1:0] };
		end else if (aw_needs_alignment)
			initial_burstlen = { 1'b0, addralign };
		else if (!aw_multiple_full_bursts)
			initial_burstlen = { 1'b0, cmd_length_w[LGMAXBURST-1:0] };
	end

	initial	r_max_burst = 0;
	always @(posedge i_clk)
	if (!r_busy || r_pre_start)
	begin
		// Force us to align ourself early
		//   That way we don't need to check for
		//   alignment (again) later
		r_max_burst <= initial_burstlen;
	end else if (phantom_start)
	begin
		// Verilator lint_off WIDTH
		if (r_increment || LGMAXBURST <= LGMAX_FIXED_BURST)
		begin
			if (!aw_multiple_bursts_remaining
				&& aw_next_remaining[LGMAXBURST:0] < (1<<LGMAXBURST))
				r_max_burst <= { 1'b0, aw_next_remaining[7:0] };
			else
				r_max_burst <= (1<<LGMAXBURST);
		end else begin
			if (!aw_multiple_bursts_remaining
				&& aw_next_remaining[LGMAXBURST:0] < MAX_FIXED_BURST)
				r_max_burst <= { 1'b0, aw_next_remaining[7:0] };
			else
				r_max_burst <= MAX_FIXED_BURST;
		end
		// Verilator lint_on WIDTH
	end
	// }}}

	// Count the number of bursts outstanding--these are the number of
	// AWVALIDs that have been accepted, but for which the BVALID has not
	// (yet) been returned.
	// {{{
	initial	aw_last_outstanding   = 0;
	initial	aw_none_outstanding   = 1;
	initial	aw_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		aw_bursts_outstanding <= 0;
		aw_none_outstanding <= 1;
		aw_last_outstanding <= 0;
	end else case ({ phantom_start, M_AXI_BVALID && M_AXI_BREADY })
	2'b01:	begin
		aw_bursts_outstanding <= aw_bursts_outstanding - 1;
		aw_none_outstanding <= (aw_bursts_outstanding == 1);
		aw_last_outstanding <= (aw_bursts_outstanding == 2);
		end
	2'b10:	begin
		aw_none_outstanding <= 0;
		aw_bursts_outstanding <= aw_bursts_outstanding + 1;
		aw_last_outstanding   <= (aw_bursts_outstanding == 0);
		end
	default: begin end
	endcase
	// }}}

	// Are we there yet?
	// {{{
	// We can't just look for the last BVALID, since ... it might be
	// possible to receive an abort before the FIFO is full enough to
	// initiate the first burst.
	always @(*)
	if (!r_busy)
		w_complete = 0;
	else
		w_complete = !M_AXI_AWVALID && (aw_none_remaining)
			&&((aw_last_outstanding && M_AXI_BVALID)
				|| aw_none_outstanding);
	// }}}

	// Are we stopping early?  Aborting something ongoing?
	// {{{
	initial	axi_abort_pending = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		axi_abort_pending <= 0;
	else begin
		if (M_AXI_BVALID && M_AXI_BREADY && M_AXI_BRESP[1])
			axi_abort_pending <= 1;
		if (cmd_abort)
			axi_abort_pending <= 1;
		if (r_err)
			axi_abort_pending <= 1;
	end
	// }}}

	// Count the number of WVALIDs yet to be sent on the write channel
	// {{{
	initial	wr_none_pending = 1;
	initial	wr_writes_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		wr_writes_pending <= 0;
		wr_none_pending   <= 1;
	end else case ({ phantom_start,
			M_AXI_WVALID && M_AXI_WREADY })
	2'b00: begin end
	2'b01: begin
		wr_writes_pending <= wr_writes_pending - 1;
		wr_none_pending   <= (wr_writes_pending == 1);
		end
	2'b10: begin
		wr_writes_pending <= wr_writes_pending + (M_AXI_AWLEN[LGMAXBURST-1:0] + 1);
		wr_none_pending   <= 0;
		end
	2'b11: begin
		wr_writes_pending <= wr_writes_pending + (M_AXI_AWLEN[LGMAXBURST-1:0]);
		wr_none_pending   <= (M_AXI_WLAST);
		end
	endcase
	// }}}

	// So that we can monitor where we are at, and perhaps restart it
	// later, keep track of the current address used by the W-channel
	// {{{
	initial	axi_addr = 0;
	always @(posedge i_clk)
	begin
		if (!r_busy)
			axi_addr <= cmd_addr;
		else if (axi_abort_pending || !r_increment)
			// Stop incrementing the address following an abort
			axi_addr <= axi_addr;
		else if (M_AXI_WVALID && M_AXI_WREADY)
			axi_addr <= axi_addr + (1<<ADDRLSB);

		if (!OPT_UNALIGNED)
			axi_addr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// Count the number of words remaining to be written on the W channel
	// {{{
	// initial	r_none_remaining = 1;
	initial	r_remaining_w = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_remaining_w <= 0;
		// r_none_remaining <= 1;
	end else if (!r_busy)
	begin
		r_remaining_w<= cmd_length_w;
		// r_none_remaining <= zero_length;
	end else if (M_AXI_WVALID && M_AXI_WREADY)
	begin
		r_remaining_w <= r_remaining_w - 1;
		// r_none_remaining <= (r_remaining_w == 1);
	end
	// }}}

	//
	// }}}

	// Phantom starts
	// {{{
	// Since we can't use the xREADY signals in our signaling, we hvae to
	// be ready to generate both AWVALID and WVALID on the same cycle,
	// and then hold AWVALID until it has been accepted.  This means we
	// can't use AWVALID as our burst start signal like we could in the
	// slave.  Instead, we'll use a "phantom" start signal.  This signal
	// is local here in our code.  When this signal goes high, AWVALID
	// and WVALID go high at the same time.  Then, if AWREADY isn't held,
	// we can still update all of our internal counters as though it were,
	// based upon the phantom_start signal, and continue as though
	// AWVALID were accepted on its first clock period.

	always @(*)
	begin
		// We start again if there's more information to transfer
		w_phantom_start = !aw_none_remaining;

		// But not if the amount of information we need isn't (yet)
		// in the FIFO.
		if (!sufficiently_filled)
			w_phantom_start = 0;

		// Insist on a minimum of one clock between burst starts,
		// since our burst length calculation takes a clock to do
		if (phantom_start || r_pre_start)
			w_phantom_start = 0;

		if (M_AXI_AWVALID && !M_AXI_AWREADY)
			w_phantom_start = 0;

		// If we're still writing the last burst, then don't start
		// any new ones
		if (M_AXI_WVALID && (!M_AXI_WLAST || !M_AXI_WREADY))
			w_phantom_start = 0;

		// Finally, don't start any new bursts if we aren't already
		// busy transmitting, or if we are in the process of aborting
		// our transfer
		if (!r_busy || cmd_abort || axi_abort_pending)
			w_phantom_start = 0;
	end

	initial	phantom_start = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_start <= 0;
	else
		phantom_start <= w_phantom_start;
	// }}}


	//
	// WLAST
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
	begin
		axi_wlast <= (cmd_length_w == 1);
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (w_phantom_start)
			axi_wlast <= (r_max_burst == 1);
		else if (phantom_start)
			axi_wlast <= (M_AXI_AWLEN == 1);
		else
			axi_wlast <= (wr_writes_pending == 1 + (M_AXI_WVALID ? 1:0));
	end
	// }}}

	// Calculate AWLEN and AWADDR for the next AWVALID
	// {{{
	//
	initial	data_available = 0;
	always @(posedge i_clk)
	if (reset_fifo)
		data_available <= 0;
	else if (axi_abort_pending)
		data_available <= fifo_fill + (write_to_fifo ? 1:0);
	else case({ write_to_fifo, phantom_start })
	2'b10: data_available <= data_available + 1;
	// Verilator lint_off WIDTH
	2'b01: data_available <= data_available - (M_AXI_AWLEN+1);
	2'b11: data_available <= data_available - (M_AXI_AWLEN);
	// Verilator lint_on  WIDTH
	default: begin end
	endcase

	always @(*)
	if (|aw_requests_remaining[LGLENW-1:LGMAXBURST])
		sufficiently_filled = |data_available[LGFIFO:LGMAXBURST];
	else
		sufficiently_filled = (data_available[LGMAXBURST-1:0]
				>= aw_requests_remaining[LGMAXBURST-1:0]);

	//
	// axi_awlen
	// {{{
	generate if (LGMAXBURST >= 8)
	begin : GEN_BIG_AWLEN

		always @(posedge i_clk)
		if (!M_AXI_AWVALID || M_AXI_AWREADY)
			axi_awlen  <= r_max_burst[7:0] - 8'd1;

	end else begin : GEN_SHORT_AWLEN

		always @(posedge i_clk)
		if (!M_AXI_AWVALID || M_AXI_AWREADY)
		begin
			axi_awlen  <= { {(8-LGMAXBURST){1'b0}}, r_max_burst } - 8'd1;
			axi_awlen[7:LGMAXBURST] <= 0;
		end

	end endgenerate
	// }}}

	always @(posedge i_clk)
	begin
		if (M_AXI_AWVALID && M_AXI_AWREADY)
		begin
			axi_awaddr[ADDRLSB-1:0] <= 0;
			// Verilator lint_off WIDTH
			if (r_increment)
				axi_awaddr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
				    <= axi_awaddr[C_AXI_ADDR_WIDTH-1:ADDRLSB]
						+ (M_AXI_AWLEN+1);
		end
		// Verilator lint_on WIDTH

		if (!r_busy)
			axi_awaddr<= cmd_addr;

		if (!OPT_UNALIGNED)
			axi_awaddr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// AWVALID
	// {{{
	initial	axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_awvalid <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		axi_awvalid <= w_phantom_start;
	// }}}

	// WVALID
	// {{{
	initial	axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_wvalid <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (M_AXI_WVALID && !M_AXI_WLAST)
			axi_wvalid <= 1;
		else
			axi_wvalid <= w_phantom_start;
	end
	// }}}

	// axi_wstrb
	// {{{
	always @(posedge i_clk)
	if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wstrb <= (axi_abort_pending) ? 0:-1;
	// }}}

	// Fixed bus values
	// {{{
	assign	M_AXI_AWVALID= axi_awvalid;
	assign	M_AXI_AWID   = AXI_ID;
	assign	M_AXI_AWADDR = axi_awaddr;
	assign	M_AXI_AWLEN  = axi_awlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_AWSIZE = $clog2(C_AXI_DATA_WIDTH)-3;
	// Verilator lint_on  WIDTH
	assign	M_AXI_AWBURST= { 1'b0, r_increment };
	assign	M_AXI_AWLOCK = 0;
	assign	M_AXI_AWCACHE= 4'h3;
	assign	M_AXI_AWPROT = 0;
	assign	M_AXI_AWQOS  = 0;

	assign	M_AXI_WVALID = axi_wvalid;
	assign	M_AXI_WSTRB  = axi_wstrb;
	assign	M_AXI_WLAST  = axi_wlast;
	// M_AXI_WLAST = ??

	assign	M_AXI_BREADY = 1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Clock gating
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_CLKGATE)
	begin : CLK_GATING
		// {{{
		reg	gatep, r_clk_active;
		reg	gaten /* verilator clock_enable */;

		// clk_active
		// {{{
		initial	r_clk_active = 1'b1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_clk_active <= 1'b1;
		else begin
			r_clk_active <= 1'b0;

			if (r_busy)
				r_clk_active <= 1'b1;
			if (awskd_valid || wskd_valid || arskd_valid)
				r_clk_active <= 1'b1;
			if (S_AXIL_BVALID || S_AXIL_RVALID)
				r_clk_active <= 1'b1;

			// Activate the clock on incoming data
				// reset_fifo = i_reset || (!r_busy && (!r_continuous || r_err));
				// !reset_fifo= r_busy || (r_continuous && !r_err)
				// !reset_fifo= (r_continuous && !r_err)
			if (sskd_valid && !fifo_full
				&& (!tlast_syncd || (r_continuous && !r_err)))
				r_clk_active <= 1'b1;
		end

		assign	clk_active = r_clk_active;
		// }}}
		// Gate the clock here locally
		// {{{
		initial	gatep = 1'b1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			gatep <= 1'b1;
		else
			gatep <= clk_active;

		initial	gaten = 1'b1;
		always @(negedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			gaten <= 1'b1;
		else
			gaten <= gatep;

		assign	gated_clk = S_AXI_ACLK && gaten;

		assign	clk_active = r_clk_active;
		// }}}
		// }}}
	end else begin : NO_CLK_GATING
		// {{{
		// Always active
		assign	clk_active = 1'b1;
		assign	gated_clk = S_AXI_ACLK;
		// }}}
	end endgenerate
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_BID,
			M_AXI_BRESP[0], fifo_empty,
			wr_none_pending, S_AXIL_ARADDR[AXILLSB-1:0],
			S_AXIL_AWADDR[AXILLSB-1:0],
			new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH],
			new_widelen };
	// Verilator coverage_on
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
	//
	// The formal properties for this unit are maintained elsewhere.
	// This core does, however, pass a full prove (w/ induction) for all
	// bus properties.
	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-stream data interface
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
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_AXIL_LGDEPTH = 4;

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
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
	);

	always @(*)
	begin
		assert(faxil_rd_outstanding == (S_AXIL_RVALID ? 1:0)
			+(S_AXIL_ARREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_WREADY ? 0:1));
		assert(faxil_awr_outstanding== (S_AXIL_BVALID ? 1:0)
			+(S_AXIL_AWREADY ? 0:1));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI master memory interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
		assert(aw_bursts_outstanding
			== faxi_awr_nbursts
				+ ((M_AXI_AWVALID&&!phantom_start) ? 1:0));

	//
	// ...
	//

	always @(posedge i_clk)
	if (M_AXI_AWVALID)
	begin
		// ...
		if (phantom_start)
		begin
			assert(wr_writes_pending == 0);
			assert(wr_none_pending);
		end else if ($past(phantom_start))
		begin
			assert(wr_writes_pending <= M_AXI_AWLEN+1);
		end
	end else begin
		// ...
		assert(wr_none_pending == (wr_writes_pending == 0));
	end

	always @(*)
	if (r_busy && !OPT_UNALIGNED)
		assert(M_AXI_AWADDR[ADDRLSB-1:0] == 0);

	always @(*)
	if (!OPT_UNALIGNED)
		assert(cmd_addr[ADDRLSB-1:0] == 0);

	//
	// ...
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Other formal properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// ...
	//

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
		assert(zero_length == (cmd_length_w == 0));

	//
	// ...
	//
	always @(*)
	if (phantom_start)
	begin
		assert(data_available >= (M_AXI_AWLEN+1));
	end else if (M_AXI_AWVALID)
	begin
		assert(data_available <= (1<<LGFIFO));
	end


	always @(*)
	if (phantom_start)
		assert(wr_writes_pending == 0);

	always @(*)
	if (phantom_start)
	begin
		assert(fifo_fill >= (M_AXI_AWLEN+1));
	end else if (!axi_abort_pending)
		assert(fifo_fill >= wr_writes_pending);

	always @(*)
	if (r_busy)
	begin
		if (!aw_none_remaining && !phantom_start)
		begin
			assert(aw_requests_remaining
				+ wr_writes_pending == r_remaining_w);

			// Make sure we don't wrap
			assert(wr_writes_pending <= r_remaining_w);
		end else if (!aw_none_remaining)
		begin
			assert(aw_requests_remaining == r_remaining_w);

			// Make sure we don't wrap
			assert(wr_writes_pending == 0);
		end
	end else
		assert(!M_AXI_WVALID);

	always @(*)
		assert(aw_none_remaining == (aw_requests_remaining == 0));

	always @(*)
	if (r_busy)
		assert(aw_multiple_bursts_remaining == (|aw_requests_remaining[LGLENW-1:LGMAXBURST+1]));

	always @(*)
	begin
		assert(aw_last_outstanding == (aw_bursts_outstanding == 1));
		assert(aw_none_outstanding == (aw_bursts_outstanding == 0));
	end

	//
	// ...
	//

	always @(*)
	if (r_complete)
		assert(!r_busy);

	always @(*)
		assert(fifo_fill >= wr_writes_pending);

	always @(*)
	if (r_busy)
		assert(r_max_burst <= (1<<LGMAXBURST));

	always @(*)
	if (r_busy && !r_pre_start)
		assert((r_max_burst > 0) || (aw_requests_remaining == 0));


	always @(*)
	if (phantom_start)
	begin
		assert(M_AXI_AWVALID && M_AXI_WVALID);
		assert(wr_none_pending);
		// assert(drain_triggered);
	end

	always @(posedge i_clk)
	if (phantom_start)
	begin
		assert(r_max_burst > 0);
		assert(M_AXI_AWLEN == $past(r_max_burst)-1);
	end

	always @(*)
	if (r_busy && !r_err && !cmd_abort && aw_requests_remaining == f_length)
		assert(initial_burstlen > 0);

	always @(*)
	if ((LGMAXBURST < 8) && (r_busy))
		assert(M_AXI_AWLEN+1 <= (1<<LGMAXBURST));

	always @(*)
	if (r_busy && !r_increment && (M_AXI_AWVALID
				|| ((aw_requests_remaining < cmd_length_w)
					&& (aw_requests_remaining > 0))))
		assert(M_AXI_AWLEN+1 <= MAX_FIXED_BURST);

	always @(*)
	if (M_AXI_AWVALID && M_AXI_AWADDR[ADDRLSB +: LGMAXBURST])
	begin
		// If we are ever unaligned, our first step should be to
		// align ourselves
		assert(M_AXI_AWLEN+1 <=
			1 +(~M_AXI_AWADDR[ADDRLSB +: LGMAXBURST]));
	end

	always @(*)
	if (!wr_none_pending)
	begin
		// Second alignment check: every burst must end aligned
		if (r_increment)
		assert(axi_addr[ADDRLSB +: LGMAXBURST] + wr_writes_pending
			<= (1<<LGMAXBURST));
	end

	always @(posedge i_clk)
	if (phantom_start)
	begin
		assert(axi_awlen == $past(r_max_burst[7:0]) - 8'd1);
		if (r_increment && (cmd_length_w > axi_awlen + 1)
			&&(aw_requests_remaining != cmd_length_w))
			assert(M_AXI_AWADDR[ADDRLSB +: LGMAXBURST] == 0);
	end

	//
	// ...
	//

	// }}}

	//
	// Synchronization properties
	// {{{
	always @(*)
	if (fifo_full || !clk_active)
	begin
		assert(!sskd_ready);
	end else if (OPT_TREADY_WHILE_IDLE)
	begin
		// If we aren't full, and we set TREADY whenever idle,
		// then we should otherwise have TREADY set at all times
		assert(sskd_ready);
	end else if (!tlast_syncd)
	begin
		// If we aren't syncd, always be ready until we finally sync up
		assert(sskd_ready);
	end else if (reset_fifo)
	begin
		// If we aren't accepting any data, but are idling with TREADY
		// low, then make sure we drop TREADY when idle
		assert(!sskd_ready);
	end else
		// In all other cases, assert TREADY
		assert(sskd_ready);


	//
	// ...
	//
	// }}}

	//
	// Error logic checking
	// {{{
	always @(*)
	if (!r_err)
	begin
		assert(r_errcode == 0);
	end else
		assert(r_errcode != 0);

	//
	// ...
	//

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN) && $past(w_cmd_start)
		&&!$past(overflow && r_continuous))
		assert(!r_err);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// 1. All data values must get sent, and none skipped
	//	Captured in logic above, since M_AXI_WDATA is registered
	//	within the FIFO and not our interface
	//
	// 2. No addresses skipped.
	// ...
	//

	// 3. If we aren't incrementing addresses, then our current address
	//	should always be the axi address
	always @(*)
	if (r_busy && !r_increment)
		assert(axi_addr == cmd_addr);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg		cvr_aborted, cvr_buserr, cvr_abort_clear;
	reg	[2:0]	cvr_continued;

	initial	{ cvr_aborted, cvr_buserr } = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ cvr_aborted, cvr_buserr } <= 0;
	else if (r_busy && !axi_abort_pending)
	begin
		if (cmd_abort && wr_writes_pending > 0)
			cvr_aborted <= 1;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			cvr_buserr <= 1;
	end

	always @(posedge i_clk)
	if (i_reset)
		cvr_abort_clear <= 1'b0;
	else if (cvr_aborted && !cvr_buserr && !cmd_abort)
	begin
		cvr_abort_clear <= 1;
	end

	always @(posedge i_clk)
	if (!i_reset)
	begin
		cover(cvr_abort_clear);
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

		//
		// Artificially force us to look for two separate runs
		if((!r_busy)&&($changed(cmd_length_w)))
			cvr_continued <= 0;
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
			cover((cmd_length_w > 5)&&(cmd_addr[11:0] == 12'hff0));
			cover(&cvr_continued && (cmd_length_w > 5));
		end
	end
	// }}}

	// This ends our formal property set
`endif
	// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
