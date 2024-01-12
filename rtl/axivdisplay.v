////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axivdisplay
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Reads from memory for the purposes of serving a video frame
// {{{
//		buffer.  The result of this core is an AXI stream having the
//	word size of the memory interface in the first place.  TLAST is set
//	based upon the end of the frame, and TUSER based upon the end of the
//	line.  An option exists to use Xilinx's encoding instead where TLAST
//	is the end of the line and TUSER is the first pixel word of the frame.
//
//	This core is in many ways similar to the AXI MM2S core, but with some
//	key differences: The AXI MM2S core generates a single transfer.  This
//	core generates a repeating set of transfers--one per line, repeated
//	per frame.
//
//	To insure high bandwidth, data is first copied into a FIFO of twice
//	the width of the longest burst.
//
// }}}
// Registers:
// {{{
//   0:	FBUF_CONTROL and status
//	bit 0: START(1)/STOP(0)
//		Command the core to start by writing a '1' to this bit.  It
//		will then remain busy/active until either you tell it to halt,
//		or an error occurrs.
//	bit 1: BUSY
//	bit 2: ERR
//		If the core receives a bus error, it assumes it has been
//		inappropriately set up, sets this error bit and then halts.
//		It will not start again until this bit is cleared.  Only a
//		write to the control register with the ERR bit set will clear
//		it.  (Don't do this unless you know what caused it to halt ...)
//	bit 3: DIRTY
//		If you update core parameters while it is running, the busy
//		bit will be set.  This bit is an indication that the current
//		configuration doesn't necessarily match the one you are reading
//		out.  To clear DIRTY, deactivate the core, wait for it to be
//		no longer busy, and then start it again.  This will also start
//		it under the new configuration so the two match.
//
//   2:	FBUF_LINESTEP
//		Controls the distance from one line to the next.  This is the
//		value added to the address of the beginning of the line to get
//		to the beginning of the next line.  This should nominally be
//		equal to the number of bytes per line, although it doesn't
//		need to be.
//
//		Any attempt to set this value to zero will simply copy the
//		number of data bytes per line into this value.
//
//   4:	FBUF_LINEBYTES
//		This is the number of data bytes necessary to capture all of
//		the video data in a line.  This value must be more than zero
//		in order to activate the core.
//
//		At present, this core can only handle a number of bytes aligned
//		with the word size of the bus.
//
//   6:	FBUF_NUMLINES
//		The number of lines of active video data in a frame.  This
//		number must be greater than zero in order to activate and
//		operate the core.
//
//   8:	FBUF_ADDRESS
//		The is the first address of video data in memory.  Each frame
//		will start reading from this address.
//
//  12:	(reserved for the upper FBUF_ADDRESS)
//
//  BUGS:
//	1. Memory reads are currently allowed to wrap around the end of memory.
//	I'm not (yet) sure if this is a good thing or a bad thing.  I mean, its
//	a great thing for small dedicated memories designated for this purpose
//	alone, but perhaps a bad thing if the memory space is shared with
//	peripherals as well as a CPU.
//
//	2. I'd still like to add an option to handle  memory addresses that
//	aren't aligned.  Until that is done, the means of interacting with the
//	core will change from one implementation to another.
//
//	3. If the configuration changes mid-write, but without de-activating
//	the core and waiting for it to come to idle, the synchronization flags
//	might out-of-sync with the pixels.  To resolve, deactivate the core and
//	let it come to whenever changing configuration parameters.
// }}}
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
//
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
module	axivdisplay #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		//
		// We support five 32-bit AXI-lite registers, requiring 5-bits
		// of AXI-lite addressing
		localparam	C_AXIL_ADDR_WIDTH = 4,
		localparam	C_AXIL_DATA_WIDTH = 32,
		//
		// The bottom ADDRLSB bits of any AXI address are subword bits
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3,
		localparam	AXILLSB = $clog2(C_AXIL_DATA_WIDTH)-3,
		//
		// OPT_UNALIGNED: Allow unaligned accesses, address requests
		// and sizes which may or may not match the underlying data
		// width.  If set, the core will quietly align these requests.
		// parameter [0:0]	OPT_UNALIGNED = 1'b0,
		//
		// OPT_LGMAXBURST
		parameter	OPT_LGMAXBURST = 8,
		//
		parameter [0:0]	DEF_ACTIVE_ON_RESET = 0,
		parameter [15:0] DEF_LINES_PER_FRAME = 1024,
		parameter [16-ADDRLSB-1:0] DEF_WORDS_PER_LINE  = (1280 * 32)/C_AXI_DATA_WIDTH,
		//
		// DEF_FRAMEADDR: the default AXI address of the frame buffer
		// containing video memory.  Unless OPT_UNALIGNED is set, this
		// should be aligned so that DEF_FRAMEADDR[ADDRLSB-1:0] == 0.
		parameter [C_AXI_ADDR_WIDTH-1:0] DEF_FRAMEADDR = 0,
		//
		// The (log-based two of  the) size of the FIFO in words.
		// I like to set this to the size of two AXI bursts, so that
		// while one is being read out the second can be read in.  Can
		// also be set larger if desired.
		parameter	LGFIFO = OPT_LGMAXBURST+1,
		//
		// AXI_ID is the ID we will use for all of our AXI transactions
		parameter	AXI_ID = 0,
		//
		// OPT_TUSER_IS_SOF.  Xilinx and I chose different stream
		// encodings.  I encode TLAST== VLAST and
		// TUSER == (optional) HLAST.  Xilinx chose TLAST == HLAST
		// and TUSER == SOF(start of frame).  Set OPT_TUSER_IS_SOF to
		// use Xilinx's encoding.
		parameter [0:0]	OPT_TUSER_IS_SOF = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		// The video stream interface
		// {{{
		output	wire					M_AXIS_TVALID,
		input	wire					M_AXIS_TREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		M_AXIS_TDATA,
		output	wire	/* VLAST or HLAST */		M_AXIS_TLAST,
		output	wire	/* HLAST or SOF */		M_AXIS_TUSER,
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
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Core logic implementation
	// {{{
	// Local parameter declarations
	// {{{
	localparam [1:0]	FBUF_CONTROL	= 2'b00,
				FBUF_FRAMEINFO	= 2'b01,
				FBUF_ADDRLO	= 2'b10,
				FBUF_ADDRHI	= 2'b11;

	localparam		CBIT_ACTIVE	= 0,
				CBIT_BUSY	= 1,
				CBIT_ERR	= 2,
				CBIT_DIRTY	= 3;

	localparam	TMPLGMAXBURST=(LGFIFO-1 > OPT_LGMAXBURST)
					? OPT_LGMAXBURST : LGFIFO-1;

	localparam	LGMAXBURST = (TMPLGMAXBURST+ADDRLSB > 12)
				? (12-ADDRLSB) : TMPLGMAXBURST;
	// }}}

	wire	i_clk   =  S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	// Signal declarations
	// {{{
	reg				soft_reset, r_err, r_stopped;
	reg				cfg_active, cfg_zero_length, cfg_dirty;
	reg	[C_AXI_ADDR_WIDTH-1:0]	cfg_frame_addr;
	reg	[15:0]			cfg_frame_lines, cfg_line_step;
	reg	[16-ADDRLSB-1:0]	cfg_line_words;

	// FIFO signals
	wire				reset_fifo, write_to_fifo,
					read_from_fifo;
	wire	[C_AXI_DATA_WIDTH-1:0]	write_data;
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
	reg	[C_AXIL_DATA_WIDTH-1:0]	w_status_word;
	reg	[2*C_AXIL_DATA_WIDTH-1:0]	wide_address, new_wideaddr;
	wire	[C_AXIL_DATA_WIDTH-1:0]	new_cmdaddrlo, new_cmdaddrhi;
	reg	[C_AXIL_DATA_WIDTH-1:0]	wide_config;
	wire	[C_AXIL_DATA_WIDTH-1:0]	new_config;

	// reg				partial_burst_requested;
	// reg	[LGMAXBURST-1:0]	addralign;
	// reg	[LGFIFO:0]		rd_uncommitted;
	// reg	[LGMAXBURST:0]		initial_burstlen;
	// reg	[LGLENWA-1:0]		rd_reads_remaining;
	// reg				rd_none_remaining,
	//				rd_last_remaining;

	// wire				realign_last_valid;

	reg	axi_arvalid, lag_start, phantom_start, start_burst,
		ar_none_outstanding;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_araddr;
	reg	[LGMAXBURST:0]		max_burst;
	reg	[7:0]			axi_arlen;
	reg	[15:0]			ar_bursts_outstanding;
	//
	wire				vlast, hlast;
	reg	[15:0]			r_frame_lines, r_line_step;
	reg	[16-ADDRLSB-1:0]	r_line_words;

	reg				req_hlast, req_vlast;
	reg	[15:0]			req_nlines;
	reg	[16-ADDRLSB-1:0]	req_line_words;
	reg	[C_AXI_ADDR_WIDTH:0]	req_addr, req_line_addr;
	//
	reg				rd_hlast, rd_vlast;
	reg	[15:0]			rd_lines;
	reg	[16-ADDRLSB-1:0]	rd_line_beats;
	wire				no_fifo_space_available;
	//
	reg	[LGMAXBURST-1:0]	till_boundary;
	reg	[LGFIFO:0]		fifo_space_available;


`ifdef	FORMAL
	reg	[C_AXI_ADDR_WIDTH:0]	f_rd_line_addr, f_rd_addr;
`endif

	wire	M_AXIS_VLAST, M_AXIS_HLAST;
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

	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
		.i_data(S_AXIL_AWADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
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
	skidbuffer #(.OPT_OUTREG(0), .DW(C_AXIL_ADDR_WIDTH-AXILLSB))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
		.i_data(S_AXIL_ARADDR[C_AXIL_ADDR_WIDTH-1:AXILLSB]),
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
	// soft_reset,  r_err
	// {{{
	initial	soft_reset = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		soft_reset <= 1;
		r_err  <= 0;
	end else if (soft_reset)
	begin

		if ((axil_write_ready && awskd_addr == FBUF_CONTROL)
				&& wskd_strb[0] && wskd_data[CBIT_ERR])
			r_err <= cfg_zero_length;

		if (cfg_active && !r_err && r_stopped)
			soft_reset <= 0;

	end else // if (!soft_reset)
	begin
		// Halt on any bus error.  We'll require user intervention
		// to start back up again
		if (M_AXI_RREADY && M_AXI_RVALID && M_AXI_RRESP[1])
		begin
			soft_reset <= 1;
			r_err  <= 1;
		end

		// Halt on any user request
		if (!cfg_active)
			soft_reset <= 1;
	end
	// }}}

	// wide_* and new_* write setup registers
	// {{{
	always @(*)
	begin
		wide_address = 0;
		wide_address[C_AXI_ADDR_WIDTH-1:0] = cfg_frame_addr;
		wide_address[ADDRLSB-1:0] = 0;

		wide_config  = { cfg_frame_lines, cfg_line_words,
					{(ADDRLSB){1'b0}} };
	end

	assign	new_cmdaddrlo = apply_wstrb(
			wide_address[C_AXIL_DATA_WIDTH-1:0],
			wskd_data, wskd_strb);

	generate if (C_AXI_ADDR_WIDTH > 32)
	begin : GEN_LARGE_AW

		assign	new_cmdaddrhi = apply_wstrb(
			wide_address[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH],
			wskd_data, wskd_strb);

	end else begin : GEN_SINGLE_WORD_AW

		assign	new_cmdaddrhi = 0;

	end endgenerate


	wire	[C_AXIL_DATA_WIDTH-1:0]	new_control;
	assign	new_control = apply_wstrb(w_status_word, wskd_data, wskd_strb);
	assign	new_config  = apply_wstrb(wide_config, wskd_data, wskd_strb);

	always @(*)
	begin
		new_wideaddr = wide_address;

		if (awskd_addr == FBUF_ADDRLO)
			new_wideaddr[C_AXIL_DATA_WIDTH-1:0] = new_cmdaddrlo;
		if (awskd_addr == FBUF_ADDRHI)
			new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH] = new_cmdaddrhi;
		new_wideaddr[ADDRLSB-1:0] = 0;
		new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH] = 0;
	end
	// }}}

	// Configuration registers (Write)
	// {{{
	initial	cfg_active      = 0;
	initial	cfg_frame_addr  = DEF_FRAMEADDR;
	initial	cfg_frame_addr[ADDRLSB-1:0] = 0;
	initial	cfg_line_words = DEF_WORDS_PER_LINE;
	initial	cfg_frame_lines = DEF_LINES_PER_FRAME;
	initial	cfg_zero_length = (DEF_WORDS_PER_LINE == 0)
				||(DEF_LINES_PER_FRAME == 0);
	always @(posedge i_clk)
	if (i_reset)
	begin
		cfg_active	<= DEF_ACTIVE_ON_RESET;
		cfg_frame_addr	<= DEF_FRAMEADDR;
		cfg_line_words	<= DEF_WORDS_PER_LINE;
		cfg_line_step	<= { DEF_WORDS_PER_LINE, {(ADDRLSB){1'b0}} };
		cfg_frame_lines	<= DEF_LINES_PER_FRAME;
		cfg_zero_length <= (DEF_WORDS_PER_LINE==0)
			||(DEF_LINES_PER_FRAME == 0);
		cfg_dirty <= 0;
	end else begin
		if (r_stopped)
			cfg_dirty <= 0;
		if (cfg_active && req_hlast && req_vlast && phantom_start)
			cfg_dirty <= 0;
		if (M_AXI_RREADY && M_AXI_RVALID && M_AXI_RRESP[1])
			cfg_active <= 0;

		if (axil_write_ready)
		case(awskd_addr)
		FBUF_CONTROL: begin
			if (wskd_strb[0])
				cfg_active <= wskd_data[CBIT_ACTIVE]
					&& (!r_err || wskd_data[CBIT_ERR])
					&& (!cfg_zero_length);

			if (new_control[31:16] == 0)
			begin
				cfg_line_step <= 0;
				cfg_line_step[16-1:ADDRLSB] <= cfg_line_words;
				// Verilator lint_off WIDTH
				cfg_dirty <= (cfg_line_step
					!= (cfg_line_words << ADDRLSB));
				// Verilator lint_on  WIDTH
			end else begin
				cfg_line_step <= new_control[31:16];
				cfg_dirty <= (cfg_line_step != new_control[31:16]);
			end end
		FBUF_FRAMEINFO: begin
			{ cfg_frame_lines, cfg_line_words }
				<= new_config[C_AXI_DATA_WIDTH-1:ADDRLSB];
			cfg_zero_length <= (new_config[31:16] == 0)
					||(new_config[15:ADDRLSB] == 0);
			if ((new_config[31:16] == 0)
					||(new_config[15:ADDRLSB] == 0))
				cfg_active <= 0;
			cfg_dirty <= 1;
			end
		FBUF_ADDRLO, FBUF_ADDRHI: begin
			cfg_frame_addr <= new_wideaddr[C_AXI_ADDR_WIDTH-1:0];
			cfg_dirty <= 1;
			end
		default: begin end
		endcase
	end
	// }}}

	// AXI-Lite read register data
	// {{{
	always @(*)
	begin
		w_status_word = 0;
		w_status_word[31:16]		= cfg_line_step;
		w_status_word[CBIT_DIRTY]	= cfg_dirty;
		w_status_word[CBIT_ERR]		= r_err;
		w_status_word[CBIT_BUSY]	= !soft_reset;
		w_status_word[CBIT_ACTIVE]	= cfg_active || (!soft_reset || !r_stopped);
	end

	always @(posedge i_clk)
	if (!axil_read_valid || S_AXIL_RREADY)
	begin
		axil_read_data <= 0;
		case(arskd_addr)
		FBUF_CONTROL:	axil_read_data <= w_status_word;
		FBUF_FRAMEINFO:	axil_read_data <= { cfg_frame_lines,
					cfg_line_words, {(ADDRLSB){1'b0}} };
		FBUF_ADDRLO:	axil_read_data <= wide_address[C_AXIL_DATA_WIDTH-1:0];
		FBUF_ADDRHI:	axil_read_data <= wide_address[2*C_AXIL_DATA_WIDTH-1:C_AXIL_DATA_WIDTH];
		default		axil_read_data <= 0;
		endcase
	end
	// }}}

	// apply_wstrb function for applying wstrbs to register words
	// {{{
	function [C_AXIL_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXIL_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXIL_DATA_WIDTH-1:0]		new_data;
		input	[C_AXIL_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
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
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	// {{{
	assign	reset_fifo = r_stopped;

	assign	write_to_fifo  = M_AXI_RVALID;
	assign	write_data = M_AXI_RDATA;
	// assign	realign_last_valid = 0;
	assign	vlast = rd_vlast;
	assign	hlast = rd_hlast;
	assign	M_AXI_RREADY  = !fifo_full;
	// }}}

	generate if (LGFIFO > 0)
	begin : GEN_SPACE_AVAILBLE
		// Here's where  we'll put the actual outgoing FIFO
		// {{{
		initial	fifo_space_available = (1<<LGFIFO);
		always @(posedge i_clk)
		if (reset_fifo)
			fifo_space_available <= (1<<LGFIFO);
		else case({phantom_start, read_from_fifo && !fifo_empty })
		2'b00: begin end
		// Verilator lint_off WIDTH
		2'b10: fifo_space_available <= fifo_space_available - (M_AXI_ARLEN+1);
		2'b11: fifo_space_available <= fifo_space_available - (M_AXI_ARLEN);
		// Verilator lint_on  WIDTH
		2'b01: fifo_space_available <= fifo_space_available + 1;
		endcase

		assign	M_AXIS_TVALID  = !fifo_empty;
		assign	read_from_fifo = M_AXIS_TVALID && M_AXIS_TREADY;

		sfifo #(.BW(C_AXI_DATA_WIDTH+2), .LGFLEN(LGFIFO))
		sfifo(i_clk, reset_fifo,
			write_to_fifo, { vlast && hlast, hlast, write_data },
				fifo_full, fifo_fill,
			read_from_fifo, { M_AXIS_VLAST, M_AXIS_HLAST,
				M_AXIS_TDATA }, fifo_empty);

		assign no_fifo_space_available = (fifo_space_available < (1<<LGMAXBURST));
		// }}}
	end else begin : NO_FIFO
		// {{{
		assign	fifo_full  = !M_AXIS_TREADY;
		assign	fifo_fill  = 0;
		assign	fifo_empty = !M_AXIS_TVALID;
		assign	M_AXIS_TVALID = write_to_fifo;

		assign	M_AXIS_VLAST = vlast && hlast;
		assign	M_AXIS_HLAST = hlast;
		assign	M_AXIS_TDATA = M_AXI_RDATA;

		assign no_fifo_space_available = (ar_bursts_outstanding >= 3);
		// }}}
	end endgenerate
	// }}}

	// Switch between TLAST/TUSER encodings if necessary
	// {{{
	generate if (OPT_TUSER_IS_SOF)
	begin : XILINX_ENCODING

		reg	SOF;

		initial	SOF = 1'b1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || r_stopped)
			SOF <= 1'b1;
		else if (M_AXIS_TVALID && M_AXIS_TREADY)
			SOF <= M_AXIS_VLAST;

		assign	M_AXIS_TLAST = M_AXIS_HLAST;
		assign	M_AXIS_TUSER = SOF;

	end else begin : VLAST_EQUALS_TLAST

		assign	M_AXIS_TLAST = M_AXIS_VLAST;
		assign	M_AXIS_TUSER = M_AXIS_HLAST;
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outoing frame address counting
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// {{{
	always @(posedge  i_clk)
	if (i_reset || r_stopped || (phantom_start && req_hlast && req_vlast))
	begin
		r_frame_lines <= cfg_frame_lines;
		r_line_words  <= cfg_line_words;
		r_line_step   <= { {(ADDRLSB){1'b0}}, cfg_line_step[15:ADDRLSB] };
	end

	initial	req_addr = 0;
	initial	req_line_addr = 0;
	always @(posedge  i_clk)
	if (i_reset || r_stopped)
	begin
		req_addr       <= { 1'b0, cfg_frame_addr };
		req_line_addr  <= { 1'b0, cfg_frame_addr };
		req_line_words <= cfg_line_words;
	end else if (phantom_start)
	begin
		if (req_hlast && req_vlast)
		begin
			req_addr       <= { 1'b0, cfg_frame_addr };
			req_line_addr  <= { 1'b0, cfg_frame_addr };
			req_line_words <= cfg_line_words;
		end else if (req_hlast)
		begin
			// verilator lint_off WIDTH
			req_addr <= req_line_addr
					+ (r_line_step << M_AXI_ARSIZE);
			req_line_addr  <= req_line_addr
					+ (r_line_step << M_AXI_ARSIZE);
			// verilator lint_on  WIDTH
			req_line_words <= r_line_words;
		end else begin
			// verilator lint_off WIDTH
			req_addr <= req_addr + (1<<(LGMAXBURST+ADDRLSB));
			req_line_words <= req_line_words - (M_AXI_ARLEN+1);
			// verilator lint_on  WIDTH

			req_addr[LGMAXBURST+ADDRLSB-1:0] <= 0;
		end
	end

	always @(posedge  i_clk)
	if (i_reset || r_stopped)
	begin
		req_nlines <= cfg_frame_lines-1;
		req_vlast <= (cfg_frame_lines <= 1);
	end else if (phantom_start && req_hlast)
	begin
		if (req_vlast)
		begin
			req_nlines <= cfg_frame_lines-1;
			req_vlast <= (cfg_frame_lines <= 1);
		end else begin
			req_nlines <= req_nlines - 1;
			req_vlast <= (req_nlines <= 1);
		end
	end
`ifdef	FORMAL
	always @(*)
	if (!r_stopped)
	begin
		assert(req_vlast == (req_nlines == 0));
		assert(req_addr >= { 1'b0, cfg_frame_addr });
		assert(req_line_addr >= { 1'b0, cfg_frame_addr });
		assert(req_line_addr <= req_addr);
	end

	always @(*)
	if (cfg_active)
	begin
		assert(cfg_frame_lines != 0);
		assert(cfg_line_words  != 0);
	end

	always @(*)
	if (!r_stopped)
	begin
		assert(r_frame_lines != 0);
		assert(r_line_words  != 0);
	end
`endif

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming frame address counting
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_stopped)
	begin
		rd_line_beats <= cfg_line_words-1;
		rd_hlast <= (cfg_line_words == 1);
	end else if (M_AXI_RVALID && M_AXI_RREADY)
	begin
		if (rd_hlast)
		begin
			rd_line_beats <= r_line_words - 1;
			rd_hlast <= (r_line_words <= 1);
		end else begin
			rd_line_beats <= rd_line_beats - 1;
			rd_hlast <= (rd_line_beats <= 1);
		end
	end

	always @(posedge i_clk)
	if (i_reset || r_stopped)
	begin
		rd_lines <= cfg_frame_lines-1;
		rd_vlast <= (cfg_frame_lines == 1);
	end else if (M_AXI_RVALID && M_AXI_RREADY && rd_hlast)
	begin
		if (vlast)
		begin
			rd_lines <= r_frame_lines - 1;
			rd_vlast <= (r_frame_lines <= 1);
		end else begin
			rd_lines <= rd_lines - 1;
			rd_vlast <= (rd_lines <= 1);
		end
	end

`ifdef	FORMAL
	always @(posedge i_clk)
	if (i_reset || r_stopped)
	begin
		f_rd_addr      <= { 1'b0, cfg_frame_addr };
		f_rd_line_addr <= { 1'b0, cfg_frame_addr };
	end else if (M_AXI_RVALID && M_AXI_RREADY)
	begin
		if (rd_vlast && rd_hlast)
		begin
			f_rd_addr <= cfg_frame_addr;
			f_rd_line_addr <= cfg_frame_addr;
		end else if (rd_hlast)
		begin
			f_rd_addr <= f_rd_line_addr + (r_line_step << M_AXI_ARSIZE);
			f_rd_line_addr <= f_rd_line_addr + (r_line_step << M_AXI_ARSIZE);
		end else begin
			f_rd_addr <= f_rd_addr + (1<<ADDRLSB);
		end
	end
`endif

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

	// ar_bursts_outstanding
	// {{{
	// Count the number of bursts outstanding--these are the number of
	// ARVALIDs that have been accepted, but for which the RVALID && RLAST
	// has not (yet) been returned.
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

	// r_stopped
	// {{{
	// Following an error or drop of cfg_active, soft_reset will go high.
	// We then come to a stop once everything becomes inactive
	initial	r_stopped = 1;
	always @(posedge  i_clk)
	if (i_reset)
		r_stopped <= 1;
	else if (r_stopped)
		r_stopped <= soft_reset || !cfg_active;
	else if (soft_reset && ar_none_outstanding && !M_AXI_ARVALID)
		r_stopped <= 1;
	// }}}

	// }}}

	//
	// start_burst
	// {{{
	always @(*)
	begin
		start_burst = 1;
		if (no_fifo_space_available)
			start_burst = 0;
		if (phantom_start || lag_start)
			// Insist on a minimum of two clocks between burst
			// starts, so we can get our lengths right
			start_burst = 0;

		// Can't start a new burst if the outgoing channel is still
		// stalled.
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			start_burst = 0;

		// If the user wants us to stop, then stop
		if (!cfg_active || soft_reset)
			start_burst  = 0;
	end
	// }}}

	// ARLEN
	// {{{
	// Coming in, req_addr and req_line_words can be trusted
	// lag_start will be true to reflect this
	always @(posedge i_clk)
	if (lag_start)
	begin
		if (req_line_words >= (1<<LGMAXBURST))
			max_burst <= (1<<LGMAXBURST);
		else
			// Verilator lint_off WIDTH
			max_burst <= req_line_words;
			// Verilator lint_on  WIDTH
	end

	always @(*)
		till_boundary = ~req_addr[ADDRLSB +: LGMAXBURST];

	always @(posedge i_clk)
	if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		// Verilator lint_off WIDTH
		if (till_boundary > 0 && max_burst <= till_boundary)
			axi_arlen <= max_burst-1;
		// Verilator lint_on  WIDTH
		else
			axi_arlen <= till_boundary;
	end
	// }}}

	// req_hlast
	// {{{
	always @(posedge i_clk)
	if (lag_start || start_burst)
	begin
		req_hlast <= 1;
		// Verilator lint_off WIDTH
		if (req_line_words > till_boundary+1)
			req_hlast <= 0;
		if (req_line_words > max_burst)
			req_hlast <= 0;
		// Verilator lint_on  WIDTH
	end

`ifdef	FORMAL
	always @(*)
	if (phantom_start)
	begin
		if (req_hlast)
		begin
			assert(axi_arlen+1 == req_line_words);
		end else
			assert(axi_arlen+1 < req_line_words);
	end else if (!soft_reset && !r_stopped && !lag_start)
	begin
		if (max_burst != req_line_words)
		begin
			assert(!req_hlast);
		end else if (!req_hlast && !M_AXI_ARVALID)
			assert(axi_arlen < max_burst);

		assert(max_burst > 0);
		if (req_line_words > (1<<LGMAXBURST))
		begin
			assert(max_burst == (1<<LGMAXBURST));
		end else
			assert(max_burst == req_line_words);
	end
`endif
	// }}}

	// phantom_start
	// {{{
	initial	phantom_start = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_start <= 0;
	else
		phantom_start <= start_burst;

	initial	lag_start = 1;
	always @(posedge i_clk)
	if (i_reset || r_stopped)
		lag_start <= 1;
	else
		lag_start <= phantom_start;
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

	// ARADDR
	// {{{
	initial	axi_araddr = 0;
	always @(posedge i_clk)
	begin
		if (start_burst)
			axi_araddr <= req_addr[C_AXI_ADDR_WIDTH-1:0];

		axi_araddr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// Set the constant M_AXI_* signals
	// {{{
	assign	M_AXI_ARVALID= axi_arvalid;
	assign	M_AXI_ARID   = AXI_ID;
	assign	M_AXI_ARADDR = axi_araddr;
	assign	M_AXI_ARLEN  = axi_arlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_ARSIZE = $clog2(C_AXI_DATA_WIDTH)-3;
	// Verilator lint_on  WIDTH
	assign	M_AXI_ARBURST= 2'b01;	// INCR
	assign	M_AXI_ARLOCK = 0;
	assign	M_AXI_ARCACHE= 0;
	assign	M_AXI_ARPROT = 0;
	assign	M_AXI_ARQOS  = 0;
	// }}}

	// End AXI protocol section
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_RID,
			M_AXI_RRESP[0], fifo_full, wskd_strb[2:0],
			S_AXIL_AWADDR[AXILLSB-1:0], S_AXIL_ARADDR[AXILLSB-1:0],
			new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH],
			new_control, new_config, fifo_fill };
	// Verilator lint_on  UNUSED
	// }}}
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// The following are only a subset of the formal properties currently
	// being used to verify this module.  They are not expected to be
	// syntactically accurate.
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
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

	always @(*)
		assert(cfg_zero_length ==
			((cfg_line_words == 0)||(cfg_frame_lines == 0)));

	always @(*)
	if (cfg_zero_length)
		assert(!cfg_active);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI master memory interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	localparam	F_AXI_LGDEPTH = 11; // LGLENW-LGMAXBURST+2 ??

	//
	// ...
	//

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		//
		// ...
		//
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// The (unused) write interface
		// {{{
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
		// }}}
		// The read interface
		// {{{
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
		.i_axi_rresp( M_AXI_RRESP),
		// ...
		// }}}
	);


	//
	// ...
	//
	always @(*)
	begin
		// ...

		assert(M_AXI_ARBURST == 2'b01);
	end

	always @(*)
	if (faxi_rd_ckvalid)
	begin
		assert(!r_stopped);
		//
		// ...
		//
	end

	//
	// ...
	//

	reg	[LGMAXBURST-1:0]	f_rd_subaddr;
	always @(*)
		f_rd_subaddr = f_rd_addr[ADDRLSB +: LGMAXBURST];

	always @(*)
	begin
		assert(cfg_frame_addr[ADDRLSB-1:0] == 0);
		if (!r_stopped)
		begin
			assert(req_addr[ADDRLSB-1:0] == 0);
			assert(req_line_addr[ADDRLSB-1:0] == 0);
		end

		if (M_AXI_RVALID)
			assert(M_AXI_RLAST == (rd_hlast || (&f_rd_subaddr)));
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read request to return address correlations
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

		if (M_AXI_RVALID)
		begin
			if (rd_hlast || (&f_rd_subaddr))
			begin
				// ...
				assert(M_AXI_RLAST);
			end else
				// ...
				assume(!M_AXI_RLAST);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Other formal properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg	cvr_full_frame, cvr_full_size;
	(* anyconst *) reg cvr_hlast_rlast;

	always @(posedge i_clk)
	if (r_stopped)
		cvr_full_size <= (cfg_line_step >= cfg_line_words)
				&&(cfg_line_words > 5)
				&&(cfg_frame_lines > 4);
	else begin
		if ($changed(cfg_line_step))
			cvr_full_size <= 0;
		if ($changed(cfg_line_words))
			cvr_full_size <= 0;
		if ($changed(cfg_frame_lines))
			cvr_full_size <= 0;
		if ($changed(cfg_frame_addr))
			cvr_full_size <= 0;
	end

	always @(posedge i_clk)
	if (r_stopped || !cvr_full_size)
		cvr_full_frame <= 0;
	else if (!cvr_full_frame)
		cvr_full_frame <= rd_vlast && rd_hlast && M_AXI_RVALID && M_AXI_RREADY;

	always @(*)
		cover(!soft_reset);

	always @(*)
		cover(start_burst);

	always @(*)
		cover(M_AXI_ARVALID && M_AXI_ARREADY);

	always @(*)
		cover(M_AXI_RVALID);

	always @(*)
		cover(M_AXI_RVALID & M_AXI_RLAST);

	always @(*)
		cover(!r_stopped && cvr_full_frame);

	always @(*)
		cover(cvr_full_frame && phantom_start && !r_stopped);

	always @(*)
	if (cvr_hlast_rlast)
	begin
		// assume(M_AXI_RLAST == (rd_hlast && M_AXI_RVALID));
		assume(M_AXI_ARREADY && M_AXI_RREADY);
		assume(M_AXIS_TREADY);
		assume(cfg_frame_addr[12:0] == 0);
		assume(cfg_line_step[3:0] == 0);
	end

	always @(*)
		cover(cvr_hlast_rlast && cvr_full_frame && phantom_start && !r_stopped);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Simplifying (careless) assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (!r_stopped || cfg_active)
	begin
		assume($stable(cfg_frame_addr));
		assume($stable(cfg_frame_lines));
		assume($stable(cfg_line_words));
		assume($stable(cfg_line_step));
	end


	always @(*)
		assume(!f_sequential);

	always @(*)
		assume(!f_biglines);

	always @(*)
		assume(!req_addr[C_AXI_ADDR_WIDTH]);

	always @(*)
		assume(!req_line_addr[C_AXI_ADDR_WIDTH]);
	// }}}
	// }}}
`endif
endmodule
