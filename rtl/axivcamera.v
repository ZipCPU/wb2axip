////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axivcamera
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Reads a video frame from a source and writes the result to
//		memory.
//
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
//	bits 15-8: FRAMES
//		Indicates the number of frames you want to copy.  Set this to
//		0 to continuously copy, or a finite number to grab only that
//		many frames.
//
//		As a feature, this isn't perhaps the most useful, since every
//		frame will be written to the same location.  A more useful
//		approach would be to increase the desired number of lines to
//		(NLINES * NFRAMES), and then to either leave this number at zero
//		or set it to one.
//
//   2:	FBUF_LINESTEP
//		Controls the distance from one line to the next.  This is the
//		value added to the address of the beginning of the line to get
//		to the beginning of the next line.  This should nominally be
//		equal to the number of bytes per line, although it doesn't
//		need to be.
//
//		Any attempt to set this value to zero will simply copy the
//		number of data bytes per line (rounded down to the neareset
//		word) into this value.  This is a recommended approach to
//		setting this value.
//
//   4:	FBUF_LINEBYTES
//		This is the number of data bytes necessary to capture all of
//		the video data in a line.  This value must be more than zero
//		in order to activate the core.
//
//		At present, this core can only handle a number of bytes aligned
//		with the word size of the bus.  To convert from bytes to words,
//		round any fractional part upwards (i.e. ceil()).  The core
//		will naturally round down internally.
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
// KNOWN ISSUES:
//
//	Does not support interlacing (yet).  (Interlacing is not on my "todo"
//	  list, so it might take a while to get said support if you need it.)
//
//	Does not support unaligned addressing.  The frame buffer address, and
//	  the line step, must all be word aligned.  While nothing is stopping
//	  me from supporting unaligned addressing, it was such a pain to do the
//	  last time that I might just hold off until I have a paying customer
//	  who wants it.
//
//	Line bytes that include a fraction of a word are rounded down and not
//	  up.
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
`default_nettype none
// }}}
module	axivcamera #(
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
		parameter	OPT_LGFIFO = OPT_LGMAXBURST+1,
		localparam	LGFIFO = (OPT_LGFIFO < OPT_LGMAXBURST+1)
						? OPT_LGMAXBURST+1 : OPT_LGFIFO,
		//
		// AXI_ID is the ID we will use for all of our AXI transactions
		parameter	AXI_ID = 0,
		//
		// OPT_IGNORE_HLAST
		parameter [0:0]	OPT_IGNORE_HLAST = 0,
		//
		// OPT_TUSER_IS_SOF.  Xilinx and I chose different encodings.
		// I encode TLAST == VLAST, and TUSER == HLAST (optional).
		// Xilinx likes TLAST == HLAST and TUSER == SOF (start of frame)
		// Set OPT_TUSER_IS_SOF to use Xilinx's encoding
		parameter [0:0]	OPT_TUSER_IS_SOF = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		// The incoming video stream data/pixel interface
		// {{{
		input	wire					S_AXIS_TVALID,
		output	wire					S_AXIS_TREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXIS_TDATA,
		input	wire	/* VLAST */			S_AXIS_TLAST,
		input	wire	/* HLAST */			S_AXIS_TUSER,
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
		// The AXI (full) write-only interface
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
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP
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
				// CBIT_DIRTY	= 3,
				CBIT_LOST_SYNC  = 4;

	localparam	TMPLGMAXBURST=(LGFIFO-1 > OPT_LGMAXBURST)
					? OPT_LGMAXBURST : LGFIFO-1;

	localparam	LGMAXBURST = (TMPLGMAXBURST+ADDRLSB > 12)
				? (12-ADDRLSB) : TMPLGMAXBURST;
	// }}}

	wire	i_clk   =  S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	// Signal declarations
	// {{{
	reg				soft_reset, r_err, r_stopped, lost_sync;
	reg				cfg_active, cfg_zero_length,
					cfg_continuous;
	reg	[C_AXI_ADDR_WIDTH-1:0]	cfg_frame_addr;
	reg	[15:0]			cfg_frame_lines, cfg_line_step;
	reg	[16-ADDRLSB-1:0]	cfg_line_words;

	// FIFO signals
	wire				reset_fifo, write_to_fifo,
					read_from_fifo;
	wire	[C_AXI_DATA_WIDTH-1:0]	write_data, fifo_data;
	wire	[LGFIFO:0]		fifo_fill;
	wire				fifo_full, fifo_empty,
					fifo_vlast, fifo_hlast;

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

	reg	axi_awvalid, axi_wvalid, axi_wlast,
					phantom_start, start_burst,
					aw_none_outstanding;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	reg	[7:0]			axi_awlen, next_awlen;
	reg	[8:0]			wr_pending;
	reg	[15:0]			aw_bursts_outstanding;
	//
	// reg				vlast;
	// reg	[15:0]			r_frame_lines, r_line_step;
	reg	[16-ADDRLSB-1:0]	next_line_words;

	reg				req_hlast, req_vlast, req_newline;
	reg	[15:0]			req_nlines;
	reg	[7:0]			req_nframes;
	reg	[16-ADDRLSB-1:0]	req_line_words;
	reg	[C_AXI_ADDR_WIDTH:0]	req_addr, req_line_addr, next_line_addr;
	//
	reg				wr_hlast, wr_vlast;
	reg	[15:0]			wr_lines;
	reg	[16-ADDRLSB-1:0]	wr_line_beats;
	// wire				no_fifo__available;
	//
	reg	[LGMAXBURST-1:0]	till_boundary;
	reg	[LGFIFO:0]		fifo_data_available;
	reg				fifo_bursts_available;
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
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// soft_reset,  r_err
	// {{{
	initial	soft_reset = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		soft_reset <= 1;
		r_err  <= 0;
	end else if (r_stopped)
	begin

		if (axil_write_ready && awskd_addr == FBUF_CONTROL
				&& wskd_strb[0] && wskd_data[CBIT_ERR])
		begin
			r_err <= cfg_zero_length;
			soft_reset <= 0;
		end

		if (!r_err)
			soft_reset <= 0;

	end else // if (!soft_reset)
	begin
		// Halt on any bus error.  We'll require user intervention
		// to start back up again
		if ((M_AXI_BVALID && M_AXI_BREADY && M_AXI_BRESP[1])
			||(req_addr[C_AXI_ADDR_WIDTH]))
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

	end else begin : SINGLE_WORD_AW

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
	initial	cfg_continuous  = 0;
	initial	cfg_frame_addr  = DEF_FRAMEADDR;
	initial	cfg_frame_addr[ADDRLSB-1:0] = 0;
	initial	cfg_line_words = DEF_WORDS_PER_LINE;
	initial	cfg_frame_lines = DEF_LINES_PER_FRAME;
	initial	cfg_zero_length = (DEF_WORDS_PER_LINE == 0)
				||(DEF_LINES_PER_FRAME == 0);
	initial	cfg_line_step	= { DEF_WORDS_PER_LINE, {(ADDRLSB){1'b0}} };
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
		req_nframes     <= 0;
		cfg_continuous  <= 0;
	end else begin
		if (phantom_start && req_vlast && req_hlast && req_nframes > 0)
			req_nframes <= req_nframes - 1;

		if (axil_write_ready)
		case(awskd_addr)
		FBUF_CONTROL: begin
			if (wskd_strb[0])
				cfg_active <= (cfg_active || r_stopped)
					&& wskd_data[CBIT_ACTIVE]
					&& (!r_err || wskd_data[CBIT_ERR])
					&& (!cfg_zero_length);

			if (!cfg_active && r_stopped && wskd_strb[1])
			begin
				req_nframes    <= wskd_data[15:8];
				cfg_continuous <= (wskd_data[15:8] == 0);
			end

			if (!cfg_active && r_stopped)
			begin
				if (new_control[31:16] == 0)
				begin
					cfg_line_step <= 0;
					cfg_line_step[16-1:ADDRLSB] <= cfg_line_words;
				end else
					cfg_line_step <= new_control[31:16];
			end end
		FBUF_FRAMEINFO:
			if (!cfg_active && r_stopped)
			begin
			{ cfg_frame_lines, cfg_line_words }
				<= new_config[C_AXIL_DATA_WIDTH-1:ADDRLSB];
			cfg_zero_length <= (new_config[31:16] == 0)
					||(new_config[15:ADDRLSB] == 0);
			end
		FBUF_ADDRLO, FBUF_ADDRHI: if (!cfg_active && r_stopped)
			cfg_frame_addr <= new_wideaddr[C_AXI_ADDR_WIDTH-1:0];
		default: begin end
		endcase

		if (M_AXI_BREADY && M_AXI_BVALID && M_AXI_BRESP[1])
			cfg_active <= 0;
		if (req_addr[C_AXI_ADDR_WIDTH])
			cfg_active <= 0;
		if (phantom_start && req_vlast && req_hlast && req_nframes <= 1
				&& !cfg_continuous)
			cfg_active <= 0;

		cfg_line_step[ADDRLSB-1:0] <= 0;
		cfg_frame_addr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// AXI-Lite read register data
	// {{{
	always @(*)
	begin
		w_status_word = 0;
		w_status_word[31:16]		= cfg_line_step;
		w_status_word[15:8]		= req_nframes;
		w_status_word[CBIT_LOST_SYNC]	= lost_sync;
		// w_status_word[CBIT_DIRTY]	= cfg_dirty;
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
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	S_AXIS_SOF, S_AXIS_HLAST, S_AXIS_VLAST;
	generate if (OPT_TUSER_IS_SOF)
	begin : XILINX_SOF_LOCK
		reg	[15:0]	axis_line;
		reg		axis_last_line;

		assign	S_AXIS_HLAST = S_AXIS_TLAST;
		assign	S_AXIS_SOF = S_AXIS_TUSER;

		//  Generate S_AXIS_VLAST from S_AXIS_SOF
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axis_line <= 0;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
		begin
			if (S_AXIS_SOF)
				axis_line <= 0;
			else if (S_AXIS_HLAST)
				axis_line <= axis_line + 1;
		end

		always @(posedge S_AXI_ACLK)
			axis_last_line <= (axis_line+1 >= cfg_frame_lines);

		assign	S_AXIS_VLAST = axis_last_line && S_AXIS_HLAST;

	end else begin : VLAST_LOCK

		assign	S_AXIS_VLAST = S_AXIS_TLAST;

		assign	S_AXIS_HLAST = S_AXIS_TUSER;

		/*
		initial	S_AXIS_SOF = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			S_AXIS_SOF <= 1'b0;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
			S_AXIS_SOF <= S_AXIS_VLAST;
		*/
		assign	S_AXIS_SOF = 1'b0;

		// Verilator lint_off UNUSED
		wire	unused_sof;
		assign	unused_sof = &{ 1'b0, S_AXIS_SOF };
		// Verilator lint_on  UNUSED
	end endgenerate

	// Read/write signaling, lost_sync detection
	// {{{
	assign	reset_fifo = (!cfg_active || r_stopped || lost_sync);

	assign	write_to_fifo  = S_AXIS_TVALID && !lost_sync && !fifo_full;
	assign	write_data = S_AXIS_TDATA;
	assign	read_from_fifo = (M_AXI_WVALID && M_AXI_WREADY);
	assign	S_AXIS_TREADY  = 1'b1;

	initial	lost_sync = 1;
	always @(posedge S_AXI_ACLK)
	begin
		if (!S_AXI_ARESETN || !cfg_active || r_stopped)
			lost_sync <= 0;
		else if (M_AXI_WVALID && M_AXI_WREADY
				&&((!OPT_IGNORE_HLAST&&(wr_hlast != fifo_hlast))
				|| (!wr_hlast && fifo_vlast)
				|| (wr_vlast && wr_hlast && !fifo_vlast)))
			// Here is where we might possibly notice we've lost sync
			lost_sync <= 1;

		// lost_sync <= 1'b0;
	end
	// }}}

	generate if (LGFIFO > 0)
	begin : GEN_SPACE_AVAILBLE
		// Here's where  we'll put the actual outgoing FIFO
		// {{{
		reg	[LGFIFO:0]	next_data_available;
		always @(*)
		begin
			next_data_available = fifo_data_available;
			// Verilator lint_off WIDTH
			if (phantom_start)
				next_data_available = fifo_data_available - (M_AXI_AWLEN + 1);
			// Verilator lint_on  WIDTH
			if (write_to_fifo)
				next_data_available = next_data_available + 1;
		end

		initial	fifo_data_available = 0;
		initial	fifo_bursts_available = 0;
		always @(posedge i_clk)
		if (reset_fifo)
		begin
			fifo_data_available <= 0;
			fifo_bursts_available <= 0;
		end else if (phantom_start || write_to_fifo)
		begin
			fifo_data_available   <=  next_data_available;
			fifo_bursts_available <= |next_data_available[LGFIFO:LGMAXBURST];
		end

		sfifo #(.BW(C_AXI_DATA_WIDTH+2), .LGFLEN(LGFIFO))
		sfifo(i_clk, reset_fifo,
			write_to_fifo, { S_AXIS_VLAST,
				(!OPT_IGNORE_HLAST && S_AXIS_HLAST),write_data},
				fifo_full, fifo_fill,
			read_from_fifo, { fifo_vlast, fifo_hlast,
				fifo_data }, fifo_empty);
		// }}}
	end else begin : NO_FIFO
		// {{{
		//
		// This isn't verified or tested.  I'm not sure I'd expect this
		// to work at all.
		assign	fifo_full  = M_AXI_WVALID && !M_AXI_WREADY;
		assign	fifo_fill  = 0;
		assign	fifo_empty = !S_AXIS_TVALID;
		assign	fifo_vlast = S_AXIS_VLAST;
		assign	fifo_hlast = (!OPT_IGNORE_HLAST && S_AXIS_HLAST);

		assign	fifo_data = write_data;
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outoing frame address counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	w_frame_needs_alignment, frame_needs_alignment,
		line_needs_alignment,
		line_multiple_bursts, req_needs_alignment, req_multiple_bursts;

	// frame_needs_alignment
	// {{{
	always @(*)
	begin
		w_frame_needs_alignment = 0;
		if (|cfg_line_words[15-ADDRLSB:LGMAXBURST])
			w_frame_needs_alignment = 1;
		if (~cfg_frame_addr[ADDRLSB +: LGMAXBURST]
				< cfg_line_words[LGMAXBURST-1:0])
			w_frame_needs_alignment = 1;
		if (cfg_frame_addr[ADDRLSB +: LGMAXBURST] == 0)
			w_frame_needs_alignment = 0;
	end

	always @(posedge i_clk)
	if (!cfg_active && r_stopped)
		frame_needs_alignment <= w_frame_needs_alignment;
	// }}}

	// line_needs_alignment
	// {{{
	always @(posedge i_clk)
	if (r_stopped)
		line_multiple_bursts <= (cfg_line_words >= (1<<LGMAXBURST));

	always @(*)
	if (!cfg_active || req_vlast)
		next_line_addr = { 1'b0, cfg_frame_addr };
	else
		next_line_addr = req_line_addr+ { {(C_AXI_ADDR_WIDTH-16){1'b0}}, cfg_line_step };

	always @(posedge i_clk)
	if (req_newline)
	begin
		line_needs_alignment <= 0;
		if (|next_line_addr[ADDRLSB +: LGMAXBURST])
		begin
			if (|cfg_line_words[15-ADDRLSB:LGMAXBURST])
				line_needs_alignment <= 1;
			if (~next_line_addr[ADDRLSB +: LGMAXBURST]
					< cfg_line_words[LGMAXBURST-1:0])
				line_needs_alignment <= 1;
		end
	end
	// }}}

	// req_addr, req_line_addr, req_line_words
	// {{{
	always @(*)
		// Verilator lint_off WIDTH
		next_line_words = req_line_words - (M_AXI_AWLEN+1);
		// Verilator lint_on  WIDTH

	initial	req_addr = 0;
	initial	req_line_addr = 0;
	always @(posedge  i_clk)
	if (i_reset || r_stopped)
	begin
		req_addr       <= { 1'b0, cfg_frame_addr };
		req_line_addr  <= { 1'b0, cfg_frame_addr };
		req_line_words <= cfg_line_words;
		req_newline    <= 1;
		req_multiple_bursts <= (cfg_line_words >= (1<<LGMAXBURST));
		req_needs_alignment <= w_frame_needs_alignment;
	end else if (phantom_start)
	begin
		req_newline <= req_hlast;
		req_needs_alignment <= 0;
		if (req_hlast && req_vlast)
		begin
			req_addr       <= { 1'b0, cfg_frame_addr };
			req_line_addr  <= { 1'b0, cfg_frame_addr };
			req_line_words <= cfg_line_words;
			req_multiple_bursts <= line_multiple_bursts;

			req_needs_alignment <= frame_needs_alignment;
		end else if (req_hlast)
		begin
			// verilator lint_off WIDTH
			req_addr <= req_line_addr + cfg_line_step;
			req_line_addr  <= req_line_addr + cfg_line_step;
			// verilator lint_on  WIDTH
			req_line_words <= cfg_line_words;
			req_needs_alignment <= line_needs_alignment;
			req_multiple_bursts <= line_multiple_bursts;
		end else begin
			req_addr <= req_addr + (1<<(LGMAXBURST+ADDRLSB));
			req_line_words <= next_line_words;
			req_multiple_bursts <= |next_line_words[15-ADDRLSB:LGMAXBURST];

			req_addr[LGMAXBURST+ADDRLSB-1:0] <= 0;
		end
	end else
		req_newline <= 0;
	// }}}

	// req_nlines, req_vlast
	// {{{
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
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing sync counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// wr_line_beats, wr_hlast
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_stopped)
	begin
		wr_line_beats <= cfg_line_words-1;
		wr_hlast <= (cfg_line_words == 1);
	end else if (M_AXI_WVALID && M_AXI_WREADY)
	begin
		if (wr_hlast)
		begin
			wr_line_beats <= cfg_line_words - 1;
			wr_hlast <= (cfg_line_words <= 1);
		end else begin
			wr_line_beats <= wr_line_beats - 1;
			wr_hlast <= (wr_line_beats <= 1);
		end
	end
	// }}}

	// wr_lines, wr_vlast
	// {{{
	always @(posedge i_clk)
	if (i_reset || r_stopped)
	begin
		wr_lines <= cfg_frame_lines-1;
		wr_vlast <= (cfg_frame_lines == 1);
	end else if (M_AXI_WVALID && M_AXI_WREADY && wr_hlast)
	begin
		if (wr_vlast)
		begin
			wr_lines <= cfg_frame_lines - 1;
			wr_vlast <= (cfg_frame_lines <= 1);
		end else begin
			wr_lines <= wr_lines - 1;
			wr_vlast <= (wr_lines <= 1);
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The outgoing AXI (full) protocol section
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Some counters to keep track of our state
	// {{{

	// aw_bursts_outstanding
	// {{{
	// Count the number of bursts outstanding--these are the number of
	// AWVALIDs that have been accepted, but for which the BVALID
	// has not (yet) been returned.
	initial	aw_none_outstanding   = 1;
	initial	aw_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		aw_bursts_outstanding <= 0;
		aw_none_outstanding <= 1;
	end else case ({ phantom_start, M_AXI_BVALID && M_AXI_BREADY })
	2'b01:	begin
			aw_bursts_outstanding <=  aw_bursts_outstanding - 1;
			aw_none_outstanding   <= (aw_bursts_outstanding == 1);
		end
	2'b10:	begin
		aw_bursts_outstanding <= aw_bursts_outstanding + 1;
		aw_none_outstanding <= 0;
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
	begin
		// Synchronize on the last pixel of an incoming frame
		if (cfg_active && S_AXIS_TVALID && S_AXIS_VLAST)
			r_stopped <= soft_reset;
	end else if ((soft_reset || lost_sync) && aw_none_outstanding
				&& !M_AXI_AWVALID && !M_AXI_WVALID)
		r_stopped <= 1;
	// }}}

	// }}}

	//
	// start_burst
	// {{{
	always @(*)
	begin
		start_burst = 1;
		if (LGFIFO > 0 && !fifo_bursts_available)
		begin
			if (!req_multiple_bursts && fifo_data_available[7:0]
							< req_line_words[7:0])
				start_burst = 0;
			if (req_multiple_bursts && !fifo_bursts_available)
				start_burst = 0;
		end

		if (phantom_start || req_newline || lost_sync)
			start_burst = 0;

		// Can't start a new burst if the outgoing channel is still
		// stalled.
		if (M_AXI_AWVALID && !M_AXI_AWREADY)
			start_burst = 0;
		if (M_AXI_WVALID && (!M_AXI_WREADY || !M_AXI_WLAST))
			start_burst = 0;

		// Don't let our aw_bursts_outstanding counter overflow
		if (aw_bursts_outstanding[15])
			start_burst = 0;

		// Don't wrap around memory
		if (req_addr[C_AXI_ADDR_WIDTH])
			start_burst = 0;

		// If the user wants us to stop, then stop
		if (soft_reset || !cfg_active || r_stopped)
			start_burst  = 0;
	end
	// }}}

	// AWLEN
	// {{{
	always @(*)
		till_boundary = ~req_addr[ADDRLSB +: LGMAXBURST];

	always @(*)
	begin
		if (req_needs_alignment)
			next_awlen = till_boundary;
		else if (req_multiple_bursts)
			next_awlen = (1<<LGMAXBURST)-1;
		else
			next_awlen = req_line_words[7:0]-1;
	end

	always @(posedge i_clk)
	if (!M_AXI_AWVALID || M_AXI_AWREADY)
		axi_awlen <= next_awlen;
	// }}}

	// wr_pending
	// {{{
	initial	wr_pending = 0;
	always @(posedge i_clk)
	begin
		if (M_AXI_WVALID && M_AXI_WREADY)
			wr_pending <= wr_pending - 1;
		if (start_burst)
			wr_pending <= next_awlen + 1;

		if (!S_AXI_ARESETN)
			wr_pending <= 0;
	end
	// }}}

	// req_hlast
	// {{{
	always @(posedge i_clk)
	// Verilator lint_off WIDTH
	if (r_stopped)
		req_hlast <= (cfg_frame_addr[ADDRLSB +: LGMAXBURST]
					+ cfg_line_words <= (1<<LGMAXBURST));
	else if (phantom_start)
	begin
		if (req_hlast && req_vlast)
			req_hlast <= (cfg_frame_addr[ADDRLSB +: LGMAXBURST]
					+ cfg_line_words <= (1<<LGMAXBURST));
		else if (req_hlast)
			req_hlast <= (next_line_addr[ADDRLSB +: LGMAXBURST]
					+ cfg_line_words <= (1<<LGMAXBURST));
		else
			req_hlast <= (req_line_words - (M_AXI_AWLEN+1)
							<= (1<<LGMAXBURST));
	// Verilator lint_on  WIDTH
	end
	// }}}

	// phantom_start
	// {{{
	initial	phantom_start = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_start <= 0;
	else
		phantom_start <= start_burst;
	// }}}

	// AWVALID
	// {{{
	initial	axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_awvalid <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		axi_awvalid <= start_burst;
	// }}}

	// ARADDR
	// {{{
	initial	axi_awaddr = 0;
	always @(posedge i_clk)
	begin
		if (start_burst)
			axi_awaddr <= req_addr[C_AXI_ADDR_WIDTH-1:0];

		axi_awaddr[ADDRLSB-1:0] <= 0;
	end
	// }}}

	// WVALID
	// {{{
	initial	axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_wvalid <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wvalid <= start_burst || (M_AXI_WVALID && !M_AXI_WLAST);
	// }}}

	// WLAST
	// {{{
	always @(posedge i_clk)
	begin
		if (M_AXI_WVALID && M_AXI_WREADY)
			axi_wlast <= (wr_pending <= 2);

		if (start_burst)
			axi_wlast <= (next_awlen == 0);
	end
	// }}}


	// Set the constant M_AXI_* signals
	// {{{
	assign	M_AXI_AWVALID= axi_awvalid;
	assign	M_AXI_AWID   = AXI_ID;
	assign	M_AXI_AWADDR = axi_awaddr;
	assign	M_AXI_AWLEN  = axi_awlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_AWSIZE = $clog2(C_AXI_DATA_WIDTH)-3;
	// Verilator lint_on  WIDTH
	assign	M_AXI_AWBURST= 2'b01;	// INCR
	assign	M_AXI_AWLOCK = 0;
	assign	M_AXI_AWCACHE= 0;
	assign	M_AXI_AWPROT = 0;
	assign	M_AXI_AWQOS  = 0;
	//
	assign	M_AXI_WVALID = axi_wvalid;
	assign	M_AXI_WLAST  = axi_wlast;
	assign	M_AXI_WDATA  = fifo_data;
	assign	M_AXI_WSTRB  = -1;
	//
	assign	M_AXI_BREADY = 1;
	// }}}

	// End AXI protocol section
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIL_AWPROT, S_AXIL_ARPROT, M_AXI_BID,
			M_AXI_BRESP[0], fifo_empty,
			S_AXIL_AWADDR[AXILLSB-1:0], S_AXIL_ARADDR[AXILLSB-1:0],
			new_wideaddr[2*C_AXIL_DATA_WIDTH-1:C_AXI_ADDR_WIDTH],
			new_control, new_config, fifo_fill, next_line_addr,
			fifo_vlast, fifo_hlast
		};
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
	// {{{

	// The formal properties for this core are maintained elsewhere

	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The formal proof for this core doesn't (yet) include a contract
	// check.

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Simplifying (careless) assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// If the FIFO gets reset, then we really don't care about what
	// gets written to memory.  However, it is possible that a value
	// on the output might get changed and so violate our protocol checker.
	// (We don't care.)  So let's just assume it never happens, and check
	// everything else instead.
	always @(*)
	if (M_AXI_WVALID)
		assume(!lost_sync && cfg_active);
	// }}}
	// }}}
`endif
endmodule
