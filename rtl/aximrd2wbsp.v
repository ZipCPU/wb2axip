////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximrd2wbsp.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Bridge an AXI read channel pair to a single wishbone read
//		channel.
//
// Rules:
// 	1. Any read channel error *must* be returned to the correct
//		read channel ID.  In other words, we can't pipeline between IDs
//	2. A FIFO must be used on getting a WB return, to make certain that
//		the AXI return channel is able to stall with no loss
//	3. No request can be accepted unless there is room in the return
//		channel for it
//
// Status:	Passes a formal bounded model check at 15 steps.  Should be
//		ready for a hardware check.
//
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
`default_nettype	none
// }}}
module	aximrd2wbsp #(
		// {{{
		parameter C_AXI_ID_WIDTH	= 6, // The AXI id width used for R&W
	                                             // This is an int between 1-16
		parameter C_AXI_DATA_WIDTH	= 32,// Width of the AXI R&W data
		parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
		localparam AXI_LSBS		= $clog2(C_AXI_DATA_WIDTH/8),
		localparam AW			= C_AXI_ADDR_WIDTH - AXI_LSBS,
		parameter LGFIFO                =  3,
		parameter [0:0] OPT_SWAP_ENDIANNESS = 1'b0,
		parameter [0:0] OPT_SIZESEL	= 1
		// parameter	WBMODE		= "B4PIPELINE"
		// Could also be "BLOCK"
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK,	// Bus clock
		input	wire			S_AXI_ARESETN,	// Bus reset
		// AXI
		// {{{
		// AXI read address channel signals
		input	wire			S_AXI_ARVALID,
		output	wire			S_AXI_ARREADY,
		input wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[7:0]		S_AXI_ARLEN,
		input	wire	[2:0]		S_AXI_ARSIZE,
		input	wire	[1:0]		S_AXI_ARBURST,
		input	wire	[0:0]		S_AXI_ARLOCK,
		input	wire	[3:0]		S_AXI_ARCACHE,
		input	wire	[2:0]		S_AXI_ARPROT,
		input	wire	[3:0]		S_AXI_ARQOS,

		// AXI read data channel signals
		output	reg			S_AXI_RVALID,
		input	wire			S_AXI_RREADY,
		output	wire [C_AXI_ID_WIDTH-1:0] S_AXI_RID,
		output	wire [C_AXI_DATA_WIDTH-1:0] S_AXI_RDATA,
		output	wire 			S_AXI_RLAST,
		output	reg [1:0]		S_AXI_RRESP,
		// }}}
		// Wishbone channel
		// {{{
		// We'll share the clock and the reset
		output	reg				o_wb_cyc,
		output	reg				o_wb_stb,
		output	reg [(AW-1):0]			o_wb_addr,
		output	wire [(C_AXI_DATA_WIDTH/8-1):0]	o_wb_sel,
		input	wire				i_wb_stall,
		input	wire				i_wb_ack,
		input	wire [(C_AXI_DATA_WIDTH-1):0]	i_wb_data,
		input	wire				i_wb_err
		// }}}
		// }}}
	);

	// Register/net definitions
	// {{{
	wire				w_reset;

	wire				lastid_fifo_full, lastid_fifo_empty,
					resp_fifo_full, resp_fifo_empty;
	wire	[LGFIFO:0]		lastid_fifo_fill, resp_fifo_fill;


	reg				last_stb, last_ack, err_state;
	reg	[C_AXI_ID_WIDTH-1:0]	axi_id;
	reg	[7:0]			stblen;

	wire				skid_arvalid;
	wire	[C_AXI_ID_WIDTH-1:0]	skid_arid;//    r_id;
	wire	[C_AXI_ADDR_WIDTH-1:0]	skid_araddr;//  r_addr;
	wire	[7:0]			skid_arlen;//   r_len;
	wire	[2:0]			skid_arsize;//  r_size;
	wire	[1:0]			skid_arburst;// r_burst;
	reg				fifo_nearfull;
	wire				accept_request;

	reg	[1:0]			axi_burst;
	reg	[2:0]			axi_size;
	reg	[C_AXI_DATA_WIDTH/8-1:0] axi_strb;
	reg	[7:0]			axi_len;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_addr;
	wire	[C_AXI_ADDR_WIDTH-1:0]	next_addr;
	wire				response_err;
	wire				lastid_fifo_wr;
	reg				midissue, wb_empty;
	reg	[LGFIFO+7:0]		acks_expected;

	reg	[C_AXI_DATA_WIDTH-1:0]	read_data;

	assign	w_reset = (S_AXI_ARESETN == 1'b0);
	// }}}

	// incoming skidbuffer
	// {{{
	skidbuffer #(
		.OPT_OUTREG(0),
		.DW(C_AXI_ID_WIDTH + C_AXI_ADDR_WIDTH + 8 + 3 + 2)
	) axirqbuf(S_AXI_ACLK, !S_AXI_ARESETN,
		S_AXI_ARVALID, S_AXI_ARREADY,
			{ S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN,
			  S_AXI_ARSIZE, S_AXI_ARBURST },
		skid_arvalid, accept_request,
			{ skid_arid, skid_araddr, skid_arlen,
			  skid_arsize, skid_arburst });
	// }}}

	// accept_request
	// {{{
	assign	accept_request = (!err_state)
			&&((!o_wb_cyc)||(!i_wb_err))
			// &&(!lastid_fifo_full)
			&&(!midissue
				||(o_wb_stb && last_stb && !i_wb_stall))
			&&(skid_arvalid)
			// One ID at a time, lest we return a bus error
			// to the wrong AXI master
			&&(wb_empty ||(skid_arid == axi_id));
	// }}}

	// o_wb_cyc, o_wb_stb, stblen, last_stb
	// {{{
	initial o_wb_cyc        = 0;
	initial o_wb_stb        = 0;
	initial stblen          = 0;
	initial last_stb        = 0;
	always @(posedge S_AXI_ACLK)
	if (w_reset)
	begin
		o_wb_stb <= 1'b0;
		o_wb_cyc <= 1'b0;
	end else if (err_state || (o_wb_cyc && i_wb_err))
	begin
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
	end else if ((!o_wb_stb)||(!i_wb_stall))
	begin
		if (accept_request)
		begin
			// Process the new request
			o_wb_cyc <= 1'b1;
			if (lastid_fifo_full && (!S_AXI_RVALID||!S_AXI_RREADY))
				o_wb_stb <= 1'b0;
			else if (fifo_nearfull && midissue
				&& (!S_AXI_RVALID||!S_AXI_RREADY))
				o_wb_stb <= 1'b0;
			else
				o_wb_stb <= 1'b1;
		end else if (!o_wb_stb && midissue)
		begin
			// Restart a transfer once the FIFO clears
			if (S_AXI_RVALID)
				o_wb_stb <= S_AXI_RREADY;
		// end else if ((o_wb_cyc)&&(i_wb_err)||(err_state))
		end else if (o_wb_stb && !last_stb)
		begin
			if (fifo_nearfull
				&& (!S_AXI_RVALID||!S_AXI_RREADY))
				o_wb_stb <= 1'b0;
		end else if (!o_wb_stb || last_stb)
		begin
			// End the request
			o_wb_stb <= 1'b0;

			// Check for the last acknowledgment
			if ((i_wb_ack)&&(last_ack))
				o_wb_cyc <= 1'b0;
			if (i_wb_err)
				o_wb_cyc <= 1'b0;
		end
	end
	// }}}

	// stblen, last_stb, midissue
	// {{{
	initial	stblen   = 0;
	initial	last_stb = 0;
	initial	midissue = 0;
	always @(posedge S_AXI_ACLK)
	if (w_reset)
	begin
		stblen   <= 0;
		last_stb <= 0;
		midissue <= 0;
	end else if (accept_request)
	begin
		stblen   <= skid_arlen;
		last_stb <= (skid_arlen == 0);
		midissue <= 1'b1;
	end else if (lastid_fifo_wr)
	begin
		if (stblen > 0)
			stblen <= stblen - 1;
		last_stb <= (stblen == 1);
		midissue <= (stblen > 0);
	end
	// }}}

	// axi_id, axi_burst, axi_size, axi_len
	// {{{
	initial	axi_size = AXI_LSBS[2:0];
	initial	axi_strb = -1;
	always @(posedge S_AXI_ACLK)
	if (accept_request)
	begin
		axi_id    <= skid_arid;
		axi_burst <= skid_arburst;
		axi_size  <= skid_arsize;
		axi_len   <= skid_arlen;

		if (OPT_SIZESEL)
			axi_strb  <= (1<<(1<<(skid_arsize)))-1;
		else
			axi_strb  <= { (C_AXI_DATA_WIDTH/8){1'b1} };
	end
`ifdef	FORMAL
	always @(*)
	case(axi_size)
	0: assert(axi_strb == 1);
	1: assert((C_AXI_DATA_WIDTH >   8) && (axi_strb ==  2'b11));
	2: assert((C_AXI_DATA_WIDTH >  16) && (axi_strb ==  4'b1111));
	3: assert((C_AXI_DATA_WIDTH >  32) && (axi_strb ==  8'hff));
	4: assert((C_AXI_DATA_WIDTH >  64) && (axi_strb ==  16'hffff));
	5: assert((C_AXI_DATA_WIDTH > 128) && (axi_strb ==  32'hffff_ffff));
	6: assert((C_AXI_DATA_WIDTH > 256) && (axi_strb == 64'hffff_ffff_ffff_ffff));
	default: assert((C_AXI_DATA_WIDTH == 1024) && (&axi_strb));
	endcase
`endif
	// }}}

	// next_addr
	// {{{
	axi_addr #(.AW(C_AXI_ADDR_WIDTH), .DW(C_AXI_DATA_WIDTH))
	next_read_addr(axi_addr, axi_size, axi_burst, axi_len, next_addr);
	// }}}

	// {{{
	always @(posedge S_AXI_ACLK)
	if (accept_request)
		axi_addr <= skid_araddr;
	else if (!i_wb_stall)
		axi_addr <= next_addr;
	// }}}

	always @(*)
		o_wb_addr = axi_addr[(C_AXI_ADDR_WIDTH-1):C_AXI_ADDR_WIDTH-AW];

	// o_wb_sel
	// {{{
	generate if (OPT_SIZESEL && C_AXI_DATA_WIDTH > 8)
	begin : MULTI_BYTE_SEL
		// {{{
		assign o_wb_sel = axi_strb << axi_addr[AXI_LSBS-1:0];
		// }}}
	end else begin : FULL_WORD_SEL
		assign	o_wb_sel = {(C_AXI_DATA_WIDTH/8){1'b1}};

		// Verilator lint_off UNUSED
		wire	unused_sel;
		assign	unused_sel = &{ 1'b0, axi_strb };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// lastid_fifo
	// {{{
	assign	lastid_fifo_wr = (o_wb_stb && (i_wb_err || !i_wb_stall))
			||(err_state && midissue && !lastid_fifo_full);

	sfifo #(.BW(C_AXI_ID_WIDTH+1), .LGFLEN(LGFIFO))
	lastid_fifo(S_AXI_ACLK, w_reset,
		lastid_fifo_wr,
		{ axi_id, last_stb },
		lastid_fifo_full, lastid_fifo_fill,
		S_AXI_RVALID && S_AXI_RREADY,
		{ S_AXI_RID, S_AXI_RLAST },
		lastid_fifo_empty);
	// }}}

	// read_data
	// {{{
	generate if (OPT_SWAP_ENDIANNESS)
	begin : SWAP_ENDIANNESS
		integer	ik;

		// AXI is little endian.  WB can be either.  Most of my WB
		// work is big-endian.
		//
		// This will convert byte ordering between the two
		always @(*)
		for(ik=0; ik<C_AXI_DATA_WIDTH/8; ik=ik+1)
			read_data[ik*8 +: 8]
				= i_wb_data[(C_AXI_DATA_WIDTH-(ik+1)*8) +: 8];

	end else begin : KEEP_ENDIANNESS

		always @(*)
			read_data = i_wb_data;

	end endgenerate
	// }}}

	// resp_fifo
	// {{{
	sfifo #(.BW(C_AXI_DATA_WIDTH+1), .LGFLEN(LGFIFO))
	resp_fifo(S_AXI_ACLK, w_reset,
		o_wb_cyc && (i_wb_ack || i_wb_err), { read_data, i_wb_err },
		resp_fifo_full, resp_fifo_fill,
		S_AXI_RVALID && S_AXI_RREADY,
		{ S_AXI_RDATA, response_err },
		resp_fifo_empty);
	// }}}

	// acks_expected
	// {{{
	// Count the number of acknowledgements we are still expecting.  This
	// is to support the last_ack calculation in the next process
	initial	acks_expected = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || err_state)
		acks_expected <= 0;
	else case({ accept_request, o_wb_cyc && i_wb_ack })
	2'b01:	acks_expected <= acks_expected -1;
	2'b10:	acks_expected <= acks_expected+({{(LGFIFO){1'b0}},skid_arlen} + 1);
	2'b11:	acks_expected <= acks_expected+{{(LGFIFO){1'b0}},skid_arlen};
	default: begin end
	endcase
	// }}}

	// last_ack
	// {{{
	// last_ack should be true if the next acknowledgment will end the bus
	// cycle
	initial	last_ack = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || err_state)
		last_ack <= 1;
	else case({ accept_request, i_wb_ack })
	2'b01:	last_ack <= (acks_expected <= 2);
	2'b10:	last_ack <= (acks_expected == 0)&&(skid_arlen == 0);
	2'b11:	last_ack <= (acks_expected < 2)&&(skid_arlen < 2)
				&&(!acks_expected[0]||!skid_arlen[0]);
	default: begin end
	endcase
	// }}}

	// fifo_nearfull
	// {{{
	initial	fifo_nearfull = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fifo_nearfull <= 1'b0;
	else case({ lastid_fifo_wr, S_AXI_RVALID && S_AXI_RREADY })
	2'b10: fifo_nearfull <= (lastid_fifo_fill >= (1<<LGFIFO)-2);
	2'b01: fifo_nearfull <= lastid_fifo_full;
	default: begin end
	endcase
	// }}}

	// wb_empty
	// {{{
	initial	wb_empty = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !o_wb_cyc)
		wb_empty <= 1'b1;
	else case({ lastid_fifo_wr, (i_wb_ack || i_wb_err) })
	2'b10: wb_empty <= 1'b0;
	2'b01: wb_empty <= (lastid_fifo_fill == resp_fifo_fill + 1);
	default: begin end
	endcase
	// }}}

	// S_AXI_RRESP, S_AXI_RVALID
	// {{{
	always @(*)
	begin
		S_AXI_RRESP[0] = 1'b0;
		S_AXI_RRESP[1] = response_err || (resp_fifo_empty && err_state);


		S_AXI_RVALID = !resp_fifo_empty
			|| (err_state && !lastid_fifo_empty);
	end
	// }}}

	// err_state
	// {{{
	initial	err_state = 0;
	always @(posedge S_AXI_ACLK)
	if (w_reset)
		err_state <= 1'b0;
	else if ((o_wb_cyc)&&(i_wb_err))
		err_state <= 1'b1;
	else if (lastid_fifo_empty && !midissue)
		err_state <= 1'b0;
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_ARLOCK, S_AXI_ARCACHE,
			S_AXI_ARPROT, S_AXI_ARQOS, resp_fifo_full };
	// verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
//
// The following are the formal properties used to verify this core.
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// The following are a subset of the properties used to verify this
	// core.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	DW = C_AXI_DATA_WIDTH;

	reg	f_past_valid;
	initial f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(w_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Ad-hoc assertions
	//
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Error state
	//
	//
	always @(*)
	if (err_state)
		assert(!o_wb_stb && !o_wb_cyc);

	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	//
	//

	localparam	F_LGDEPTH = (LGFIFO>8) ? LGFIFO+1 : 10, F_LGRDFIFO = 72; // 9*F_LGFIFO;
	//
	// ...
	//
	wire	[(F_LGDEPTH-1):0]
			fwb_nreqs, fwb_nacks, fwb_outstanding;

	fwb_master #(.AW(AW), .DW(C_AXI_DATA_WIDTH), .F_MAX_STALL(2),
		.F_MAX_ACK_DELAY(3), .F_LGDEPTH(F_LGDEPTH),
		.F_OPT_DISCONTINUOUS(1))
		fwb(S_AXI_ACLK, w_reset,
			o_wb_cyc, o_wb_stb, 1'b0, o_wb_addr, {(DW){1'b0}}, 4'hf,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			fwb_nreqs, fwb_nacks, fwb_outstanding);

	always @(*)
	if (err_state)
		assert(fwb_outstanding == 0);


	faxi_slave	#(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.F_LGDEPTH(F_LGDEPTH),
		.F_AXI_MAXSTALL(0),
		.F_AXI_MAXDELAY(0)
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		.i_axi_awready(1'b0),
		.i_axi_awaddr(0),
		.i_axi_awlen(8'h0),
		.i_axi_awsize(3'h0),
		.i_axi_awburst(2'h0),
		.i_axi_awlock(1'b0),
		.i_axi_awcache(4'h0),
		.i_axi_awprot(3'h0),
		.i_axi_awqos(4'h0),
		.i_axi_awvalid(1'b0),
		//
		.i_axi_wready(1'b0),
		.i_axi_wdata(0),
		.i_axi_wstrb(0),
		.i_axi_wlast(0),
		.i_axi_wvalid(1'b0),
		//
		.i_axi_bid(0),
		.i_axi_bresp(0),
		.i_axi_bvalid(1'b0),
		.i_axi_bready(1'b0),
		//
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_arid(S_AXI_ARID),
		.i_axi_araddr(S_AXI_ARADDR),
		.i_axi_arlen(S_AXI_ARLEN),
		.i_axi_arsize(S_AXI_ARSIZE),
		.i_axi_arburst(S_AXI_ARBURST),
		.i_axi_arlock(S_AXI_ARLOCK),
		.i_axi_arcache(S_AXI_ARCACHE),
		.i_axi_arprot(S_AXI_ARPROT),
		.i_axi_arqos(S_AXI_ARQOS),
		.i_axi_arvalid(S_AXI_ARVALID),
		//
		.i_axi_rresp(S_AXI_RRESP),
		.i_axi_rid(S_AXI_RID),
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rdata(S_AXI_RDATA),
		.i_axi_rlast(S_AXI_RLAST),
		.i_axi_rready(S_AXI_RREADY)
		//
		// ...
		//
			);

	//
	// ...
	//

	always @(*)
	if (!resp_fifo_empty && response_err)
		assert(resp_fifo_fill == 1);

	always @(*)
		assert(midissue == ((stblen > 0)||(last_stb)));

	always @(*)
	if (last_stb && !err_state)
		assert(o_wb_stb || lastid_fifo_full);

	always @(*)
	if (last_stb)
		assert(stblen == 0);

	always @(*)
	if (lastid_fifo_full)
	begin
		assert(!o_wb_stb);
		assert(!lastid_fifo_wr);
	end

	always @(*)
	if (!err_state)
	begin
		if (midissue && !last_stb)
			assert(!last_ack);

		assert(lastid_fifo_fill - resp_fifo_fill
			== fwb_outstanding);

		if (fwb_outstanding > 1)
			assert(!last_ack);
		else if (fwb_outstanding == 1)
			assert(midissue || last_ack);
		else if (o_wb_cyc) // && (fwb_outstanding ==0)
			assert(last_ack == last_stb);

		if (midissue)
			assert(o_wb_cyc);
	end

	// wb_empty
	// {{{
	always @(*)
	if (o_wb_cyc)
		assert(wb_empty == (lastid_fifo_fill == resp_fifo_fill));
	// }}}

	// !o_wb_cyc, if nothing pending
	// {{{
	always @(*)
	if ((fwb_nacks == fwb_nreqs)&&(!midissue))
		assert(!o_wb_cyc);
	// }}}

	always @(*)
		assert(fwb_outstanding <= (1<<LGFIFO));

	// fifo_nearfull
	// {{{
	always @(*)
		assert(fifo_nearfull == (lastid_fifo_fill >= (1<<LGFIFO)-1));
	// }}}

	always @(*)
	if (o_wb_stb)
		assert(last_ack == (last_stb&& wb_empty));//&&(!i_wb_stall);
	else if (o_wb_cyc && !midissue)
		assert(last_ack == (resp_fifo_fill + 1 >= lastid_fifo_fill));

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg [3:0]	cvr_reads, cvr_read_bursts, cvr_rdid_bursts;
	reg [C_AXI_ID_WIDTH-1:0]	cvr_read_id;

	// cvr_reads
	// {{{
	initial	cvr_reads = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_reads <= 1;
	else if (i_wb_err)
		cvr_reads <= 0;
	else if (S_AXI_RVALID && S_AXI_RREADY && !cvr_reads[3]
			&& cvr_reads > 0)
		cvr_reads <= cvr_reads + 1;
	// }}}

	// cvr_read_bursts
	// {{{
	initial	cvr_read_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_read_bursts <= 1;
	else if (S_AXI_ARVALID && S_AXI_ARLEN < 1)
		cvr_read_bursts <= 0;
	else if (i_wb_err)
		cvr_read_bursts <= 0;
	else if (S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST
			&& !cvr_read_bursts[3] && cvr_read_bursts > 0)
		cvr_read_bursts <= cvr_read_bursts + 1;
	// }}}

	// cvr_read_id
	// {{{
	initial	cvr_read_id = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_read_id <= 1;
	else if (S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST)
		cvr_read_id <= cvr_read_id + 1;
	// }}}

	// cvr_rdid_bursts
	// {{{
	initial	cvr_rdid_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_rdid_bursts <= 1;
	else if (S_AXI_ARVALID && S_AXI_ARLEN < 1)
		cvr_rdid_bursts <= 0;
	else if (i_wb_err)
		cvr_rdid_bursts <= 0;
	else if (S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST
			&& S_AXI_RID == cvr_read_id
			&& !cvr_rdid_bursts[3] && cvr_rdid_bursts > 0)
		cvr_rdid_bursts <= cvr_rdid_bursts + 1;
	// }}}

	always @(*)
		cover(cvr_reads == 4);

	always @(*)
		cover(cvr_read_bursts == 4);

	always @(*)
		cover(cvr_rdid_bursts == 4);
	// }}}
`endif
// }}}
endmodule
