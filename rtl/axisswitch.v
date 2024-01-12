////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axisswitch.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Switch from among several AXI streams based upon an AXI-lite
//		controlled index.  All streams must have the same width.
//	The switch will use TLAST to guarantee that it will not change
//	mid-packet.  If TLAST is unused for a particular input, simply set it
//	to 1'b1.
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
module	axisswitch #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have a single configuration words.
		parameter	C_AXI_ADDR_WIDTH = 2,
		localparam	C_AXI_DATA_WIDTH = 32,
		//
		parameter	NUM_STREAMS = 4,
		parameter	C_AXIS_DATA_WIDTH = 32,
		parameter [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		// AXI-Lite control
		// {{{
		input	wire					S_AXI_AWVALID,
		output	wire					S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		output	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		output	wire	[1:0]				S_AXI_BRESP,
		//
		input	wire					S_AXI_ARVALID,
		output	wire					S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		//
		output	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_RDATA,
		output	wire	[1:0]				S_AXI_RRESP,
		// }}}
		// AXI stream inputs to be switched
		// {{{
		input	wire	[NUM_STREAMS-1:0]		S_AXIS_TVALID,
		output	wire	[NUM_STREAMS-1:0]		S_AXIS_TREADY,
		input wire [NUM_STREAMS*C_AXIS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		input	wire	[NUM_STREAMS-1:0]		S_AXIS_TLAST,
		// }}}
		// AXI stream output result
		// {{{
		output	reg					M_AXIS_TVALID,
		input	wire					M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]		M_AXIS_TDATA,
		output	reg					M_AXIS_TLAST
		// }}}
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam	LGNS = $clog2(NUM_STREAMS);
	localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3;

	wire	i_reset = !S_AXI_ARESETN;

	wire				axil_write_ready;
	wire	[0:0]			awskd_addr;	// UNUSED
	//
	wire	[C_AXI_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				axil_read_ready;
	wire	[0:0]			arskd_addr;	// UNUSED
	reg	[C_AXI_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	reg	[LGNS-1:0]		r_index;
	wire	[31:0]			wskd_index;

	genvar	gk;
	reg	[NUM_STREAMS-1:0]	skd_switch_ready;
	reg	[LGNS-1:0]		switch_index;
	wire	[C_AXIS_DATA_WIDTH-1:0]	skd_data	[0:NUM_STREAMS-1];
	wire	[NUM_STREAMS-1:0]	skd_valid, skd_last;
	reg				mid_packet, r_mid_packet;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	//
	// {{{

	wire	awskd_valid, wskd_valid;

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER), .DW(1))
	axilawskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
		.i_data(1'b0),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data(awskd_addr));

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8))
	axilwskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
		.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));

	assign	axil_write_ready = awskd_valid && wskd_valid
			&& (!S_AXI_BVALID || S_AXI_BREADY);

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXI_BREADY)
		axil_bvalid <= 0;

	assign	S_AXI_BVALID = axil_bvalid;
	assign	S_AXI_BRESP = 2'b00;
	// }}}

	//
	// Read signaling
	//
	// {{{

	wire	arskd_valid;

	skidbuffer #(.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(1))
	axilarskid(//
		.i_clk(S_AXI_ACLK), .i_reset(i_reset),
		.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
		.i_data(1'b0),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data(arskd_addr));

	assign	axil_read_ready = arskd_valid
				&& (!axil_read_valid || S_AXI_RREADY);

	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (S_AXI_RREADY)
		axil_read_valid <= 1'b0;

	assign	S_AXI_RVALID = axil_read_valid;
	assign	S_AXI_RDATA  = axil_read_data;
	assign	S_AXI_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// apply_wstrb(old_data, new_data, write_strobes)
	// r_index, (wskd_index)
	// {{{
	assign	wskd_index = apply_wstrb(
		{ {(C_AXI_DATA_WIDTH-LGNS){1'b0}}, r_index },
		wskd_data, wskd_strb);

	// r_index
	initial	r_index = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		r_index <= 0;
	else if (axil_write_ready)
		r_index <= wskd_index[LGNS-1:0];
	// }}}

	// axil_read_data
	// {{{
	initial	axil_read_data = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		axil_read_data <= 0;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		axil_read_data <= 0;
		axil_read_data[LGNS-1:0] <= r_index;

		if (OPT_LOWPOWER && !axil_read_ready)
			axil_read_data <= 0;
	end
	// }}}

	// function apply_wstrb
	// {{{
	function [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXI_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXI_DATA_WIDTH-1:0]		new_data;
		input	[C_AXI_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXI_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The actual AXI switch
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Place a skidbuffer on every incoming stream input
	// {{{
	generate for(gk=0; gk<NUM_STREAMS; gk=gk+1)
	begin
		skidbuffer #(
			// {{{
			.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXIS_DATA_WIDTH+1)
			// }}}
		) skdswitch(//
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXIS_TVALID[gk]),.o_ready(S_AXIS_TREADY[gk]),
			.i_data({ S_AXIS_TDATA[gk*C_AXIS_DATA_WIDTH
				+: C_AXIS_DATA_WIDTH], S_AXIS_TLAST[gk] }),
			.o_valid(skd_valid[gk]), .i_ready(skd_switch_ready[gk]),
			.o_data({ skd_data[gk], skd_last[gk] })
			// }}}
		);

		
	end endgenerate
	// }}}

	// skd_switch_ready
	// {{{
	always @(*)
	begin
		skd_switch_ready = (1<<switch_index);
		if (M_AXIS_TVALID && !M_AXIS_TREADY)
			skd_switch_ready = 0;
		if (!mid_packet && r_index != switch_index)
			skd_switch_ready = 0;
	end
	// }}}

	// mid_packet -- are we currently within a packet or not
	// {{{
	initial	r_mid_packet = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_mid_packet <= 0;
	else if (M_AXIS_TVALID)
		r_mid_packet <= !M_AXIS_TLAST;

	always @(*)
	if (M_AXIS_TVALID)
		mid_packet = !M_AXIS_TLAST;
	else
		mid_packet = r_mid_packet;
	// }}}

	// switch_index -- the current index of the skidbuffer switch
	// {{{
	initial	switch_index = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		switch_index <= 0;
	else if (!mid_packet)
		switch_index <= r_index;
	// }}}

	// M_AXIS_TVALID
	// {{{
	initial	M_AXIS_TVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 1'b0;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
		M_AXIS_TVALID <= |(skd_valid & skd_switch_ready);
	// }}}

	// M_AXIS_TDATA, M_AXIS_TLAST
	// {{{
	initial	M_AXIS_TDATA = 0;
	initial	M_AXIS_TLAST = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
	begin
		M_AXIS_TDATA <= 0;
		M_AXIS_TLAST <= 0;
	end else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		M_AXIS_TDATA <= skd_data[switch_index];
		M_AXIS_TLAST <= skd_last[switch_index];

		if (OPT_LOWPOWER && (skd_valid | skd_switch_ready) == 0)
		begin
			M_AXIS_TDATA <= 0;
			M_AXIS_TLAST <= 0;
		end
	end
	// }}}
	
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
			S_AXI_ARADDR[ADDRLSB-1:0], awskd_addr, arskd_addr,
			S_AXI_AWADDR[ADDRLSB-1:0], wskd_index };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awprot( S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arprot( S_AXI_ARPROT),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rresp( S_AXI_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
	);

	always @(*)
	begin
		assert(faxil_awr_outstanding== (S_AXI_BVALID ? 1:0)
			+(S_AXI_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0)
			+(S_AXI_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(S_AXI_ARREADY ? 0:1));
	end

	always @(*)
		assert(S_AXI_RDATA[C_AXI_DATA_WIDTH-1:LGNS] == 0);

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN
			&& axil_read_ready))
	begin
		assert(S_AXI_RVALID);
		assert(S_AXI_RDATA[LGNS-1:0] == $past(r_index));
	end

	//
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXI_RVALID)
		assert(S_AXI_RDATA == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NUM_STREAMS; gk=gk+1)
	begin : S_STREAM_ASSUMPTIONS

		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || $past(!S_AXI_ARESETN))
			assume(S_AXIS_TVALID[gk] == 0);
		else if ($past(S_AXIS_TVALID[gk] && !S_AXIS_TREADY[gk]))
		begin
			assume(S_AXIS_TVALID[gk]);
			assume($stable(S_AXIS_TDATA[gk*C_AXIS_DATA_WIDTH +: C_AXIS_DATA_WIDTH]));
			assume($stable(S_AXIS_TLAST[gk]));
		end
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!M_AXIS_TVALID);
	else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
	end

	always @(*)
	if (OPT_LOWPOWER && !M_AXIS_TVALID)
	begin
		assert(M_AXIS_TDATA == 0);
		assert(M_AXIS_TLAST == 0);
	end

	(* anyconst *) reg [LGNS-1:0]		f_const_index;
	(* anyconst *) reg [C_AXIS_DATA_WIDTH-1:0] f_never_data;
		reg	[LGNS-1:0]		f_this_index;
		reg	[3:0]			f_count, f_recount;
		reg		f_accepts, f_delivers;

	always @(*)
		assume(f_const_index < NUM_STREAMS);

	// f_this_index
	// {{{
	initial	f_this_index = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_this_index <= 1'b0;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
		f_this_index <= switch_index;

	always @(*)
		assert(f_this_index < NUM_STREAMS);

	always @(*)
		assert(switch_index < NUM_STREAMS);
	// }}}

	// f_count
	// {{{
	always @(*)
	begin
		f_accepts = S_AXIS_TVALID[f_const_index]
					&& S_AXIS_TREADY[f_const_index];
		f_delivers = M_AXIS_TVALID && M_AXIS_TREADY
					&& f_this_index == f_const_index;
	end

	initial	f_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_count <= 0;
	else case( { f_accepts, f_delivers })
	2'b01: f_count <= f_count - 1;
	2'b10: f_count <= f_count + 1;
	default: begin end
	endcase
	// }}}

	// f_count induction
	// {{{
	always @(*)
	begin
		f_recount = 0;
		if (!S_AXIS_TREADY[f_const_index])
			f_recount = 1;
		if (M_AXIS_TVALID && f_this_index == f_const_index)
			f_recount = f_recount + 1;

		assert(f_recount == f_count);
	end
	// }}}

	// f_this_index induction
	always @(*)
	if (M_AXIS_TVALID && !M_AXIS_TLAST)
		assert(f_this_index == switch_index);

	// assume != f_never_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID[f_const_index])
		assume({ S_AXIS_TDATA[f_const_index * C_AXIS_DATA_WIDTH +: C_AXIS_DATA_WIDTH], S_AXIS_TLAST[f_const_index] } != f_never_data);
	// }}}

	// Never data induction
	// {{{
	always @(*)
	begin
		if (skd_valid[f_const_index])
			assert({ skd_data[f_const_index], skd_last[f_const_index] } != f_never_data);
		if (M_AXIS_TVALID && f_this_index == f_const_index)
			assert({ M_AXIS_TDATA, M_AXIS_TLAST } != f_never_data);
	end
	// }}}

	
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// While there are already cover properties in the formal property
	// set above, you'll probably still want to cover something
	// application specific here

	// }}}
`endif
	// }}}
endmodule
