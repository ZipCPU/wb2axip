////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilgpio
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A simple and basic AXI-lite input and output module.
//		Tristates are not supported internally, although output bits
//	may be used externally to create a tristate input.  For example, when
//	driving an I2C controller, you might wish to do something like:
//
//	assign	i2c_scl = gpio_output[1] ? 1'bz : gpio_output[1];
//	assign	i2c_sda = gpio_output[0] ? 1'bz : gpio_output[0];
//
//	Or, as another example:
//
//	assign	generic_io = gpio_output[3] ? 1'bz : gpio_output[2];
//
// Registers:
//	 0: LOAD
//		Write to this register will overwrite the output data bits.
//	 4: SET
//		Writes to this register will set every output data bit where
//		the written bit is set.
//
//		OUTPUT[k] = OLD BIT[k] || NEW_BIT[k]
//
//	 8: CLEAR
//		Writes to this register will clear every output data bit where
//		the written bit is set.
//
//		OUTPUT[k] = OLD BIT[k] && (!NEW_BIT[k])
//
//	12: TOGGLE
//		Writes to this register will toggle every output bit where
//		the bit written is set.
//
//		OUTPUT[k] = OLD BIT[k] ^ NEW_BIT[k]
//
//	The next four registers are present if (and only if) NIN > 0.  If not,
//	the prior four registers will be repeated.
//
//	16: Input data (if NIN > 0)
//		This is the input data, following a two-register CDC.
//	20: Input data toggle detection
//		A bit will be set in this register if ever the associated
//		input data bit toggles.  To clear, write a '1' to the toggled
//		bit in this register.
//
//		Bits from this register that are set will then create an
//		outgoing interrupt--provided they are not masked.
//
//	24: Input data interrupt mask
//		If any "mask" bit is set, then toggled data will not trigger
//		an interrupt.
//	28: Input data interrupts active
//		This is the AND of toggled data and a clear interrupt mask bit.
//
//	An output interrupt is generated if any of the bits in the interrupt
//	active register is high.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
module	axilgpio #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXI_ADDR_WIDTH = 5,
		localparam	C_AXI_DATA_WIDTH = 32,
		// OPT_SKIDBUFFER will increase throughput to 100% from 50%
		parameter [0:0]	OPT_SKIDBUFFER = 1'b1,
		// OPT_LOWPOWER will force RDATA to zero if ever !RVALID
		parameter [0:0]	OPT_LOWPOWER = 0,
		// NOUT : Number of output bits.  Must be > 0
		parameter	NOUT = 30,
		// NIN: Number of input bits.  May be zero if desired.
		parameter	NIN = 5,
		parameter [NOUT-1:0]	DEFAULT_OUTPUT = 0
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		// AXI-lite interface
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
		output	wire	[NOUT-1:0]			o_gpio,
		input	wire	[((NIN>0) ? (NIN-1):0):0]	i_gpio,
		output	wire					o_int
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3;
	localparam	[2:0]	// ADDR_LOAD   = 3'b000,
				// ADDR_SET    = 3'b001,
				// ADDR_CLEAR  = 3'b010,
				// ADDR_TOGGLE = 3'b011,
				ADDR_INDATA = 3'b100,
				ADDR_CHANGED= 3'b101,
				ADDR_MASK   = 3'b110,
				ADDR_INT    = 3'b111;


	wire	i_reset = !S_AXI_ARESETN;

	wire				axil_write_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	awskd_addr;
	//
	wire	[C_AXI_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				axil_read_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	arskd_addr;
	reg	[C_AXI_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	reg	[31:0]	r_gpio;
	wire	[31:0]	ck_gpio, ck_toggled, w_mask, int_toggled, wskd_gpio;


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

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_WRITE
		// {{{
		wire	awskd_valid, wskd_valid;

		skidbuffer #(
			// {{{
			.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_ADDR_WIDTH-ADDRLSB)
			// }}}
		) axilawskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data(S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(awskd_valid), .i_ready(axil_write_ready),
			.o_data(awskd_addr)
			// }}}
		);

		skidbuffer #(
			// {{{
			.OPT_OUTREG(0),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8)
			// }}}
		) axilwskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
			.o_valid(wskd_valid), .i_ready(axil_write_ready),
			.o_data({ wskd_data, wskd_strb })
			// }}}
		);

		assign	axil_write_ready = awskd_valid && wskd_valid
				&& (!S_AXI_BVALID || S_AXI_BREADY);
		// }}}
	end else begin : SIMPLE_WRITES
		// {{{
		reg	axil_awready;

		initial	axil_awready = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axil_awready <= 1'b0;
		else
			axil_awready <= !axil_awready
				&& (S_AXI_AWVALID && S_AXI_WVALID)
				&& (!S_AXI_BVALID || S_AXI_BREADY);

		assign	S_AXI_AWREADY = axil_awready;
		assign	S_AXI_WREADY  = axil_awready;

		assign 	awskd_addr = S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	wskd_data  = S_AXI_WDATA;
		assign	wskd_strb  = S_AXI_WSTRB;

		assign	axil_write_ready = axil_awready;
		// }}}
	end endgenerate

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

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_READ
		// {{{
		wire	arskd_valid;

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
		axilarskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data(S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(arskd_valid), .i_ready(axil_read_ready),
			.o_data(arskd_addr));

		assign	axil_read_ready = arskd_valid
				&& (!axil_read_valid || S_AXI_RREADY);
		// }}}
	end else begin : SIMPLE_READS
		// {{{
		reg	axil_arready;

		always @(*)
			axil_arready = !S_AXI_RVALID;

		assign	arskd_addr = S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	S_AXI_ARREADY = axil_arready;
		assign	axil_read_ready = (S_AXI_ARVALID && S_AXI_ARREADY);
		// }}}
	end endgenerate

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

	assign	wskd_gpio = apply_wstrb(r_gpio, wskd_data, wskd_strb);

	// r_gpio, o_gpio
	// {{{
	initial	r_gpio = 0;
	always @(posedge S_AXI_ACLK)
	begin
		if (axil_write_ready)
		begin
			case({ (awskd_addr[2] && (NIN > 0)), awskd_addr[1:0] })
			3'b000:	r_gpio <= wskd_gpio;
			3'b001:	begin // SET
			// {{{
			if (wskd_strb[0])
				r_gpio[ 7: 0]<= r_gpio[ 7: 0]| wskd_data[ 7: 0];
			if (wskd_strb[1])
				r_gpio[15: 8]<= r_gpio[15: 8]| wskd_data[15: 8];
			if (wskd_strb[2])
				r_gpio[23:16]<= r_gpio[23:16]| wskd_data[23:16];
			if (wskd_strb[3])
				r_gpio[31:24]<= r_gpio[31:24]| wskd_data[31:24];
			end
			// }}}
			3'b010:	begin // CLEAR
			// {{{
			if (wskd_strb[0])
				r_gpio[ 7: 0]<= r_gpio[ 7: 0]&~wskd_data[ 7: 0];
			if (wskd_strb[1])
				r_gpio[15: 8]<= r_gpio[15: 8]&~wskd_data[15: 8];
			if (wskd_strb[2])
				r_gpio[23:16]<= r_gpio[23:16]&~wskd_data[23:16];
			if (wskd_strb[3])
				r_gpio[31:24]<= r_gpio[31:24]&~wskd_data[31:24];
			end
			// }}}
			3'b011:	begin // TOGGLE
			// {{{
			if (wskd_strb[0])
				r_gpio[ 7: 0]<=r_gpio[ 7: 0] ^ wskd_data[ 7: 0];
			if (wskd_strb[1])
				r_gpio[15: 8]<=r_gpio[15: 8] ^ wskd_data[15: 8];
			if (wskd_strb[2])
				r_gpio[23:16]<=r_gpio[23:16] ^ wskd_data[23:16];
			if (wskd_strb[3])
				r_gpio[31:24]<=r_gpio[31:24] ^ wskd_data[31:24];
			end
			// }}}
			default: begin end // Input registers
			endcase
		end

		if (i_reset)
			r_gpio[NOUT-1:0] <= DEFAULT_OUTPUT;
		if (NOUT < 32)
			r_gpio[31:((NOUT < 32) ? NOUT : 31)] <= 0;
	end

	assign	o_gpio = r_gpio[NOUT-1:0];
	// }}}

	// i_gpio -> ck_gpio, $changed(i_gpio) -> ck_toggled, r_mask
	// {{{
	generate if (NIN > 0)
	begin : INPUT_HANDLING
		// {{{
		// Poss interrupts: Toggle, Rise, Fall
		//	Only toggle is implemented here
		reg	[NIN-1:0]	last_gpio, qq_gpio, q_gpio, toggled,
					r_mask;
		wire	[31:0]		wstrb_mask;
		reg			r_int;
		integer			ik;

		// r_int
		// {{{
		initial	r_int = 0;
		always @(posedge S_AXI_ACLK)
		if (i_reset)
			r_int <= 0;
		else
			r_int <= |(r_mask & toggled);
		// }}}

		// Two clock CDC: last_gpio, qq_gpio, q_gpio
		// {{{
		initial	{ last_gpio, qq_gpio, q_gpio } = 0;
		always @(posedge S_AXI_ACLK)
		if (i_reset)
			{ last_gpio, qq_gpio, q_gpio } <= 0;
		else
			{ last_gpio, qq_gpio, q_gpio }
						<= { qq_gpio, q_gpio, i_gpio };
		// }}}

		// Toggled
		// {{{
		initial	toggled = 0;
		always @(posedge S_AXI_ACLK)
		if (i_reset)
			toggled <= 0;
		else begin
			for(ik=0; ik<NIN; ik=ik+1)
			begin
				if (axil_write_ready && awskd_addr == 3'b101
					  &&  wskd_strb[ik/8] && wskd_data[ik])
					toggled[ik] <= 1'b0;
				if (last_gpio[ik] ^ qq_gpio[ik])
					toggled[ik] <= 1'b1;
			end
		end
		// }}}

		// r_mask
		// {{{
		assign	wstrb_mask = apply_wstrb(w_mask, wskd_data, wskd_strb);

		initial	r_mask = 0;
		always @(posedge S_AXI_ACLK)
		if (i_reset)
			r_mask <= 0;
		else if (axil_write_ready && awskd_addr == 3'b110)
			r_mask <= wstrb_mask[NIN-1:0];
		// }}}

		assign	ck_gpio     = { {(32-NIN){1'b0}}, qq_gpio };
		assign	ck_toggled  = { {(32-NIN){1'b0}}, toggled };
		assign	w_mask      = { {(32-NIN){1'b0}}, r_mask };
		assign	int_toggled = { {(32-NIN){1'b0}}, (r_mask & toggled) };
		assign	o_int = r_int;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_inputs;
		assign	unused_inputs = &{ 1'b0, wstrb_mask[31:NIN] };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end else begin : NO_INPUTS
		// {{{
		assign	ck_gpio     = 32'h0;
		assign	ck_toggled  = 32'h0;
		assign	w_mask      = 32'h0;
		assign	int_toggled = 32'h0;
		assign	o_int       = 1'b0;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_inputs;
		assign	unused_inputs = &{ 1'b0, i_gpio };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end endgenerate
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

		casez({ ((NIN>0)&& arskd_addr[2]), arskd_addr[1:0] })
		3'b0??:	axil_read_data[NOUT-1:0] <= r_gpio[NOUT-1:0];
		ADDR_INDATA:	axil_read_data <= ck_gpio;
		ADDR_CHANGED:	axil_read_data <= ck_toggled;
		ADDR_MASK:	axil_read_data <= w_mask;
		ADDR_INT:	axil_read_data <= int_toggled;
		endcase

		if (OPT_LOWPOWER && !axil_read_ready)
			axil_read_data <= 0;
	end
	// }}}

	function [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		// {{{
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

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
			S_AXI_ARADDR[ADDRLSB-1:0],
			S_AXI_AWADDR[ADDRLSB-1:0] };
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
		.F_AXI_MAXWAIT(3),
		.F_AXI_MAXDELAY(3),
		.F_AXI_MAXRSTALL(5),
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
	if (OPT_SKIDBUFFER)
	begin
		assert(faxil_awr_outstanding== (S_AXI_BVALID ? 1:0)
			+(S_AXI_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0)
			+(S_AXI_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(S_AXI_ARREADY ? 0:1));
	end else begin
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0));
		assert(faxil_awr_outstanding == faxil_wr_outstanding);

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0));
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
	// Register return checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`define	CHECK_REGISTERS
`ifdef	CHECK_REGISTERS
	(* anyconst *) reg [$clog2(NOUT)-1:0]	f_obit;

	always @(*)
		assume(f_obit < NOUT);

	// Verify o_gpio
	// {{{
	always @(posedge S_AXI_ACLK)
	if ($past(i_reset) || i_reset)
	begin
		if ($past(i_reset))
			assert(o_gpio[f_obit] == DEFAULT_OUTPUT[f_obit]);
	end else if ($past(axil_write_ready && wskd_strb[f_obit/8]))
	begin
		case($past(awskd_addr[2:0]))
		3'b000: assert(o_gpio[f_obit] == $past(wskd_data[f_obit]));
		3'b001: assert(o_gpio[f_obit] == $past(o_gpio[f_obit] || wskd_data[f_obit]));
		3'b010: assert(o_gpio[f_obit] == $past(o_gpio[f_obit] && !wskd_data[f_obit]));
		3'b011: assert(o_gpio[f_obit] == $past(o_gpio[f_obit] ^ wskd_data[f_obit]));
		default: begin end
		endcase
	end

	faxil_register #(
		// {{{
		.AW(C_AXI_ADDR_WIDTH),
		.DW(C_AXI_DATA_WIDTH),
		.ADDR({ 3'b000, {(ADDRLSB){1'b0}} }),
		.MASK({(C_AXI_DATA_WIDTH){1'b0}})
		// }}}
	) foutputs (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIL_AWW(axil_write_ready),
		.S_AXIL_AWADDR({ awskd_addr[2], {(ADDRLSB+2){1'b0}} }),
		.S_AXIL_WDATA(wskd_data),
		.S_AXIL_WSTRB(wskd_strb),
		.S_AXIL_BVALID(S_AXI_BVALID),
		.S_AXIL_AR(axil_read_ready),
		.S_AXIL_ARADDR({ arskd_addr[2], {(ADDRLSB+2){1'b0}} }),
		.S_AXIL_RVALID(S_AXI_RVALID),
		.S_AXIL_RDATA(S_AXI_RDATA),
		.i_register(o_gpio)
		// }}}
	);

	// }}}

	generate if (NIN > 0)
	begin : CHECK_INPUT
		(* anyconst *) reg [$clog2(NIN)-1:0]	f_ibit;

		always @(*)
			assume(f_ibit < NIN);

		always @(posedge S_AXI_ACLK)
		if ($past(i_reset) || i_reset)
		begin
			if ($past(i_reset))
				assert(!ck_gpio[f_ibit]);
		end else begin
			if (!$past(i_reset, 2)
				&& $past(ck_gpio[f_ibit]) != $past(ck_gpio[f_ibit],2))
				assert(ck_toggled[f_ibit]);
			else if ($past(axil_write_ready
					&& awskd_addr == ADDR_CHANGED
					&& wskd_strb[f_ibit/8]
					&& wskd_data[f_ibit]))
				assert(!ck_toggled[f_ibit]);
		end

		faxil_register #(
			// {{{
			.AW(C_AXI_ADDR_WIDTH),
			.DW(C_AXI_DATA_WIDTH),
			.ADDR({ ADDR_INDATA, {(ADDRLSB){1'b0}} }),
			.MASK({(C_AXI_DATA_WIDTH){1'b0}})
			// }}}
		) finputs (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			.S_AXIL_AWW(axil_write_ready),
			.S_AXIL_AWADDR({ awskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_WDATA(wskd_data),
			.S_AXIL_WSTRB(wskd_strb),
			.S_AXIL_BVALID(S_AXI_BVALID),
			.S_AXIL_AR(axil_read_ready),
			.S_AXIL_ARADDR({ arskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_RVALID(S_AXI_RVALID),
			.S_AXIL_RDATA(S_AXI_RDATA),
			.i_register(ck_gpio)
			// }}}
		);

		faxil_register #(
			// {{{
			.AW(C_AXI_ADDR_WIDTH),
			.DW(C_AXI_DATA_WIDTH),
			.ADDR({ ADDR_CHANGED, {(ADDRLSB){1'b0}} }),
			.MASK({(C_AXI_DATA_WIDTH){1'b0}})
			// }}}
		) ftoggled (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			.S_AXIL_AWW(axil_write_ready),
			.S_AXIL_AWADDR({ awskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_WDATA(wskd_data),
			.S_AXIL_WSTRB(wskd_strb),
			.S_AXIL_BVALID(S_AXI_BVALID),
			.S_AXIL_AR(axil_read_ready),
			.S_AXIL_ARADDR({ arskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_RVALID(S_AXI_RVALID),
			.S_AXIL_RDATA(S_AXI_RDATA),
			.i_register(ck_toggled)
			// }}}
		);

		faxil_register #(
			// {{{
			.AW(C_AXI_ADDR_WIDTH),
			.DW(C_AXI_DATA_WIDTH),
			.ADDR({ ADDR_MASK, {(ADDRLSB){1'b0}} }),
			.MASK({ {(C_AXI_DATA_WIDTH-NIN){1'b0}}, {(NIN){1'b1}} })
			// }}}
		) fmask (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			.S_AXIL_AWW(axil_write_ready),
			.S_AXIL_AWADDR({ awskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_WDATA(wskd_data),
			.S_AXIL_WSTRB(wskd_strb),
			.S_AXIL_BVALID(S_AXI_BVALID),
			.S_AXIL_AR(axil_read_ready),
			.S_AXIL_ARADDR({ arskd_addr, {(ADDRLSB){1'b0}} }),
			.S_AXIL_RVALID(S_AXI_RVALID),
			.S_AXIL_RDATA(S_AXI_RDATA),
			.i_register(w_mask)
			// }}}
		);
	end endgenerate
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction checks
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

	always @(posedge S_AXI_ACLK)
	if (!i_reset)
		cover(o_int);

	always @(posedge S_AXI_ACLK)
	if (!i_reset)
		cover($fell(o_int));

	// }}}
`endif
// }}}
endmodule
