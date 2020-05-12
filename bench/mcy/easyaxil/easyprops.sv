////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	easyprops
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
// }}}
//
`default_nettype none
//
module	easyprops #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXI_ADDR_WIDTH = 4,
		localparam	C_AXI_DATA_WIDTH = 32,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 0,
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		//
		input	wire					S_AXI_AWVALID,
		input	wire					S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		input	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		input	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		input	wire	[1:0]				S_AXI_BRESP,
		//
		input	wire					S_AXI_ARVALID,
		input	wire					S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		//
		input	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_RDATA,
		input	wire	[1:0]				S_AXI_RRESP,
		// }}}
		// input	wire	i_clk,
		input	wire	[31:0]	r0,
		input	wire	[31:0]	r1,
		input	wire	[31:0]	r2,
		input	wire	[31:0]	r3,
		input	wire	axil_read_ready, axil_write_ready,
		input	wire	[1:0]	awskd_addr, arskd_addr,
		input	wire	[31:0]	wskd_data,
		input	wire	[3:0]	wskd_strb
	);

`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties used in verfiying this core
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
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
		.i_axi_awcache(4'h0),
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
		.i_axi_arcache(4'h0),
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

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN
			&& axil_read_ready))
	begin
		assert(S_AXI_RVALID);
		case($past(arskd_addr))
		0: assert(S_AXI_RDATA == $past(r0));
		1: assert(S_AXI_RDATA == $past(r1));
		2: assert(S_AXI_RDATA == $past(r2));
		3: assert(S_AXI_RDATA == $past(r3));
		endcase
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
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// While there are already cover properties in the formal property
	// set above, you'll probably still want to cover something
	// application specific here

	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Round #1 -- double check writes to registers
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg[3:0]	f_addr;
	reg [7:0]	f_byte, f_rbyte;

	generate if (OPT_SKIDBUFFER)
	begin
		initial	f_byte = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			f_byte <= 0;
		else if (axil_write_ready)
		begin
			if (awskd_addr == f_addr[3:2]
					&& wskd_strb[f_addr[1:0]])
				f_byte <= S_AXI_WDATA >> (8*f_addr[1:0]);
		end

	end else begin
	
		initial	f_byte = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			f_byte <= 0;
		else if (S_AXI_AWVALID && S_AXI_WVALID && S_AXI_AWREADY && S_AXI_WREADY)
		begin
			if (S_AXI_AWADDR[3:2] == f_addr[3:2]
					&& S_AXI_WSTRB[f_addr[1:0]])
				f_byte <= S_AXI_WDATA >> (8*f_addr[1:0]);
		end

	end endgenerate

	always @(*)
	case(f_addr[3:2])
	2'b00: f_rbyte = (r0 >> (8*f_addr[1:0]));
	2'b01: f_rbyte = (r1 >> (8*f_addr[1:0]));
	2'b10: f_rbyte = (r2 >> (8*f_addr[1:0]));
	2'b11: f_rbyte = (r3 >> (8*f_addr[1:0]));
	endcase

	always @(*)
		assert(f_byte == f_rbyte);

	////////////////////////////////////////////////////////////////////////
	//
	// Round #2 -- double check ?WREADY signaling
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// ???
`endif
endmodule


module skidprops #(
	parameter	[0:0]	OPT_LOWPOWER = 0,
	parameter	[0:0]	OPT_OUTREG = 1,
	//
	parameter	[0:0]	OPT_PASSTHROUGH = 0,
	parameter		DW = 8
	) (
	input	wire			i_clk, i_reset,
	input	wire			i_valid,
	input	wire			o_ready,
	input	wire	[DW-1:0]	i_data,
	input	wire			o_valid,
	input	wire			i_ready,
	input	wire	[DW-1:0]	o_data,

	input	wire	[DW-1:0]	r_data
	);

	// Reset properties
	property RESET_CLEARS_IVALID;
		@(posedge i_clk) i_reset |=> !i_valid;
	endproperty

	property IDATA_HELD_WHEN_NOT_READY;
		@(posedge i_clk) disable iff (i_reset)
		i_valid && !o_ready |=> i_valid && $stable(i_data);
	endproperty

	assert	property (IDATA_HELD_WHEN_NOT_READY);

	generate if (!OPT_PASSTHROUGH)
	begin

		assert property (@(posedge i_clk)
			OPT_OUTREG && i_reset |=> o_ready && !o_valid);

		assert property (@(posedge i_clk)
			!OPT_OUTREG && i_reset |-> !o_valid);

		// Rule #1:
		//	Once o_valid goes high, the data cannot change until the
		//	clock after i_ready
		assert property (@(posedge i_clk)
			disable iff (i_reset)
			o_valid && !i_ready
			|=> (o_valid && $stable(o_data)));

		// Rule #2:
		//	All incoming data must either go directly to the
		//	output port, or into the skid buffer
		assert property (@(posedge i_clk)
			disable iff (i_reset)
			(i_valid && o_ready
				&& (!OPT_OUTREG || o_valid) && !i_ready)
				|=> (!o_ready && r_data == $past(i_data)));

		// Rule #3:
		//	After the last transaction, o_valid should become idle
		if (!OPT_OUTREG)
		begin

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				i_ready |=> (o_valid == i_valid));

		end else begin

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				i_valid && o_ready |=> o_valid);

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				!i_valid && o_ready && i_ready |=> !o_valid);

		end

		// Rule #4
		//	Same thing, but this time for r_valid
		assert property (@(posedge i_clk)
			!o_ready && i_ready |=> o_ready);


		if (OPT_LOWPOWER)
		begin
			//
			// If OPT_LOWPOWER is set, o_data and r_data both need
			// to be zero any time !o_valid or !r_valid respectively
			assert property (@(posedge i_clk)
				(OPT_OUTREG || !i_reset) && !o_valid |-> o_data == 0);

			assert property (@(posedge i_clk)
				o_ready |-> r_data == 0);

			// else
			//	if OPT_LOWPOWER isn't set, we can lower our
			//	logic count by not forcing these values to zero.
		end

	end endgenerate

endmodule

bind easyaxil easyprops copy (.*);
`ifdef	CHECK_SKID
bind easyaxil.SKIDBUFFER_WRITE.axilawskid skidprops #(.OPT_OUTREG(0), .OPT_LOWPOWER(easyaxil.OPT_LOWPOWER), .DW(2)) copy (.*);
bind easyaxil.SKIDBUFFER_WRITE.axilwskid  skidprops #(.OPT_OUTREG(0), .OPT_LOWPOWER(easyaxil.OPT_LOWPOWER), .DW(36)) copy (.*);
bind easyaxil.SKIDBUFFER_READ.axilarskid  skidprops #(.OPT_OUTREG(0), .OPT_LOWPOWER(easyaxil.OPT_LOWPOWER), .DW(2)) copy (.*);
`endif
