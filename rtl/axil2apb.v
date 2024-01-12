////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axil2apb.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	High throughput AXI-lite bridge to APB.  With both skid
//		buffers enabled, it can handle 50% throughput--the maximum
//	that APB can handle.
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
`default_nettype none
// }}}
module	axil2apb #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		// OPT_OUTGOING_SKIDBUFFER: required for 50% throughput
		parameter [0:0]	OPT_OUTGOING_SKIDBUFFER = 1'b0
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// The AXI-lite interface
		// {{{
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire [C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[2:0]			S_AXI_AWPROT,
		//
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire [C_AXI_DATA_WIDTH-1 : 0]	S_AXI_WDATA,
		input	wire [(C_AXI_DATA_WIDTH/8)-1:0]	S_AXI_WSTRB,
		//
		output	reg				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	reg	[1:0]			S_AXI_BRESP,
		//
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[2:0]			S_AXI_ARPROT,
		//
		output	reg				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	reg	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	reg	[1:0]			S_AXI_RRESP,
		// }}}
		//
		// The APB interface
		// {{{
		output	reg 				M_APB_PSEL,
		output	reg 				M_APB_PENABLE,
		input	wire				M_APB_PREADY,
		output	reg [C_AXI_ADDR_WIDTH-1:0]	M_APB_PADDR,
		output	reg 				M_APB_PWRITE,
		output	reg [C_AXI_DATA_WIDTH-1:0]	M_APB_PWDATA,
		output	reg [C_AXI_DATA_WIDTH/8-1:0]	M_APB_PWSTRB,
		output	reg	[2:0]			M_APB_PPROT,
		input	wire [C_AXI_DATA_WIDTH-1:0]	M_APB_PRDATA,
		input	wire				M_APB_PSLVERR
		// }}}
		// }}}
	);

	// Register declarations
	// {{{
	localparam	AW = C_AXI_ADDR_WIDTH;
	localparam	DW = C_AXI_DATA_WIDTH;
	localparam	AXILLSB = $clog2(C_AXI_DATA_WIDTH)-3;
	wire				awskd_valid, wskd_valid, arskd_valid;
	reg				axil_write_ready, axil_read_ready,
					write_grant, apb_idle;
	wire	[AW-AXILLSB-1:0]	awskd_addr, arskd_addr;
	wire	[DW-1:0]		wskd_data;
	wire	[DW/8-1:0]		wskd_strb;
	wire	[2:0]			awskd_prot, arskd_prot;
	reg	apb_bvalid, apb_rvalid, apb_error, out_skid_full;
	reg	[DW-1:0]	apb_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming AXI-lite write interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// awskd - write address skid buffer
	// {{{
	skidbuffer #(.DW(C_AXI_ADDR_WIDTH-AXILLSB + 3),
		.OPT_OUTREG(0)
	) awskd (.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
		.i_data({ S_AXI_AWADDR[AW-1:AXILLSB], S_AXI_AWPROT }),
		.o_valid(awskd_valid), .i_ready(axil_write_ready),
		.o_data({ awskd_addr, awskd_prot }));
	// }}}

	// wskd - write data skid buffer
	// {{{
	skidbuffer #(.DW(DW+(DW/8)),
		.OPT_OUTREG(0)
	) wskd (.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
		.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
		.o_valid(wskd_valid), .i_ready(axil_write_ready),
		.o_data({ wskd_data, wskd_strb }));
	// }}}

	// apb_idle
	// {{{
	always @(*)
	begin
		apb_idle = !M_APB_PSEL;// || (M_APB_PENABLE && M_APB_PREADY);
		if (OPT_OUTGOING_SKIDBUFFER && (M_APB_PENABLE && M_APB_PREADY))
			apb_idle = 1'b1;
	end
	// }}}

	// axil_write_ready
	// {{{
	always @(*)
	begin
		axil_write_ready = apb_idle;
		if (S_AXI_BVALID && !S_AXI_BREADY)
			axil_write_ready = 1'b0;
		if (!awskd_valid || !wskd_valid)
			axil_write_ready = 1'b0;
		if (!write_grant && arskd_valid)
			axil_write_ready = 1'b0;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming AXI-lite read interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// arskd buffer
	// {{{
	skidbuffer #(.DW(C_AXI_ADDR_WIDTH-AXILLSB+3),
		.OPT_OUTREG(0)
	) arskd (.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
		.i_data({ S_AXI_ARADDR[AW-1:AXILLSB], S_AXI_ARPROT }),
		.o_valid(arskd_valid), .i_ready(axil_read_ready),
		.o_data({ arskd_addr, arskd_prot }));
	// }}}

	// axil_read_ready
	// {{{
	always @(*)
	begin
		axil_read_ready = apb_idle;
		if (S_AXI_RVALID && !S_AXI_RREADY)
			axil_read_ready = 1'b0;
		if (write_grant && awskd_valid && wskd_valid)
			axil_read_ready = 1'b0;
		if (!arskd_valid)
			axil_read_ready = 1'b0;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate among reads and writes --- alternating arbitration
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// write_grant -- alternates
	// {{{
	always @(posedge S_AXI_ACLK)
	if (apb_idle)
	begin
		if (axil_write_ready)
			write_grant <= 1'b0;
		else if (axil_read_ready)
			write_grant <= 1'b1;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Drive the APB bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// APB bus
	// {{{
	initial	M_APB_PSEL    = 1'b0;
	initial	M_APB_PENABLE = 1'b0;
	always @(posedge S_AXI_ACLK)
	begin
		if (apb_idle)
		begin
			M_APB_PSEL   <= 1'b0;
			if (axil_read_ready)
			begin
				M_APB_PSEL   <= 1'b1;
				M_APB_PADDR  <= { arskd_addr, {(AXILLSB){1'b0}} };
				M_APB_PWRITE <= 1'b0;
				M_APB_PPROT  <= arskd_prot;
			end else if (axil_write_ready)
			begin
				M_APB_PSEL   <= 1'b1;
				M_APB_PADDR  <= { awskd_addr, {(AXILLSB){1'b0}} };
				M_APB_PWRITE <= 1'b1;
				M_APB_PPROT  <= awskd_prot;
			end

			if (wskd_valid)
			begin
				M_APB_PWDATA <= wskd_data;
				M_APB_PWSTRB <= wskd_strb;
			end

			M_APB_PENABLE <= 1'b0;
		end else if (!M_APB_PENABLE)
			M_APB_PENABLE <= 1'b1;
		else if (M_APB_PREADY)
		begin // if (M_APB_PSEL && M_APB_ENABLE)
			M_APB_PENABLE <= 1'b0;
			M_APB_PSEL <= 1'b0;
		end

		if (!S_AXI_ARESETN)
		begin
			M_APB_PSEL    <= 1'b0;
			M_APB_PENABLE <= 1'b0;
		end
	end
	// }}}

	reg			r_apb_bvalid, r_apb_rvalid, r_apb_error;
	reg	[DW-1:0]	r_apb_data;

	generate if (OPT_OUTGOING_SKIDBUFFER)
	begin : GEN_OSKID
		// {{{
		// r_apb_bvalid, r_apb_rvalid, r_apb_error, r_apb_data
		// {{{
		initial	r_apb_bvalid = 1'b0;
		initial	r_apb_rvalid = 1'b0;
		always @(posedge S_AXI_ACLK)
		begin
			if (M_APB_PSEL && M_APB_PENABLE && M_APB_PREADY)
			begin
			r_apb_bvalid <= (S_AXI_BVALID && !S_AXI_BREADY) && M_APB_PWRITE;
			r_apb_rvalid <= (S_AXI_RVALID && !S_AXI_RREADY) && !M_APB_PWRITE;
				if (!M_APB_PWRITE)
					r_apb_data  <= M_APB_PRDATA;
				r_apb_error <= M_APB_PSLVERR;
			end else begin
				if (S_AXI_BREADY)
					r_apb_bvalid <= 1'b0;
				if (S_AXI_RREADY)
					r_apb_rvalid <= 1'b0;
			end

			if (!S_AXI_ARESETN)
			begin
				r_apb_bvalid <= 1'b0;
				r_apb_rvalid <= 1'b0;
			end
		end
		// }}}

		// apb_bvalid
		// {{{
		always @(*)
			apb_bvalid = (M_APB_PSEL && M_APB_PENABLE
				&& M_APB_PREADY && M_APB_PWRITE)|| r_apb_bvalid;
		// }}}

		// apb_rvalid
		// {{{
		always @(*)
			apb_rvalid = (M_APB_PSEL && M_APB_PENABLE
				&& M_APB_PREADY && !M_APB_PWRITE)||r_apb_rvalid;
		// }}}

		// apb_data
		// {{{
		always @(*)
		if (out_skid_full)
			apb_data = r_apb_data;
		else
			apb_data = M_APB_PRDATA;
		// }}}

		// apb_error
		// {{{
		always @(*)
		if (out_skid_full)
			apb_error = r_apb_error;
		else
			apb_error = M_APB_PSLVERR;
		// }}}

		always @(*)
			out_skid_full = r_apb_bvalid || r_apb_rvalid;
		// }}}
	end else begin : NO_OSKID
		// {{{

		initial	r_apb_bvalid = 1'b0;
		initial	r_apb_rvalid = 1'b0;
		initial	r_apb_error = 1'b0;
		initial	r_apb_data = 0;
		always @(*)
		begin
			r_apb_bvalid = 1'b0;
			r_apb_rvalid = 1'b0;
			r_apb_error = 1'b0;
			r_apb_data = 0;

			apb_bvalid = M_APB_PSEL && M_APB_PENABLE
				&& M_APB_PREADY && M_APB_PWRITE;

			apb_rvalid = M_APB_PSEL && M_APB_PENABLE
				&& M_APB_PREADY && !M_APB_PWRITE;

			apb_data = M_APB_PRDATA;

			apb_error = M_APB_PSLVERR;

			out_skid_full = 1'b0;
		end

		// Verilator lint_off UNUSED
		wire	skd_unused;
		assign	skd_unused = &{ 1'b0, r_apb_bvalid, r_apb_rvalid,
				r_apb_data, r_apb_error, out_skid_full };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite write return signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// BVALID
	// {{{
	initial	S_AXI_BVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXI_BVALID <= 1'b0;
	else if (!S_AXI_BVALID || S_AXI_BREADY)
		S_AXI_BVALID <= apb_bvalid;
	// }}}

	// BRESP
	// {{{
	initial	S_AXI_BRESP  = 2'b00;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXI_BRESP  <= 2'b00;
	else if (!S_AXI_BVALID || S_AXI_BREADY)
		S_AXI_BRESP <= { apb_error, 1'b0 };
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite read return signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// RVALID
	// {{{
	initial	S_AXI_RVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXI_RVALID <= 1'b0;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
		S_AXI_RVALID <= apb_rvalid;
	// }}}

	// RRESP
	// {{{
	initial	S_AXI_RRESP  = 2'b00;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXI_RRESP  <= 2'b00;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
		S_AXI_RRESP <= { apb_error, 1'b0 };
	// }}}

	// RDATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if ((!S_AXI_RVALID || S_AXI_RREADY) && apb_rvalid)
		S_AXI_RDATA <= apb_data;
	// }}}

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
		S_AXI_AWADDR[AXILLSB-1:0], S_AXI_ARADDR[AXILLSB-1:0]
		};
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
	localparam	F_LGDEPTH = 3;

	wire	[F_LGDEPTH-1:0]	faxi_rd_outstanding,
				faxi_wr_outstanding,
				faxi_awr_outstanding;
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxil_slave #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH (C_AXI_DATA_WIDTH),
		.F_OPT_COVER_BURST(4),
		.F_AXI_MAXWAIT(17),
		.F_AXI_MAXDELAY(17),
		.F_AXI_MAXRSTALL(3),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxil (
		// {{{
		.i_clk(S_AXI_ACLK),	// System clock
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr(S_AXI_AWADDR),
		.i_axi_awprot(S_AXI_AWPROT),
		//
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata(S_AXI_WDATA),
		.i_axi_wstrb(S_AXI_WSTRB),
		.i_axi_wvalid(S_AXI_WVALID),
		//
		.i_axi_bresp(S_AXI_BRESP),
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr(S_AXI_ARADDR),
		.i_axi_arprot(S_AXI_ARPROT),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rresp(S_AXI_RRESP),
		.i_axi_rdata(S_AXI_RDATA),
		//
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		.f_axi_wr_outstanding(faxi_wr_outstanding),
		.f_axi_awr_outstanding(faxi_awr_outstanding)
		// }}}
	);

	// Correlate outstanding counters against our state
	// {{{
	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(faxi_awr_outstanding == (S_AXI_AWREADY ? 0:1)
				+ (r_apb_bvalid ? 1:0)
				+ (S_AXI_BVALID ? 1:0)
				+ ((M_APB_PSEL && M_APB_PWRITE) ? 1:0));

		assert(faxi_wr_outstanding == (S_AXI_WREADY ? 0:1)
				+ (r_apb_bvalid ? 1:0)
				+ (S_AXI_BVALID ? 1:0)
				+ ((M_APB_PSEL && M_APB_PWRITE) ? 1:0));

		assert(faxi_rd_outstanding == (S_AXI_ARREADY ? 0:1)
				+ (r_apb_rvalid ? 1:0)
				+ (S_AXI_RVALID ? 1:0)
				+ ((M_APB_PSEL && !M_APB_PWRITE) ? 1:0));

		if (r_apb_bvalid)
			assert(S_AXI_BVALID);
		if (r_apb_rvalid)
			assert(S_AXI_RVALID);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// APB interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fapb_master #(
		// {{{
		.AW(C_AXI_ADDR_WIDTH),
		.DW(C_AXI_DATA_WIDTH),
		.F_OPT_MAXSTALL(3)
		// }}}
	) fapb (
		// {{{
		.PCLK(S_AXI_ACLK), .PRESETn(S_AXI_ARESETN),
		.PSEL(   M_APB_PSEL),
		.PENABLE(M_APB_PENABLE),
		.PREADY( M_APB_PREADY),
		.PADDR(  M_APB_PADDR),
		.PWRITE( M_APB_PWRITE),
		.PWDATA( M_APB_PWDATA),
		.PWSTRB( M_APB_PWSTRB),
		.PPROT(  M_APB_PPROT),
		.PRDATA( M_APB_PRDATA),
		.PSLVERR(M_APB_PSLVERR)
		// }}}
	);

	always @(*)
	if (!M_APB_PSEL)
		assert(!M_APB_PENABLE);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction invariants
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
		assert(!axil_write_ready || !axil_read_ready);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg			f_never_test;
	(* anyconst *)	reg	[AW-1:0]	f_never_addr;
	(* anyconst *)	reg	[DW-1:0]	f_never_data;
	(* anyconst *)	reg	[DW/8-1:0]	f_never_strb;
	(* anyconst *)	reg	[2:0]		f_never_prot;

	// Assume the never values are never received
	// {{{
	always @(*)
	if (f_never_test)
	begin
		assume(f_never_addr[AXILLSB-1:0] == 0);

		if (S_AXI_AWVALID)
		begin
			assume(S_AXI_AWADDR[AW-1:AXILLSB] != f_never_addr[AW-1:AXILLSB]);
			assume(S_AXI_AWPROT != f_never_prot);
		end

		if (S_AXI_WVALID)
		begin
			assume(S_AXI_WDATA != f_never_data);
			assume(S_AXI_WSTRB != f_never_strb);
		end

		if (S_AXI_ARVALID)
		begin
			assume(S_AXI_ARADDR[AW-1:AXILLSB] != f_never_addr[AW-1:AXILLSB]);
			assume(S_AXI_ARPROT != f_never_prot);
		end

		if (M_APB_PSEL && M_APB_PENABLE && M_APB_PREADY&& !M_APB_PWRITE)
			assume(M_APB_PRDATA != f_never_data);
	end
	// }}}

	// Assert the never values are never in the incoming skid buffers
	// {{{
	always @(*)
	if (f_never_test)
	begin
		if (awskd_valid)
		begin
			assert(awskd_addr != f_never_addr[AW-1:AXILLSB]);
			assert(awskd_prot != f_never_prot);
		end

		if (wskd_valid)
		begin
			assert(wskd_data != f_never_data);
			assert(wskd_strb != f_never_strb);
		end

		if (arskd_valid)
		begin
			assert(arskd_addr != f_never_addr[AW-1:AXILLSB]);
			assert(arskd_prot != f_never_prot);
		end

		if (r_apb_rvalid)
			assert(r_apb_data != f_never_data);
	end
	// }}}

	// Assert the never values are never output
	// {{{
	always @(*)
	if (f_never_test)
	begin
		if (M_APB_PSEL)
		begin
			assert(M_APB_PADDR != f_never_addr);
			assert(M_APB_PPROT != f_never_prot);
			if (M_APB_PWRITE)
			begin
				assert(M_APB_PWDATA != f_never_data);
				assert(M_APB_PWSTRB != f_never_strb);
			end
		end

		if (S_AXI_RVALID)
			assert(S_AXI_RDATA != f_never_data);
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

	// None (yet)

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
