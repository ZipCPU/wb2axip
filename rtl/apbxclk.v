////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	apbxclk.v
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
// }}}
`default_nettype	none
//
module	apbxclk #(
		// {{{
		parameter	C_APB_ADDR_WIDTH = 12,
		parameter	C_APB_DATA_WIDTH = 32,
		parameter [0:0]	OPT_REGISTERED = 1'b0,
		localparam	AW = C_APB_ADDR_WIDTH,
		localparam	DW = C_APB_DATA_WIDTH
		// }}}
	) (
		// {{{
		input	wire			S_APB_PCLK, S_PRESETn,
		input	wire			S_APB_PSEL,
		input	wire			S_APB_PENABLE,
		output	reg			S_APB_PREADY,
		input	wire	[AW-1:0]	S_APB_PADDR,
		input	wire			S_APB_PWRITE,
		input	wire	[DW-1:0]	S_APB_PWDATA,
		input	wire	[DW/8-1:0]	S_APB_PWSTRB,
		input	wire	[2:0]		S_APB_PPROT,
		output	wire	[DW-1:0]	S_APB_PRDATA,
		output	wire			S_APB_PSLVERR,
		//
		input	wire			M_APB_PCLK,
		output	reg			M_PRESETn,
		output	reg			M_APB_PSEL,
		output	reg			M_APB_PENABLE,
		input	wire			M_APB_PREADY,
		output	wire	[AW-1:0]	M_APB_PADDR,
		output	wire			M_APB_PWRITE,
		output	wire	[DW-1:0]	M_APB_PWDATA,
		output	wire	[DW/8-1:0]	M_APB_PWSTRB,
		output	wire	[2:0]		M_APB_PPROT,
		input	wire	[DW-1:0]	M_APB_PRDATA,
		input	wire			M_APB_PSLVERR
		// }}}
	);

	// Local declarations
	// {{{
	reg			reset_pipe, full_reset_pipe, full_reset;

	reg			s_request, s_tfr_request;
	reg			m_request, m_request_pipe;

	reg			m_ack;
	reg			s_ack, s_ack_pipe;
	reg	[DW-1:0]	m_prdata;
	reg			m_pslverr;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronize resets
	// {{{
	always @(posedge M_APB_PCLK or negedge S_PRESETn)
	if (!S_PRESETn)
		{ M_PRESETn, reset_pipe } <= 0;
	else
		{ M_PRESETn, reset_pipe } <= { reset_pipe, 1'b1 };

	always @(posedge S_APB_PCLK or negedge M_PRESETn)
	if (!M_PRESETn)
		{ full_reset, full_reset_pipe } <= 0;
	else
		{ full_reset, full_reset_pipe } <= { full_reset_pipe, 1'b1 };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move the request across clock domains
	// {{{

	// s_request
	// {{{
	// Step 1: Register the request
	//	Always register anything before moving cross clock domains
	always @(posedge S_APB_PCLK or negedge S_PRESETn)
	if (!S_PRESETn)
		s_request <= 0;
	else if (S_APB_PREADY)
		s_request <= 0;
	else if (S_APB_PSEL && !S_APB_PENABLE)
		s_request <= 1;
	// }}}

	// s_tfr_request
	// {{{
	// Step 2: Forward requests--but only when the downstream handshake
	//	is ready to accept them
	always @(posedge S_APB_PCLK or negedge S_PRESETn)
	if (!S_PRESETn)
		s_tfr_request <= 0;
	else if (S_APB_PREADY)
		s_tfr_request <= 0;
	else if ((S_APB_PSEL && !S_APB_PENABLE) || s_request)
		s_tfr_request <= (full_reset && !s_ack);
	// }}}

	// m_request, m_request_pipe -- 3. Capture the request in new clk domain
	// {{{
	always @(posedge M_APB_PCLK or negedge M_PRESETn)
	if (!M_PRESETn)
		{ m_request, m_request_pipe } <= 0;
	else
		{ m_request, m_request_pipe }
				<= { m_request_pipe, s_tfr_request };
	// }}}

	// M_APB_PSEL, M_APB_PENABLE -- 4. Forward the request downstream
	// {{{
	always @(posedge M_APB_PCLK or negedge M_PRESETn)
	if (!M_PRESETn)
	begin
		M_APB_PSEL <= 0;
		M_APB_PENABLE <= 1'b0;
	end else begin
		M_APB_PSEL    <= m_request && !m_ack
				&& (!M_APB_PSEL || !M_APB_PENABLE || !M_APB_PREADY);
		M_APB_PENABLE <= M_APB_PSEL && (!M_APB_PSEL || !M_APB_PENABLE || !M_APB_PREADY);
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move the response back across clock domains
	// {{{

	// m_ack
	// {{{
	always @(posedge M_APB_PCLK or negedge M_PRESETn)
	if (!M_PRESETn)
		m_ack <= 0;
	else if (m_request && !m_ack && M_APB_PSEL && M_APB_PREADY && M_APB_PENABLE)
		m_ack <= 1'b1;
	else if (!m_request)
		m_ack <= 1'b0;
	// }}}

	// s_ack, s_ack_pipe
	// {{{
	always @(posedge S_APB_PCLK or negedge S_PRESETn)
	if (!S_PRESETn)
		{ s_ack, s_ack_pipe } <= 0;
	else
		{ s_ack, s_ack_pipe } <= { s_ack_pipe, m_ack };
	// }}}

	// S_APB_PREADY
	// {{{
	always @(posedge S_APB_PCLK or negedge S_PRESETn)
	if (!S_PRESETn)
		S_APB_PREADY <= 0;
	else
		S_APB_PREADY <= !S_APB_PREADY && s_tfr_request && s_ack;
	// }}}

	// m_prdata
	// {{{
	always @(posedge M_APB_PCLK)
	if (M_APB_PSEL && M_APB_PREADY)
		m_prdata  <= M_APB_PRDATA;
	// }}}

	// m_pslverr
	// {{{
	always @(posedge M_APB_PCLK or negedge M_PRESETn)
	if (!M_PRESETn)
		m_pslverr <= 0;
	else if (M_APB_PSEL && M_APB_PREADY)
		m_pslverr <= M_APB_PSLVERR;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Handle the ancillary (data bearing) signals
	// {{{

	generate if (OPT_REGISTERED)
	begin : GEN_REGISTERS
		// {{{
		// Register all results into the new domain when
		// crossing clock domains
		reg	[AW-1:0]	m_paddr;
		reg			m_pwrite;
		reg	[DW-1:0]	m_pwdata;
		reg	[DW/8-1:0]	m_pwstrb;
		reg	[2:0]		m_pprot;

		reg	[DW-1:0]	s_prdata;
		reg			s_pslverr;

		always @(posedge M_APB_PCLK)
		if (m_request && !m_ack)
		begin
			m_paddr  <= S_APB_PADDR;
			m_pwrite <= S_APB_PWRITE;
			m_pwdata <= S_APB_PWDATA;
			m_pwstrb <= S_APB_PWSTRB;
			m_pprot  <= S_APB_PPROT;
		end

		assign	M_APB_PADDR  = m_paddr;
		assign	M_APB_PWRITE = m_pwrite;
		assign	M_APB_PWDATA = m_pwdata;
		assign	M_APB_PWSTRB = m_pwstrb;
		assign	M_APB_PPROT  = m_pprot;

		always @(posedge S_APB_PCLK or negedge S_PRESETn)
		if (!S_PRESETn)
			s_pslverr <= 1'b0;
		else if (s_tfr_request && s_ack
					&& (!S_APB_PREADY || !S_APB_PENABLE))
			s_pslverr <= m_pslverr;
		else
			s_pslverr <= 0;

		always @(posedge S_APB_PCLK)
		if (s_request && s_ack)
		begin
			s_prdata  <= m_prdata;
		end else begin
			s_prdata  <= 0;
		end

		assign	S_APB_PRDATA  = s_prdata;
		assign	S_APB_PSLVERR = s_pslverr;
		// }}}
	end else begin : NO_REGISTERING
		// {{{
		// Results will be stable whenever PSEL is true.  There's
		// really no *need* to register them

		assign	M_APB_PADDR  = S_APB_PADDR;
		assign	M_APB_PWRITE = S_APB_PWRITE;
		assign	M_APB_PWDATA = S_APB_PWDATA;
		assign	M_APB_PWSTRB = S_APB_PWSTRB;
		assign	M_APB_PPROT  = S_APB_PPROT;

		assign	S_APB_PRDATA  = m_prdata;
		assign	S_APB_PSLVERR = m_pslverr && S_APB_PREADY;
		// }}}
	end endgenerate
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
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
	(* gclk *)	reg	gbl_clk;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fapb_slave #(
		// {{{
		.AW(C_APB_ADDR_WIDTH), .DW(C_APB_DATA_WIDTH),
		.F_OPT_MAXSTALL(0), .F_OPT_ASYNC_RESET(1'b1),
		.F_OPT_SLVERR(1'b1)
		// }}}
	) fslv (
		// {{{
		.PCLK(S_APB_PCLK), .PRESETn(S_PRESETn),
		.PSEL(S_APB_PSEL),
			.PENABLE(S_APB_PENABLE),
			.PREADY(S_APB_PREADY),
			.PADDR(S_APB_PADDR),
		.PWRITE(S_APB_PWRITE), .PWDATA(S_APB_PWDATA),
			.PWSTRB(S_APB_PWSTRB),
		.PPROT(S_APB_PPROT),
		.PRDATA(S_APB_PRDATA), .PSLVERR(S_APB_PSLVERR)
		// }}}
	);

	fapb_master #(
		// {{{
		.AW(C_APB_ADDR_WIDTH), .DW(C_APB_DATA_WIDTH),
		.F_OPT_MAXSTALL(0), .F_OPT_ASYNC_RESET(1'b1),
		.F_OPT_SLVERR(1'b1)
		// }}}
	) fmas (
		// {{{
		.PCLK(M_APB_PCLK), .PRESETn(M_PRESETn),
		.PSEL(M_APB_PSEL), .PENABLE(M_APB_PENABLE),
			.PREADY(M_APB_PREADY), .PADDR(M_APB_PADDR),
		.PWRITE(M_APB_PWRITE), .PWDATA(M_APB_PWDATA),
			.PWSTRB(M_APB_PWSTRB),
		.PPROT(M_APB_PPROT),
		.PRDATA(M_APB_PRDATA), .PSLVERR(M_APB_PSLVERR)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock stability
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_past_valid_gbl;

	initial	f_past_valid_gbl <= 1'b0;
	always @(posedge gbl_clk)
		f_past_valid_gbl <= 1'b1;

	always @(*)
	if (!f_past_valid_gbl)
		assume(!S_PRESETn);

	always @(posedge gbl_clk)
	if (!$rose(S_APB_PCLK))
	begin
		assume(!$rose(S_PRESETn));
		assume($stable(S_APB_PSEL));
		assume($stable(S_APB_PENABLE));
		assume($stable(S_APB_PADDR));
		assume($stable(S_APB_PWRITE));
		assume($stable(S_APB_PWDATA));
		assume($stable(S_APB_PWSTRB));
		assume($stable(S_APB_PPROT));
		//
		if (f_past_valid_gbl && S_PRESETn)
		begin
			assert($stable(S_APB_PREADY));
			if (OPT_REGISTERED)
			begin
				assert($stable(S_APB_PRDATA));
				assert($stable(S_APB_PSLVERR));
			end else if ($past(S_APB_PREADY) && S_APB_PREADY)
			begin
				assert($stable(S_APB_PRDATA));
				assert($stable(S_APB_PSLVERR));
			end
		end
	end

	always @(posedge gbl_clk)
	if (!$rose(M_APB_PCLK))
	begin
		if (f_past_valid_gbl)
		begin
			assert(!$rose(M_PRESETn));
		end

		if (f_past_valid_gbl && M_PRESETn)
		begin
			assert($stable(M_APB_PSEL));
			assert($stable(M_APB_PENABLE));
			if (OPT_REGISTERED)
			begin
				assert($stable(M_APB_PADDR));
				assert($stable(M_APB_PWRITE));
				assert($stable(M_APB_PWDATA));
				assert($stable(M_APB_PWSTRB));
				assert($stable(M_APB_PPROT));
			end else if ($past(M_APB_PSEL) && M_APB_PSEL)
			begin
				assert($stable(M_APB_PADDR));
				assert($stable(M_APB_PWRITE));
				assert($stable(M_APB_PWDATA));
				assert($stable(M_APB_PWSTRB));
				assert($stable(M_APB_PPROT));
			end
		end
		//
		assume($stable(M_APB_PREADY));
		assume($stable(M_APB_PRDATA));
		assume($stable(M_APB_PSLVERR));
	end

	always @(posedge gbl_clk)
	if ($past(S_APB_PSEL && !S_APB_PREADY) && $past(S_PRESETn) && S_PRESETn)
	begin
		assume($stable(S_APB_PSEL));
		assume($stable(S_APB_PADDR));
		assume($stable(S_APB_PWRITE));
		assume($stable(S_APB_PWDATA));
		assume($stable(S_APB_PWSTRB));
		assume($stable(S_APB_PPROT));
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction invariants
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	case({ S_PRESETn, reset_pipe, M_PRESETn, full_reset_pipe, full_reset })
	5'b0_00_00: begin end
	5'b1_00_00: begin end
	5'b1_10_00: begin end
	5'b1_11_00: begin end
	5'b1_11_10: begin end
	5'b1_11_11: begin end
	default: assert(0);
	endcase

	always @(*)
	casez({ s_request, s_tfr_request, m_request_pipe, m_request, m_ack, s_ack_pipe, s_ack })
	7'b00_00_000: begin end
	7'b10_00_000: begin end
	7'b11_00_000: begin end
	7'b11_10_000: begin end
	7'b11_11_000: begin end
	7'b11_11_100: begin end
	7'b11_11_110: begin end
	7'b11_11_111: begin end
	7'b?0_11_111: begin end
	7'b?0_01_111: begin end
	7'b?0_00_111: begin end
	7'b?0_00_011: begin end
	7'b?0_00_001: begin end
	7'b?0_00_000: begin end
	default: assert(0);
	endcase

	always @(posedge S_APB_PCLK)
	if (s_request && S_PRESETn)
		assert(S_APB_PSEL && S_APB_PENABLE);

	always @(posedge gbl_clk)
	if (!s_tfr_request && S_PRESETn)
		assert(!M_APB_PSEL);

	always @(posedge gbl_clk)
	if (M_APB_PSEL)
		assert(m_request && !m_ack);

	always @(posedge gbl_clk)
	if (S_PRESETn && (m_ack || s_ack_pipe || s_ack || S_APB_PREADY))
		assert(!M_APB_PSEL);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg			fnvr_check;
	(* anyconst *)	reg	[3+DW/8+DW:0]	fnvr_write;
	(* anyconst *)	reg	[AW-1:0]	fnvr_addr;
	(* anyconst *)	reg	[1+DW-1:0]	fnvr_return;

	always @(posedge gbl_clk)
	if (S_APB_PSEL && fnvr_check)
	begin
		assume({ S_APB_PPROT, S_APB_PWSTRB, S_APB_PWDATA } != fnvr_write);
		assume(S_APB_PADDR != fnvr_addr);
	end

	always @(posedge gbl_clk)
	if (M_APB_PSEL && fnvr_check && M_PRESETn)
	begin
		assert({ M_APB_PPROT, M_APB_PWSTRB, M_APB_PWDATA } != fnvr_write);
		assert(M_APB_PADDR != fnvr_addr);
	end

	always @(posedge gbl_clk)
	if (M_APB_PSEL && M_PRESETn)
	begin
		assert(M_APB_PADDR  == S_APB_PADDR);
		assert(M_APB_PWRITE == S_APB_PWRITE);
		assert(M_APB_PWDATA == S_APB_PWDATA);
		assert(M_APB_PWSTRB == S_APB_PWSTRB);
	end

	always @(posedge gbl_clk)
	if (fnvr_check && M_APB_PSEL && M_APB_PENABLE && M_APB_PREADY)
		assume({ M_APB_PSLVERR, M_APB_PRDATA } != fnvr_return);
	
	always @(posedge gbl_clk)
	if (fnvr_check && m_ack)
		assert({ m_pslverr, m_prdata } != fnvr_return);

	always @(posedge gbl_clk)
	if (fnvr_check && S_APB_PSEL && S_APB_PENABLE && S_APB_PREADY)
		assert({ S_APB_PSLVERR, S_APB_PRDATA } != fnvr_return);
	

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[2:0]	cvr_reads, cvr_writes;

	initial	cvr_writes = 0;
	always @(posedge S_APB_PCLK)
	if (!S_PRESETn)
		cvr_writes <= 0;
	else if (S_APB_PSEL && S_APB_PENABLE && S_APB_PREADY && S_APB_PWRITE
			&& !cvr_writes[2])
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge S_APB_PCLK)
	if (!S_PRESETn)
		cvr_reads <= 0;
	else if (S_APB_PSEL && S_APB_PENABLE && S_APB_PREADY && !S_APB_PWRITE
			&& !cvr_reads[2])
		cvr_reads <= cvr_reads + 1;

	always @(*)
	if (S_PRESETn)
	begin
		cover(cvr_writes >= 2);
		cover(cvr_reads  >= 2);

		cover(cvr_writes >= 3);
		cover(cvr_reads  >= 3);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_NCLK = 5;
	reg	[F_NCLK-1:0]	gbl_sclk, gbl_mclk;

	always @(posedge gbl_clk)
		gbl_sclk <= { gbl_sclk[F_NCLK-2:0], S_APB_PCLK };

	always @(posedge gbl_clk)
		gbl_mclk <= { gbl_mclk[F_NCLK-2:0], M_APB_PCLK };

	always @(posedge gbl_clk)
	if (gbl_sclk == 0)
		assume(S_APB_PCLK);
	else if (&gbl_sclk)
		assume(!S_APB_PCLK);

	always @(posedge gbl_clk)
	if (gbl_mclk == 0)
		assume(M_APB_PCLK);
	else if (&gbl_mclk)
		assume(!M_APB_PCLK);


	// }}}
`endif
// }}}
endmodule
