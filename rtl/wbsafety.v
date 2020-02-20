////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbsafety.v
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019-2020, Gisselquist Technology, LLC
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
`default_nettype	none
//
module wbsafety(i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_stall, o_wb_ack, o_wb_idata, o_wb_err,
		o_reset, o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			o_wb_sel,
		i_wb_stall, i_wb_ack, i_wb_idata, i_wb_err,
		o_fault);
	parameter	AW = 28, DW = 32;
	parameter	OPT_TIMEOUT = 12;
	parameter	MAX_DEPTH = (OPT_TIMEOUT);
	localparam	LGTIMEOUT = $clog2(OPT_TIMEOUT+1);
	localparam	LGDEPTH   = $clog2(MAX_DEPTH+1);
	parameter [0:0]	OPT_SELF_RESET = 1'b1;
	parameter [0:0]	F_OPT_FAULTLESS = 1'b1;
	//
	input	wire	i_clk, i_reset;
	//
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[AW-1:0]	i_wb_addr;
	input	wire	[DW-1:0]	i_wb_data;
	input	wire	[DW/8-1:0]	i_wb_sel;
	output	reg			o_wb_ack, o_wb_err, o_wb_stall;
	output	reg	[DW-1:0]	o_wb_idata;
	//
	output	reg			o_reset;
	output	reg			o_wb_cyc, o_wb_stb, o_wb_we;
	output	reg	[AW-1:0]	o_wb_addr;
	output	reg	[DW-1:0]	o_wb_data;
	output	reg	[DW/8-1:0]	o_wb_sel;
	input	wire			i_wb_ack, i_wb_err, i_wb_stall;
	input	wire	[DW-1:0]	i_wb_idata;
	//
	output	reg			o_fault;

	reg			none_expected;
	reg	[LGDEPTH-1:0]	expected_returns;
	reg	[LGTIMEOUT-1:0]	stall_timer, wait_timer;
	reg			timeout;
	reg			faulty_return;

	wire			skd_stb, skd_o_ready, skd_we;
	reg			skd_stall;
	wire	[AW-1:0]	skd_addr;
	wire	[DW-1:0]	skd_data;
	wire	[DW/8-1:0]	skd_sel;

	////////////////////////////////////////////////////////////////////////
	//
	// Start with a skid buffer on all incoming signals
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	FORMAL
	//
	// We know the skid buffer works.  It's irrelevant to our proof.
	// Therefore, remove it during formal testing, lest we need to
	// check it as well.  Further, we make this a parameter--but only
	// when FORMAL is defined--so that it may be overridden in that case.
	//
	parameter	[0:0]	SKID_PASSTHROUGH = 1'b1;
`else
	localparam	[0:0]	SKID_PASSTHROUGH = 1'b0;
`endif

	skidbuffer #(.DW(1+AW+DW+(DW/8)),
		.OPT_PASSTHROUGH(SKID_PASSTHROUGH))
	skd(i_clk, i_reset || !i_wb_cyc, i_wb_stb, skd_o_ready,
		{ i_wb_we, i_wb_addr, i_wb_data, i_wb_sel },
		skd_stb, !skd_stall, { skd_we, skd_addr, skd_data, skd_sel });

	always @(*)
		o_wb_stall = !skd_o_ready;


	////////////////////////////////////////////////////////////////////////
	//
	//


	initial	stall_timer = 0;
	always @(posedge i_clk)
	if (!i_reset && o_wb_stb && i_wb_stall)
	begin
		if (stall_timer <= OPT_TIMEOUT)
			stall_timer <= stall_timer + 1;
	end else 
		stall_timer <= 0;

	initial	wait_timer = 0;
	always @(posedge i_clk)
	if (!i_reset && o_wb_cyc && !o_wb_stb && !i_wb_ack && !i_wb_err
		&& !none_expected)
	begin
		if (wait_timer <= OPT_TIMEOUT)
			wait_timer <= wait_timer + 1;
	end else
		wait_timer <= 0;

	initial	timeout = 0;
	always @(posedge i_clk)
	if (timeout && o_wb_err)
		timeout <= 0;
	else
		timeout <= (i_wb_stall)&&(stall_timer >= OPT_TIMEOUT)
			|| ((!i_wb_ack && !i_wb_err)&&(wait_timer >= OPT_TIMEOUT));

	initial	none_expected = 1;
	initial	expected_returns = 0;
	always @(posedge i_clk)
	if (i_reset || o_reset || o_wb_err || !i_wb_cyc)
	begin
		expected_returns <= 0;
		none_expected    <= 1;
	end else case({skd_stb && !skd_stall, o_wb_ack })
	2'b10: begin
		expected_returns <= expected_returns + 1;
		none_expected <= 1'b0;
		end
	2'b01: begin
		expected_returns <= expected_returns - 1;
		none_expected <= (expected_returns == 1);
		end
	default: begin end
	endcase

	generate if (OPT_SELF_RESET)
	begin

		initial	o_reset = 1;
		always @(posedge i_clk)
		if (i_reset || o_fault)
			o_reset <= 1;
		else begin
			o_reset <= 0;
			if (o_wb_cyc && none_expected
					&&(i_wb_ack || i_wb_err))
				o_reset <= 1;
			if (timeout)
				o_reset <= 1;
		end
	end else begin

		always @(*)
			o_reset = i_reset || o_fault;

	end endgenerate

	always @(*)
	begin
		faulty_return = 0;
		if (expected_returns <= ((o_wb_stb && i_wb_stall) ? 1:0)
				+ ((o_wb_ack || o_wb_err) ? 1:0))
			faulty_return = i_wb_ack || i_wb_err;
		if (i_wb_ack && i_wb_err)
			faulty_return = 1;
		if (!i_wb_cyc || !o_wb_cyc)
			faulty_return = 0;
	end

	initial	o_fault = 0;
	always @(posedge i_clk)
	if (o_reset && !i_wb_cyc)
		o_fault <= 0;
	else begin
		if (o_wb_cyc && faulty_return)
			o_fault <= 1;
		if (i_wb_cyc && timeout)
			o_fault <= 1;
	end

	initial	o_wb_cyc = 1'b0;
	always @(posedge i_clk)
	if (i_reset || (o_wb_cyc && i_wb_err) || o_reset || o_fault
			|| (i_wb_cyc && o_wb_err))
		o_wb_cyc <= 1'b0;
	else
		o_wb_cyc  <= i_wb_cyc && (o_wb_cyc || i_wb_stb);

	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset || (o_wb_cyc && i_wb_err) || o_reset || o_fault || !i_wb_cyc
			|| (i_wb_cyc && o_wb_err))
		o_wb_stb <= 1'b0;
	else if (!o_wb_stb || !i_wb_stall)
		o_wb_stb  <= skd_stb;

	always @(posedge i_clk)
	if (!o_wb_stb || !i_wb_stall)
	begin
		o_wb_we   <= skd_we;
		o_wb_addr <= skd_addr;
		o_wb_data <= skd_data;
		o_wb_sel  <= skd_sel;
	end

	always @(posedge i_clk)
		o_wb_idata <= i_wb_idata;

	always @(*)
	begin
		skd_stall = (o_wb_stb && i_wb_stall);
		if (i_reset)
			skd_stall = 1'b1;
		if (o_fault)
			skd_stall = 1'b0;
		else if (o_reset)
			skd_stall = 1'b1;
	end

	initial	o_wb_ack   = 0;
	initial	o_wb_err   = 0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
	begin
		o_wb_ack   <= 1'b0;
		o_wb_err   <= 1'b0;
	end else if (!o_reset && !o_fault)
	begin
		if (timeout || faulty_return || i_wb_err)
		begin
			o_wb_ack <= 1'b0;
			o_wb_err <= (expected_returns > ((o_wb_ack||o_wb_err) ? 1:0));
		end else begin
			o_wb_ack <= o_wb_cyc && i_wb_ack && !i_wb_err;
			o_wb_err <= 1'b0;
		end
	end else begin
		o_wb_ack   <= 1'b0;
		o_wb_err   <= (i_wb_stb && !skd_stall);
	end


`ifdef	FORMAL
	localparam	DOWNSTREAM_ACK_DELAY = OPT_TIMEOUT/2-1;
	localparam	UPSTREAM_ACK_DELAY = OPT_TIMEOUT + 3;
	wire	[LGDEPTH-1:0]	fwbs_nreqs, fwbs_nacks, fwbs_outstanding;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	fwb_slave #(.AW(AW), .DW(DW),
		// .F_MAX_ACK_DELAY(UPSTREAM_ACK_DELAY),
		.F_LGDEPTH(LGDEPTH),
		.F_OPT_DISCONTINUOUS(1),
		.F_OPT_MINCLOCK_DELAY(0)
	) wbs (i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_ack, o_wb_stall, o_wb_idata, o_wb_err,
		fwbs_nreqs, fwbs_nacks, fwbs_outstanding
	);

	always @(*)
		assert(none_expected == (expected_returns == 0));

	// Just so we pass the skid buffer's assumptions ...
	always @(posedge i_clk)
	if (f_past_valid && $past(i_wb_stb && o_wb_stall))
		assume($stable(i_wb_data));

	always @(*)
	if (i_wb_cyc && !o_wb_err && !o_fault)
		assert(expected_returns == fwbs_outstanding);

	always @(*)
		cover(!i_reset && skd_stb);

	always @(*)
		cover(!i_reset && skd_stb && !o_reset);

	always @(*)
		cover(!i_reset && skd_stb && !skd_stall);

	always @(*)
		cover(!i_reset && skd_stb && o_wb_stb);

	always @(*)
		cover(!i_reset && skd_stb && o_wb_stb && i_wb_ack);

	always @(*)
		cover(!i_reset && fwbs_nacks > 4);

	generate if (F_OPT_FAULTLESS)
	begin
		wire	[LGDEPTH-1:0]	fwbm_nreqs, fwbm_nacks,fwbm_outstanding;
		reg	[LGDEPTH-1:0]	mreqs, sacks;


		fwb_master #(.AW(AW), .DW(DW),
			.F_MAX_ACK_DELAY(DOWNSTREAM_ACK_DELAY),
			.F_MAX_ACK_DELAY(DOWNSTREAM_ACK_DELAY),
			.F_MAX_STALL(DOWNSTREAM_ACK_DELAY),
			.F_LGDEPTH(LGDEPTH),
			.F_OPT_DISCONTINUOUS(1),
			.F_OPT_MINCLOCK_DELAY(0)
		) wbm (i_clk, o_reset,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_idata, i_wb_err,
			fwbm_nreqs, fwbm_nacks, fwbm_outstanding);

		always @(*)
			assert(!o_fault);

		always @(*)
		if (!i_reset && i_wb_cyc && o_wb_cyc)
			assert(expected_returns == fwbm_outstanding
				+ (o_wb_stb ? 1:0)
				+ ((o_wb_ack|o_wb_err) ? 1:0));

		always @(*)
			assert(!timeout);

		always @(*)
		if (o_wb_err)
			assert(!o_wb_cyc);

		always @(*)
			sacks = fwbs_nacks + (o_wb_ack ? 1:0);

		always @(*)
		if (!o_wb_err && i_wb_cyc && o_wb_cyc)
			assert(sacks == fwbm_nacks);

		always @(posedge i_clk)
		if (!i_reset && i_wb_cyc && expected_returns > 0)
			assert(o_wb_cyc || o_wb_err);

		always @(*)
			mreqs = fwbm_nreqs + (o_wb_stb ? 1:0);

		always @(*)
		if (!o_wb_err && i_wb_cyc && o_wb_cyc)
			assert(fwbs_nreqs == mreqs);

		always @(*)
		if (i_wb_cyc && o_wb_cyc && fwbs_outstanding > 0)
			assert(i_wb_we == o_wb_we);

		always @(*)
		if (fwbs_nacks != 0 && i_wb_cyc)
			assert(o_wb_cyc || o_wb_err);

	end else begin

		always @(posedge i_clk)
			cover(o_fault);

		always @(posedge i_clk)
		if (f_past_valid && $past(faulty_return))
			cover(o_fault);

		always @(posedge i_clk)
		if (f_past_valid && $past(timeout))
			cover(o_fault);

		if (OPT_SELF_RESET)
		begin

			reg	faulted;

			initial	faulted = 0;
			always @(posedge i_clk)
			if (i_reset)
				faulted <= 0;
			else if (o_fault)
				faulted <= 1;


			always @(posedge i_clk)
				cover(faulted && $fell(o_reset));

		end

	end endgenerate
`endif
endmodule
