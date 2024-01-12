////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fapb_slave.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Formal properties to describe a slave of the APB bus.  These
//		have been built based upon the AMBA 3 specification, dated
//	2003 and labeled as ARM IHI 0024B.
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
module	fapb_slave #(
		// {{{
		parameter	AW =32,	// Address width
				DW = 32, // Data width
		parameter F_OPT_MAXSTALL = 4,
		// Set F_OPT_SLVERR to 1 if your slave supports PSLVERR
		// assertion, otherwise we'll assert it remains false.
		parameter [0:0] F_OPT_SLVERR = 1'b0,
		parameter [0:0]	F_OPT_ASYNC_RESET = 1'b0,
		parameter [0:0]	F_OPT_INITIAL = 1'b1
		// }}}
	) (
		// {{{
		input	wire			PCLK, PRESETn,
		input	wire			PSEL,
		input	wire			PENABLE,
		input	wire			PREADY,	// From the slave
		input	wire	[AW-1:0]	PADDR,
		input	wire			PWRITE,
		input	wire	[DW-1:0]	PWDATA,
		input	wire	[DW/8-1:0]	PWSTRB,
		input	wire	[2:0]		PPROT,
		input	wire	[DW-1:0]	PRDATA, // Following from slave
		input	wire			PSLVERR
		// }}}
	);

`define	SLAVE_ASSUME	assume
`define	SLAVE_ASSERT	assert
	////////////////////////////////////////////////////////////////////////
	//
	// Reset
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge PCLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(!PRESETn);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//
	//

	//
	// PSEL
	// {{{
	always @(posedge PCLK)
	if (!f_past_valid && !F_OPT_ASYNC_RESET)
	begin
		`SLAVE_ASSUME(!PSEL || !F_OPT_INITIAL);
	end else if (!$past(PRESETn) || (F_OPT_ASYNC_RESET && !PRESETn))
	begin
		`SLAVE_ASSUME(!PSEL);
	end else if ($past(PSEL) && !$past(PENABLE && PREADY))
		`SLAVE_ASSUME(PSEL);
	// }}}

	//
	// PENABLE
	// {{{
	always @(posedge PCLK)
	if (!f_past_valid && !F_OPT_ASYNC_RESET)
	begin
		`SLAVE_ASSUME(!PENABLE || !F_OPT_INITIAL);
	end else if (!$past(PRESETn) || (F_OPT_ASYNC_RESET && !PRESETn))
	begin
		`SLAVE_ASSUME(!PENABLE);
	end else if (PSEL)
	begin
		if (!$past(PSEL))
			// PSEL rose, this is therefore the setup phase and
			// so PENABLE is must be false
			`SLAVE_ASSUME(!PENABLE);
		else if ($past(PENABLE))
			// Last cycle was an access phase.  PENABLE can only
			// stay high if the slave wasn't ready
			//
			// PENABLE holds if we were stalled, otherwise
			// it needs to fall to start a new transaction
			`SLAVE_ASSUME(PENABLE == !$past(PREADY));
		else
			// The last cycle was the setup phase, so we must
			// now be in the access phase.  In the access phase,
			// PENABLE should always be high
			`SLAVE_ASSUME(PENABLE);
	end // else if !PSEL -- the master might be talking to a different
		// slave, and so we don't care about PENABLE
	// }}}


	// PADDR, PWRITE, and PWDATA need to hold while stalled
	// {{{
	always @(posedge PCLK)
	if (!f_past_valid && !F_OPT_ASYNC_RESET)
	begin
		`SLAVE_ASSERT(!PREADY || !F_OPT_INITIAL);
	end else if (!$past(PRESETn) || (F_OPT_ASYNC_RESET && !PRESETn))
	begin
		`SLAVE_ASSERT(!PREADY);
	end else if ($past(PSEL) && (!$past(PENABLE) || !$past(PREADY)))
	begin
		// Stall condition.  Nothing is allowed to change
		`SLAVE_ASSUME($stable(PADDR));
		`SLAVE_ASSUME($stable(PWRITE));
		`SLAVE_ASSUME($stable(PPROT));
		if (PWRITE)
		begin
			`SLAVE_ASSUME($stable(PWDATA));
			`SLAVE_ASSUME($stable(PWSTRB));
		end
	end
	// }}}

	//
	// PREADY, and maximum stall check
	// {{{
	//	Can take on any value when PSEL is low
	//	Can take on any value when PENABLE is low
	//	If PSEL and PENABLE, can only stall F_OPT_MAXSTALL cycles before
	//	  raising PREADY
	generate if (F_OPT_MAXSTALL > 0)
	begin : MAX_STALL_CHECK

		reg	[$clog2(F_OPT_MAXSTALL+1)-1:0]	f_stall_count;

		initial	f_stall_count = 0;
		always @(posedge PCLK)
		if (!PRESETn || !PSEL || !PENABLE)
			f_stall_count <= 0;
		else if (!PREADY)
			f_stall_count <= f_stall_count + 1;

		always @(*)
			`SLAVE_ASSERT(f_stall_count < F_OPT_MAXSTALL);
	end endgenerate
	// }}}

	// PSLVERR
	// {{{
	// "Recommended" that PSLVERR be low when any of PSEL, PENABLE, or
	// PREADY are low
	// Can't generate a slave error when not ready
	always @(posedge PCLK)
	if (f_past_valid || F_OPT_INITIAL)
	begin
		if (!PSEL || !PENABLE || !PREADY || !F_OPT_SLVERR)
			`SLAVE_ASSERT(!PSLVERR);
	end
	// }}}
endmodule
