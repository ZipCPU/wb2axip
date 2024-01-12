////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxil_register.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	While it may be fairly easy to verify that a core follows the
//		bus protocol, it's another thing to prove that the answers it
//	returns are the right ones.
//
//	This core is meant to be a complement to the fwb_slave logic, for slaves
//	that consist of a series of registers.  This core will test whether a
//	register can be written to using Wishbone, and/or read back properly
//	later.  It assumes a register having a single clock latency.
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
module	faxil_register #(
		// {{{
		parameter		AW = 4,
		parameter		DW = 32,
		parameter [AW-1:0]	ADDR = 0,
		parameter [DW-1:0]	MASK = -1,
		parameter [DW-1:0]	FIXED_BIT_MASK = 0,
		localparam		AXILLSB = $clog2(DW/8),
		parameter [0:0]		OPT_ASYNC_RESET = 1'b0,
		parameter [0:0]		OPT_INITIAL = 1'b0
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire			S_AXIL_AWW,
		input	wire	[AW-1:0]	S_AXIL_AWADDR,
		input	wire	[DW-1:0]	S_AXIL_WDATA,
		input	wire	[DW/8-1:0]	S_AXIL_WSTRB,
		input	wire			S_AXIL_BVALID,
		//
		input	wire			S_AXIL_AR,
		input	wire	[AW-1:0]	S_AXIL_ARADDR,
		input	wire			S_AXIL_RVALID,
		input	wire	[DW-1:0]	S_AXIL_RDATA,
		input	wire	[DW-1:0]	i_register
		// }}}
	);

	// Local register, reset assumption
	// {{{
	reg		f_past_valid;
	reg [DW-1:0]	f_reg;
	integer		ik;
	reg [DW-1:0]	non_ro_write;
	wire	[31:0]	error_mask;


	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(*)
		assert((MASK & FIXED_BIT_MASK) == 0);
	// }}}

	// f_reg -- A formal copy of the register of interest
	// {{{
	always @(*)
	begin
		non_ro_write = f_reg;
		for(ik=0; ik < DW/8; ik=ik+1)
		if (S_AXIL_WSTRB[ik])
			non_ro_write[ik*8 +: 8] = S_AXIL_WDATA[ik*8 +: 8];

		non_ro_write = (non_ro_write & ~FIXED_BIT_MASK)
				| (f_reg & FIXED_BIT_MASK);
	end

	generate if (OPT_ASYNC_RESET)
	begin : OPT_ASYNC
		always @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN)
		if (!S_AXI_ARESETN)
			f_reg <= i_register;
		else if (S_AXIL_AWW
			&& S_AXIL_AWADDR[AW-1:AXILLSB] == ADDR[AW-1:AXILLSB])
		begin
			f_reg <= non_ro_write;
		end
	end else begin : SYNC_RESET
		reg	last_reset;

		initial	last_reset = 1'b1;
		always @(posedge S_AXI_ACLK)
			last_reset <= !S_AXI_ARESETN;

		always @(posedge S_AXI_ACLK)
		if (last_reset)
			f_reg <= i_register;
		else if (S_AXIL_AWW
			&& S_AXIL_AWADDR[AW-1:AXILLSB] == ADDR[AW-1:AXILLSB])
		begin
			f_reg <= non_ro_write;
		end

	end endgenerate
	// }}}

	// Comparing f_reg against i_register
	// {{{
	assign	error_mask = (f_reg ^ i_register) & MASK;

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		assert(error_mask == 0);
	// }}}

	// Verifying S_AXIL_BVALID && S_AXIL_RVALID
	// {{{
	// This is a challenge if for no other reason than that we don't
	// have access to the full protocol here.  Therefore, we're only
	// going to verify that these flags are high--not that they fall
	// properly.
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN)
			|| (OPT_ASYNC_RESET && !S_AXI_ARESETN))
		assert(!S_AXIL_BVALID || (!f_past_valid && !OPT_INITIAL));
	else if ($past(S_AXIL_AWW
			&& S_AXIL_AWADDR[AW-1:AXILLSB] == ADDR[AW-1:AXILLSB]))
		assert(S_AXIL_BVALID);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN)
			|| (OPT_ASYNC_RESET && !S_AXI_ARESETN))
		assert(!S_AXIL_RVALID || (!f_past_valid && !OPT_INITIAL));
	else if ($past(S_AXIL_AR
			&& S_AXIL_ARADDR[AW-1:AXILLSB] == ADDR[AW-1:AXILLSB]))
		assert(S_AXIL_RVALID);
	// }}}

	// Verifying S_AXIL_RDATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN && S_AXIL_AR
		&& S_AXIL_ARADDR[AW-1:AXILLSB] == ADDR[AW-1:AXILLSB]))
		assert(S_AXIL_RDATA == $past(i_register));
	// }}}

endmodule
