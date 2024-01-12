////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	faxis_master.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Formal properties for verifying the proper functionality of an
//		AXI Stream master.
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
`default_nettype none
// }}}
module	faxis_master #(
		// {{{
		parameter	F_MAX_PACKET = 0,
		parameter	F_MIN_PACKET = 0,
		parameter	F_MAX_STALL  = 0,
		parameter	C_S_AXI_DATA_WIDTH  = 32,
		parameter	C_S_AXI_ID_WIDTH = 1,
		parameter	C_S_AXI_ADDR_WIDTH = 1,
		parameter	C_S_AXI_USER_WIDTH = 1,
		parameter [0:0]	OPT_ASYNC_RESET = 1'b0,
		//
		// F_LGDEPTH is the number of bits necessary to represent a
		// packets length
		parameter	F_LGDEPTH = 32,
		//
		localparam	AW  = C_S_AXI_ADDR_WIDTH,
		localparam	DW  = C_S_AXI_DATA_WIDTH,
		localparam	IDW  = C_S_AXI_ID_WIDTH,
		localparam	UW  = C_S_AXI_USER_WIDTH
		// }}}
	) (
		// {{{
		input	wire			i_aclk, i_aresetn,
		input	wire			i_tvalid,
		input	wire			i_tready = 1,
		input	wire	[DW-1:0]	i_tdata,
		input	wire	[DW/8-1:0]	i_tstrb = {(DW/8){1'b1}},
		input	wire	[DW/8-1:0]	i_tkeep = {(DW/8){1'b1}},
		input	wire			i_tlast,
		input	wire	[(IDW>0?IDW:1)-1:0]	i_tid = {(IDW){1'b0}},
		input	wire	[(AW>0?AW:1)-1:0]	i_tdest = {(AW){1'b0}},
		input	wire	[(UW>0?UW:1)-1:0]	i_tuser = {(UW){1'b0}},
		//
		output	reg	[F_LGDEPTH-1:0]	f_bytecount,
		(* anyconst *) output	reg	[AW+IDW-1:0]	f_routecheck
		// }}}
	);

	// Signal declarations
	// {{{
`define	SLAVE_ASSUME	assert
`define	SLAVE_ASSERT	assume

	localparam	F_STALLBITS	= (F_MAX_STALL <= 1)
						? 1 : $clog2(F_MAX_STALL+2);
	reg				f_past_valid;
	reg	[F_LGDEPTH-1:0]		f_vbytes;
	reg	[F_STALLBITS-1:0]	f_stall_count;
	integer	iB;
	genvar	k;

	//
	// f_past_valid is used to make certain that temporal assertions
	// depending upon past values depend upon *valid* past values.
	// It is true for all clocks other than the first clock.
	initial	f_past_valid = 1'b0;
	always @(posedge i_aclk)
		f_past_valid <= 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Reset should always be active (low) initially
	always @(posedge i_aclk)
	if (!f_past_valid)
		`SLAVE_ASSUME(!i_aresetn);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stability properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// During and following a reset, TVALID should be deasserted
	// {{{
	always @(posedge i_aclk)
	if ((!f_past_valid)||(!i_aresetn && OPT_ASYNC_RESET)||($past(!i_aresetn)))
		`SLAVE_ASSUME(!i_tvalid);
	// }}}

	// Stability during a stall
	// {{{
	// If TVALID but not TREADY, then the master isn't allowed to change
	// anything until the slave asserts TREADY.
	always @(posedge i_aclk)
	if ((f_past_valid)&&($past(i_aresetn))&&(!OPT_ASYNC_RESET || i_aresetn)
		&&($past(i_tvalid))&&(!$past(i_tready)))
	begin
		`SLAVE_ASSUME(i_tvalid);
		`SLAVE_ASSUME($stable(i_tstrb));
		`SLAVE_ASSUME($stable(i_tkeep));
		`SLAVE_ASSUME($stable(i_tlast));
		`SLAVE_ASSUME($stable(i_tid));
		`SLAVE_ASSUME($stable(i_tdest));
		`SLAVE_ASSUME($stable(i_tuser));
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Partial data check
	// {{{
	generate for(k=0; k<DW/8; k=k+1)
	begin : CHECK_PARTIAL_DATA

		// If TVALID && !TREADY, only those TDATA values with TKEEP
		// high are required to maintain their values until TREADY
		// becomes true.
		always @(posedge i_aclk)
		if ((f_past_valid)&&($past(i_aresetn))
			&&(!OPT_ASYNC_RESET || i_aresetn)
			&&($past(i_tvalid))&&(!$past(i_tready)))
		begin
			if (i_tkeep[k])
				`SLAVE_ASSUME($stable(i_tdata[k*8 +: 8]));
			// else this is a null (don't care) byte, with
			// no data within it
			//
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Other properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	//
	// TKEEP == LOW and TSTRB == HIGH is reserved per the spec, and
	// must not be used
	always @(posedge i_aclk)
	if (i_tvalid)
		`SLAVE_ASSUME((~i_tkeep & i_tstrb)==0);

	// f_vbytes -- a count of the number of valid bytes in the current beat
	// {{{
	// It is used for counting packet lengths below.
	always @(*)
	if (!i_tvalid)
		f_vbytes = 0;
	else begin
		f_vbytes = 0;
		for(iB=0; iB < DW/8; iB=iB+1)
		if (i_tkeep[iB] && i_tstrb[iB])
			f_vbytes = f_vbytes + 1;
	end
	// }}}

	// f_bytecount
	// {{{
	// f_bytecount is the number of bytes that have taken place so far in
	// the current packet transmission.  Note that we are *only* counting
	// our location within the stream if the TUSER and TDEST fields match
	// our (solver chosen) ROUTECHECK.  That way we don't have to check
	// *EVERY POSSIBLE* TUSER and TDEST combination.
	initial	f_bytecount = 0;
	always @(posedge i_aclk)
	if (!i_aresetn)
		f_bytecount <= 0;
	else if (i_tready && i_tvalid && ({ i_tuser, i_tdest } == f_routecheck))
	begin
		if (i_tlast)
			f_bytecount <= 0;
		else
			f_bytecount <= f_bytecount + f_vbytes;
	end
	// }}}

	// f_stall_count
	// {{{
	// Count the number of clock cycles between ready's.  We'll use this in
	// a bit to insist on an (optional) minimum transfer speed.
	initial	f_stall_count = 0;
	always @(posedge i_aclk)
	if (!i_aresetn || !i_tvalid || i_tready)
		f_stall_count <= 0;
	else if (!(&f_stall_count))
		f_stall_count <= f_stall_count + 1;
	// }}}

	// F_MAX_PACKET
	// {{{
	// An optional check, to make certain packets don't exceed some maximum
	// length
	generate if (F_MAX_PACKET > 0)
	begin : MAX_PACKET

		always @(*)
			`SLAVE_ASSUME(f_bytecount + f_vbytes <= F_MAX_PACKET);

	end endgenerate
	// }}}

	// F_MIN_PACKET
	// {{{
	// An optional check, forcing a minimum packet length
	generate if (F_MIN_PACKET > 0)
	begin : MIN_PACKET

		always @(*)
		if (i_tvalid && i_tlast)
			`SLAVE_ASSUME(f_bytecount + f_vbytes >= F_MIN_PACKET);

	end endgenerate
	// }}}
	//
	// F_MAX_STALL
	// {{{
	// Another optional check, this time insisting that the READY flag can
	// only be low for up to F_MAX_STALL clocks.
	//
	generate if (F_MAX_STALL > 0)
	begin : MAX_STALL_CHECK

		always @(*)
			`SLAVE_ASSERT(f_stall_count < F_MAX_STALL);

	end endgenerate
	// }}}
	// }}}
endmodule
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
