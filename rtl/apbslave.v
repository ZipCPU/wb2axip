////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	apbslave.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Just a simple demonstration APB slave
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
module	apbslave #(
		parameter	C_APB_ADDR_WIDTH = 12,
		parameter	C_APB_DATA_WIDTH = 32,
		localparam	AW = C_APB_ADDR_WIDTH,
		localparam	DW = C_APB_DATA_WIDTH
	) (
		input	wire			PCLK, PRESETn,
		input	wire			PSEL,
		input	wire			PENABLE,
		output	reg			PREADY,
		input	wire	[AW-1:0]	PADDR,
		input	wire			PWRITE,
		input	wire	[DW-1:0]	PWDATA,
		output	reg	[DW-1:0]	PRDATA,
		output	reg			PSLVERR
	);

	// Register declarations
	// {{{
	// Just our demonstration "memory" here
	reg	[DW-1:0]	mem	[0:(1<<AW)-1];
	// }}}

	// PREADY
	// {{{
	initial	PREADY = 1'b0;
	always @(posedge PCLK)
	if (!PRESETn)
		PREADY <= 1'b0;
	else if (PSEL && !PENABLE)
		PREADY <= 1'b1;
	else
		PREADY <= 1'b0;
	// }}}

	// mem writes
	// {{{
	always @(posedge PCLK)
	if (PRESETn && PSEL && !PENABLE && PWRITE)
		mem[PADDR] <= PWDATA;
	// }}}

	// PRDATA, memory reads
	// {{{
	always @(posedge PCLK)
	if (PSEL && !PENABLE && !PWRITE)
		PRDATA <= mem[PADDR];
	// }}}

	// PSLVERR -- unused in this design, and so kept at zero
	// {{{
	always @(*)
		PSLVERR = 1'b0;
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
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fapb_slave #(.AW(C_APB_ADDR_WIDTH), .DW(C_APB_DATA_WIDTH),
		.F_OPT_MAXSTALL(1)
	) fapb (PCLK, PRESETn,
		PSEL, PENABLE, PREADY, PADDR, PWRITE, PWDATA, PRDATA, PRSLVERR);

	always @(*)
	if (PRESETn && PSEL && PENABLE)
		assert(PREADY);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg [AW-1:0]	f_addr;
	reg	[DW-1:0]		f_data;

	integer	ik;
	initial for(ik=0; ik<(1<<AW); ik=ik+1)
		mem[ik] = 0;

	initial	f_data = 0;
	always @(posedge PCLK)
	if (PRESETn && PSEL && !PENABLE && PWRITE && PADDR == f_addr)
		f_data <= PWDATA;

	always @(posedge PCLK)
	if (PSEL && PENABLE && PREADY && !PWRITE && PADDR == f_addr)
		assert(PRDATA == f_data);

	always @(*)
		assert(f_data == mem[f_addr]);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[2:0]	cvr_reads, cvr_writes, cvr_seq;

	initial	cvr_writes = 0;
	always @(posedge PCLK)
	if (!PRESETn)
		cvr_writes <= 0;
	else if (PSEL && PENABLE && PREADY && PWRITE && !cvr_writes[2])
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge PCLK)
	if (!PRESETn)
		cvr_reads <= 0;
	else if (PSEL && PENABLE && PREADY && !PWRITE && !cvr_reads[2])
		cvr_reads <= cvr_reads + 1;

	always @(*)
		cover(cvr_writes[2]);

	always @(*)
		cover(cvr_reads[2]);

	initial	cvr_seq = 0;
	always @(posedge PCLK)
	if (!PRESETn)
		cvr_seq <= 0;
	else if (PSEL && PENABLE && PREADY && !PWRITE && PADDR == f_addr)
	begin
		if (cvr_seq == 0 && PRDATA == 32'h12345678)
			cvr_seq[0] <= 1'b1;
		if (cvr_seq[0] && PRDATA == 32'h87654321)
			cvr_seq[1] <= 1'b1;
		if (cvr_seq[1] && PRDATA == 32'h0)
			cvr_seq[2] <= 1'b1;
	end

	always @(*)
		cover(PRESETn && !PSEL && !PENABLE && cvr_seq[2]);
	// }}}
`endif
// }}}
endmodule
