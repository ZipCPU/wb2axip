////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sfifothresh.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A synchronous data FIFO, generated from sfifo.v.  This
//		particular version extends the FIFO interface with a threshold
//	calculator, to create an interrupt/signal when the FIFO has greater
//	than the threshold elements within it.
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
module sfifothresh(i_clk, i_reset,
		i_wr, i_data, o_full, o_fill,
		i_rd, o_data, o_empty,
		i_threshold, o_int);
	parameter	BW=8;	// Byte/data width
	parameter 	LGFLEN=4;
	parameter [0:0]	OPT_ASYNC_READ = 1'b1;
	localparam	FLEN=(1<<LGFLEN);

	//
	//
	input	wire		i_clk;
	input	wire		i_reset;
	//
	// Write interface
	input	wire		i_wr;
	input	wire [(BW-1):0]	i_data;
	output	wire 		o_full;
	output	wire [LGFLEN:0]	o_fill;
	//
	// Read interface
	input	wire		i_rd;
	output	wire [(BW-1):0]	o_data;
	output	wire		o_empty;	// True if FIFO is empty
	// 
	input	wire [LGFLEN:0]	i_threshold;
	output	reg		o_int;

	wire	w_wr = (i_wr && !o_full);
	wire	w_rd = (i_rd && !o_empty);

	sfifo #(
		.BW(BW), .LGFLEN(LGFLEN), .OPT_ASYNC_READ(OPT_ASYNC_READ)
	) sfifoi(
		i_clk, i_reset, i_wr, i_data, o_full, o_fill, i_rd,
		o_data, o_empty
	);

	initial	o_int = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_int <= 0;
	else case({ w_wr, w_rd })
	2'b01: o_int <= (o_fill-1 >= i_threshold);
	2'b10: o_int <= (o_fill+1 >= i_threshold);
	default: o_int <= o_fill >= i_threshold;
	endcase

`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_int);
	else
		assert(o_int == (o_fill >= $past(i_threshold)));
`endif
endmodule
