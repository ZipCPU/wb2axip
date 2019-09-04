////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sfifothresh.v
//
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
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// The WB2AXIP project is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.
//
// You should have received a copy of the GNU General Public License along with
// this program.  (It's in the $(ROOT)/doc directory.  Run make with no target
// there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
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

	sfifo #(.BW(BW), .LGFLEN(LGFLEN), .OPT_ASYNC_READ(OPT_ASYNC_READ))
	sfifoi(i_clk, i_reset, i_wr, i_data, o_full, o_fill, i_rd,
		o_data, o_empty);

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
