////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fav_slave.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Formal properties of an Avalon slave.  These are the properties
//		the module owning the slave should use: they assume inputs from
//	the bus master, and assert that the outputs from the slave are valid.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
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
module	fav_slave(i_clk, i_reset,
		i_av_read,
		i_av_write,
		i_av_address,
		i_av_writedata,
			i_av_byteenable,
		i_av_lock,
		i_av_waitrequest,	// = wb_stall
		//
		i_av_writeresponsevalid,
		//
		i_av_readdatavalid,
		i_av_readdata,
		i_av_response,	// Error response = 2'b11
		f_rd_nreqs, f_rd_nacks, f_rd_outstanding,
		f_wr_nreqs, f_wr_nacks, f_wr_outstanding);
	parameter	DW=32, AW=14;
	parameter	F_LGDEPTH=6;
	parameter	[(F_LGDEPTH-1):0]	F_MAX_REQUESTS = 62;
	input	wire			i_clk, i_reset;
	input	wire			i_av_read;
	input	wire			i_av_write;
	input	wire	[(AW-1):0]	i_av_address;
	input	wire	[(DW-1):0]	i_av_writedata;
	input	wire	[(DW/8-1):0]	i_av_byteenable;
	input	wire			i_av_lock;
	//
	input	wire			i_av_waitrequest;
	input	wire			i_av_writeresponsevalid;
	input	wire			i_av_readdatavalid;
	input	wire	[(DW-1):0]	i_av_readdata;
	input	wire	[1:0]		i_av_response;
	//
	output	reg	[(F_LGDEPTH-1):0] f_rd_nreqs, f_rd_nacks;
	output	wire	[(F_LGDEPTH-1):0] f_rd_outstanding;
	output	reg	[(F_LGDEPTH-1):0] f_wr_nreqs, f_wr_nacks;
	output	wire	[(F_LGDEPTH-1):0] f_wr_outstanding;

	assert	property(F_MAX_REQUESTS < {(F_LGDEPTH){1'b1}});



	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(*)
		assert((f_past_valid) || (i_reset));

	wire	[AW:0]	f_rd_request;
	assign	f_rd_request = { i_av_read,  i_av_address };

	wire	[(AW+DW+(DW/8)):0]	f_wr_request;
	assign	f_wr_request = { i_av_write, i_av_address, i_av_writedata,
					i_av_byteenable };


	always @($global_clock)
	if ((f_past_valid)&&(!$rose(i_clk)))
	begin
		assume($stable(f_rd_request));
		assume($stable(f_wr_request));
		assume($stable(i_av_lock));

		assert($stable(i_av_readdatavalid));
		assert($stable(i_av_writeresponsevalid));
		assert($stable(i_av_readdata));
		assert($stable(i_av_response));
	end

	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_av_lock)))
			assume((!i_av_lock)||(i_av_read)||(i_av_write));

	initial	f_rd_nreqs = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_rd_nreqs <= 0;
		else if ((i_av_read)&&(!i_av_waitrequest))
			f_rd_nreqs <= f_rd_nreqs + 1'b1;

	initial	f_rd_nacks = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_rd_nacks <= 0;
		else if (i_av_readdatavalid)
			f_rd_nacks <= f_rd_nacks + 1'b1;

	assign	f_rd_outstanding = f_rd_nreqs - f_rd_nacks;

	initial	f_wr_nreqs = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_wr_nreqs <= 0;
		else if ((i_av_write)&&(!i_av_waitrequest))
			f_wr_nreqs <= f_wr_nreqs + 1'b1;

	initial	f_wr_nacks = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_wr_nacks <= 0;
		else if (i_av_writeresponsevalid)
			f_wr_nacks <= f_wr_nacks + 1'b1;

	assign	f_wr_outstanding = f_wr_nreqs - f_wr_nacks;


	initial	assume(!i_av_read);
	initial	assume(!i_av_write);
	initial	assume(!i_av_lock);
	//
	initial	assert(!i_av_readdatavalid);
	initial	assert(!i_av_writeresponsevalid);
	//

	always @(posedge i_clk)
		if (i_reset)
		begin
			assume(!i_av_read);
			assume(!i_av_write);
		end

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_reset)))
		begin
			assert(!i_av_readdatavalid);
			assert(!i_av_writeresponsevalid);
			assert(f_rd_nreqs == 0);
			assert(f_rd_nacks == 0);
			assert(f_wr_nreqs == 0);
			assert(f_wr_nacks == 0);
		end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_av_waitrequest))&&($past(i_av_read)))
		assume($stable(f_rd_request));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_av_waitrequest))&&($past(i_av_write)))
		assume($stable(f_wr_request));

	always @(*)
		assume((!i_av_read)||(!i_av_write));

	always @(*)
		assert((!i_av_writeresponsevalid)||(!i_av_readdatavalid));

	always @(posedge i_clk)
		if (f_rd_outstanding == 0)
			assert(!i_av_readdatavalid);

	always @(posedge i_clk)
		if (f_wr_outstanding == 0)
			assert(!i_av_writeresponsevalid);

endmodule
