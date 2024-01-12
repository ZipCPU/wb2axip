////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fav_slave.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Formal properties of an Avalon slave.  These are the properties
//		the module owning the slave should use: they assume inputs from
//	the bus master, and assert that the outputs from the slave are valid.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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

	wire	[AW+(DW/8):0]	f_rd_request;
	assign	f_rd_request = { i_av_read,  i_av_byteenable, i_av_address };

	wire	[(AW+DW+(DW/8)):0]	f_wr_request;
	assign	f_wr_request = { i_av_write, i_av_address, i_av_writedata,
					i_av_byteenable };

	/////////////////////////////
	//
	// Require that nothing changes, save on a clock tick.
	//
	// This is only required if yosys is using the clk2fflogic
	// command, a command only required if multiple clocks are
	// in use.  Since this can greatly slow down formal proofs,
	// we limit any code associated with this option to only
	// those times the option is in play.
	//
	/////////////////////////////

	generate if (F_OPT_CLK2FFLOGIC)
	begin
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
	end endgenerate

	/////////////////////////////
	//
	// Assumptions about a slave's inputs
	//
	/////////////////////////////


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
			assume(!i_av_lock);
		end

	always @(*)
		if (i_av_write)
			assume(|i_av_byteenable);

	// It is a protocol violation to issue both read and write requests
	// on the same clock
	always @(*)
		assume((!i_av_read)||(!i_av_write));

	// Once a read request has been placed upon the bus, it will remain
	// there until wait request goes low
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_av_waitrequest))&&($past(i_av_read)))
		assume((i_reset)||(f_rd_request == $past(f_rd_request)));

	// Same thing for a write request
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_av_waitrequest))&&($past(i_av_write)))
		assume((i_reset)||(f_wr_request == $past(f_wr_request)));

	// A lock request can only be asserted at the same time a read or
	// write request is being made.
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_av_lock)))
			assume((!i_av_lock)||(i_av_read)||(i_av_write));

	// A lock request can only be de-asserted following the last read
	// or write request made with it asserted
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_av_lock)
				&&(!i_av_read)&&(!i_av_write)))
			assume((i_reset)||(i_av_lock)
				||(i_av_read)||(i_av_write));


	/////////////////////////////
	//
	// Internal state variables
	//
	/////////////////////////////

	// Count the number of read requests
	initial	f_rd_nreqs = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_rd_nreqs <= 0;
		else if ((i_av_read)&&(!i_av_waitrequest))
			f_rd_nreqs <= f_rd_nreqs + 1'b1;

	// Count the number of read acknowledgements
	initial	f_rd_nacks = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_rd_nacks <= 0;
		else if (i_av_readdatavalid)
			f_rd_nacks <= f_rd_nacks + 1'b1;

	// The difference between read requests and acknowledgements is
	// the number of outstanding read requests
	assign	f_rd_outstanding = (i_reset) ? 0 : (f_rd_nreqs - f_rd_nacks);

	// Count the number of write requests
	initial	f_wr_nreqs = 0;
	always @(posedge i_clk)
		if (i_reset)
			f_wr_nreqs <= 0;
		else if ((i_av_write)&&(!i_av_waitrequest))
			f_wr_nreqs <= f_wr_nreqs + 1'b1;

	// Count the number of write acknowledgements/responses
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

	// Just like a read and write request cannot both be made at the same
	// time, neither can both responses come back at the same time
	always @(*)
		assert((!i_av_writeresponsevalid)||(!i_av_readdatavalid));

	// If nothing is outstanding, then there should be no responses.
	// If i_reset is asserted, a response may have been registered, and
	// so may still return on this clock.
	always @(posedge i_clk)
		if ((f_rd_outstanding == 0)&&(!i_reset)
				&&((!i_av_read)||(i_av_waitrequest)))
			assert(!i_av_readdatavalid);

	always @(posedge i_clk)
		if ((f_wr_outstanding == 0)&&(!i_reset)
				&&((!i_av_write)||(i_av_waitrequest)))
			assert(!i_av_writeresponsevalid);

	always @(*)
		assert({1'b0, f_wr_outstanding} + { 1'b0, f_rd_outstanding }
			< F_MAX_REQUESTS);

	generate if (F_OPT_MAX_STALL > 0)
	begin
		reg	[(LGWAIT-1):0]	stall_count;

		initial	stall_count = 0;
		always @(posedge i_clk)
			if (i_reset)
				stall_count <= 0;
			else if (((i_av_read)||(i_av_write))&&(i_av_waitrequest))
				stall_count <= stall_count + 1'b1;
			else
				stall_count <= 0;

		always @(*)
			assert((i_reset)||(stall_count < F_OPT_MAX_STALL));
	end endgenerate

	generate if (F_OPT_MAX_WAIT > 0)
	begin
		reg	[(LGWAIT-1):0]	read_wait, write_wait;

		//
		// Insist on a minimum amount of time to wait for a *read*
		// response.
		//
		always @(posedge i_clk)
			if (i_reset)
				read_wait <= 0;
			else if ((i_av_readdatavalid)
					||((i_av_read)&&(!i_av_waitrequest)))
				read_wait <= 0;
			else if (f_rd_outstanding > 0)
				read_wait <= read_wait + 1'b1;

		always @(*)
			assert((i_av_readdatavalid)
				||(f_rd_outstanding == 0)
				||(read_wait < F_OPT_MAX_WAIT));


		//
		// Insist on a minimum amount of time to wait for a *write*
		// response.
		//
		always @(posedge i_clk)
			if (i_reset)
				write_wait <= 0;
			else if ((i_av_writeresponsevalid)
					||((i_av_write)&&(!i_av_waitrequest)))
				write_wait <= 0;
			else if (f_wr_outstanding > 0)
				write_wait <= write_wait + 1'b1;

		always @(*)
			assert((i_av_writeresponsevalid)
				||(f_wr_outstanding == 0)
				||(write_wait < F_OPT_MAX_WAIT));
	end endgenerate

endmodule
