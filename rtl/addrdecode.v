////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addrdecode.v
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
module	addrdecode(i_clk, i_reset, i_valid, o_stall, i_addr, i_data,
			o_valid, i_stall, o_decode, o_addr, o_data);
	parameter	NS=8;
	parameter	AW = 32, DW=32+32/8+1+1;
	//
	// SLAVE_ADDR contains address assignments for each of the various
	// slaves we are adjudicating between.
	parameter	[NS*AW-1:0]	SLAVE_ADDR = {
				{ 3'b111, {(AW-3){1'b0}}},
				{ 3'b110, {(AW-3){1'b0}}},
				{ 3'b101, {(AW-3){1'b0}}},
				{ 3'b100, {(AW-3){1'b0}}},
				{ 3'b011, {(AW-3){1'b0}}},
				{ 3'b010, {(AW-3){1'b0}}},
				{ 4'b0010, {(AW-4){1'b0}}},
				{ 4'b0000, {(AW-4){1'b0}}} };
	//
	// SLAVE_MASK contains a mask of those address bits in SLAVE_ADDR
	// which are relevant.  It shall be true that if
	//	!SLAVE_MASK[k] then !SLAVE_ADDR[k], for any bits of k
	parameter	[NS*AW-1:0]	SLAVE_MASK = (NS <= 1) ? 0
		: { {(NS-2){ 3'b111, {(AW-3){1'b0}}}},
			{(2){ 4'b1111, {(AW-4){1'b0}} }} };
	//
	// ACCESS_ALLOWED is a bit-wise mask indicating which slaves may get
	// access to the bus.  If ACCESS_ALLOWED[slave] is true, then a master
	// can connect to the slave via this method.  This parameter is
	// primarily here to support AXI (or other similar buses) which may have
	// separate accesses for both read and write.  By using this, a
	// read-only slave can be connected, which would also naturally create
	// an error on any attempt to write to it.
	parameter	[NS-1:0]	ACCESS_ALLOWED = -1;
	//
	// If OPT_REGISTERED is set, address decoding will take an extra clock,
	// and will register the results of the decoding operation.
	parameter [0:0]	OPT_REGISTERED = 0;
	//
	// If OPT_LOWPOWER is set, then whenever the output is not valid, any
	// respective data linse will also be forced to zero in an effort
	// to minimize power.
	parameter [0:0]	OPT_LOWPOWER = 0;
	//
	// OPT_NONESEL controls whether or not the address lines are fully
	// proscribed, or whether or not a "no-slave identified" slave should
	// be created.  To avoid a "no-slave selected" output, slave zero must
	// have no mask bits set (and therefore no address bits set), and it
	// must also allow access.
	localparam [0:0] OPT_NONESEL = (!ACCESS_ALLOWED[0])
					|| (SLAVE_MASK[AW-1:0] != 0);
	//
	input	wire			i_clk, i_reset;
	//
	input	wire			i_valid;
	output	reg			o_stall;
	input	wire	[AW-1:0]	i_addr;
	input	wire	[DW-1:0]	i_data;
	//
	output	reg			o_valid;
	input	wire			i_stall;
	output	reg	[NS:0]		o_decode;
	output	reg	[AW-1:0]	o_addr;
	output	reg	[DW-1:0]	o_data;

	reg	[NS:0]		request;
	reg	[NS-1:0]	prerequest;
	reg			none_sel;
	integer			iM;

	always @(*)
	for(iM=0; iM<NS; iM=iM+1)
		prerequest[iM] = (((i_addr ^ SLAVE_ADDR[iM*AW +: AW])
				&SLAVE_MASK[iM*AW +: AW])==0)
			&&(ACCESS_ALLOWED[iM]);

	generate if (OPT_NONESEL)
	begin : NO_DEFAULT_REQUEST

		// Need to create a slave to describe when nothing is selected
		//
		always @(*)
		begin
			for(iM=0; iM<NS; iM=iM+1)
				request[iM] = i_valid && prerequest[iM];
			if (!OPT_NONESEL && (NS > 1 && |prerequest[NS-1:1]))
				request[0] = 1'b0;
		end

	end else if (NS == 1)
	begin

		always @(*)
			request = { 1'b0, i_valid };

	end else begin

		always @(*)
		begin
			for(iM=0; iM<NS; iM=iM+1)
				request[iM] = i_valid && prerequest[iM];
			if (!OPT_NONESEL && (NS > 1 && |prerequest[NS-1:1]))
				request[0] = 1'b0;
		end

	end endgenerate

	generate if (OPT_NONESEL)
	begin
		always @(*)
		begin
			// Let's assume nothing's been selected, and then check
			// to prove ourselves wrong.
			//
			// Note that none_sel will be considered an error
			// condition in the follow-on processing.  Therefore
			// it's important to clear it if no request is pending.
			none_sel = i_valid && (prerequest == 0);
			//
			// request[NS] indicates a request for a non-existent
			// slave.  A request that should (eventually) return a
			// bus error
			//
			request[NS] = none_sel;
		end
	end else begin
		always @(*)
			{ request[NS], none_sel } = 2'b00;

		// Verilator lint_off UNUSED
		wire	all_assigned_unused = none_sel;
		// Verilator lint_on  UNUSED
	end endgenerate

	generate if (OPT_REGISTERED)
	begin
		initial	o_valid = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_valid <= 0;
		else if (!o_stall)
			o_valid <= i_valid;


		initial	o_addr   = 0;
		initial	o_data   = 0;
		always @(posedge i_clk)
		if (i_reset && OPT_LOWPOWER)
		begin
			o_addr   <= 0;
			o_data   <= 0;
		end else if ((!o_valid || !i_stall)
				 && (i_valid || !OPT_LOWPOWER))
		begin
			o_addr   <= i_addr;
			o_data   <= i_data;
		end else if (OPT_LOWPOWER && !i_stall)
		begin
			o_addr   <= 0;
			o_data   <= 0;
		end

		initial	o_decode = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_decode <= 0;
		else if ((!o_valid || !i_stall)
				 && (i_valid || !OPT_LOWPOWER))
			o_decode <= request;
		else if (OPT_LOWPOWER && !i_stall)
			o_decode <= 0;

		always @(*)
			o_stall = (o_valid && i_stall);
	end else begin

		always @(*)
		begin
			o_valid = i_valid;
			o_stall = i_stall;
			o_addr  = i_addr;
			o_data  = i_data;

			o_decode = request;
		end

		// verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0,
`ifdef	VERILATOR
				// Can't declare the clock as unused for formal,
				// lest it not be recognized as *the* clock
				i_clk,
`endif
				i_reset };
		// verilator lint_on UNUSED
	end endgenerate

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	reg	[AW+DW-1:0]	f_idata;
	always @(*)
		f_idata = { i_addr, i_data };

`ifdef	ADDRDECODE
	always @(posedge i_clk)
	if (!f_past_valid)
		assume(i_reset);

	/*
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_valid);
	else if ($past(i_valid && o_stall))
	begin
		assume(i_valid);
		// assume($stable(f_idata));
	end
	*/
`else
	always @(posedge i_clk)
	if (!f_past_valid)
		assert(i_reset);

/*
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!i_valid);
	else if ($past(i_valid && o_stall))
	begin
		assert(i_valid);
		// assert($stable(f_idata) || (!OPT_REGISTERED && i_reset));
	end
*/
`endif	// ADDRDECODE
	always @(posedge i_clk)
	if (OPT_REGISTERED && (!f_past_valid || $past(i_reset)))
	begin
		assert(!o_valid);
		assert(o_decode == 0);
	end else if ($past(o_valid && i_stall) && OPT_REGISTERED)
	begin
		assert($stable(o_addr));
		assert($stable(o_decode));
		assert($stable(o_data));
	end

	// If the output is ever valid, there must be at least one
	// decoded output
	always @(*)
		assert(o_valid == (o_decode != 0));

	always @(*)
	for(iM=0; iM<NS; iM=iM+1)
	if (o_decode[iM])
	begin
		// The address must match
		assert((((o_addr ^ SLAVE_ADDR[iM*AW +: AW])
				& SLAVE_MASK[iM*AW +: AW])==0)
			&& ACCESS_ALLOWED[iM]);
		//
		// And nothing else must match
		assert(o_decode == (1<<iM));
	end

	always @(*)
	for(iM=0; iM<NS; iM=iM+1)
	if (!ACCESS_ALLOWED[iM])
		assert(!o_decode[iM]);

	generate if (OPT_LOWPOWER && OPT_REGISTERED)
	begin
		always @(*)
		if (!o_valid)
		begin
			assert(o_addr   == 0);
			assert(o_decode == 0);
			assert(o_data   == 0);
		end
	end endgenerate

	//
	// The output decoded value may only ever have one value high,
	// never more--i.e. $onehot0
	//
`ifdef	VERIFIC
	always @(*)
		assert($onehot0(request));
`else
	reg	onehot_request;
	always @(*)
	begin
		onehot_request = 0;
		for(iM=0; iM<NS+1; iM=iM+1)
		if ((request ^ (1<<iM))==0)
			onehot_request = 1;
	end

	always @(*)
	if (request != 0)
		assert(onehot_request);
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	// Make sure all addresses are reachable
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[NS:0]	f_reached;

	always @(posedge i_clk)
		cover(i_valid);

	always @(posedge i_clk)
		cover(o_valid);

	always @(posedge i_clk)
		cover(o_valid && !i_stall);

	initial	f_reached = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_reached = 0;
	else if (o_valid)
		f_reached = f_reached | o_decode;

	generate if (!OPT_NONESEL && ACCESS_ALLOWED[0]
			&& SLAVE_MASK == 0 && NS == 1)
	begin
		
		always @(*)
			cover(f_reached[0]);

		always @(posedge i_clk)
		if (f_past_valid && $stable(o_valid))
			assert($stable(o_decode));

	end else begin

		always @(*)
			cover(&f_reached);

		always @(posedge i_clk)
		if (f_past_valid && $stable(o_valid))
			cover($changed(o_decode));

	end endgenerate

`endif	// FORMAL
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
