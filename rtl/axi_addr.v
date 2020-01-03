////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axi_addr.v
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	The AXI (full) standard has some rather complicated addressing
//		modes, where the address can either be FIXED, INCRementing, or
//	even where it can WRAP around some boundary.  When in either INCR or
//	WRAP modes, the next address must always be aligned.  In WRAP mode,
//	the next address calculation needs to wrap around a given value, and
//	that value is dependent upon the burst size (i.e. bytes per beat) and
//	length (total numbers of beats).  Since this calculation can be
//	non-trivial, and since it needs to be done multiple times, the logic
//	below captures it for every time it might be needed.
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
`default_nettype none
//
//
module	axi_addr(i_last_addr,
		i_size,
		i_burst,
		i_len,
		o_next_addr);
	parameter	AW = 32,
			DW = 32;
	input	wire	[AW-1:0]	i_last_addr;
	input	wire	[2:0]		i_size; // 1b, 2b, 4b, 8b, etc
	input	wire	[1:0]		i_burst; // fixed, incr, wrap, reserved
	input	wire	[7:0]		i_len;
	output	reg	[AW-1:0]	o_next_addr;

	localparam		DSZ = $clog2(DW)-3;
	localparam [1:0]	FIXED     = 2'b00;
	localparam [1:0]	INCREMENT = 2'b01;
	localparam [1:0]	WRAP      = 2'b10;

	reg	[AW-1:0]	wrap_mask, increment;

	always @(*)
	begin
		increment = 0;
		if (i_burst != 0)
		begin
			if (DSZ == 0)
				increment = 1;
			else if (DSZ == 1)
				increment = (i_size[0]) ? 2 : 1;
			else if (DSZ == 2)
				increment = (i_size[1]) ? 4 : ((i_size[0]) ? 2 : 1);
			else if (DSZ == 3)
				case(i_size[1:0])
				2'b00: increment = 1;
				2'b01: increment = 2;
				2'b10: increment = 4;
				2'b11: increment = 8;
				endcase
			else
				increment = (1<<i_size);
		end
	end

	always @(*)
	begin
		// Start with the default, minimum mask
		wrap_mask = 1;

		/*
		// Here's the original code.  It works, but it's
		// not economical (uses too many LUTs)
		//
		if (i_len[3:0] == 1)
			wrap_mask = (1<<(i_size+1));
		else if (i_len[3:0] == 3)
			wrap_mask = (1<<(i_size+2));
		else if (i_len[3:0] == 7)
			wrap_mask = (1<<(i_size+3));
		else if (i_len[3:0] == 15)
			wrap_mask = (1<<(i_size+4));
		wrap_mask = wrap_mask - 1;
		*/

		// Here's what we *want*
		//
		// wrap_mask[i_size:0] = -1;
		//
		// On the other hand, since we're already guaranteed that our
		// addresses are aligned, do we really care about
		// wrap_mask[i_size-1:0] ?

		// What we want:
		//
		// wrap_mask[i_size+3:i_size] |= i_len[3:0]
		//
		// We could simplify this to
		//
		// wrap_mask = wrap_mask | (i_len[3:0] << (i_size));
		//
		// But verilator complains about the left-hand side of
		// the shift having only 3 bits.
		//
		if (DSZ < 2)
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size[0]));
		else if (DSZ < 4)
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size[1:0]));
		else
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size));

		if (AW > 12)
			wrap_mask[((AW>12)?(AW-1):(AW-1)):((AW>12)?12:(AW-1))] = 0;
	end

	always @(*)
	begin
		o_next_addr = i_last_addr + increment;
		if (i_burst != FIXED)
		begin
			if (DSZ < 2)
			begin
				// Align any subsequent address
				if (i_size[0])
					o_next_addr[  0] = 0;
			end else if (DSZ < 4)
			begin
				// Align any subsequent address
				case(i_size[1:0])
				2'b00:  o_next_addr = o_next_addr;
				2'b01:  o_next_addr[  0] = 0;
				2'b10:  o_next_addr[(AW-1>1) ? 1 : (AW-1):0]= 0;
				2'b11:  o_next_addr[(AW-1>2) ? 2 : (AW-1):0]= 0;
				endcase
			end else
			begin
				// Align any subsequent address
				case(i_size)
				3'b001:  o_next_addr[  0] = 0;
				3'b010:  o_next_addr[(AW-1>1) ? 1 : (AW-1):0]=0;
				3'b011:  o_next_addr[(AW-1>2) ? 2 : (AW-1):0]=0;
				3'b100:  o_next_addr[(AW-1>3) ? 3 : (AW-1):0]=0;
				3'b101:  o_next_addr[(AW-1>4) ? 4 : (AW-1):0]=0;
				3'b110:  o_next_addr[(AW-1>5) ? 5 : (AW-1):0]=0;
				3'b111:  o_next_addr[(AW-1>6) ? 6 : (AW-1):0]=0;
				default: o_next_addr = o_next_addr;
				endcase
			end
		end
		if (i_burst[1])
		begin
			// WRAP!
			o_next_addr[AW-1:0] = (i_last_addr & ~wrap_mask)
					| (o_next_addr & wrap_mask);
		end

		if (AW > 12)
			o_next_addr[AW-1:((AW>12)?12:(AW-1))]
				= i_last_addr[AW-1:((AW>12) ? 12:(AW-1))];
	end

	// Verilator lint_off UNUSED
	wire	[4:0]	unused;
	assign	unused = { i_len[7:4], i_len[0] };
	// Verilator lint_on UNUSED

endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
