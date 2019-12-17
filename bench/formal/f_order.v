////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	f_order.v
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
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
//
`default_nettype	none
//
//
module	f_order(i_clk, i_reset, i_head, i_neck, i_torso, i_tail);
	parameter	LGFIFO = 8;
	//
	input	wire	i_clk, i_reset;
	//
	input	wire	[(LGFIFO-1):0]	i_head, i_neck, i_torso, i_tail;


	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
	begin
		assert(i_head  == 0);
		assert(i_neck  == 0);
		assert(i_torso == 0);
		assert(i_tail  == 0);
	end

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if (i_head == i_tail)
		begin
			assert(i_neck  == i_head);
			assert(i_torso == i_head);
		end else if (i_head > i_tail)
		begin
			assert((i_neck  <= i_head)&&(i_neck >= i_tail));
			assert((i_torso <= i_head)&&(i_torso >= i_tail));
			assert(i_neck >= i_torso);
		end else if (i_head < i_tail)
		begin
			assert((i_neck  <= i_head)||(i_neck  >= i_tail));
			assert((i_torso <= i_head)||(i_torso >= i_tail));

			if (i_neck < i_head)
				assert((i_torso<= i_neck)||(i_torso >= i_tail));
			else if (i_neck >= i_tail)
				assert(i_torso <= i_neck);
		end
	end

	wire	[(LGFIFO-1):0]	f_next_head, f_next_neck,
				f_next_torso, f_next_tail;
	assign	f_next_head  = i_head + 1'b1;
	assign	f_next_neck  = i_neck + 1'b1;
	assign	f_next_torso = i_torso + 1'b1;
	assign	f_next_tail  = i_tail + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if ($past(f_next_head) == $past(i_tail))
			assert(i_head != f_next_head);
		assert((i_head== $past(i_head))||(i_head== $past(f_next_head)));
		assert((i_neck== $past(i_neck))||(i_neck== $past(f_next_neck)));
		assert((i_torso==$past(i_torso))
			||(i_torso== $past(f_next_torso)));
		assert((i_tail== $past(i_tail))||(i_tail== $past(f_next_tail)));
	end

endmodule
