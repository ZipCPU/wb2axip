////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	f_order.v
//
// Project:	Pipelined Wishbone to AXI converter
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
