////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	fapb_slave.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Formal properties to describe a slave of the APB bus
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
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
module	fapb_slave(PCLK, PRESETn,
		PADDR, PSEL, PENABLE, PWRITE, PWDATA, PREADY, PRDATA, PSLVERR);
	input	wire			PCLK, PRESETn;
	input	wire	[AW-1:0]	PADDR;
	input	wire			PSEL;
	input	wire			PENABLE;
	input	wire			PWRITE;
	input	wire	[DW-1:0]	PWDATA;
	input	wire			PREADY;
	input	wire	[DW-1:0]	PRDATA;
	input	wire			PSLVERR;

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if (!f_past_valid)
		`SLAVE_ASSUME(!PRESETn);

	// PSEL
	// PREADY
	// Constant PADDR and PWRITE
	// PWDATA
	always @(posedge i_clk)
	if ((!f_past_valid)||(!$past(PRESETn)))
	begin
		`SLAVE_ASSUME(!PSEL);
		`SLAVE_ASSERT(!PREADY);
	end else if ($past(PSEL))
	begin
		if (!$past(PENABLE) || ($past(PENABLE) && !$past(PREADY)))
		begin
			`SLAVE_ASSUME($stable(PADDR));
			`SLAVE_ASSUME($stable(PWRITE));
			if (PWRITE)
				`SLAVE_ASSUME($stable(PWDATA));
		end
	end else
		`SLAVE_ASSUME(!PENABLE);

	//
	// ENABLE
	always @(posedge i_clk)
	if (f_past_valid && $past(PRESETn))
	begin
		if ($past(PENABLE) && $past(PSEL))
		begin
			if ($past(PREADY))
				`SLAVE_ASSUME(!PENABLE);
			else
				`SLAVE_ASSUME(PENABLE);
		end else if ((!$past(PSEL))&&(PSEL))
			`SLAVE_ASSUME(!PENABLE);
	end

	//
	// PREADY
	//	Can take on any value when PSEL is low
	// always @(posedge i_clk)
	// if !(f_past_valid)&&(!$past(PSEL)))
	//	`SLAVE_ASSERT(!PREADY);

	always @(*)
	if (!PREADY)
		`SLAVE_ASSERT(!SLVERR);
endmodule
