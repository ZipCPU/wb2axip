////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axim2wbsp.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	So ... this converter works in the other direction.  This 
//		converter takes AXI commands, and organizes them into pipelined
//	wishbone commands.
//
//
//	We'll treat AXI as two separate busses: one for writes, another for
//	reads, further, we'll insist that the two channels AXI uses for writes
//	combine into one channel for our purposes.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016, Gisselquist Technology, LLC
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
module axim2wbsp #(
	parameter C_AXI_ID_WIDTH	= 6, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 32,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28	// AXI Address width
	) (
	input				i_clk,	// System clock
	input				i_axi_reset_n,

// AXI write address channel signals
	output	wire			o_axi_awready, // Slave is ready to accept
	input		[C_AXI_ID_WIDTH-1:0]	i_axi_awid,	// Write ID
	input		[C_AXI_ADDR_WIDTH-1:0]	i_axi_awaddr,	// Write address
	input		[7:0]		i_axi_awlen,	// Write Burst Length
	input		[2:0]		i_axi_awsize,	// Write Burst size
	input		[1:0]		i_axi_awburst,	// Write Burst type
	input		[0:0]		i_axi_awlock,	// Write lock type
	input		[3:0]		i_axi_awcache,	// Write Cache type
	input		[2:0]		i_axi_awprot,	// Write Protection type
	input		[3:0]		i_axi_awqos,	// Write Quality of Svc
	input				i_axi_awvalid,	// Write address valid
  
// AXI write data channel signals
	output	wire			o_axi_wready,  // Write data ready
	input		[C_AXI_DATA_WIDTH-1:0]	i_axi_wdata,	// Write data
	input		[C_AXI_DATA_WIDTH/8-1:0] i_axi_wstrb,	// Write strobes
	input				i_axi_wlast,	// Last write transaction   
	input				i_axi_wvalid,	// Write valid
  
// AXI write response channel signals
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_bid,	// Response ID
	output	wire [1:0]		o_axi_bresp,	// Write response
	output	wire 			o_axi_bvalid,  // Write reponse valid
	input				i_axi_bready,  // Response ready
  
// AXI read address channel signals
	output	wire			o_axi_arready,	// Read address ready
	input		[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
	input		[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr,	// Read address
	input		[7:0]		i_axi_arlen,	// Read Burst Length
	input		[2:0]		i_axi_arsize,	// Read Burst size
	input		[1:0]		i_axi_arburst,	// Read Burst type
	input		[0:0]		i_axi_arlock,	// Read lock type
	input		[3:0]		i_axi_arcache,	// Read Cache type
	input		[2:0]		i_axi_arprot,	// Read Protection type
	input		[3:0]		i_axi_arqos,	// Read Protection type
	input				i_axi_arvalid,	// Read address valid
  
// AXI read data channel signals   
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_rid,     // Response ID
	output	wire [1:0]		o_axi_rresp,   // Read response
	output	wire			o_axi_rvalid,  // Read reponse valid
	output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata,    // Read data
	output	wire			o_axi_rlast,    // Read last
	input				i_axi_rready,  // Read Response ready

	// We'll share the clock and the reset
	output	reg			o_reset,
	output	wire			o_wb_cyc,
	output	wire			o_wb_stb,
	output	wire			o_wb_we,
	output	wire [(C_AXI_ADDR_WIDTH-1):0]	o_wb_addr,
	output	wire [(C_AXI_DATA_WIDTH-1):0]	o_wb_data,
	output	wire [(C_AXI_DATA_WIDTH/8-1):0]	o_wb_sel,
	input				i_wb_ack,
	input				i_wb_stall,
	input	[(C_AXI_DATA_WIDTH-1):0]	i_wb_data,
	input				i_wb_err
);

	//
	//
	//


	wire	[(C_AXI_ADDR_WIDTH-1):0]	w_wb_addr, r_wb_addr;
	wire	[(C_AXI_DATA_WIDTH-1):0]	w_wb_data, r_wb_data;
	wire	[(C_AXI_DATA_WIDTH/8-1):0]	w_wb_sel, r_wb_sel;
	wire	r_wb_we, r_wb_err, r_wb_cyc, r_wb_stb, r_wb_stall, r_wb_ack;
	wire	w_wb_we, w_wb_err, w_wb_cyc, w_wb_stb, w_wb_stall, w_wb_ack;

	aximwr2wbsp #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH))
		axi_write_decoder ( i_clk, i_axi_reset_n,
		o_axi_awready, i_axi_awid, i_axi_awaddr, i_axi_awlen,
			i_axi_awsize, i_axi_awburst, i_axi_awlock,
			i_axi_awcache, i_axi_awprot, i_axi_awqos,
			i_axi_awvalid,
		o_axi_wready, i_axi_wdata, i_axi_wstrb, i_axi_wlast,
			i_axi_wvalid,
		o_axi_bid, o_axi_bresp, o_axi_bvalid, i_axi_bready,
		w_wb_cyc, w_wb_stb, w_wb_addr, w_wb_data, w_wb_sel,
			w_wb_ack, w_wb_stall, w_wb_err);
	assign	w_wb_we = 1'b1;

	aximrd2wbsp #(
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH))
		axi_read_decoder(i_clk, i_axi_reset_n,
		o_axi_arready, i_axi_arid, i_axi_araddr,
			i_axi_arlen, i_axi_arsize, i_axi_arburst, i_axi_arlock,
			i_axi_arcache, i_axi_arprot, i_axi_arqos, i_axi_arvalid,
		o_axi_rid, o_axi_rresp, o_axi_rvalid, o_axi_rdata, o_axi_rlast,
			i_axi_rready,
		r_wb_cyc, r_wb_stb, r_wb_addr,
			r_wb_ack, r_wb_stall, i_wb_data, r_wb_err);
	assign	r_wb_we = 1'b0;
	assign	r_wb_sel = ~0;
	assign	r_wb_data = w_wb_data; // Irrelevant, so lets minimize logic

	wbarbiter	#(
		.DW(C_AXI_DATA_WIDTH),
		.AW(C_AXI_ADDR_WIDTH))
		readorwrite(i_clk,
		r_wb_cyc, r_wb_stb, r_wb_we, r_wb_addr, w_wb_data, r_wb_sel,
			r_wb_ack, r_wb_stall, r_wb_err,
		w_wb_cyc, w_wb_stb, w_wb_we, w_wb_addr, w_wb_data, w_wb_sel,
			w_wb_ack, w_wb_stall, w_wb_err,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_err);

	always @(posedge i_clk)
		o_reset <= (i_axi_reset_n == 1'b0);

endmodule

