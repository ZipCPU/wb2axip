////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilite2axi.v
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
`default_nettype none
//
module axilite2axi #(
	parameter	C_AXI_ID_WIDTH	= 4,
			C_AXI_ADDR_WIDTH= 32,
			C_AXI_DATA_WIDTH= 32,
	parameter [C_AXI_ID_WIDTH-1:0]	C_AXI_WRITE_ID = 0,
					C_AXI_READ_ID = 0
	) (
	input	wire				ACLK,
	input	wire				ARESETN,
	// Slave write signals
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
	input	wire	[3-1:0]			S_AXI_AWPROT,
	input	wire				S_AXI_AWVALID,
	output	wire				S_AXI_AWREADY,
	// Slave write data signals
	input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
	input	wire	[C_AXI_DATA_WIDTH/8-1:0] S_AXI_WSTRB,
	input	wire				S_AXI_WVALID,
	output	wire				S_AXI_WREADY,
	// Slave return write response
	output	wire	[2-1:0]			S_AXI_BRESP,
	output	wire				S_AXI_BVALID,
	input	wire				S_AXI_BREADY,
	// Slave read signals
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
	input	wire	[3-1:0]			S_AXI_ARPROT,
	input	wire				S_AXI_ARVALID,
	output	wire				S_AXI_ARREADY,
	// Slave read data signals
	output	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
	output	wire	[2-1:0]			S_AXI_RRESP,
	output	wire	[2-1:0]			S_AXI_RVALID,
	input	wire	[2-1:0]			S_AXI_RREADY,
	//
	// Master interface write address
	output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
	output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
	output	wire	[8-1:0]			M_AXI_AWLEN,
	output	wire	[3-1:0]			M_AXI_AWSIZE,
	output	wire	[2-1:0]			M_AXI_AWBURST,
	output	wire				M_AXI_AWLOCK,
	output	wire	[4-1:0]			M_AXI_AWCACHE,
	output	wire	[3-1:0]			M_AXI_AWPROT,
	output	wire	[4-1:0]			M_AXI_AWQOS,
	output	wire				M_AXI_AWVALID,
	input	wire				M_AXI_AWREADY,
	// Master write data
	output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
	output	wire	[C_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB,
	output	wire				M_AXI_WLAST,
	output	wire				M_AXI_WVALID,
	input	wire				M_AXI_WREADY,
	// Master write response
	input	wire	[1:0]			M_AXI_BRESP,
	input	wire				M_AXI_BVALID,
	output	wire				M_AXI_BREADY,
	// Master interface read address
	output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
	output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
	output	wire	[8-1:0]			M_AXI_ALEN,
	output	wire	[3-1:0]			M_AXI_ARSIZE,
	output	wire	[2-1:0]			M_AXI_ARBURST,
	output	wire				M_AXI_ARLOCK,
	output	wire	[4-1:0]			M_AXI_ARCACHE,
	output	wire	[3-1:0]			M_AXI_ARPROT,
	output	wire	[3-1:0]			M_AXI_ARQOS,
	output	wire				M_AXI_ARVALID,
	input	wire				M_AXI_ARREADY,
	// Master interface read data return
	input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
	input	wire	[2-1:0]			M_AXI_RRESP,
	input	wire				M_AXI_RVALID,
	output	wire				M_AXI_RREADY
	);

	assign	M_AXI_AWID    = C_AXI_WRITE_ID;
	assign	M_AXI_AWADDR  = S_AXI_AWADDR;
	assign	M_AXI_AWLEN   = 0;
	assign	M_AXI_AWSIZE  = $clog2(C_AXI_DATA_WIDTH)-3;
	assign	M_AXI_AWBURST = 0;
	assign	M_AXI_AWLOCK  = 0;
	assign	M_AXI_AWCACHE = 0;
	assign	M_AXI_AWPROT  = S_AXI_AWPROT;
	assign	M_AXI_AWQOS   = 0;
	assign	M_AXI_AWVALID = S_AXI_AWVALID;
	assign	S_AXI_AWREADY = M_AXI_AWREADY;
	// Master write data
	assign	M_AXI_WDATA   = S_AXI_WDATA;
	assign	M_AXI_WLAST   = 1;
	assign	M_AXI_WSTRB   = S_AXI_WSTRB;
	assign	M_AXI_WVALID  = S_AXI_WVALID;
	assign	S_AXI_WREADY  = M_AXI_WREADY;
	// Master write response
	assign	S_AXI_BRESP   = M_AXI_BRESP;
	assign	S_AXI_BVALID  = M_AXI_BVALID;
	assign	M_AXI_BREADY  = S_AXI_BREADY;
	//
	//
	assign	M_AXI_ARID    = C_AXI_READ_ID;
	assign	M_AXI_ARADDR  = S_AXI_ARADDR;
	assign	M_AXI_ARLEN   = 0;
	assign	M_AXI_ARSIZE  = $clog2(C_AXI_ADDR_WIDTH)-3;
	assign	M_AXI_ARBURST = 0;
	assign	M_AXI_ARLOCK  = 0;
	assign	M_AXI_ARCACHE = 0;
	assign	M_AXI_ARPROT  = S_AXI_ARPROT;
	assign	M_AXI_ARQOS   = 0;
	assign	M_AXI_ARVALID = S_AXI_ARVALID;
	assign	S_AXI_ARREADY = M_AXI_ARREADY;
	//
	assign	S_AXI_RDATA   = M_AXI_RDATA;
	assign	S_AXI_RRESP   = M_AXI_RRESP;
	assign	S_AXI_RVALID  = M_AXI_RVALID;
	assign	M_AXI_RREADY  = S_AXI_RREADY;

`ifdef	FORMAL
// WARNING: This module has not (yet) been formally verified.
//	It has passed a desk-check inspection only
`endif
endmodule
`default_nettype wire
