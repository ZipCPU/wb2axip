////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbm2axilite.v (Wishbone master to AXI slave, pipelined)
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Convert from a wishbone master to an AXI lite interface.  The
//		big difference is that AXI lite doesn't support bursting,
//	or transaction ID's.  This actually makes the task a *LOT* easier.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018, Gisselquist Technology, LLC
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
module wbm2axilite (
	i_clk, i_reset,
	// AXI write address channel signals
	i_axi_awready, o_axi_awaddr, o_axi_awcache, o_axi_awprot, o_axi_awvalid,
	// AXI write data channel signals
	i_axi_wready, o_axi_wdata, o_axi_wstrb, o_axi_wvalid,
	// AXI write response channel signals
	i_axi_bresp, i_axi_bvalid, o_axi_bready,
	// AXI read address channel signals
	i_axi_arready, o_axi_araddr, o_axi_arcache, o_axi_arprot, o_axi_arvalid,
	// AXI read data channel signals   
	i_axi_rresp, i_axi_rvalid, i_axi_rdata, o_axi_rready,
	// We'll share the clock and the reset
	i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
		o_wb_ack, o_wb_stall, o_wb_data, o_wb_err);

	localparam C_AXI_DATA_WIDTH	=  32;// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	=  28;// AXI Address width
	localparam DW			=  C_AXI_DATA_WIDTH;// Wishbone data width
	parameter AW			=  C_AXI_ADDR_WIDTH-2;// WB addr width (log wordsize)
	input	wire			i_clk;	// System clock
	input	wire			i_reset;// Reset signal,drives AXI rst

// AXI write address channel signals
	input	wire			i_axi_awready;//Slave is ready to accept
	output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_awaddr;	// Write address
	output	wire	[3:0]		o_axi_awcache;	// Write Cache type
	output	wire	[2:0]		o_axi_awprot;	// Write Protection type
	output	reg			o_axi_awvalid;	// Write address valid

// AXI write data channel signals
	input	wire			i_axi_wready;  // Write data ready
	output	reg	[C_AXI_DATA_WIDTH-1:0]	o_axi_wdata;	// Write data
	output	reg	[C_AXI_DATA_WIDTH/8-1:0] o_axi_wstrb;	// Write strobes
	output	reg			o_axi_wvalid;	// Write valid

// AXI write response channel signals
	input	wire [1:0]		i_axi_bresp;	// Write response
	input	wire			i_axi_bvalid;  // Write reponse valid
	output	wire			o_axi_bready;  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready;	// Read address ready
	output	wire	[C_AXI_ADDR_WIDTH-1:0]	o_axi_araddr;	// Read address
	output	wire	[3:0]		o_axi_arcache;	// Read Cache type
	output	wire	[2:0]		o_axi_arprot;	// Read Protection type
	output	reg			o_axi_arvalid;	// Read address valid

// AXI read data channel signals   
	input	wire	[1:0]		i_axi_rresp;   // Read response
	input	wire			i_axi_rvalid;  // Read reponse valid
	input wire [C_AXI_DATA_WIDTH-1:0] i_axi_rdata;    // Read data
	output	wire			o_axi_rready;  // Read Response ready

	// We'll share the clock and the reset
	input	wire			i_wb_cyc;
	input	wire			i_wb_stb;
	input	wire			i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	input	wire	[(DW-1):0]	i_wb_data;
	input	wire	[(DW/8-1):0]	i_wb_sel;
	output	reg			o_wb_ack;
	output	wire			o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	output	reg			o_wb_err;

//*****************************************************************************
// Local Parameter declarations
//*****************************************************************************

	localparam	LG_AXI_DW	= ( C_AXI_DATA_WIDTH ==   8) ? 3
					: ((C_AXI_DATA_WIDTH ==  16) ? 4
					: ((C_AXI_DATA_WIDTH ==  32) ? 5
					: ((C_AXI_DATA_WIDTH ==  64) ? 6
					: ((C_AXI_DATA_WIDTH == 128) ? 7
					: 8))));

	localparam	LG_WB_DW	= ( DW ==   8) ? 3
					: ((DW ==  16) ? 4
					: ((DW ==  32) ? 5
					: ((DW ==  64) ? 6
					: ((DW == 128) ? 7
					: 8))));
	localparam	LGFIFOLN = 5;
	localparam	FIFOLN = (1<<LGFIFOLN);


//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

// Things we're not changing ...
	assign o_axi_awcache = 4'h3;	// Normal: no cache, no buffer
	assign o_axi_arcache = 4'h3;	// Normal: no cache, no buffer
	assign o_axi_awprot  = 3'b000;	// Unpriviledged, unsecure, data access
	assign o_axi_arprot  = 3'b000;	// Unpriviledged, unsecure, data access

	reg	full_fifo, err_state, axi_reset_state, wb_we;
	reg	[3:0]	reset_count;
	reg			pending;
	reg	[LGFIFOLN-1:0]	outstanding, err_pending;


// Master bridge logic
	assign	o_wb_stall = (full_fifo)
			||((!i_wb_we)&&( wb_we)&&(pending))
			||(( i_wb_we)&&(!wb_we)&&(pending))
			||(err_state)||(axi_reset_state)
			||(o_axi_arvalid)&&(!i_axi_arready)
			||(o_axi_awvalid)&&(!i_axi_awready)
			||(o_axi_wvalid)&&(!i_axi_wready);

	initial	axi_reset_state = 1'b1;
	initial	reset_count = 4'hf;
	always @(posedge i_clk)
	if (i_reset)
	begin
		axi_reset_state <= 1'b1;
		if (reset_count > 0)
			reset_count <= reset_count - 1'b1;
	end else if ((axi_reset_state)&&(reset_count > 0))
		reset_count <= reset_count - 1'b1;
	else begin
		axi_reset_state <= 1'b0;
		reset_count <= 4'hf;
	end

	// Count outstanding transactions
	initial	pending = 0;
	initial	outstanding = 0;
	always @(posedge i_clk)
	if ((i_reset)||(axi_reset_state))
	begin
		pending <= 0;
		outstanding <= 0;
		full_fifo <= 0;
	end else if ((err_state)||(!i_wb_cyc))
	begin
		pending <= 0;
		outstanding <= 0;
		full_fifo <= 0;
	end else case({ ((i_wb_stb)&&(!o_wb_stall)), (o_wb_ack) })
	2'b01: begin
		outstanding <= outstanding - 1'b1;
		pending <= (outstanding >= 2);
		full_fifo <= 1'b0;
		end
	2'b10: begin
		outstanding <= outstanding + 1'b1;
		pending <= 1'b1;
		full_fifo <= (outstanding >= {{(LGFIFOLN-2){1'b1}},2'b01});;
		end
	default: begin end
	endcase

	always @(posedge i_clk)
	if ((i_wb_stb)&&(!o_wb_stall))
		wb_we <= i_wb_we;

	//
	//
	// Write address logic
	//
	initial	o_axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_awvalid <= 0;
	else
		o_axi_awvalid <= (!o_wb_stall)&&(i_wb_stb)&&(i_wb_we)
			||(o_axi_awvalid)&&(!i_axi_awready);

	always @(posedge i_clk)
	if (!o_wb_stall)
		o_axi_awaddr <= { i_wb_addr, 2'b00 };

	//
	//
	// Read address logic
	//
	initial	o_axi_arvalid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_arvalid <= 1'b0;
	else
		o_axi_arvalid <= (!o_wb_stall)&&(i_wb_stb)&&(!i_wb_we)
			||((o_axi_arvalid)&&(!i_axi_arready));
	always @(posedge i_clk)
	if (!o_wb_stall)
		o_axi_araddr <= { i_wb_addr, 2'b00 };

	//
	//
	// Write data logic
	//
	always @(posedge i_clk)
	if (!o_wb_stall)
	begin
		o_axi_wdata <= i_wb_data;
		o_axi_wstrb <= i_wb_sel;
	end

	initial	o_axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_wvalid <= 0;
	else
		o_axi_wvalid <= ((!o_wb_stall)&&(i_wb_stb)&&(i_wb_we))
			||((o_axi_wvalid)&&(!i_axi_wready));

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(!i_wb_cyc)||(err_state))
		o_wb_ack <= 1'b0;
	else if (err_state)
		o_wb_ack <= 1'b0;
	else if ((i_axi_bvalid)&&(!i_axi_bresp[1]))
		o_wb_ack <= 1'b1;
	else if ((i_axi_rvalid)&&(!i_axi_rresp[1]))
		o_wb_ack <= 1'b1;
	else
		o_wb_ack <= 1'b0;

	always @(posedge i_clk)
		o_wb_data <= i_axi_rdata;

	// Read data channel / response logic
	assign	o_axi_rready = 1'b1;
	assign	o_axi_bready = 1'b1;

	initial	o_wb_err = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(!i_wb_cyc)||(err_state))
		o_wb_err <= 1'b0;
	else if ((i_axi_bvalid)&&(i_axi_bresp[1]))
		o_wb_err <= 1'b1;
	else if ((i_axi_rvalid)&&(i_axi_rresp[1]))
		o_wb_err <= 1'b1;
	else
		o_wb_err <= 1'b0;

	initial	err_state = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		err_state <= 0;
	else if ((i_axi_bvalid)&&(i_axi_bresp[1]))
		err_state <= 1'b1;
	else if ((i_axi_rvalid)&&(i_axi_rresp[1]))
		err_state <= 1'b1;
	else if ((pending)&&(!i_wb_cyc))
		err_state <= 1'b1;
	else if (err_pending == 0)
		err_state <= 0;

	initial	err_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
		err_pending <= 0;
	else case({ ((i_wb_stb)&&(!o_wb_stall)),
					((i_axi_bvalid)||(i_axi_rvalid)) })
	2'b01: err_pending <= err_pending - 1'b1;
	2'b10: err_pending <= err_pending + 1'b1;
	default: begin end
	endcase

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[2:0]	unused;
	assign	unused = { i_wb_cyc, i_axi_bresp[0], i_axi_rresp[0] };
	// verilator lint_on  UNUSED

/////////////////////////////////////////////////////////////////////////
//
//
//
// Formal methods section
//
// These are only relevant when *proving* that this translator works
//
//
//
/////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Formal proof exists elsewhere
`endif
endmodule
