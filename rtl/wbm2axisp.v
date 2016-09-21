////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbm2axisp.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	The B4 Wishbone SPEC allows transactions at a speed as fast as
//		one per clock.  The AXI bus allows transactions at a speed of
//	one read and one write transaction per clock.  These capabilities work
//	by allowing requests to take place prior to responses, such that the
//	requests might go out at once per clock and take several clocks, and
//	the responses may start coming back several clocks later.  In other
//	words, both protocols allow multiple transactions to be "in flight" at
//	the same time.  Current wishbone to AXI converters, however, handle only
//	one transaction at a time: initiating the transaction, and then waiting
//	for the transaction to complete before initiating the next.
//
//	The purpose of this core is to maintain the speed of both busses, while
//	transiting from the Wishbone (as master) to the AXI bus (as slave) and
//	back again.
//
//	Since the AXI bus allows transactions to be reordered, whereas the 
//	wishbone does not, this core can be configured to reorder return
//	transactions as well.
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
module wbm2axisp #(
	parameter C_AXI_ID_WIDTH	= 6, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
	parameter DW			= 32,	// Wishbone data width
	parameter AW			= 26,	// Wishbone address width
	parameter STRICT_ORDER		= 0	// Reorder, or not? 0 -> Reorder
	) (
	input				i_clk,	// System clock
	// input			i_reset,// Wishbone reset signal--unused

// AXI write address channel signals
	input				i_axi_awready, // Slave is ready to accept
	output	reg	[C_AXI_ID_WIDTH-1:0]	o_axi_awid,	// Write ID
	output	reg	[C_AXI_ADDR_WIDTH-1:0]	o_axi_awaddr,	// Write address
	output	wire	[7:0]		o_axi_awlen,	// Write Burst Length
	output	wire	[2:0]		o_axi_awsize,	// Write Burst size
	output	wire	[1:0]		o_axi_awburst,	// Write Burst type
	output	wire	[0:0]		o_axi_awlock,	// Write lock type
	output	wire	[3:0]		o_axi_awcache,	// Write Cache type
	output	wire	[2:0]		o_axi_awprot,	// Write Protection type
	output	wire	[3:0]		o_axi_awqos,	// Write Quality of Svc
	output	reg			o_axi_awvalid,	// Write address valid
  
// AXI write data channel signals
	input				i_axi_wready,  // Write data ready
	output	reg	[C_AXI_DATA_WIDTH-1:0]	o_axi_wdata,	// Write data
	output	reg	[C_AXI_DATA_WIDTH/8-1:0] o_axi_wstrb,	// Write strobes
	output	wire			o_axi_wlast,	// Last write transaction   
	output	reg			o_axi_wvalid,	// Write valid
  
// AXI write response channel signals
	input	[C_AXI_ID_WIDTH-1:0]	i_axi_bid,	// Response ID
	input	[1:0]			i_axi_bresp,	// Write response
	input				i_axi_bvalid,  // Write reponse valid
	output	wire			o_axi_bready,  // Response ready
  
// AXI read address channel signals
	input				i_axi_arready,	// Read address ready
	output	wire	[C_AXI_ID_WIDTH-1:0]	o_axi_arid,	// Read ID
	output	wire	[C_AXI_ADDR_WIDTH-1:0]	o_axi_araddr,	// Read address
	output	wire	[7:0]		o_axi_arlen,	// Read Burst Length
	output	wire	[2:0]		o_axi_arsize,	// Read Burst size
	output	wire	[1:0]		o_axi_arburst,	// Read Burst type
	output	wire	[0:0]		o_axi_arlock,	// Read lock type
	output	wire	[3:0]		o_axi_arcache,	// Read Cache type
	output	wire	[2:0]		o_axi_arprot,	// Read Protection type
	output	wire	[3:0]		o_axi_arqos,	// Read Protection type
	output	reg			o_axi_arvalid,	// Read address valid
  
// AXI read data channel signals   
	input	[C_AXI_ID_WIDTH-1:0]	i_axi_rid,     // Response ID
	input	[1:0]			i_axi_rresp,   // Read response
	input				i_axi_rvalid,  // Read reponse valid
	input	[C_AXI_DATA_WIDTH-1:0]	i_axi_rdata,    // Read data
	input				i_axi_rlast,    // Read last
	output	wire			o_axi_rready,  // Read Response ready

	// We'll share the clock and the reset
	input				i_wb_cyc,
	input				i_wb_stb,
	input				i_wb_we,
	input		[(AW-1):0]	i_wb_addr,
	input		[(DW-1):0]	i_wb_data,
	input		[(DW/8-1):0]	i_wb_sel,
	output	reg			o_wb_ack,
	output	wire			o_wb_stall,
	output	reg	[(DW-1):0]	o_wb_data,
	output	reg			o_wb_err
);

//*****************************************************************************
// Parameter declarations
//*****************************************************************************

	localparam	CTL_SIG_WIDTH	= 3;	// Control signal width
	localparam	RD_STS_WIDTH	= 16;	// Read status signal width
	localparam	WR_STS_WIDTH	= 16;	// Write status signal width

//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

// Things we're not changing ...
	assign o_axi_awlen = 8'h0;	// Burst length is one
	assign o_axi_awsize = 3'b101;	// maximum bytes per burst is 32
	assign o_axi_awburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_arburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_awlock  = 1'b0;	// Normal signaling
	assign o_axi_arlock  = 1'b0;	// Normal signaling
	assign o_axi_awcache = 4'h2;	// Normal: no cache, no buffer
	assign o_axi_arcache = 4'h2;	// Normal: no cache, no buffer
	assign o_axi_awprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_arprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_awqos  = 4'h0;	// Lowest quality of service (unused)
	assign o_axi_arqos  = 4'h0;	// Lowest quality of service (unused)

// Command logic
// Write address logic

	always @(posedge i_clk)
		o_axi_awvalid <= (!o_wb_stall)&&(i_wb_stb)&&(i_wb_we)
			||(o_wb_stall)&&(o_axi_awvalid)&&(!i_axi_awready);

	generate
	if (DW == 32)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall) // 26 bit address becomes 28 bit ...
				o_axi_awaddr <= { i_wb_addr[AW-1:2], 4'b00 };
	end else if (DW == 128)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall) // 28 bit address ...
				o_axi_awaddr <= { i_wb_addr[AW-1:0], 4'b00 };
	end endgenerate

	reg	[5:0]	transaction_id;
	always @(posedge i_clk)
		if (!i_wb_cyc)
			transaction_id <= 6'h00;
		else if ((i_wb_stb)&&(~o_wb_stall))
			transaction_id <= transaction_id + 6'h01;
	always @(posedge i_clk)
		if ((i_wb_stb)&&(~o_wb_stall))
			o_axi_awid <= transaction_id;

// Read address logic
	assign	o_axi_arid = o_axi_awid;
	assign	o_axi_araddr = o_axi_awaddr;
	assign	o_axi_arlen  = o_axi_awlen;
	assign	o_axi_arsize = 3'b101;	// maximum bytes per burst is 32
	always @(posedge i_clk)
		o_axi_arvalid <= (!o_wb_stall)&&(i_wb_stb)&&(!i_wb_we)
			||(o_wb_stall)&&(o_axi_arvalid)&&(!i_axi_arready);


// Write data logic
	generate
	if (DW == 32)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wdata <= { i_wb_data, i_wb_data, i_wb_data, i_wb_data };
		always @(posedge i_clk)
			if (!o_wb_stall)
			case(i_wb_addr[1:0])
			2'b00:o_axi_wstrb<={    4'h0,    4'h0,   4'h0,i_wb_sel};
			2'b01:o_axi_wstrb<={    4'h0,    4'h0,i_wb_sel,   4'h0};
			2'b10:o_axi_wstrb<={    4'h0,i_wb_sel,    4'h0,   4'h0};
			2'b11:o_axi_wstrb<={i_wb_sel,    4'h0,    4'h0,   4'h0};
			endcase
	end else if (DW == 128)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wdata <= i_wb_data;
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wstrb <= i_wb_sel;
	end endgenerate

	assign	o_axi_wlast = 1'b1;
	always @(posedge i_clk)
		o_axi_wvalid <= ((!o_wb_stall)&&(i_wb_stb)&&(i_wb_we))
			||(o_wb_stall)&&(o_axi_wvalid)&&(!i_axi_wready);

// Read data channel / response logic
	assign	o_axi_rready = 1'b1;
	assign	o_axi_bready = 1'b1;

	wire	w_fifo_full;
	generate
	if (STRICT_ORDER == 0)
	begin
		// Reorder FIFO
		//
		localparam	LGFIFOLN = C_AXI_ID_WIDTH;
		localparam	FIFOLN = (1<<LGFIFOLN);
		// FIFO reorder buffer
		reg	[(LGFIFOLN-1):0]	fifo_tail;
		reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data [0:(FIFOLN-1)];
		reg	[(FIFOLN-1):0]	reorder_fifo_valid;
		reg	[(FIFOLN-1):0]	reorder_fifo_err;

		initial reorder_fifo_valid = 0;
		initial reorder_fifo_err = 0;

		if (DW == 32)
		begin
			reg	[1:0]	reorder_fifo_addr [0:(FIFOLN-1)];


			reg	[1:0]	low_addr;
			always @(posedge i_clk)
				if ((i_wb_stb)&&(!o_wb_stall))
					low_addr <= i_wb_addr[1:0];
			always @(posedge i_clk)
				if ((o_axi_arvalid)&&(i_axi_arready))
					reorder_fifo_addr[o_axi_arid] <= low_addr;

			always @(posedge i_clk)
			case(reorder_fifo_addr[fifo_tail][1:0])
			2'b00: o_wb_data <=reorder_fifo_data[fifo_tail][ 31: 0];
			2'b01: o_wb_data <=reorder_fifo_data[fifo_tail][ 63:32];
			2'b10: o_wb_data <=reorder_fifo_data[fifo_tail][ 95:64];
			2'b11: o_wb_data <=reorder_fifo_data[fifo_tail][127:96];
			endcase

		end else if (DW == 128)
		begin
			always @(posedge i_clk)
				o_wb_data <= reorder_fifo_data[fifo_tail];
		end


		wire	[(LGFIFOLN-1):0]	fifo_head;
		assign	fifo_head = transaction_id;

		// Let's do some math to figure out where the FIFO head will
		// point to next, but let's also insist that it be LGFIFOLN
		// bits in size as well.  This'll be part of the fifo_full
		// calculation below.
		wire	[(LGFIFOLN-1):0]	n_fifo_head, nn_fifo_head;
		assign	n_fifo_head = fifo_head+1'b1;
		assign	nn_fifo_head = { fifo_head[(LGFIFOLN-1):1]+1'b1, fifo_head[0] };

		always @(posedge i_clk)
		begin
			if ((i_axi_rvalid)&&(o_axi_rready))
				reorder_fifo_data[i_axi_rid]<= i_axi_rdata;
			if ((i_axi_rvalid)&&(o_axi_rready))
			begin
				reorder_fifo_valid[i_axi_rid] <= 1'b1;
				reorder_fifo_err[i_axi_rid] <= i_axi_rresp[1];
			end
			if ((i_axi_bvalid)&&(o_axi_bready))
			begin
				reorder_fifo_valid[i_axi_bid] <= 1'b1;
				reorder_fifo_err[i_axi_bid] <= i_axi_bresp[1];
			end

			if (reorder_fifo_valid[fifo_tail])
			begin
				o_wb_ack <= 1'b1;
				o_wb_err <= reorder_fifo_err[fifo_tail];
				fifo_tail <= fifo_tail + 6'h1;
				reorder_fifo_valid[fifo_tail] <= 1'b0;
				reorder_fifo_err[fifo_tail]   <= 1'b0;
			end else begin
				o_wb_ack <= 1'b0;
				o_wb_err <= 1'b0;
			end

			if (!i_wb_cyc)
			begin
				reorder_fifo_valid <= {(FIFOLN){1'b0}};
				reorder_fifo_err   <= {(FIFOLN){1'b0}};
				fifo_tail <= 6'h0;
				o_wb_err <= 1'b0;
				o_wb_ack <= 1'b0;
			end
		end

		reg	r_fifo_full;
		always @(posedge i_clk)
		begin
			if (!i_wb_cyc)
				r_fifo_full <= 1'b0;
			else if ((i_wb_stb)&&(~o_wb_stall)
					&&(reorder_fifo_valid[fifo_tail]))
				r_fifo_full <= (fifo_tail==n_fifo_head);
			else if ((i_wb_stb)&&(~o_wb_stall))
				r_fifo_full <= (fifo_tail==nn_fifo_head);
			else if (reorder_fifo_valid[fifo_tail])
				r_fifo_full <= 1'b0;
			else
				r_fifo_full <= (fifo_tail==n_fifo_head);
		end
		assign w_fifo_full = r_fifo_full;
	end else begin
		//
		// Strict ordering, but can only read every fourth addresses
		//
		assign w_fifo_full = 1'b0;
		always @(posedge i_clk)
			o_wb_data <= i_axi_rdata[31:0];
		always @(posedge i_clk)
			o_wb_ack <= (i_wb_cyc)&&(
				((i_axi_rvalid)&&(o_axi_rready))
				  ||((i_axi_bvalid)&&(o_axi_bready)));
		always @(posedge i_clk)
			o_wb_err <= (i_wb_cyc)&&((o_wb_err)
				||((i_axi_rvalid)&&(i_axi_rresp[1]))
				||((i_axi_bvalid)&&(i_axi_bresp[1])));
	end endgenerate
	

	// Now, the difficult signal ... the stall signal
	// Let's build for a single cycle input ... and only stall if something
	// outgoing is valid and nothing is ready.
	assign	o_wb_stall = (i_wb_cyc)&&(
				(w_fifo_full)
				||((o_axi_awvalid)&&(!i_axi_awready))
				||((o_axi_wvalid )&&(!i_axi_wready ))
				||((o_axi_arvalid)&&(!i_axi_arready)));
endmodule

