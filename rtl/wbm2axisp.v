////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbm2axisp.v (Wishbone master to AXI slave, pipelined)
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
// Copyright (C) 2016-2018, Gisselquist Technology, LLC
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
module wbm2axisp #(
	parameter C_AXI_ID_WIDTH	=   3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	=  28,	// AXI Address width (log wordsize)
	parameter DW			=  32,	// Wishbone data width
	parameter AW			=  26,	// Wishbone address width (log wordsize)
	parameter [0:0] STRICT_ORDER	= 1	// Reorder, or not? 0 -> Reorder
	) (
	input	wire			i_clk,	// System clock
	input	wire			i_reset,// Reset signal,drives AXI rst

// AXI write address channel signals
	input	wire			i_axi_awready, // Slave is ready to accept
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
	input	wire			i_axi_wready,  // Write data ready
	output	reg	[C_AXI_DATA_WIDTH-1:0]	o_axi_wdata,	// Write data
	output	reg	[C_AXI_DATA_WIDTH/8-1:0] o_axi_wstrb,	// Write strobes
	output	wire			o_axi_wlast,	// Last write transaction   
	output	reg			o_axi_wvalid,	// Write valid

// AXI write response channel signals
	input wire [C_AXI_ID_WIDTH-1:0]	i_axi_bid,	// Response ID
	input	wire [1:0]		i_axi_bresp,	// Write response
	input	wire			i_axi_bvalid,  // Write reponse valid
	output	wire			o_axi_bready,  // Response ready

// AXI read address channel signals
	input	wire			i_axi_arready,	// Read address ready
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
	input wire [C_AXI_ID_WIDTH-1:0]	i_axi_rid,     // Response ID
	input	wire	[1:0]		i_axi_rresp,   // Read response
	input	wire			i_axi_rvalid,  // Read reponse valid
	input wire [C_AXI_DATA_WIDTH-1:0] i_axi_rdata,    // Read data
	input	wire			i_axi_rlast,    // Read last
	output	wire			o_axi_rready,  // Read Response ready

	// We'll share the clock and the reset
	input	wire			i_wb_cyc,
	input	wire			i_wb_stb,
	input	wire			i_wb_we,
	input	wire	[(AW-1):0]	i_wb_addr,
	input	wire	[(DW-1):0]	i_wb_data,
	input	wire	[(DW/8-1):0]	i_wb_sel,
	output	reg			o_wb_ack,
	output	wire			o_wb_stall,
	output	reg	[(DW-1):0]	o_wb_data,
	output	reg			o_wb_err
);

//*****************************************************************************
// Parameter declarations
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
	localparam	LGFIFOLN = C_AXI_ID_WIDTH;
	localparam	FIFOLN = (1<<LGFIFOLN);


//*****************************************************************************
// Internal register and wire declarations
//*****************************************************************************

// Things we're not changing ...
	assign o_axi_awlen   = 8'h0;	// Burst length is one
	assign o_axi_awsize  = 3'b101;	// maximum bytes per burst is 32
	assign o_axi_awburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_arburst = 2'b01;	// Incrementing address (ignored)
	assign o_axi_awlock  = 1'b0;	// Normal signaling
	assign o_axi_arlock  = 1'b0;	// Normal signaling
	assign o_axi_awcache = 4'h2;	// Normal: no cache, no buffer
	assign o_axi_arcache = 4'h2;	// Normal: no cache, no buffer
	assign o_axi_awprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_arprot  = 3'b010;	// Unpriviledged, unsecure, data access
	assign o_axi_awqos   = 4'h0;	// Lowest quality of service (unused)
	assign o_axi_arqos   = 4'h0;	// Lowest quality of service (unused)

	reg	wb_mid_cycle, wb_mid_abort;
	wire	wb_abort;

// Command logic
// Transaction ID logic
	wire	[(LGFIFOLN-1):0]	fifo_head;
	reg	[(C_AXI_ID_WIDTH-1):0]	transaction_id;

	initial	transaction_id = 0;
	always @(posedge i_clk)
	if (i_reset)
		transaction_id <= 0;
	else if ((i_wb_stb)&&(!o_wb_stall))
		transaction_id <= transaction_id + 1'b1;

	assign	fifo_head = transaction_id;

	wire	[(DW/8-1):0]			no_sel;
	wire	[(LG_AXI_DW-4):0]	axi_bottom_addr;
	assign	no_sel = 0;
	assign	axi_bottom_addr = 0;


// Write address logic

	initial	o_axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_awvalid <= 0;
	else
		o_axi_awvalid <= (!o_wb_stall)&&(i_wb_stb)&&(i_wb_we)
			||(o_axi_awvalid)&&(!i_axi_awready);

	generate

	initial	o_axi_awid = -1;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_awid <= -1;
	else if ((i_wb_stb)&&(!o_wb_stall))
		o_axi_awid <= transaction_id;

	if (C_AXI_DATA_WIDTH == DW)
	begin
		always @(posedge i_clk)
		if ((i_wb_stb)&&(!o_wb_stall)) // 26 bit address becomes 28 bit ...
			o_axi_awaddr <= { i_wb_addr[AW-1:0], axi_bottom_addr };
	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin

		always @(posedge i_clk)
		if ((i_wb_stb)&&(!o_wb_stall)) // 26 bit address becomes 28 bit ...
			o_axi_awaddr <= { i_wb_addr[AW-1:1], axi_bottom_addr };

	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin
		always @(posedge i_clk)
		if ((i_wb_stb)&&(!o_wb_stall)) // 26 bit address becomes 28 bit ...
			o_axi_awaddr <= { i_wb_addr[AW-1:2], axi_bottom_addr };
	end endgenerate


// Read address logic
	assign	o_axi_arid   = o_axi_awid;
	assign	o_axi_araddr = o_axi_awaddr;
	assign	o_axi_arlen  = o_axi_awlen;
	assign	o_axi_arsize = 3'b101;	// maximum bytes per burst is 32
	initial	o_axi_arvalid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_arvalid <= 1'b0;
	else
		o_axi_arvalid <= (!o_wb_stall)&&(i_wb_stb)&&(!i_wb_we)
			||(o_axi_arvalid)&&(!i_axi_arready);

// Write data logic
	generate
	if (C_AXI_DATA_WIDTH == DW)
	begin

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				o_axi_wdata <= i_wb_data;

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				o_axi_wstrb<= i_wb_sel;

	end else if (C_AXI_DATA_WIDTH/2 == DW)
	begin

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				o_axi_wdata <= { i_wb_data, i_wb_data };

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
			case(i_wb_addr[0])
			1'b0:o_axi_wstrb<={  no_sel,i_wb_sel };
			1'b1:o_axi_wstrb<={i_wb_sel,  no_sel };
			endcase

	end else if (C_AXI_DATA_WIDTH/4 == DW)
	begin

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				o_axi_wdata <= { i_wb_data, i_wb_data, i_wb_data, i_wb_data };

		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
			case(i_wb_addr[1:0])
			2'b00:o_axi_wstrb<={   no_sel,   no_sel,   no_sel, i_wb_sel };
			2'b01:o_axi_wstrb<={   no_sel,   no_sel, i_wb_sel,   no_sel };
			2'b10:o_axi_wstrb<={   no_sel, i_wb_sel,   no_sel,   no_sel };
			2'b11:o_axi_wstrb<={ i_wb_sel,   no_sel,   no_sel,   no_sel };
			endcase

	end endgenerate

	assign	o_axi_wlast = 1'b1;
	initial	o_axi_wvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_axi_wvalid <= 0;
	else
		o_axi_wvalid <= ((!o_wb_stall)&&(i_wb_stb)&&(i_wb_we))
			||(o_axi_wvalid)&&(!i_axi_wready);

	// Read data channel / response logic
	assign	o_axi_rready = 1'b1;
	assign	o_axi_bready = 1'b1;

	wire	[(LGFIFOLN-1):0]	n_fifo_head, nn_fifo_head;
	assign	n_fifo_head = fifo_head+1'b1;
	assign	nn_fifo_head = { fifo_head[(LGFIFOLN-1):1]+1'b1, fifo_head[0] };


	wire	w_fifo_full;
	reg	[(LGFIFOLN-1):0]	fifo_tail;

	generate
	if (C_AXI_DATA_WIDTH == DW)
	begin
		if (STRICT_ORDER == 0)
		begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data [0:(FIFOLN-1)];

			always @(posedge i_clk)
				if ((o_axi_rready)&&(i_axi_rvalid))
					reorder_fifo_data[i_axi_rid] <= i_axi_rdata;
			always @(posedge i_clk)
				o_wb_data <= reorder_fifo_data[fifo_tail];
		end else begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data;

			always @(posedge i_clk)
				reorder_fifo_data <= i_axi_rdata;
			always @(posedge i_clk)
				o_wb_data <= reorder_fifo_data;
		end
	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin
		reg		reorder_fifo_addr [0:(FIFOLN-1)];

		reg		low_addr;
		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				low_addr <= i_wb_addr[0];
		always @(posedge i_clk)
			if ((o_axi_arvalid)&&(i_axi_arready))
				reorder_fifo_addr[o_axi_arid] <= low_addr;

		if (STRICT_ORDER == 0)
		begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data [0:(FIFOLN-1)];

			always @(posedge i_clk)
				if ((o_axi_rready)&&(i_axi_rvalid))
					reorder_fifo_data[i_axi_rid] <= i_axi_rdata;
			always @(posedge i_clk)
				reorder_fifo_data[i_axi_rid] <= i_axi_rdata;
			always @(posedge i_clk)
			case(reorder_fifo_addr[fifo_tail])
			1'b0: o_wb_data <=reorder_fifo_data[fifo_tail][(  DW-1):    0 ];
			1'b1: o_wb_data <=reorder_fifo_data[fifo_tail][(2*DW-1):(  DW)];
			endcase
		end else begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data;

			always @(posedge i_clk)
				reorder_fifo_data <= i_axi_rdata;
			always @(posedge i_clk)
			case(reorder_fifo_addr[fifo_tail])
			1'b0: o_wb_data <=reorder_fifo_data[(  DW-1):    0 ];
			1'b1: o_wb_data <=reorder_fifo_data[(2*DW-1):(  DW)];
			endcase
		end
	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin
		reg	[1:0]	reorder_fifo_addr [0:(FIFOLN-1)];


		reg	[1:0]	low_addr;
		always @(posedge i_clk)
			if ((i_wb_stb)&&(!o_wb_stall))
				low_addr <= i_wb_addr[1:0];
		always @(posedge i_clk)
			if ((o_axi_arvalid)&&(i_axi_arready))
				reorder_fifo_addr[o_axi_arid] <= low_addr;

		if (STRICT_ORDER == 0)
		begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data [0:(FIFOLN-1)];

			always @(posedge i_clk)
				if ((o_axi_rready)&&(i_axi_rvalid))
					reorder_fifo_data[i_axi_rid] <= i_axi_rdata;
			always @(posedge i_clk)
			case(reorder_fifo_addr[fifo_tail][1:0])
			2'b00: o_wb_data <=reorder_fifo_data[fifo_tail][(  DW-1):    0 ];
			2'b01: o_wb_data <=reorder_fifo_data[fifo_tail][(2*DW-1):(  DW)];
			2'b10: o_wb_data <=reorder_fifo_data[fifo_tail][(3*DW-1):(2*DW)];
			2'b11: o_wb_data <=reorder_fifo_data[fifo_tail][(4*DW-1):(3*DW)];
			endcase
		end else begin
			reg	[(C_AXI_DATA_WIDTH-1):0] reorder_fifo_data;

			always @(posedge i_clk)
				reorder_fifo_data <= i_axi_rdata;
			always @(posedge i_clk)
			case(reorder_fifo_addr[fifo_tail][1:0])
			2'b00: o_wb_data <=reorder_fifo_data[(  DW-1): 0];
			2'b01: o_wb_data <=reorder_fifo_data[(2*DW-1):(  DW)];
			2'b10: o_wb_data <=reorder_fifo_data[(3*DW-1):(2*DW)];
			2'b11: o_wb_data <=reorder_fifo_data[(4*DW-1):(3*DW)];
			endcase
		end
	end

	endgenerate

	// verilator lint_off UNUSED
	wire	axi_rd_ack, axi_wr_ack, axi_ard_req, axi_awr_req, axi_wr_req,
		axi_rd_err, axi_wr_err;
	// verilator lint_on  UNUSED

	//
	assign	axi_ard_req = (o_axi_arvalid)&&(i_axi_arready);
	assign	axi_awr_req = (o_axi_awvalid)&&(i_axi_awready);
	assign	axi_wr_req  = (o_axi_wvalid )&&(i_axi_wready);
	//
	assign	axi_rd_ack = (i_axi_rvalid)&&(o_axi_rready);
	assign	axi_wr_ack = (i_axi_bvalid)&&(o_axi_bready);
	assign	axi_rd_err = (axi_rd_ack)&&(i_axi_rresp[1]);
	assign	axi_wr_err = (axi_wr_ack)&&(i_axi_bresp[1]);

	//
	// We're going to need a FIFO on the return to make certain that we can
	// select the right bits from the return value, in the case where
	// DW != the axi data width.
	//
	// If we aren't using a strict order, this FIFO is can be used as a
	// reorder buffer as well, to place our out of order bus responses
	// back into order.  Responses on the wishbone, however, are *always*
	// done in order.
	generate
	if (STRICT_ORDER == 0)
	begin
		// Reorder FIFO
		//
		// FIFO reorder buffer
		reg	[(FIFOLN-1):0]	reorder_fifo_valid;
		reg	[(FIFOLN-1):0]	reorder_fifo_err;

		initial reorder_fifo_valid = 0;
		initial reorder_fifo_err = 0;


		initial	fifo_tail = 0;
		initial	o_wb_ack  = 0;
		initial	o_wb_err  = 0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			reorder_fifo_valid <= 0;
			reorder_fifo_err <= 0;
			o_wb_ack  <= 0;
			o_wb_err  <= 0;
			fifo_tail <= 0;
		end else begin
			if (axi_rd_ack)
			begin
				reorder_fifo_valid[i_axi_rid] <= 1'b1;
				reorder_fifo_err[i_axi_rid] <= axi_rd_err;
			end
			if (axi_wr_ack)
			begin
				reorder_fifo_valid[i_axi_bid] <= 1'b1;
				reorder_fifo_err[i_axi_bid] <= axi_wr_err;
			end

			if (reorder_fifo_valid[fifo_tail])
			begin
				o_wb_ack <= (!wb_abort)&&(!reorder_fifo_err[fifo_tail]);
				o_wb_err <= (!wb_abort)&&( reorder_fifo_err[fifo_tail]);
				fifo_tail <= fifo_tail + 1'b1;
				reorder_fifo_valid[fifo_tail] <= 1'b0;
				reorder_fifo_err[fifo_tail]   <= 1'b0;
			end else begin
				o_wb_ack <= 1'b0;
				o_wb_err <= 1'b0;
			end

			if (!i_wb_cyc)
			begin
				// reorder_fifo_valid <= 0;
				// reorder_fifo_err   <= 0;
				o_wb_err <= 1'b0;
				o_wb_ack <= 1'b0;
			end
		end

		reg	r_fifo_full;
		initial	r_fifo_full = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_fifo_full <= 0;
		else begin
			if ((i_wb_stb)&&(!o_wb_stall)
					&&(reorder_fifo_valid[fifo_tail]))
				r_fifo_full <= (fifo_tail==n_fifo_head);
			else if ((i_wb_stb)&&(!o_wb_stall))
				r_fifo_full <= (fifo_tail==nn_fifo_head);
			else if (reorder_fifo_valid[fifo_tail])
				r_fifo_full <= 1'b0;
			else
				r_fifo_full <= (fifo_tail==n_fifo_head);
		end
		assign w_fifo_full = r_fifo_full;
	end else begin
		//
		// Strict ordering
		//
		reg	reorder_fifo_valid;
		reg	reorder_fifo_err;

		initial	reorder_fifo_valid = 1'b0;
		initial	reorder_fifo_err   = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			reorder_fifo_valid <= 0;
			reorder_fifo_err   <= 0;
		end else begin
			if (axi_rd_ack)
			begin
				reorder_fifo_valid <= 1'b1;
				reorder_fifo_err   <= axi_rd_err;
			end else if (axi_wr_ack)
			begin
				reorder_fifo_valid <= 1'b1;
				reorder_fifo_err   <= axi_wr_err;
			end else begin
				reorder_fifo_valid <= 1'b0;
				reorder_fifo_err   <= 1'b0;
			end
		end

		initial	fifo_tail = 0;
		always @(posedge i_clk)
		if (i_reset)
			fifo_tail <= 0;
		else if (reorder_fifo_valid)
			fifo_tail <= fifo_tail + 1'b1;

		initial	o_wb_ack  = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_wb_ack <= 0;
		else
			o_wb_ack <= (reorder_fifo_valid)&&(i_wb_cyc)&&(!wb_abort);

		initial	o_wb_err  = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_wb_err <= 0;
		else
			o_wb_err <= (reorder_fifo_err)&&(i_wb_cyc)&&(!wb_abort);

		reg	r_fifo_full;
		initial	r_fifo_full = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_fifo_full <= 0;
		else begin
			if ((i_wb_stb)&&(!o_wb_stall)
					&&(reorder_fifo_valid))
				r_fifo_full <= (fifo_tail==n_fifo_head);
			else if ((i_wb_stb)&&(!o_wb_stall))
				r_fifo_full <= (fifo_tail==nn_fifo_head);
			else if (reorder_fifo_valid)
				r_fifo_full <= 1'b0;
			else
				r_fifo_full <= (fifo_tail==n_fifo_head);
		end

		assign w_fifo_full = r_fifo_full;

		// verilator lint_off UNUSED
		wire	[2*C_AXI_ID_WIDTH-1:0]	strict_unused;
		assign	strict_unused = { i_axi_bid, i_axi_rid };
		// verilator lint_on  UNUSED
	end endgenerate

	//
	// Wishbone abort logic
	//

	// Else, are we mid-cycle?
	initial	wb_mid_cycle = 0;
	always @(posedge i_clk)
	if (i_reset)
		wb_mid_cycle <= 0;
	else if ((fifo_head != fifo_tail)
			||(o_axi_arvalid)||(o_axi_awvalid)
			||(o_axi_wvalid)
			||(i_wb_cyc)&&(i_wb_stb)&&(!o_wb_stall))
		wb_mid_cycle <= 1'b1;
	else
		wb_mid_cycle <= 1'b0;

	initial	wb_mid_abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		wb_mid_abort <= 0;
	else if (wb_mid_cycle)
		wb_mid_abort <= (wb_mid_abort)||(!i_wb_cyc);
	else
		wb_mid_abort <= 1'b0;

	assign	wb_abort = ((wb_mid_cycle)&&(!i_wb_cyc))||(wb_mid_abort);

	// Now, the difficult signal ... the stall signal
	// Let's build for a single cycle input ... and only stall if something
	// outgoing is valid and nothing is ready.
	assign	o_wb_stall = (i_wb_cyc)&&(
				(w_fifo_full)||(wb_mid_abort)
				||((o_axi_awvalid)&&(!i_axi_awready))
				||((o_axi_wvalid )&&(!i_axi_wready ))
				||((o_axi_arvalid)&&(!i_axi_arready)));

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire    [2:0]   unused;
	assign  unused = { i_axi_bresp[0], i_axi_rresp[0], i_axi_rlast };
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
//
// This section has been removed from this release.
//
endmodule
