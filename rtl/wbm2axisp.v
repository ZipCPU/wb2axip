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
`default_nettype	none
//
module wbm2axisp #(
	parameter C_AXI_ID_WIDTH	= 3, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 128,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width (log wordsize)
	parameter DW			= 32,	// Wishbone data width
	parameter AW			= 26,	// Wishbone address width (log wordsize)
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
// Transaction ID logic
	wire	[(LGFIFOLN-1):0]	fifo_head;
	reg	[(C_AXI_ID_WIDTH-1):0]	transaction_id;

	initial	transaction_id = 0;
	always @(posedge i_clk)
		if (!i_wb_cyc)
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
		o_axi_awvalid <= (!o_wb_stall)&&(i_wb_stb)&&(i_wb_we)
			||(o_wb_stall)&&(o_axi_awvalid)&&(!i_axi_awready);

	generate

	initial	o_axi_awid = 0;
	always @(posedge i_clk)
		if ((i_wb_stb)&&(!o_wb_stall))
			o_axi_awid <= transaction_id;

	if (C_AXI_DATA_WIDTH == DW)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall) // 26 bit address becomes 28 bit ...
				o_axi_awaddr <= { i_wb_addr[AW-1:0], axi_bottom_addr };
	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin

		always @(posedge i_clk)
			if (!o_wb_stall) // 26 bit address becomes 28 bit ...
				o_axi_awaddr <= { i_wb_addr[AW-1:1], axi_bottom_addr };

	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin
		always @(posedge i_clk)
			if (!o_wb_stall) // 26 bit address becomes 28 bit ...
				o_axi_awaddr <= { i_wb_addr[AW-1:2], axi_bottom_addr };
	end endgenerate


// Read address logic
	assign	o_axi_arid   = o_axi_awid;
	assign	o_axi_araddr = o_axi_awaddr;
	assign	o_axi_arlen  = o_axi_awlen;
	assign	o_axi_arsize = 3'b101;	// maximum bytes per burst is 32
	initial	o_axi_arvalid = 1'b0;
	always @(posedge i_clk)
		o_axi_arvalid <= (!o_wb_stall)&&(i_wb_stb)&&(!i_wb_we)
			||(o_wb_stall)&&(o_axi_arvalid)&&(!i_axi_arready);

// Write data logic
	generate
	if (C_AXI_DATA_WIDTH == DW)
	begin

		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wdata <= i_wb_data;

		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wstrb<= i_wb_sel;

	end else if (C_AXI_DATA_WIDTH/2 == DW)
	begin

		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wdata <= { i_wb_data, i_wb_data };

		always @(posedge i_clk)
			if (!o_wb_stall)
			case(i_wb_addr[0])
			1'b0:o_axi_wstrb<={  no_sel,i_wb_sel };
			1'b1:o_axi_wstrb<={i_wb_sel,  no_sel };
			endcase

	end else if (C_AXI_DATA_WIDTH/4 == DW)
	begin

		always @(posedge i_clk)
			if (!o_wb_stall)
				o_axi_wdata <= { i_wb_data, i_wb_data, i_wb_data, i_wb_data };

		always @(posedge i_clk)
			if (!o_wb_stall)
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
		o_axi_wvalid <= ((!o_wb_stall)&&(i_wb_stb)&&(i_wb_we))
			||(o_wb_stall)&&(o_axi_wvalid)&&(!i_axi_wready);

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
			case(reorder_fifo_addr[fifo_tail][1:0])
			2'b00: o_wb_data <=reorder_fifo_data[(  DW-1): 0];
			2'b01: o_wb_data <=reorder_fifo_data[(2*DW-1):(  DW)];
			2'b10: o_wb_data <=reorder_fifo_data[(3*DW-1):(2*DW)];
			2'b11: o_wb_data <=reorder_fifo_data[(4*DW-1):(3*DW)];
			endcase
		end
	end

	endgenerate

	wire	axi_rd_ack, axi_wr_ack, axi_ard_req, axi_awr_req, axi_wr_req;
	//
	assign	axi_ard_req = (o_axi_arvalid)&&(i_axi_arready);
	assign	axi_awr_req = (o_axi_awvalid)&&(i_axi_awready);
	assign	axi_wr_req  = (o_axi_wvalid )&&(i_axi_wready);
	//
	assign	axi_rd_ack = (i_axi_rvalid)&&(o_axi_rready);
	assign	axi_wr_ack = (i_axi_bvalid)&&(o_axi_bready);

	//
	// We're going to need a FIFO on the return to make certain that we can
	// select the right bits from the return value, in the case where DW != the
	// axi data width.
	//
	// If we aren't using a strict order, this FIFO is can be used as a reorder buffer
	// as well, to place our out of order bus responses back into order.  Responses
	// on the wishbone, however, are *always* done in order.
`ifdef	FORMAL
	reg	[31:0]	reorder_count;
`endif
	integer	k;
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
		begin
			if (axi_rd_ack)
			begin
				reorder_fifo_valid[i_axi_rid] <= 1'b1;
				reorder_fifo_err[i_axi_rid] <= i_axi_rresp[1];
			end
			if (axi_wr_ack)
			begin
				reorder_fifo_valid[i_axi_bid] <= 1'b1;
				reorder_fifo_err[i_axi_bid] <= i_axi_bresp[1];
			end

			if (reorder_fifo_valid[fifo_tail])
			begin
				o_wb_ack <= 1'b1;
				o_wb_err <= reorder_fifo_err[fifo_tail];
				fifo_tail <= fifo_tail + 1'b1;
				reorder_fifo_valid[fifo_tail] <= 1'b0;
				reorder_fifo_err[fifo_tail]   <= 1'b0;
			end else begin
				o_wb_ack <= 1'b0;
				o_wb_err <= 1'b0;
			end

			if (!i_wb_cyc)
			begin
				reorder_fifo_valid <= 0;
				reorder_fifo_err   <= 0;
				fifo_tail <= 0;
				o_wb_err <= 1'b0;
				o_wb_ack <= 1'b0;
			end
		end

`ifdef	FORMAL
		always @(*)
		begin
			reorder_count = 0;
			for(k=0; k<FIFOLN; k=k+1)
				if (reorder_fifo_valid[k])
					reorder_count = reorder_count + 1;
		end
`endif

		reg	r_fifo_full;
		initial	r_fifo_full = 0;
		always @(posedge i_clk)
		begin
			if (!i_wb_cyc)
				r_fifo_full <= 1'b0;
			else if ((i_wb_stb)&&(!o_wb_stall)
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
			if (!i_wb_cyc)
			begin
				reorder_fifo_valid <= 1'b0;
				reorder_fifo_err   <= 1'b0;
			end else if (axi_rd_ack)
			begin
				reorder_fifo_valid <= 1'b1;
				reorder_fifo_err   <= i_axi_rresp[1];
			end else if (axi_wr_ack)
			begin
				reorder_fifo_valid <= 1'b1;
				reorder_fifo_err   <= i_axi_bresp[1];
			end else begin
				reorder_fifo_valid <= 1'b0;
				reorder_fifo_err   <= 1'b0;
			end

		always @(*)
			reorder_count = (reorder_fifo_valid) ? 1 : 0;

		always @(posedge i_clk)
			if (!i_wb_cyc)
				fifo_tail <= 0;
			else if ((axi_rd_ack)||(axi_wr_ack))
				fifo_tail <= fifo_tail + 6'h1;

		always @(posedge i_clk)
			o_wb_ack <= (reorder_fifo_valid)&&(i_wb_cyc);

		always @(posedge i_clk)
			o_wb_err <= (reorder_fifo_err)&&(i_wb_cyc);

		always @(posedge i_clk)
			if ((axi_rd_ack)||(axi_wr_ack))
				fifo_tail <= fifo_tail + 6'h1;

		reg	r_fifo_full;
		initial	r_fifo_full = 0;
		always @(posedge i_clk)
		begin
			if (!i_wb_cyc)
				r_fifo_full <= 1'b0;
			else if ((i_wb_stb)&&(!o_wb_stall)
					&&(reorder_fifo_valid))
				r_fifo_full <= (fifo_tail==n_fifo_head);
			else if ((i_wb_stb)&&(!o_wb_stall))
				r_fifo_full <= (fifo_tail==nn_fifo_head);
			else if (reorder_fifo_valid[fifo_tail])
				r_fifo_full <= 1'b0;
			else
				r_fifo_full <= (fifo_tail==n_fifo_head);
		end

		assign w_fifo_full = r_fifo_full;
	end endgenerate
	

	// Now, the difficult signal ... the stall signal
	// Let's build for a single cycle input ... and only stall if something
	// outgoing is valid and nothing is ready.
	assign	o_wb_stall = (i_wb_cyc)&&(
				(w_fifo_full)
				||((o_axi_awvalid)&&(!i_axi_awready))
				||((o_axi_wvalid )&&(!i_axi_wready ))
				||((o_axi_arvalid)&&(!i_axi_arready)));


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
//
`ifdef	WBM2AXISP
// If we are the top-level of the design ...
`define	ASSUME	assume
`define	FORMAL_CLOCK	assume(i_clk == !f_last_clk); f_last_clk <= i_clk;
`else
`define	ASSUME	assert
`define	FORMAL_CLOCK	f_last_clk <= i_clk; // Clock will be given to us valid already
`endif

	// Parameters
	initial	assert(	  (C_AXI_DATA_WIDTH / DW == 4)
			||(C_AXI_DATA_WIDTH / DW == 2)
			||(C_AXI_DATA_WIDTH      == DW));
	//
	initial	assert( C_AXI_ADDR_WIDTH - LG_AXI_DW + LG_WB_DW == AW);

	//
	// Setup
	//

	reg	f_past_valid, f_last_clk;

	always @($global_clock)
	begin
		`FORMAL_CLOCK

		// Assume our inputs will only change on the positive edge
		// of the clock
		if (!$rose(i_clk))
		begin
			// AXI inputs
			`ASSUME($stable(i_axi_awready));
			`ASSUME($stable(i_axi_wready));
			`ASSUME($stable(i_axi_bid));
			`ASSUME($stable(i_axi_bresp));
			`ASSUME($stable(i_axi_bvalid));
			`ASSUME($stable(i_axi_arready));
			`ASSUME($stable(i_axi_rid));
			`ASSUME($stable(i_axi_rresp));
			`ASSUME($stable(i_axi_rvalid));
			`ASSUME($stable(i_axi_rdata));
			`ASSUME($stable(i_axi_rlast));
			// Wishbone inputs
			`ASSUME($stable(i_wb_cyc));
			`ASSUME($stable(i_wb_stb));
			`ASSUME($stable(i_wb_we));
			`ASSUME($stable(i_wb_addr));
			`ASSUME($stable(i_wb_data));
			`ASSUME($stable(i_wb_sel));
		end
	end

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	//////////////////////////////////////////////
	//
	//
	// Assumptions about the WISHBONE inputs
	//
	//
	//////////////////////////////////////////////

	// Strobes are only allowed if CYC is also true
	initial	`ASSUME(!i_wb_cyc);
	always @(posedge i_clk)
		if (i_wb_stb)
			`ASSUME(i_wb_cyc);

	// Assume any request made on the bus will not change prior to that
	// request being sent
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if (($past(o_wb_stall))&&($past(i_wb_stb))&&(i_wb_cyc))
		begin
			`ASSUME(i_wb_we   == $past(i_wb_we));
			`ASSUME(i_wb_addr == $past(i_wb_addr));
			`ASSUME(i_wb_data == $past(i_wb_data));
			`ASSUME(i_wb_sel  == $past(i_wb_sel));
		end
	end

	// Any wishbone write request *must* also indicate one or more bytes
	// to write
	always @(posedge i_clk)
		if ((i_wb_stb)&&(i_wb_we))
			`ASSUME(|i_wb_sel);

	//////////////////////////////////////////////
	//
	//
	// Assertions about the AXI4 ouputs
	//
	//
	//////////////////////////////////////////////

	// Nothing should be returning a result on the first clock
	initial	`ASSUME(!i_axi_bvalid);
	initial	`ASSUME(!i_axi_rvalid);

	// If valid, but not ready, on any channel is true, nothing changes
	// until valid && ready
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_axi_awvalid))&&(!$past(i_axi_awready))&&($past(i_wb_cyc)))
	begin
		assert($stable(o_axi_awid));
		assert($stable(o_axi_awaddr));
		assert($stable(o_axi_awlen));
		assert($stable(o_axi_awsize));
		assert($stable(o_axi_awburst));
		assert($stable(o_axi_awlock));
		assert($stable(o_axi_awcache));
		assert($stable(o_axi_awprot));
		assert($stable(o_axi_awqos));
		assert($stable(o_axi_awvalid));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_axi_wvalid))&&(!$past(i_axi_wready))
		&&($past(i_wb_cyc)))
	begin
		// AXI write data channel signals
		assert($stable(o_axi_wdata));
		assert($stable(o_axi_wstrb));
		assert($stable(o_axi_wlast));
		assert($stable(o_axi_wvalid));
	end

	// Write response channel
	always @(posedge i_clk)
		// We keep bready high, so the other condition doesn't
		// need to be checked
		assert(o_axi_bready);

	// Read address chanel
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_axi_arvalid))&&(!$past(i_axi_arready))
		&&($past(i_wb_cyc)))
	begin
		assert($stable(o_axi_arid));
		assert($stable(o_axi_araddr));
		assert($stable(o_axi_arlen));
		assert($stable(o_axi_arsize));
		assert($stable(o_axi_arburst));
		assert($stable(o_axi_arlock));
		assert($stable(o_axi_arcache));
		assert($stable(o_axi_arprot));
		assert($stable(o_axi_arqos));
		assert($stable(o_axi_arvalid));
	end

	// AXI read data channel signals   
	always @(posedge i_clk)
		// We keep o_axi_rready high, so the other condition's
		// don't need to be checked here
		assert(o_axi_rready);

	//
	// Let's look into write requests
	//
	initial	assert(!o_axi_awvalid);
	initial	assert(!o_axi_wvalid);
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we))&&(!$past(o_wb_stall)))
	begin
		// Following any write request that we accept, awvalid and
		// wvalid should both be true
		assert(o_axi_awvalid);
		assert(o_axi_wvalid);
	end

	// Let's assume all responses will come within 120 clock ticks
	parameter	[(C_AXI_ID_WIDTH-1):0]	F_MAXDELAY = 3; // 7'd120;
	localparam	[(C_AXI_ID_WIDTH):0]	F_WB_MAXDELAY = F_MAXDELAY + 4;

	reg	[(C_AXI_ID_WIDTH):0]	f_wb_outstanding, f_axi_delay;
	reg	[(2*C_AXI_ID_WIDTH):0]	f_wb_delay;
	initial	f_wb_outstanding = 0;
	always @(posedge i_clk)
		if (!i_wb_cyc)
			f_wb_outstanding <= 0;
		else casez({ i_wb_stb, o_wb_stall, o_wb_ack })
		3'b0?1: f_wb_outstanding <= f_wb_outstanding - 1'b1;
		3'b100: f_wb_outstanding <= f_wb_outstanding + 1'b1;
		3'b111: f_wb_outstanding <= f_wb_outstanding - 1'b1;
		default: f_wb_outstanding<= f_wb_outstanding;
		endcase

	always @(posedge i_clk)
		if (o_wb_ack)
			assert(f_wb_outstanding > 0);

	always @(posedge i_clk)
		if (!i_wb_cyc)
			restrict(f_wb_outstanding == 0);

	always @(posedge i_clk)
		if ((!i_wb_cyc)||(axi_rd_ack)||(axi_wr_ack))
			f_axi_delay <= 0;
		else if ((f_axi_rd_outstanding>0)||(f_axi_awr_outstanding>0)||(f_axi_wr_outstanding>0))
			f_axi_delay <= f_axi_delay + 1'b1;
	always @(posedge i_clk)
		restrict(f_axi_delay < { 1'b0, F_MAXDELAY });

	initial	f_wb_delay = 0;
	always @(posedge i_clk)
		if ((!i_wb_cyc)||(o_wb_ack))
			f_wb_delay <= 0;
		else if (f_wb_outstanding > 0)
			f_wb_delay <= f_wb_delay + 1'b1;

	always @(posedge i_clk)
		if (STRICT_ORDER)
			assert(f_wb_delay < { {(C_AXI_ID_WIDTH){1'b0}}, F_WB_MAXDELAY });
		else
			assert(f_wb_delay < { F_WB_MAXDELAY, {(C_AXI_ID_WIDTH){1'b0}} });

	//
	// AXI write address channel
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_wb_stall)))
	begin
		if (!$past(i_wb_stb))
			assert(!o_axi_awvalid);
		else
			assert(o_axi_awvalid == $past(i_wb_we));
	end
	//
	generate
	if (C_AXI_DATA_WIDTH      == DW)
	begin
		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we))
			&&(!$past(o_wb_stall)))
			assert(o_axi_awaddr == { $past(i_wb_addr[AW-1:0]), axi_bottom_addr });

	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we))
			&&(!$past(o_wb_stall)))
			assert(o_axi_awaddr == { $past(i_wb_addr[AW-1:1]), axi_bottom_addr });

	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we))
			&&(!$past(o_wb_stall)))
			assert(o_axi_awaddr == { $past(i_wb_addr[AW-1:2]), axi_bottom_addr });

	end endgenerate
		
	//
	// AXI write data channel
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_wb_stall)))
	begin
		if (!$past(i_wb_stb))
			assert(!o_axi_wvalid);
		else
			assert(o_axi_wvalid == $past(i_wb_we));
	end
	//
	generate
	if (C_AXI_DATA_WIDTH == DW)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we)))
		begin
			assert(o_axi_wdata == $past(i_wb_data));
			assert(o_axi_wstrb == $past(i_wb_sel));
		end

	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&($past(i_wb_we)))
		begin
			case($past(i_wb_addr[0]))
			1'b0: assert(o_axi_wdata[(  DW-1): 0] == $past(i_wb_data));
			1'b1: assert(o_axi_wdata[(2*DW-1):DW] == $past(i_wb_data));
			endcase

			case($past(i_wb_addr[0]))
			1'b0: assert(o_axi_wstrb == {  no_sel,$past(i_wb_sel)});
			1'b1: assert(o_axi_wstrb == {  $past(i_wb_sel),no_sel});
			endcase
		end

	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_stb))&&(!$past(o_wb_stall))&&($past(i_wb_we)))
		begin
			case($past(i_wb_addr[1:0]))
			2'b00: assert(o_axi_wdata[  (DW-1):    0 ] == $past(i_wb_data));
			2'b00: assert(o_axi_wdata[(2*DW-1):(  DW)] == $past(i_wb_data));
			2'b00: assert(o_axi_wdata[(3*DW-1):(2*DW)] == $past(i_wb_data));
			2'b11: assert(o_axi_wdata[(4*DW-1):(3*DW)] == $past(i_wb_data));
			endcase

			case($past(i_wb_addr[1:0]))
			2'b00: assert(o_axi_wstrb == { {(3){no_sel}},$past(i_wb_sel)});
			2'b01: assert(o_axi_wstrb == { {(2){no_sel}},$past(i_wb_sel), {(1){no_sel}}});
			2'b10: assert(o_axi_wstrb == { {(1){no_sel}},$past(i_wb_sel), {(2){no_sel}}});
			2'b11: assert(o_axi_wstrb == {       $past(i_wb_sel),{(3){no_sel}}});
			endcase
		end
	end endgenerate

	//
	// AXI read address channel
	//
	initial	assert(!o_axi_arvalid);
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_wb_stall)))
	begin
		if (!$past(i_wb_stb))
			assert(!o_axi_arvalid);
		else
			assert(o_axi_arvalid == !$past(i_wb_we));
	end
	//
	generate
	if (C_AXI_DATA_WIDTH == DW)
	begin
		always @(posedge i_clk)
			if ((f_past_valid)&&($past(i_wb_stb))&&($past(!i_wb_we))
				&&(!$past(o_wb_stall)))
				assert(o_axi_araddr == $past({ i_wb_addr[AW-1:0], axi_bottom_addr }));

	end else if (C_AXI_DATA_WIDTH / DW == 2)
	begin

		always @(posedge i_clk)
			if ((f_past_valid)&&($past(i_wb_stb))&&($past(!i_wb_we))
				&&(!$past(o_wb_stall)))
				assert(o_axi_araddr == $past({ i_wb_addr[AW-1:1], axi_bottom_addr }));

	end else if (C_AXI_DATA_WIDTH / DW == 4)
	begin
		always @(posedge i_clk)
			if ((f_past_valid)&&($past(i_wb_stb))&&($past(!i_wb_we))
				&&(!$past(o_wb_stall)))
				assert(o_axi_araddr == $past({ i_wb_addr[AW-1:2], axi_bottom_addr }));

	end endgenerate

	//
	// AXI write response channel
	//
	reg	[(C_AXI_ID_WIDTH-1):0]	f_axi_wr_outstanding, f_axi_awr_outstanding;
	reg	[6:0]			f_axi_wr_delay;
	//input	[C_AXI_ID_WIDTH-1:0]	i_axi_bid,	// Response ID
	initial	f_axi_awr_outstanding = 0;
	initial	f_axi_wr_outstanding = 0;
	always @(posedge i_clk)
		if ((axi_awr_req)&&(!axi_wr_ack))
			f_axi_awr_outstanding <= f_axi_awr_outstanding + 1'b1;
		else if ((!axi_awr_req)&&(axi_wr_ack))
		begin
			`ASSUME(f_axi_awr_outstanding > 0);
			f_axi_awr_outstanding <= f_axi_awr_outstanding - 1'b1;
		end
	always @(posedge i_clk)
		if ((axi_wr_req)&&(!axi_wr_ack))
			f_axi_wr_outstanding <= f_axi_wr_outstanding + 1'b1;
		else if ((!axi_wr_req)&&(axi_wr_ack))
		begin
			`ASSUME(f_axi_wr_outstanding > 0);
			f_axi_wr_outstanding <= f_axi_wr_outstanding - 1'b1;
		end

	always @(posedge i_clk)
		assert(f_axi_wr_outstanding < {(C_AXI_ID_WIDTH){1'b1}});
	always @(posedge i_clk)
		`ASSUME(f_axi_wr_outstanding <= f_wb_outstanding);
	initial	f_axi_wr_delay = 0;
	always @(posedge i_clk)
		if (f_axi_wr_outstanding == 0)
			f_axi_wr_delay <= 0;
		else if (axi_wr_ack)
			f_axi_wr_delay <= 0;
		else
			f_axi_wr_delay <= f_axi_wr_delay + 1'b1;
	always @(posedge i_clk)
		`ASSUME(f_axi_wr_delay < F_MAXDELAY);
 
	// 
	// AXI read data channel signals   
	//
	reg	[(C_AXI_ID_WIDTH-1):0]	f_axi_rd_outstanding;
	reg	[6:0]			f_axi_rd_delay;
	initial	f_axi_rd_outstanding = 0;
	always @(posedge i_clk)
		if ((axi_ard_req)&&(!axi_rd_ack))
			f_axi_rd_outstanding <= f_axi_rd_outstanding + 1'b1;
		else if ((!axi_ard_req)&&(axi_rd_ack))
		begin
			`ASSUME(f_axi_rd_outstanding > 0);
			f_axi_rd_outstanding <= f_axi_rd_outstanding - 1'b1;
		end
	always @(posedge i_clk)
		assert(f_axi_rd_outstanding < {(C_AXI_ID_WIDTH){1'b1}});
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_outstanding <= f_wb_outstanding);
	//
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_outstanding + f_axi_wr_outstanding  <= f_wb_outstanding);
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_outstanding + f_axi_awr_outstanding <= f_wb_outstanding);
	//
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_outstanding + f_axi_wr_outstanding +2 > f_wb_outstanding);
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_outstanding + f_axi_awr_outstanding +2 > f_wb_outstanding);

	initial	f_axi_wr_delay = 0;
	always @(posedge i_clk)
		if (f_axi_rd_outstanding == 0)
			f_axi_rd_delay <= 0;
		else if ((i_axi_rvalid)&&(o_axi_rready))
			f_axi_rd_delay <= 0;
		else
			f_axi_rd_delay <= f_axi_rd_delay + 1'b1;
	always @(posedge i_clk)
		`ASSUME(f_axi_rd_delay < F_MAXDELAY);
 

	//input	[C_AXI_ID_WIDTH-1:0]	i_axi_rid,     // Response ID
	//input	[1:0]			i_axi_rresp,   // Read response
	//input				i_axi_rvalid,  // Read reponse valid
	//input	[C_AXI_DATA_WIDTH-1:0]	i_axi_rdata,    // Read data
	//input				i_axi_rlast,    // Read last
	//output	wire			o_axi_rready,  // Read Response ready

	// Now, let's look into that FIFO.  Without it, we know nothing about the ID's

	// Head and tail pointers

	// The head should only increment when something goes through
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_cyc))
				&&((!$past(i_wb_stb))||($past(o_wb_stall))))
			assert($stable(fifo_head));

	// Can't overrun the FIFO
	wire	[(LGFIFOLN-1):0]	f_fifo_tail_minus_one;
	assign	f_fifo_tail_minus_one = fifo_tail - 1'b1;
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_cyc))
				&&($past(fifo_head == f_fifo_tail_minus_one)))
			assert(fifo_head != fifo_tail);

	// Take care of the reorder buffer
	reg	[(FIFOLN-1):0]	f_rd_reorder_fifo_outstanding, f_wr_reorder_fifo_outstanding;
	reg			f_pre_ack;

	wire	[(LGFIFOLN-1):0]	f_fifo_used;
	assign	f_fifo_used = fifo_head - fifo_tail;

	initial	assert(fifo_tail == 0);
	initial assert(reorder_fifo_valid        == 0);
	initial assert(reorder_fifo_err          == 0);
	initial f_rd_reorder_fifo_outstanding = 0;
	initial f_wr_reorder_fifo_outstanding = 0;
	initial f_pre_ack = 1'b0;
	always @(posedge i_clk)
		if (!i_wb_cyc)
		begin
			f_wr_reorder_fifo_outstanding = 0;
			f_rd_reorder_fifo_outstanding = 0;
		end else begin
			// When issuing a write
			if (axi_awr_req)
			begin
				assert(f_wr_reorder_fifo_outstanding[o_axi_awid] == 1'b0);
				assert(f_rd_reorder_fifo_outstanding[o_axi_awid] == 1'b0);
				f_wr_reorder_fifo_outstanding[o_axi_awid] = 1'b1;
			end

			// When issuing a read
			if (axi_ard_req)
			begin
				assert(f_wr_reorder_fifo_outstanding[o_axi_arid] == 1'b0);
				assert(f_rd_reorder_fifo_outstanding[o_axi_arid] == 1'b0);
				f_rd_reorder_fifo_outstanding[o_axi_arid] = 1'b1;
			end

			// When a write is acknowledged
			if (axi_wr_ack)
			begin
				`ASSUME(f_wr_reorder_fifo_outstanding[i_axi_bid]);
				f_wr_reorder_fifo_outstanding[i_axi_bid] = 1'b0;
				`ASSUME((!STRICT_ORDER)||(!f_wr_reorder_fifo_outstanding[i_axi_bid-1'b1]));
			end

			// When a read is acknowledged
			if (axi_rd_ack)
			begin
				`ASSUME(f_rd_reorder_fifo_outstanding[i_axi_rid]);
				f_rd_reorder_fifo_outstanding[i_axi_rid] = 1'b0;
				`ASSUME((!STRICT_ORDER)||(!f_rd_reorder_fifo_outstanding[i_axi_rid-1'b1]));
			end

			// No responses will or can issue, unless there's a
			// transaction outstanding
			if (f_axi_awr_outstanding == 0)
				`ASSUME(!i_axi_bvalid);
			if (f_axi_wr_outstanding == 0)
				`ASSUME(!i_axi_bvalid);
			if (f_axi_rd_outstanding == 0)
				`ASSUME(!i_axi_rvalid);

			// 
			f_pre_ack <= (axi_rd_ack)||(axi_wr_ack);
			if (STRICT_ORDER)
			begin
				`ASSUME((!axi_rd_ack)||(!axi_wr_ack));

				assert((!$past(i_wb_cyc))||(o_wb_ack == $past(f_pre_ack)));
			end else begin
				// Not sure what to assert here.
			end
		end
 
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_wb_cyc)))
		begin
			`ASSUME(f_rd_reorder_fifo_outstanding == 0);
			`ASSUME(f_wr_reorder_fifo_outstanding == 0);
		end

	reg	[31:0]	f_rd_reorder_outstanding_count, f_wr_reorder_outstanding_count;

	initial	f_rd_reorder_outstanding_count = 0;
	initial	f_wr_reorder_outstanding_count = 0;
	always @(*)
	begin
		f_rd_reorder_outstanding_count = 0;
		for(k=0; k< FIFOLN; k=k+1)
			if (f_rd_reorder_fifo_outstanding[k])
				f_rd_reorder_outstanding_count = f_rd_reorder_outstanding_count +1;
		f_wr_reorder_outstanding_count = 0;
		for(k=0; k< FIFOLN; k=k+1)
			if (f_wr_reorder_fifo_outstanding[k])
				f_wr_reorder_outstanding_count = f_wr_reorder_outstanding_count +1;
	end

	always @(posedge i_clk)
		assert(f_axi_awr_outstanding == f_wr_reorder_outstanding_count);

	always @(posedge i_clk)
		assert(f_axi_rd_outstanding == f_rd_reorder_outstanding_count);

	// always @(posedge i_clk)
		// assert(f_wr_reorder_outstanding_count + reorder_valid + == reorder_count);

	/*
	*
	* wire	[(LGFIFOLN-1):0]	f_request_head;
	* always @(posedge i_clk)
	*	if (!i_wb_cyc)
	*		f_request_head = 0;
	*	else if ((i_wb_stb)&&(!o_wb_stall))
	*		f_request_head <= f_request_head + 1'b1;
	* 
	* always @(posedge i_clk)
	*	if ((i_wb_stb)&&(!o_wb_stall))
	*		f_request[f_request_head] <= { i_wb_addr };
	*
	*
	* Still haven't checked that the proper bits are selected from the return
	* value.
	*/

`endif
endmodule
