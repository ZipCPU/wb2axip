////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximrd2wbsp.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Bridge an AXI read channel pair to a single wishbone read
//		channel.
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
module	aximrd2wbsp #(
	parameter C_AXI_ID_WIDTH	= 6, // The AXI id width used for R&W
                                             // This is an int between 1-16
	parameter C_AXI_DATA_WIDTH	= 32,// Width of the AXI R&W data
	parameter C_AXI_ADDR_WIDTH	= 28,	// AXI Address width
	parameter AW			= 26,	// AXI Address width
	parameter LGFIFO                =  4
	// parameter	WBMODE		= "B4PIPELINE"
		// Could also be "BLOCK"
	) (
	input	wire			i_axi_clk,	// Bus clock
	input	wire			i_axi_reset_n,	// Bus reset

// AXI read address channel signals
	output	wire			o_axi_arready,	// Read address ready
	input	wire	[C_AXI_ID_WIDTH-1:0]	i_axi_arid,	// Read ID
	input	wire	[C_AXI_ADDR_WIDTH-1:0]	i_axi_araddr,	// Read address
	input	wire	[7:0]		i_axi_arlen,	// Read Burst Length
	input	wire	[2:0]		i_axi_arsize,	// Read Burst size
	input	wire	[1:0]		i_axi_arburst,	// Read Burst type
	input	wire	[0:0]		i_axi_arlock,	// Read lock type
	input	wire	[3:0]		i_axi_arcache,	// Read Cache type
	input	wire	[2:0]		i_axi_arprot,	// Read Protection type
	input	wire	[3:0]		i_axi_arqos,	// Read Protection type
	input	wire			i_axi_arvalid,	// Read address valid
  
// AXI read data channel signals   
	output	wire [C_AXI_ID_WIDTH-1:0] o_axi_rid,     // Response ID
	output	wire [1:0]		o_axi_rresp,   // Read response
	output	reg			o_axi_rvalid,  // Read reponse valid
	output	wire [C_AXI_DATA_WIDTH-1:0] o_axi_rdata,    // Read data
	output	wire 			o_axi_rlast,    // Read last
	input	wire			i_axi_rready,  // Read Response ready

	// We'll share the clock and the reset
	output	reg				o_wb_cyc,
	output	reg				o_wb_stb,
	output	wire [(AW-1):0]	o_wb_addr,
	input	wire				i_wb_ack,
	input	wire				i_wb_stall,
	input	[(C_AXI_DATA_WIDTH-1):0]	i_wb_data,
	input	wire				i_wb_err
	);

	localparam	DW = C_AXI_DATA_WIDTH;

	wire	w_reset;
	assign	w_reset = (i_axi_reset_n == 1'b0);


	reg	[(C_AXI_ID_WIDTH+AW+1)-1:0]	afifo	[0:((1<<(LGFIFO))-1)];
	reg	[(DW+1)-1:0]			dfifo	[0:((1<<(LGFIFO))-1)];
	reg	[(C_AXI_ID_WIDTH+AW+1)-1:0]	fifo_at_neck, afifo_at_tail;
	reg	[(DW+1)-1:0]			dfifo_at_tail;

	// We're going to need to keep track of transaction bursts in progress,
	// since the wishbone doesn't.  For this, we'll use a FIFO, but with
	// multiple pointers:
	//
	//	fifo_head	- pointer to where to write the next incoming
	//				bus request .. adjusted when
	//				(o_axi_arready)&&(i_axi_arvalid)
	//	fifo_neck	- pointer to where to read from the FIFO in
	//				order to issue another request.  Used
	//				when (o_wb_stb)&&(!i_wb_stall)
	//	fifo_torso	- pointer to where to write a wishbone
	//				transaction upon return.
	//				when (i_ack)
	//	fifo_tail	- pointer to where the last transaction is to
	//				be retired when
	//					(i_axi_rvalid)&&(i_axi_rready)
	//
	// All of these are to be set to zero upon a reset signal.
	//
	reg	[LGFIFO-1:0]	fifo_head, fifo_neck, fifo_torso, fifo_tail;

	// Since we need to insure that these pointers wrap properly at
	// LGFIFO bits, and since it is confusing to do that within IF 
	// statements, 
	wire	[LGFIFO-1:0]	next_head, next_neck, next_torso, next_tail,
				almost_head;
	wire		fifo_full;
	assign	next_head  = fifo_head  + 1;
	assign	next_neck  = fifo_neck  + 1;
	assign	next_torso = fifo_torso + 1;
	assign	next_tail  = fifo_tail  + 1;
	assign	almost_head = fifo_head  + 1;

	assign fifo_full = (almost_head == fifo_tail);

	reg	wr_last, filling_fifo, incr;
	reg	[7:0]			len;
	reg	[(AW-1):0]		wr_fifo_addr;
	reg	[(C_AXI_ID_WIDTH-1):0]	wr_fifo_id;

	//
	//
	//
	//
	// Here's our plan: Any time READY & VALID are both true, initiate a
	// transfer (unless one is ongoing).  Hold READY false while initiating
	// any burst transaction.  Keep the request RID and burst length stuffs
	// into a FIFO.
	// queue are both valid, issue the wishbone read request.  Once a read
	// request returns, retire the value in the FIFO queue.
	//
	// The FIFO queue *must* include:
	//
	//	RQ, ADDR, LAST
	//
	initial len          = 0;
	initial filling_fifo = 0;
	initial fifo_head    = 0;
	always @(posedge i_axi_clk)
	begin
		wr_last <= 1'b0;

		if (filling_fifo)
		begin
			if (!fifo_full)
			begin
				len <= len - 1;
				if (len == 1)
					filling_fifo <= 1'b0;
				fifo_head <= next_head;
				wr_fifo_addr <= wr_fifo_addr
					+ {{(AW-1){1'b0}}, incr};
				wr_last <= (len == 1);
			end
		end else begin
			wr_fifo_addr <= i_axi_araddr[(C_AXI_ADDR_WIDTH-1):(C_AXI_ADDR_WIDTH-AW)];
			wr_fifo_id <= i_axi_arid;
			incr <= i_axi_arburst[0];
			if ((o_axi_arready)&&(i_axi_arvalid))
			begin
				fifo_head <= next_head;
				len <= i_axi_arlen;
				filling_fifo <= (i_axi_arlen != 0);
				wr_last <= 1'b1;
			end
		end

		if (w_reset)
		begin
			len <= 0;
			filling_fifo <= 1'b0;
			fifo_head <= 0;
		end
	end

	always @(posedge i_axi_clk)
		afifo[fifo_head] <= { wr_fifo_id, wr_last, wr_fifo_addr };

	reg	err_state;	
	initial o_wb_cyc   = 1'b0;
	initial o_wb_stb   = 1'b0;
	initial fifo_neck  = 0;
	initial fifo_torso = 0;
	initial err_state  = 0;
	always @(posedge i_axi_clk)
	begin
		if (w_reset)
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;

			fifo_neck  <= 0;
			fifo_torso <= 0;

			err_state <= 0;
		end else if (o_wb_stb)
		begin
			if (i_wb_err)
			begin
				o_wb_stb <= 1'b0;
				err_state <= 1'b1;
			end else if (!i_wb_stall)
			begin
				o_wb_stb <= (fifo_head != next_neck);
						// && (WBMODE != "B3SINGLE");
				// o_wb_cyc <= (WBMODE != "B3SINGLE");
			end

			if (!i_wb_stall)
				fifo_neck <= next_neck;
			if (i_wb_ack)
				fifo_torso <= next_torso;
		end else if (err_state)
		begin
			fifo_torso <= next_torso;
			if (fifo_neck == next_torso)
				err_state <= 1'b0;
			o_wb_cyc <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if (i_wb_ack)
				fifo_torso <= next_torso;
			if (fifo_neck == next_torso)
				o_wb_cyc <= 1'b0;
		end else if (fifo_neck != fifo_head)
		begin
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
		end
	end

	always @(posedge i_axi_clk)
		fifo_at_neck <= afifo[fifo_neck];
	assign	o_wb_addr = fifo_at_neck[(AW-1):0];

	always @(posedge i_axi_clk)
		dfifo[fifo_torso] <= { (err_state)||(i_wb_err), i_wb_data };


	always @(posedge i_axi_clk)
		if (w_reset)
			fifo_tail <= 0;
		else if ((o_axi_rvalid)&&(i_axi_rready))
			fifo_tail <= next_tail;

	always @(posedge i_axi_clk)
	begin
		afifo_at_tail <= afifo[fifo_tail];
		dfifo_at_tail <= dfifo[fifo_tail];
		// o_axi_rdata <= dfifo[fifo_tail];
		// o_axi_rlast <= afifo[fifo_tail];
		// o_axi_rid   <= afifo[fifo_tail];
	end
	assign	o_axi_rlast = afifo_at_tail[AW];
	assign	o_axi_rid   = afifo_at_tail[(C_AXI_ID_WIDTH+AW):(AW+1)];
	assign	o_axi_rresp = { (2){dfifo_at_tail[DW]} };
	assign	o_axi_rdata = dfifo_at_tail[(DW-1):0];

	initial	o_axi_rvalid = 1'b0;
	always @(posedge i_axi_clk)
		if (w_reset)
			o_axi_rvalid <= 0;
		else
			o_axi_rvalid <= (fifo_tail != fifo_neck + 1);

	assign o_axi_arready = (!fifo_full)&&(!filling_fifo);

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[(C_AXI_ID_WIDTH+1)+(C_AXI_ADDR_WIDTH-AW)
		+3+1+1+4+3+4-1:0]	unused;
	assign	unused = { i_axi_arsize, i_axi_arburst[1],
			i_axi_arlock, i_axi_arcache, i_axi_arprot,
			i_axi_arqos,
			fifo_at_neck[(C_AXI_ID_WIDTH+AW+1)-1:AW],
			i_axi_araddr[(C_AXI_ADDR_WIDTH-AW-1):0] };
	// verilator lint_on  UNUSED
endmodule
