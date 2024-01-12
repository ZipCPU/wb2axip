////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axivfifo.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A virtual FIFO, using an AXI based memory on the back end.  Data
//		written via the AXI stream interface is written to an external
//	memory once enough is available to fill a burst.  It's then copied from
//	this external memory to a FIFO from which it can drive an outgoing
//	stream.
//
// Registers:
//	This core is simple--providing no control interface nor registers
//	whereby it may be controlled.  To place it in a particular region of
//	SDRAM, limit the address width and fill the rest of the address with
//	the region you want.  Note: THIS CORE DEPENDS UPON ALIGNED MEMORY
//	ACCESSES.  Hence, it must be aligned to the memory to keep these
//	accesses aligned.
//
// Performance goals:
//	100% throughput
//	Stay off the bus until you can drive it hard
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
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
`default_nettype	none
//
// `define			AXI3
// }}}
module	axivfifo #(
		// {{{
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		//
		// This core requires that the stream data width be identical
		// to the bus data width.  Use an upstream core if you need to
		// pack a smaller width into your bus's width, or a downstream
		// core if you need to unpack it.
		localparam	C_AXIS_DATA_WIDTH = C_AXI_DATA_WIDTH,
		//
		// LGMAXBURST determines the size of the maximum AXI burst.
		// In AXI4, the maximum burst size is 256 beats the log_2()
		// of which is 8.  In AXI3, it's a 16 beat burst of which the
		// log_2() is 4.  Smaller numbers are also permissible here,
		// although not verified.  I expect problems if LGMAXBURST is
		// ever set to zero (no bursting).  An upgrade should fix that.
		// Lower LGMAXBURST values will decrease the latency in this
		// core while possibly causing throughput to be decreased
		// (in the rest of the system--this core can handle 100%
		// throughput either way.)
		//
		// Beware of the AXI requirement that bursts cannot cross
		// 4kB boundaries.  If your bus is larger than 128 bits wide,
		// you'll need to lower this maximum burst size to meet that
		// requirement.
`ifdef	AXI3
		parameter	LGMAXBURST=4,	// 16 beats max
`else
		parameter	LGMAXBURST=8,	// 256 beats
`endif
		//
		// LGFIFO: This is the (log-based-2) size of the internal FIFO.
		// Hence if LGFIFO=8, the internal FIFO will have 256 elements
		// (words) in it.  High throughput transfers are accomplished
		// by first storing data into a FIFO, then once a full burst
		// size is available bursting that data over the bus.  In
		// order to be able to keep receiving data while bursting it
		// out, the FIFO size must be at least twice the size of the
		// maximum burst size--that is LGFIFO must be at least one more
		// than LGMAXBURST.  Larger sizes are possible as well.
		parameter	LGFIFO = LGMAXBURST+1,	// 512 element FIFO
		//
		// AXI uses ID's to transfer information.  This core rather
		// ignores them.  Instead, it uses a constant ID for all
		// transfers.  The following two parameters control that ID.
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_READ_ID = 0,
		parameter	[C_AXI_ID_WIDTH-1:0]	AXI_WRITE_ID = 0,
		//
		localparam	ADDRLSB= $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		// The AXI4-stream interface
		// {{{
		// This core does not support TLAST, TKEEP, or TSTRB.  If you
		// want to support these extra values, expand the width of
		// TDATA, and unpack them on the output of the FIFO.
		//
		// The incoming stream
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire	[C_AXIS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		//
		// The outgoing stream
		output	wire				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]	M_AXIS_TDATA,
		// }}}
		//
		// The AXI Master (DMA) interface
		// {{{
		// First to write data to the (external) AXI buffer
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
`ifdef	AXI3
		output	wire	[3:0]			M_AXI_AWLEN,
`else
		output	wire	[7:0]			M_AXI_AWLEN,
`endif
		output	wire	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
`ifdef	AXI3
		output	wire	[1:0]			M_AXI_AWLOCK,
`else
		output	wire				M_AXI_AWLOCK,
`endif
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		//
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
`ifdef	AXI3
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_WID,
`endif
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		//
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		//
		// Then the read interface to read the data back
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
`ifdef	AXI3
		output	wire	[3:0]			M_AXI_ARLEN,
`else
		output	wire	[7:0]			M_AXI_ARLEN,
`endif
		output	wire	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
`ifdef	AXI3
		output	wire	[1:0]			M_AXI_ARLOCK,
`else
		output	wire				M_AXI_ARLOCK,
`endif
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP,
		// }}}
		//
		// {{{
		// Request a soft-reset: reset the FIFO without resetting th bus
		input	wire				i_reset,
		// o_err is a hard error.  If ever true, the core will come
		// to a hard stop.
		output	reg				o_err,
		// o_overflow is an indication of data changing before it is
		// accepted.
		output	reg				o_overflow,
		// o_mm2s_full is a reference to the last FIFO in our
		// processing pipeline.  It's true if a burst of (1<<LGMAXBURST)
		// words of (1<<ADDRLSB) bytes may be read from the downstream
		// FIFO without waiting on the external memory.
		output	reg				o_mm2s_full,
		// o_empty is true if nothing is in the core.
		output	reg				o_empty,
		// o_fill counts the number of items in the core.  Just because
		// the number of items is non-zero, however, doesn't mean you
		// can read them out.  In general, you will need to write at
		// least a full (1<<LGMAXBURST) words to the core, those will
		// need to be written to memory, read from memory, and then
		// used to fill the downstream FIFO before you can read.  This
		// number is just available for your informational use.
		output reg [C_AXI_ADDR_WIDTH-ADDRLSB:0]	o_fill
		// }}}
		// }}}
	);

	// Register and signal definitions
	// {{{
	// The number of beats in this maximum burst size is automatically
	// determined from LGMAXBURST, and so its forced to be a power of
	// two this way.
	localparam	MAXBURST=(1<<LGMAXBURST);
	localparam	BURSTAW = C_AXI_ADDR_WIDTH-LGMAXBURST-ADDRLSB;

	reg				soft_reset, vfifo_empty, vfifo_full;
	wire				reset_fifo;
	reg	[C_AXI_ADDR_WIDTH-ADDRLSB:0]	vfifo_fill;
	reg	[BURSTAW:0]		mem_data_available_w,
					writes_outstanding;
	reg	[BURSTAW:0]		mem_space_available_w,
					reads_outstanding;
	reg				s_last_stalled;
	reg	[C_AXI_DATA_WIDTH-1:0]	s_last_tdata;
	wire				read_from_fifo, ififo_full, ififo_empty;
	wire	[C_AXI_DATA_WIDTH-1:0]	ififo_data;
	wire	[LGFIFO:0]		ififo_fill;

	reg				start_write, phantom_write,
					axi_awvalid, axi_wvalid, axi_wlast,
					writes_idle;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	reg	[LGMAXBURST:0]		writes_pending;

	reg				start_read, phantom_read, reads_idle,
					axi_arvalid;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_araddr;

	reg				skd_valid;
	reg	[C_AXI_DATA_WIDTH-1:0]	skd_data;

	reg	[LGFIFO:0]	ofifo_space_available;
	wire			write_to_fifo, ofifo_empty, ofifo_full;
	wire	[LGFIFO:0]	ofifo_fill;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Global FIFO signal handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// A soft reset
	// {{{
	// This is how we reset the FIFO without resetting the rest of the AXI
	// bus.  On a reset request, we raise the soft_reset flag and reset all
	// of our internal FIFOs.  We also stop issuing bus commands.  Once all
	// outstanding bus commands come to a halt, then we release from reset
	// and start operating as a FIFO.
	initial	soft_reset = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		soft_reset <= 0;
	else if (i_reset)
		soft_reset <= 1;
	else if (writes_idle && reads_idle)
		soft_reset <= 0;

	assign	reset_fifo = soft_reset || !S_AXI_ARESETN;
	// }}}

	//
	// Calculating the fill of the virtual FIFO, and the associated
	// full/empty flags that go with it
	// {{{
	initial	vfifo_fill  = 0;
	initial	vfifo_empty = 1;
	initial	vfifo_full  = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset)
	begin
		vfifo_fill  <= 0;
		vfifo_empty <= 1;
		vfifo_full  <= 0;
	end else case({ S_AXIS_TVALID && S_AXIS_TREADY,
			M_AXIS_TVALID && M_AXIS_TREADY })
	2'b10:	begin
		vfifo_fill  <= vfifo_fill + 1;
		vfifo_empty <= 0;
		vfifo_full  <= (&vfifo_fill[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]);
		end
	2'b01:	begin
		vfifo_fill <= vfifo_fill - 1;
		vfifo_full <= 0;
		vfifo_empty<= (vfifo_fill <= 1);
		end
	default: begin end
	endcase

	always @(*)
		o_fill = vfifo_fill;

	always @(*)
		o_empty = vfifo_empty;
	// }}}

	// Determining when the write half is idle
	// {{{
	// This is required to know when to come out of soft reset.
	//
	// The first step is to count the number of bursts that remain
	// outstanding
	initial	writes_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		writes_outstanding <= 0;
	else case({ phantom_write,M_AXI_BVALID && M_AXI_BREADY})
	2'b01: writes_outstanding <= writes_outstanding - 1;
	2'b10: writes_outstanding <= writes_outstanding + 1;
	default: begin end
	endcase

	// The second step is to use this counter to determine if we are idle.
	// If WVALID is ever high, or start_write goes high, then we are
	// obviously not idle.  Otherwise, we become idle when the number of
	// writes outstanding transitions to (or equals) zero.
	initial	writes_idle = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		writes_idle <= 1;
	else if (start_write || M_AXI_WVALID)
		writes_idle <= 0;
	else
		writes_idle <= (writes_outstanding
				== ((M_AXI_BVALID && M_AXI_BREADY) ? 1:0));
	// }}}

	// Count how much space is used in the memory device
	// {{{
	// Well, obviously, we can't fill our memory device or we have problems.
	// To make sure we don't overflow, we count memory usage here.  We'll
	// count memory usage in units of bursts of (1<<LGMAXBURST) words of
	// (1<<ADDRLSB) bytes each.  So ... here we count the amount of device
	// memory that hasn't (yet) been committed.  This is different from the
	// memory used (which we don't calculate), or the memory which may yet
	// be read--which we'll calculate in a moment.
	initial	mem_space_available_w = (1<<BURSTAW);
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset)
		mem_space_available_w <= (1<<BURSTAW);
	else case({ phantom_write,M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST })
	2'b01: mem_space_available_w <= mem_space_available_w + 1;
	2'b10: mem_space_available_w <= mem_space_available_w - 1;
	default: begin end
	endcase
	// }}}

	// Determining when the read half is idle
	// {{{
	// Count the number of read bursts that we've committed to.  This
	// includes bursts that have ARVALID but haven't been accepted, as well
	// as any the downstream device will yet return an RLAST for.
	initial	reads_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		reads_outstanding <= 0;
	else case({ phantom_read,M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST})
	2'b01: reads_outstanding <= reads_outstanding - 1;
	2'b10: reads_outstanding <= reads_outstanding + 1;
	default: begin end
	endcase

	// Now, using the reads_outstanding counter, we can check whether or not
	// we are idle (and can exit a reset) of if instead there are more
	// bursts outstanding to wait for.
	//
	// By registering this counter, we can keep the soft_reset release
	// simpler.  At least this way, it doesn't need to check two counters
	// for zero.
	initial	reads_idle = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		reads_idle <= 1;
	else if (start_read || M_AXI_ARVALID)
		reads_idle <= 0;
	else
		reads_idle <= (reads_outstanding
		== ((M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST) ? 1:0));
	// }}}

	// Count how much data is in the memory device that we can read out
	// {{{
	// In AXI, after you issue a write, you can't depend upon that data
	// being present on the device and available for a read until the
	// associated BVALID is returned.  Therefore we don't count any memory
	// as available to be read until BVALID comes back.  Once a read
	// command is issued, the memory is again no longer available to be
	// read.  Note also that we are counting bursts here.  A second
	// conversion below converts this count to bytes.
	initial	mem_data_available_w = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset)
		mem_data_available_w <= 0;
	else case({ M_AXI_BVALID, phantom_read })
	2'b10: mem_data_available_w <= mem_data_available_w + 1;
	2'b01: mem_data_available_w <= mem_data_available_w - 1;
	default: begin end
	endcase
	// }}}

	//
	// Error detection
	// {{{
	initial	o_err = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_err <= 1'b0;
	else begin
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			o_err <= 1'b1;
		if (M_AXI_RVALID && M_AXI_RRESP[1])
			o_err <= 1'b1;
	end
	// }}}

	//
	// Incoming stream overflow detection
	// {{{
	// The overflow flag is set if ever an incoming value violates the
	// stream protocol and changes while stalled.  Internally, however,
	// the overflow flag is ignored.  It's provided for your information.
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		s_last_stalled <= 0;
	else
		s_last_stalled <= S_AXIS_TVALID && !S_AXIS_TREADY;

	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID)
		s_last_tdata <= S_AXIS_TDATA;

	initial	o_overflow = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset)
		o_overflow <= 0;
	else if (s_last_stalled)
	begin
		if (!S_AXIS_TVALID)
			o_overflow <= 1;
		if (S_AXIS_TDATA != s_last_tdata)
			o_overflow <= 1;
	end
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming FIFO
	// {{{
	// Incoming data stream info the FIFO
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	S_AXIS_TREADY = !reset_fifo && !ififo_full && !vfifo_full;
	assign	read_from_fifo= (!skd_valid || (M_AXI_WVALID && M_AXI_WREADY));

	sfifo #(.BW(C_AXIS_DATA_WIDTH), .LGFLEN(LGFIFO))
	ififo(S_AXI_ACLK, reset_fifo,
		S_AXIS_TVALID && S_AXIS_TREADY,
			S_AXIS_TDATA, ififo_full, ififo_fill,
		read_from_fifo, ififo_data, ififo_empty);

	//
	// We need a quick 1-element buffer here in order to keep the soft
	// reset, which resets the FIFO pointer, from adjusting any FIFO data.
	// {{{
	// Here's the rule: we need to fill the buffer before it ever gets
	// used.  Then, once used, it should be able to maintain 100%
	// throughput.
	initial	skd_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (reset_fifo)
		skd_valid <= 0;
	else if (!ififo_empty)
		skd_valid <= 1;
	else if (M_AXI_WVALID && M_AXI_WREADY)
		skd_valid <= 0;

	always @(posedge S_AXI_ACLK)
	if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (!skd_valid || M_AXI_WREADY)
			skd_data <= ififo_data;
	end
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// AXI write processing
	// {{{
	// Write data from our FIFO onto the bus
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// start_write: determining when to issue a write burst
	// {{{
	always @(*)
	begin
		start_write = 0;

		if (ififo_fill >= (1<<LGMAXBURST))
			start_write = 1;
		if (vfifo_full || soft_reset || phantom_write)
			start_write = 0;
		if (mem_space_available_w == 0)
			start_write = 0;

		if (M_AXI_WVALID && (!M_AXI_WREADY || !M_AXI_WLAST))
			start_write = 0;
		if (M_AXI_AWVALID && !M_AXI_AWREADY)
			start_write = 0;
		if (o_err)
			start_write = 0;
	end
	// }}}

	// Register the start write signal into AWVALID and phantom write
	// {{{
	// phantom_write contains the start signal, but immediately clears
	// on the next clock cycle.  This allows us some time to calculate
	// the data for the next burst which and if AWVALID remains high and
	// not yet accepted.
	initial	phantom_write = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		phantom_write <= 0;
	else
		phantom_write <= start_write;

	// Set AWVALID to start_write if every the channel isn't stalled.
	// Incidentally, start_write is guaranteed to be zero if the channel
	// is stalled, since that signal is used by other things as well.
	initial	axi_awvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_awvalid <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		axi_awvalid <= start_write;
	// }}}

	// Write address
	// {{{
	// We insist on alignment.  On every accepted burst, we step forward by
	// one burst length.  On reset, we reset the address at our first
	// opportunity.
	initial	axi_awaddr = 0;
	always @(posedge S_AXI_ACLK)
	begin
		if (M_AXI_AWVALID && M_AXI_AWREADY)
			axi_awaddr[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB]
			<= axi_awaddr[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB] +1;

		if ((!M_AXI_AWVALID || M_AXI_AWREADY) && soft_reset)
			axi_awaddr <= 0;

		if (!S_AXI_ARESETN)
			axi_awaddr <= 0;

		axi_awaddr[LGMAXBURST+ADDRLSB-1:0] <= 0;
	end
	// }}}

	// Write data channel valid
	// {{{
	initial	axi_wvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_wvalid <= 0;
	else if (start_write)
		axi_wvalid <= 1;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wvalid <= M_AXI_WVALID && !M_AXI_WLAST;
	// }}}

	// WLAST generation
	// {{{
	// On the beginning of any burst, start a counter of the number of items
	// in it.  Once the counter gets to 1, set WLAST.
	initial	writes_pending = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		writes_pending <= 0;
	else if (start_write)
		writes_pending <= MAXBURST;
	else if (M_AXI_WVALID && M_AXI_WREADY)
		writes_pending <= writes_pending -1;

	always @(posedge S_AXI_ACLK)
	if (start_write)
		axi_wlast <= (LGMAXBURST == 0);
	else if (!M_AXI_WVALID || M_AXI_WREADY)
		axi_wlast <= (writes_pending == 1 + (M_AXI_WVALID ? 1:0));
	// }}}

	// Bus assignments based upon the above
	// {{{
	assign	M_AXI_AWVALID = axi_awvalid;
	assign	M_AXI_AWID    = AXI_WRITE_ID;
	assign	M_AXI_AWADDR  = axi_awaddr;
	assign	M_AXI_AWLEN   = MAXBURST-1;
	assign	M_AXI_AWSIZE  = ADDRLSB[2:0];
	assign	M_AXI_AWBURST = 2'b01;
	assign	M_AXI_AWLOCK  = 0;
	assign	M_AXI_AWCACHE = 0;
	assign	M_AXI_AWPROT  = 0;
	assign	M_AXI_AWQOS   = 0;

	assign	M_AXI_WVALID = axi_wvalid;
	assign	M_AXI_WDATA  = skd_data;
`ifdef	AXI3
	assign	M_AXI_WID    = AXI_WRITE_ID;
`endif
	assign	M_AXI_WLAST  = axi_wlast;
	assign	M_AXI_WSTRB  = -1;

	assign	M_AXI_BREADY = 1;
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// AXI read processing
	// {{{
	// Read data into our FIFO
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// How much FIFO space is available?
	// {{{
	// One we issue a read command, the FIFO space isn't available any more.
	// That way we can determine when a second read can be issued--even
	// before the first has returned--while also guaranteeing that there's
	// always room in the outgoing FIFO for anything that might return.
	// Remember: NEVER generate backpressure in a bus master
	initial	ofifo_space_available = (1<<LGFIFO);
	always @(posedge S_AXI_ACLK)
	if (reset_fifo)
		ofifo_space_available <= (1<<LGFIFO);
	else case({phantom_read, M_AXIS_TVALID && M_AXIS_TREADY})
	2'b10:	ofifo_space_available <= ofifo_space_available - MAXBURST;
	2'b01:	ofifo_space_available <= ofifo_space_available + 1;
	2'b11:	ofifo_space_available <= ofifo_space_available - MAXBURST + 1;
	default: begin end
	endcase
	// }}}

	// Determine when to start a next read-from-memory-to-FIFO burst
	// {{{
	always @(*)
	begin
		start_read = 1;

		// We can't read yet if we don't have space available.
		// Note the comparison is carefully chosen to make certain
		// it doesn't use all ofifo_space_available bits, but rather
		// only the number of bits between LGFIFO and
		// LGMAXBURST--nominally a single bit.
		if (ofifo_space_available < MAXBURST)	// FIFO space ?
			start_read = 0;

		// If there's no memory available for us to read from, then
		// we can't start a read yet.
		if (!M_AXI_BVALID && mem_data_available_w == 0)
			start_read = 0;

		// Don't start anything while waiting on a reset.  Likewise,
		// insist on a minimum one clock between read burst issuances.
		if (soft_reset || phantom_read)
			start_read = 0;

		// We can't start a read request if the AR* channel is stalled
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			start_read = 0;

		// Following a bus error, we come to a complete halt.  Such a
		// bus error is an indication that something *SERIOUSLY* went
		// wrong--perhaps we aren't accessing the memory we are supposed
		// to.  To prevent damage to external devices, we disable
		// ourselves entirely.  There is no fall back.  We only
		// restart on a full bus restart.
		if (o_err)
			start_read = 0;
	end
	// }}}

	// Set phantom_read and ARVALID
	// {{{
	initial	phantom_read = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		phantom_read <= 0;
	else
		phantom_read <= start_read;

	initial	axi_arvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_arvalid <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		axi_arvalid <= start_read;
	// }}}

	// Calculate the next ARADDR
	// {{{
	initial	axi_araddr = 0;
	always @(posedge S_AXI_ACLK)
	begin
		if (M_AXI_ARVALID && M_AXI_ARREADY)
			axi_araddr[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB]
			<= axi_araddr[C_AXI_ADDR_WIDTH-1:LGMAXBURST+ADDRLSB]+ 1;

		if ((!M_AXI_ARVALID || M_AXI_ARREADY) && soft_reset)
			axi_araddr <= 0;

		if (!S_AXI_ARESETN)
			axi_araddr <= 0;

		axi_araddr[LGMAXBURST+ADDRLSB-1:0] <= 0;
	end
	// }}}

	// Assign values to our bus wires
	// {{{
	assign	M_AXI_ARVALID = axi_arvalid;
	assign	M_AXI_ARID    = AXI_READ_ID;
	assign	M_AXI_ARADDR  = axi_araddr;
	assign	M_AXI_ARLEN   = MAXBURST-1;
	assign	M_AXI_ARSIZE  = ADDRLSB[2:0];
	assign	M_AXI_ARBURST = 2'b01;
	assign	M_AXI_ARLOCK  = 0;
	assign	M_AXI_ARCACHE = 0;
	assign	M_AXI_ARPROT  = 0;
	assign	M_AXI_ARQOS   = 0;

	assign	M_AXI_RREADY = 1;
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing AXI stream processing
	// {{{
	// Send data out from the MM2S FIFO
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We basically just stuff the data read from memory back into our
	// outgoing FIFO here.  The logic is quite straightforward.
	assign	write_to_fifo = M_AXI_RVALID && M_AXI_RREADY;
	assign	M_AXIS_TVALID = !ofifo_empty;

	sfifo #(.BW(C_AXIS_DATA_WIDTH), .LGFLEN(LGFIFO))
	ofifo(S_AXI_ACLK, reset_fifo,
		write_to_fifo,
			M_AXI_RDATA, ofifo_full, ofifo_fill,
		M_AXIS_TVALID && M_AXIS_TREADY, M_AXIS_TDATA, ofifo_empty);

	always @(*)
		o_mm2s_full = |ofifo_fill[LGFIFO:LGMAXBURST];
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_BID, M_AXI_RID,
			M_AXI_BRESP[0], M_AXI_RRESP[0],
			ififo_empty, ofifo_full, ofifo_fill
			// fifo_full, fifo_fill, fifo_empty,
			};

	// Verilator lint_on UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
//
// The following are a subset of the formal properties used to verify this
// core.  The full set of formal properties, together with the formal
// property set itself, are available for purchase.
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// FAXI_DEPTH controls the width of the counters in the bus property
	// interface file.  In order to support bursts of length 8 (or more),
	// there's a minimum of 9.  Otherwise, we'll just set this to the width
	// of the AXI address bus.
	localparam	FAXI_DEPTH = (C_AXI_ADDR_WIDTH > 8)
					? (C_AXI_ADDR_WIDTH+1) : 9;

	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	//
	// Wires necessary for interacting with the formal property file
	// {{{
	// ...
	// }}}

	// Other registers to keep simplify keeping track of our progress
	// {{{
	reg	[C_AXI_ADDR_WIDTH-1:0]	faxi_rd_cknext, faxi_wr_cknext,
					f_read_beat_addr, f_write_beat_addr,
					faxi_read_beat_addr;
	reg	[C_AXI_ADDR_WIDTH-1:0]	f_read_ckbeat_addr;
	reg	[FAXI_DEPTH-1:0]	f_rd_bursts_after_check;

	reg	[C_AXI_ADDR_WIDTH:0]	f_vfill;
	reg	[C_AXI_ADDR_WIDTH:0]	f_space_available,
					f_data_available;

	reg	[C_AXI_ADDR_WIDTH-1:0]	f_read_checksum;
	reg	[C_AXI_ADDR_WIDTH:0]	mem_space_available, mem_data_available;
	// }}}


	////////////////////////////////////////////////////////////////////////
	//
	// The main AXI data interface bus property check
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The number of beats in the maximum burst size is
	// automatically determined from LGMAXBURST, and so its
	// forced to be a power of two this way.
	localparam	MAXBURST=(1<<LGMAXBURST);

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_MAXBURST(MAXBURST-1),
		.OPT_NARROW_BURST(1'b0),
		.OPT_ASYNC_RESET(1'b0),	// We don't use asynchronous resets
		.OPT_EXCLUSIVE(1'b0),	// We don't use the LOCK signal
		.F_OPT_ASSUME_RESET(1'b1), // We aren't generating the reset
		.F_OPT_NO_RESET(1'b1),
		.F_LGDEPTH(FAXI_DEPTH)	// Width of the counters
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// Write signals
		// {{{
		.i_axi_awvalid(M_AXI_AWVALID),
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awid(   M_AXI_AWID),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awlen(  M_AXI_AWLEN),
		.i_axi_awsize( M_AXI_AWSIZE),
		.i_axi_awburst(M_AXI_AWBURST),
		.i_axi_awlock( M_AXI_AWLOCK),
		.i_axi_awcache(M_AXI_AWCACHE),
		.i_axi_awprot( M_AXI_AWPROT),
		.i_axi_awqos(  M_AXI_AWQOS),
		//
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		//
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(   M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		// }}}
		// Read signals
		// {{{
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_arid(   M_AXI_ARID),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arlen(  M_AXI_ARLEN),
		.i_axi_arsize( M_AXI_ARSIZE),
		.i_axi_arburst(M_AXI_ARBURST),
		.i_axi_arlock( M_AXI_ARLOCK),
		.i_axi_arcache(M_AXI_ARCACHE),
		.i_axi_arprot( M_AXI_ARPROT),
		.i_axi_arqos(  M_AXI_ARQOS),
		//
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rid(   M_AXI_RID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rlast( M_AXI_RLAST),
		.i_axi_rresp( M_AXI_RRESP),
		// }}}
		// Induction signals
		// {{{
		// ...
		// }}}
		// }}}
	);

	// Some quick sanity checks
	// {{{
	always @(*)
	begin
		//
		// ...
		//
	end
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Write sanity checking
	// {{{
	always @(*)
		mem_space_available = { mem_space_available_w,
			{(LGMAXBURST+ADDRLSB){1'b0} } };

	// Let's calculate the address of each write beat
	// {{{
	initial	f_write_beat_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_write_beat_addr <= 0;
	else if ((!M_AXI_WVALID || (M_AXI_WREADY && M_AXI_WLAST)) && soft_reset)
		f_write_beat_addr <= 0;
	else if (M_AXI_WVALID && M_AXI_WREADY)
		f_write_beat_addr <= f_write_beat_addr + (1<<ADDRLSB);
	// }}}

	//
	// ...
	//

	// Verify during any write burst that all the burst parameters are
	// correct
	// {{{
	// ...
	// }}}

	always @(*)
	if (M_AXI_AWVALID)
	begin
		assert(writes_pending == (1<<LGMAXBURST));
		// ...
	end else
		// ...

	always @(*)
		assert(M_AXI_WVALID == (writes_pending != 0));

	//
	// ...
	//

	// Check the writes-idle signal
	// {{{
	// ...
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Read sanity checking
	// {{{

	always @(*)
		mem_data_available = { mem_data_available_w,
			{(LGMAXBURST+ADDRLSB){1'b0} } };
	//
	// ...
	// Check the reads-idle signal
	// {{{
	// ...
	// }}}

	// Regenerate the read beat address
	// {{{
	// This works because we are using a single AXI ID for all of our reads.
	// Therefore we can guarantee that reads will come back in order, thus
	// we can count the return address here.
	initial	f_read_beat_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_read_beat_addr <= 0;
	else if (soft_reset && reads_idle)
		f_read_beat_addr <= 0;
	else if (M_AXI_RVALID && M_AXI_RREADY)
		f_read_beat_addr <= f_read_beat_addr + (1<<ADDRLSB);
	// }}}

	// Read burst checking
	// {{{

	//
	// ...
	//

	// }}}


	// Match our read beat address to ARADDR
	// {{{
	// ...
	// }}}

	// Insist that our burst counters are consistent with bursts of a full
	// length only
	// {{{
	// ...
	// }}}

	// RLAST checking
	// {{{
	// ...
	// }}}

	// Match the read beat address to the number of items remaining in this
	// burst
	// {{{
	// ...
	// }}}
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Internal assertions (Induction)
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// On either error, or while waiting for a soft reset to complete
	// nothing new should issue
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && ($past(soft_reset) || $past(o_err)))
	begin
		assert(!$rose(M_AXI_AWVALID));
		assert(!$rose(M_AXI_WVALID));
		assert(!$rose(M_AXI_ARVALID));
		assert(!phantom_write);
		assert(!phantom_read);
	end
	// }}}

	//
	// Writes and reads always have enough room

	// Bus writes aren't allowed to drain the incoming FIFO dry
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!soft_reset && M_AXI_WVALID)
		assert(ififo_fill + (skd_valid ? 1:0) >= writes_pending);
	// }}}

	// Bus reads aren't allowed to overflow the return FIFO
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!soft_reset && M_AXI_RVALID)
		assert(!ofifo_full);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Write checks
	//

	// Make sure the skid buffer only reads when either there's nothing
	// held in the buffer, or the write channel has accepted data.  Indeed,
	// the write channel should never be active unless the skid buffer is
	// full.
	// {{{
	always @(*)
	if (!soft_reset && !skd_valid)
		assert(!M_AXI_WVALID);

	always @(*)
	if (M_AXI_WVALID && M_AXI_WREADY)
	begin
		assert(read_from_fifo);
	end else if (!skd_valid && !ififo_empty)
		assert(read_from_fifo);
	// }}}


	////////////////////////////////////////////////////////////////////////
	//
	// Read checks
	// {{{

	// No read checks in addition to the ones above

	// }}}

	////////////////////////////////////////
	//
	// Errors or resets -- do we properly end gracefully
	//
	// {{{
	// Set o_err on any bus error.  Only clear it on reset
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN))
	begin
		if ($past(M_AXI_BVALID && M_AXI_BRESP[1]))
			assert(o_err);
		if ($past(M_AXI_RVALID && M_AXI_RRESP[1]))
			assert(o_err);
		if ($past(!M_AXI_BVALID || !M_AXI_BRESP[1])
			&& $past(!M_AXI_RVALID || !M_AXI_RRESP[1]))
			assert(!$rose(o_err));
	end

	// Only release soft_reset once the bus is idle
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN) && $fell(soft_reset))
	begin
		//
		// ...
		//
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(!M_AXI_ARVALID);
	end
	// }}}
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checks
	// {{{

	// Check the global fill/emtpy values
	// {{{
	always @(*)
		assert(vfifo_full == (vfifo_fill == (1<<(C_AXI_ADDR_WIDTH-ADDRLSB))));

	always @(*)
		assert(vfifo_fill <= (1<<(C_AXI_ADDR_WIDTH-ADDRLSB)));

	always @(*)
		assert(vfifo_empty == (vfifo_fill == 0));
	// }}}

	// An equation for vfill based upon our property checker's counters
	// {{{
	always @(*)
	begin
		f_vfill = M_AXI_AWADDR - M_AXI_ARADDR;
		f_vfill[C_AXI_ADDR_WIDTH] = 0;
		if (!M_AXI_AWVALID)
			f_vfill = f_vfill - (writes_pending << ADDRLSB);
		// ...
		if (skd_valid)
			f_vfill = f_vfill + (1<<ADDRLSB);
		f_vfill = f_vfill + ((ififo_fill + ofifo_fill)<<ADDRLSB);
	end
	// }}}

	// Make sure the virtual FIFO's fill matches that counter
	// {{{
	always @(*)
	if (!soft_reset)
	begin
		assert(vfifo_fill == (f_vfill >> ADDRLSB));
		assert(f_vfill <= (1<<(C_AXI_ADDR_WIDTH)));

		// Before the equation check, double check that we
		// don't overflow any of our arithmetic.  Then check our
		// virtual FIFO's fill counter against the various internal
		// FIFO fills and read counters.

		// These are just inequality checks, however, so we'll still
		// need a full equation check elsewhere
		//
		// ...
		//
	end

	// Make certain we aren't overflowing in our subtraction above
	always @(*)
	if (M_AXI_ARVALID && !soft_reset)
		assert(M_AXI_ARADDR != M_AXI_AWADDR);
	// }}}

	// Check mem_space_available
	// {{{
	always @(*)
	begin
		f_space_available = (M_AXI_AWADDR - M_AXI_ARADDR);
		f_space_available[C_AXI_ADDR_WIDTH] = 0;
		f_space_available = (1<<C_AXI_ADDR_WIDTH) - f_space_available;
		if (M_AXI_AWVALID && !phantom_write)
			f_space_available = f_space_available
					- (1 << (LGMAXBURST+ADDRLSB));
		//
		// ...
	end

	always @(*)
	begin
		assert({ mem_data_available_w, {(LGMAXBURST){1'b0}} }
			<= vfifo_fill);
		// ...
		assert(mem_data_available  <= (1<<C_AXI_ADDR_WIDTH));
		assert(mem_space_available <= (1<<C_AXI_ADDR_WIDTH));
		if (!soft_reset)
		begin
			assert(mem_space_available == f_space_available);

			if (mem_space_available[C_AXI_ADDR_WIDTH])
			begin
				assert(M_AXI_ARADDR == M_AXI_AWADDR);
				assert(!M_AXI_AWVALID || phantom_write);
				// ...
			end
		end
	end
	// }}}

	// Check mem_data_available
	// {{{
	// First, generate an equation to describe it
	always @(*)
	begin
		f_data_available = M_AXI_AWADDR - M_AXI_ARADDR;
		f_data_available[C_AXI_ADDR_WIDTH] = 0;
		// ...
		if (M_AXI_ARVALID && !phantom_read)
			f_data_available = f_data_available
				- (1 << (ADDRLSB + LGMAXBURST));
	end

	// Then compare it against that equation
	always @(*)
	if (!soft_reset)
	begin
		assert(mem_data_available == f_data_available);
		if (mem_data_available[C_AXI_ADDR_WIDTH])
		begin
			assert(vfifo_fill[C_AXI_ADDR_WIDTH]);
			assert(ofifo_empty);
		end
	end
	// }}}

	// ofifo_space_available
	// {{{
	always @(*)
	if (!reset_fifo)
	begin
		// ...

		// Make sure we don't overflow above
		assert(ofifo_space_available <= (1<<LGFIFO));
	end
	// }}}

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Initial (only) constraints
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(!M_AXI_ARVALID);

		assert(mem_space_available == (1<<C_AXI_ADDR_WIDTH));
		assert(mem_data_available  == 0);

		assert(!phantom_read);
		assert(!phantom_write);

		assert(vfifo_fill == 0);
	end
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This core doesn't (yet) have any formal contract check

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[2:0]		cvr_write_bursts, cvr_read_bursts;
	(* anyconst *)	reg	cvr_high_speed;

	always @(posedge S_AXI_ACLK)
	if (cvr_high_speed)
	begin
		assume(!$fell(S_AXIS_TVALID));
		// if (S_AXI_ARESETN && $past(S_AXIS_TVALID && !S_AXIS_TREADY))
			// assume(S_AXIS_TVALID && $stable(S_AXIS_TDATA));

		assume(M_AXI_AWREADY || writes_pending > 0);
		assume(M_AXIS_TREADY);
		assume(M_AXI_WREADY);
		assume(M_AXI_ARREADY);
	end

	initial	cvr_write_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset || o_err || o_overflow)
		cvr_write_bursts <= 0;
	else if (M_AXI_BVALID && !cvr_write_bursts[2])
		cvr_write_bursts <= cvr_write_bursts + 1;

	initial	cvr_read_bursts = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || soft_reset || o_err || o_overflow)
		cvr_read_bursts <= 0;
	else if (M_AXI_RVALID && M_AXI_RLAST && !cvr_read_bursts[2])
		cvr_read_bursts <= cvr_read_bursts + 1;

	//
	// ...
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && !soft_reset)
		cover(cvr_read_bursts > 1 && cvr_write_bursts > 1);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && !soft_reset)
		cover(cvr_read_bursts > 1 && cvr_write_bursts > 1
							&& cvr_high_speed);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions (i.e. constraints)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// No careless assumptions.  Indeed, no assumptions at all beyond
	// what's in the bus property file, and some optional cover assumptions.

	// }}}
	// }}}
`endif
endmodule
