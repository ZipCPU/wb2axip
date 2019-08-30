////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilsingle.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Create a special slave which can be used to reduce crossbar
//		logic for multiple simplified slaves.
//
//	To use this, the slave must follow specific (simplified AXI) rules:
//
//	Write interface
//	1. The slave must guarantee that AWREADY == WREADY = 1
//		(This core doesn't have AWREADY or WREADY inputs)
//	2. The slave must also guarantee that BVALID == $past(AWVALID)
//		(This core internally generates BVALID)
//	3. The controller will guarantee that AWVALID == WVALID
//		(You can connect AWVALID to WVALID when connecting to your core)
//	4. The controller will also guarantee that BREADY = 1
//		(This core doesn't have a BVALID input)
//
//	Read interface
//	1. The slave must guarantee that ARREADY == 1
//		(This core doesn't have an ARREADY input)
//	2. The slave must also guarantee that RVALID == $past(ARVALID)
//		(This core doesn't have an RVALID input, trusting the slave
//			instead)
//	3. The controller will guarantee that RREADY = 1
//		(This core doesn't have an RREADY output)
//
//	In this simplified controller, the AxADDR lines have been dropped.
//	Slaves may only have one address, and that one will be aligned with the
//	  bus width
//
//
//	Why?  This simplifies slave logic.  Slaves may interact with the bus
//	using only the logic below:
//
//		always @(posedge S_AXI_ACLK)
//		if (AWVALID)
//		begin
//			if (WSTRB[0])
//				slvreg[ 7: 0] <= WDATA[ 7: 0];
//			if (WSTRB[1])
//				slvreg[15: 8] <= WDATA[15: 8];
//			if (WSTRB[2])
//				slvreg[23:16] <= WDATA[23:16];
//			if (WSTRB[3])
//				slvreg[31:24] <= WDATA[31:24];
//		end
//
//		always @(*)
//			BRESP 2'b00;
//
//		always @(posedge S_AXI_ACLK)
//		if (ARVALID)
//			RDATA <= slvreg;
//
//		always @(*)
//			RRESP 2'b00;
//
//	This core will then keep track of the more complex bus logic,
//	simplifying both slaves and connection logic.  Slaves with the more
//	complicated (and proper/accurate) logic, but with only one bus address,
//	and that follow the rules above, should have no problems with this
//	additional logic.
//
// Performance: (Not measured yet)
//
//	I'm expecting to be able to sustain one read/write per clock as long as
//	the keeps S_AXI_[BR]READY high.  If S_AXI_[BR]READY ever drops,
//	there's some flexibility provided by the return FIFO, so the master
//	might not notice a drop in throughput until the FIFO fills.
//
//	The more practical performance measure is the latency of this core.
//	For that, I'm expecting a latency of three clocks as long as the
//	master holds the S_AXI_[BR]READY line high.
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
// `ifdef	VERILATOR
// `define	FORMAL
// `endif
//
module	axilsingle #(
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 32,
		//
		// NS is the number of slave interfaces
		parameter	NS = 16,
		//
		// AW, and DW, are short-hand abbreviations used locally.
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		//
		// If you really want high throughput, and you expect any
		// back pressure at all, then increase LGFLEN.  Otherwise the
		// default value of 2 (FIFO size = 4) should be sufficient
		parameter	LGFLEN=2,
		//
		// If set, OPT_LOWPOWER will set all unused registers, both
		// internal and external, to zero anytime their corresponding
		// *VALID bit is clear
		parameter [0:0]	OPT_LOWPOWER = 0
	) (
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		//
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[3-1:0]			S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		output	wire	[2-1:0]			S_AXI_BRESP,
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		//
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[3-1:0]			S_AXI_ARPROT,
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		//
		output	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire	[2-1:0]			S_AXI_RRESP,
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		//
		//
		//
		output	wire	[NS-1:0]			M_AXI_AWVALID,
		output	wire	[3-1:0]				M_AXI_AWPROT,
		//
		output	wire	[C_AXI_DATA_WIDTH-1:0]		M_AXI_WDATA,
		output	wire	[C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		//
		input	wire	[NS*2-1:0]			M_AXI_BRESP,
		//
		output	wire	[NS-1:0]			M_AXI_ARVALID,
		output	wire	[3-1:0]				M_AXI_ARPROT,
		//
		input	wire	[NS*C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire	[NS*2-1:0]			M_AXI_RRESP
	);
	//
	//
	localparam	LGNS = (NS>1) ? $clog2(NS+1) : 1;
	//
	// In order to use indexes, and hence fully balanced mux trees, it helps
	// to make certain that we have a power of two based lookup.  NMFULL
	// is the number of masters in this lookup, with potentially some
	// unused extra ones.  NSFULL is defined similarly.
	localparam	NSFULL = (NS>1) ? (1<<LGNS) : 2;
	localparam	INTERCONNECT_ERROR = 2'b11;
	localparam	ADDR_LSBS = $clog2(DW)-3;
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Write logic:
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire			awskid_valid, wskid_valid, bffull,bempty,
				woskid_valid, woskid_ready;
	wire			write_ready;
	reg			write_bvalid, bfull;
	wire	[DW+DW/8-1:0]	wskid_data;
	wire	[AW-ADDR_LSBS-1:0]	awskid_addr, wout_addr;
	reg	[AW-ADDR_LSBS-1:0]	write_index;
	wire	[NS:0]		awskid_sel, wout_valids;
	wire	[3-1:0]		awskid_prot;
	reg	[NSFULL-1:0]	s_awskid_sel;
	wire	[LGFLEN:0]	bfill;
	reg	[1:0]		write_resp;

	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(0),
			.DW((AW-ADDR_LSBS)+3))
	awskid(	.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID),
			.o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWPROT, S_AXI_AWADDR[AW-1:ADDR_LSBS] }),
		.o_valid(awskid_valid), .i_ready(write_ready),
			.o_data({ awskid_prot, awskid_addr }));

	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(0),
			.DW(DW+DW/8))
	wskid(	.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_WVALID),
			.o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
		.o_valid(wskid_valid), .i_ready(write_ready),
			.o_data({ wskid_data }));

	assign	write_ready = awskid_valid & wskid_valid & !bfull & woskid_ready;

	always @(*)
	begin
		s_awskid_sel = 0;
		s_awskid_sel[NSFULL-1:0] = (1<<awskid_addr);
		if (awskid_addr >= NS-1)
			s_awskid_sel[NS] = 1'b1;
	end

	assign	awskid_sel = s_awskid_sel[NS:0];


	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(1),
			.DW((AW-ADDR_LSBS)+(NS+1)+3+DW+DW/8))
	wout( .i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(awskid_valid & wskid_valid & !bfull),
			.o_ready(woskid_ready),
			.i_data({ awskid_addr,
				awskid_sel, awskid_prot, wskid_data }),
		.o_valid(woskid_valid), .i_ready(1'b1),
		.o_data({ wout_addr, wout_valids, M_AXI_AWPROT,
			M_AXI_WDATA, M_AXI_WSTRB}));

	assign	M_AXI_AWVALID = (woskid_valid) ? wout_valids[NS-1:0]
					: {(NS){1'b0}};

	always @(posedge S_AXI_ACLK)
		write_index <= wout_addr;

	initial	write_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		write_bvalid <= 0;
	else
		write_bvalid <= woskid_valid;

	always @(posedge S_AXI_ACLK)
	if (write_index >= NS)
		write_resp <= INTERCONNECT_ERROR;
	else
		write_resp <= M_AXI_BRESP[2*write_index +: 2];

	initial	bfull = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		bfull <= 0;
	else case({ write_bvalid, S_AXI_BVALID & S_AXI_BREADY })
	2'b01:   bfull <= (bfill + 1) >= (1<<LGFLEN);
	2'b10:   bfull <= (bfill + 3) >= (1<<LGFLEN);
	default: bfull <= (bfill + 2) >= (1<<LGFLEN);
	endcase

	sfifo #(.BW(2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	bfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(write_bvalid), .i_data(write_resp), .o_full(bffull),
			.o_fill(bfill),
		.i_rd(S_AXI_BVALID && S_AXI_BREADY), .o_data(S_AXI_BRESP),
			.o_empty(bempty));

	assign	S_AXI_BVALID = !bempty;

`ifdef	FORMAL
	always @(*)
		assert(!bffull || !write_bvalid);
	always @(*)
		assert(woskid_ready);
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire			roskid_valid, read_ready, arskid_valid;
	wire			rempty, rdfull, roskid_ready;
	wire	[LGFLEN:0]	rfill;
	wire	[2:0]		arskid_prot;
	wire	[AW-1:0]	arskid_addr;
	reg	[NSFULL-1:0]	s_arskid_sel;
	wire	[NS:0]			arskid_sel, rout_valids;
	wire	[AW-ADDR_LSBS-1:0]	rout_addr;
	reg	[AW-ADDR_LSBS-1:0]	read_index;
	reg	[1:0]			read_resp;
	reg	[DW-1:0]		read_rdata;
	reg				read_rvalid, rfull;

	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(0),
			.DW(AW-ADDR_LSBS+3))
	arskid(	.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_ARVALID),
			.o_ready(S_AXI_ARREADY),
			.i_data({ S_AXI_ARPROT, S_AXI_ARADDR[AW-1:ADDR_LSBS] }),
		.o_valid(arskid_valid), .i_ready(read_ready),
			.o_data({ arskid_prot, arskid_addr[AW-1:ADDR_LSBS] }));

	assign	arskid_addr[ADDR_LSBS-1:0] = 0;
	assign	read_ready = arskid_valid & !rfull;

	always @(*)
	begin
		s_arskid_sel = 0;
		s_arskid_sel[NSFULL-1:0] = (1<<arskid_addr);
		if (arskid_addr[AW-1:ADDR_LSBS] >= NS-1)
			s_arskid_sel[NS] = 1'b1;
	end

	assign	arskid_sel = s_arskid_sel[NS:0];


	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(1),
			.DW((AW-ADDR_LSBS)+(NS+1)+3))
	rout( .i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(read_ready),
			.o_ready(roskid_ready),
			.i_data({ arskid_addr[AW-1:ADDR_LSBS],
					arskid_sel, arskid_prot }),
		.o_valid(roskid_valid), .i_ready(1'b1),
		.o_data({ rout_addr, rout_valids, M_AXI_ARPROT }));

`ifdef	FORMAL
	always @(*)
		assert(roskid_ready);
	always @(*)
		assert(!rdfull || !read_rvalid);
`endif

	assign	M_AXI_ARVALID = (roskid_valid) ? rout_valids[NS-1:0]
					: {(NS){1'b0}};

	always @(posedge S_AXI_ACLK)
		read_index <= rout_addr;

	always @(posedge S_AXI_ACLK)
		read_rdata <= M_AXI_RDATA[DW*read_index +: DW];

	always @(posedge S_AXI_ACLK)
	if (read_index >= NS)
		read_resp <= INTERCONNECT_ERROR;
	else
		read_resp <= M_AXI_RRESP[2*read_index +: 2];

	initial	read_rvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		read_rvalid <= 1'b0;
	else
		read_rvalid <= roskid_valid;

	initial	rfull = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rfull <= 0;
	else case({ read_rvalid, S_AXI_RVALID & S_AXI_RREADY })
	2'b01:   rfull <= (rfill + 1) >= (1<<LGFLEN);
	2'b10:   rfull <= (rfill + 3) >= (1<<LGFLEN);
	default: rfull <= (rfill + 2) >= (1<<LGFLEN);
	endcase


	sfifo #(.BW(DW+2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	rfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(read_rvalid), .i_data({ read_rdata, read_resp }),
			.o_full(rdfull), .o_fill(rfill),
		.i_rd(S_AXI_RVALID && S_AXI_RREADY),
			.o_data({ S_AXI_RDATA, S_AXI_RRESP }),.o_empty(rempty));

	assign	S_AXI_RVALID = !rempty;

	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, woskid_ready, roskid_ready,
			S_AXI_AWADDR[ADDR_LSBS-1:0],
			S_AXI_ARADDR[ADDR_LSBS-1:0],
			s_awskid_sel[NSFULL-1:NS+1],
			s_arskid_sel[NSFULL-1:NS+1],
			bffull, rdfull,
			rout_valids[NS], wout_valids[NS] };
	// verilator lint_on  UNUSED
`ifdef	FORMAL
	localparam	F_LGDEPTH = LGFLEN+1;
	reg	f_past_valid;
	reg	[F_LGDEPTH-1:0]	count_awr_outstanding, count_wr_outstanding,
				count_rd_outstanding;


	wire	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding,
					f_axi_wr_outstanding,
					f_axi_rd_outstanding;

	faxil_slave #(// .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			// .F_OPT_NO_READS(1'b0),
			// .F_OPT_NO_WRITES(1'b0),
			.F_OPT_XILINX(1),
			.F_LGDEPTH(F_LGDEPTH))
		properties (
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awaddr(S_AXI_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot(S_AXI_AWPROT),
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		//
		.i_axi_wdata(S_AXI_WDATA),
		.i_axi_wstrb(S_AXI_WSTRB),
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		//
		.i_axi_bresp(S_AXI_BRESP),
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		//
		.i_axi_araddr(S_AXI_ARADDR),
		.i_axi_arprot(S_AXI_ARPROT),
		.i_axi_arcache(4'h0),
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		//
		.i_axi_rdata(S_AXI_RDATA),
		.i_axi_rresp(S_AXI_RRESP),
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		//
		.f_axi_rd_outstanding(f_axi_rd_outstanding),
		.f_axi_wr_outstanding(f_axi_wr_outstanding),
		.f_axi_awr_outstanding(f_axi_awr_outstanding));

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	///////
	//
	// Properties necessary to pass induction
	//
	always @(*)
	begin
		count_awr_outstanding = 0;
		if (!S_AXI_AWREADY)
			count_awr_outstanding = count_awr_outstanding + 1;
		if (woskid_valid)
			count_awr_outstanding = count_awr_outstanding + 1;
		if (write_bvalid)
			count_awr_outstanding = count_awr_outstanding + 1;
		count_awr_outstanding = count_awr_outstanding + bfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_awr_outstanding == count_awr_outstanding);

	always @(*)
	begin
		count_wr_outstanding = 0;
		if (!S_AXI_WREADY)
			count_wr_outstanding = count_wr_outstanding + 1;
		if (woskid_valid)
			count_wr_outstanding = count_wr_outstanding + 1;
		if (write_bvalid)
			count_wr_outstanding = count_wr_outstanding + 1;
		count_wr_outstanding = count_wr_outstanding + bfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_wr_outstanding == count_wr_outstanding);


	// Exclusive access is not allowed in AXI-lite
	always @(*)
		assume(M_AXI_BRESP[2*write_index +: 2] != 2'b01);

	//
	//
	//
	always @(*)
	begin
		count_rd_outstanding = 0;
		if (!S_AXI_ARREADY)
			count_rd_outstanding = count_rd_outstanding + 1;
		if (roskid_valid)
			count_rd_outstanding = count_rd_outstanding + 1;
		if (read_rvalid)
			count_rd_outstanding = count_rd_outstanding + 1;
		count_rd_outstanding = count_rd_outstanding + rfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_rd_outstanding == count_rd_outstanding);

	// Exclusive access is not allowed in AXI-lite
	always @(*)
		assume(M_AXI_RRESP[2*read_index +: 2] != 2'b01);

`endif
endmodule
// `ifndef	YOSYS
// `default_nettype wire
// `endif
