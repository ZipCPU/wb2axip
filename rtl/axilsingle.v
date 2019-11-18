////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilsingle.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	Create a special AXI-lite slave which can be used to reduce
//		crossbar logic for multiple simplified AXI-lite slaves.
//
//	To use this, the slave must follow specific (simplified AXI-lite) rules:
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
//			BRESP = 2'b00;	// Or other constant, such as 2'b10
//
//		always @(posedge S_AXI_ACLK)
//		if (ARVALID)
//			RDATA <= slvreg;
//
//		always @(*)
//			RRESP = 2'b00;	// Or other constant, such as 2'b10
//
//	This core will then keep track of the more complex bus logic,
//	simplifying both slaves and connection logic.  Slaves with the more
//	complicated (and proper/accurate) logic, but with only one bus address,
//	and that follow the rules above, should have no problems with this
//	additional logic.
//
// Performance:
//
//	This core can sustain one read/write per clock as long as the upstream
//	AXI-Lite master keeps S_AXI_[BR]READY high.  If S_AXI_[BR]READY ever
//	drops, there's some flexibility provided by the return FIFO, so the
//	master might not notice a drop in throughput until the FIFO fills.
//
//	The more practical performance measure is the latency of this core.
//	That is measured at four clocks contingent (again) on the master holding
//	S_AXI_[BR]READY line high.
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
		//
		// NS is the number of slave interfaces
		parameter	NS = 16,
		//
		parameter integer C_AXI_DATA_WIDTH = 32,
		localparam integer C_AXI_ADDR_WIDTH = $clog2(NS)+$clog2(C_AXI_DATA_WIDTH)-3,
		//
		// AW, and DW, are short-hand abbreviations used locally.
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		//
		// LGFLEN specifies the log (based two) of the number of
		// transactions that may need to be held outstanding internally.
		// If you really want high throughput, and if you expect any
		// back pressure at all, then increase LGFLEN.  Otherwise the
		// default value of 3 (FIFO size = 8) should be sufficient
		// to maintain full loading
		parameter	LGFLEN=3,
		//
		// If set, OPT_LOWPOWER will set all unused registers, both
		// internal and external, to zero anytime their corresponding
		// *VALID bit is clear
		parameter [0:0]	OPT_LOWPOWER = 0
	) (
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[3-1:0]			S_AXI_AWPROT,
		//
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire [C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
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
		output	wire	[NS-1:0]		M_AXI_AWVALID,
		output	wire	[3-1:0]			M_AXI_AWPROT,
		//
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		//
		input	wire	[NS*2-1:0]		M_AXI_BRESP,
		//
		output	wire	[NS-1:0]		M_AXI_ARVALID,
		output	wire	[3-1:0]			M_AXI_ARPROT,
		//
		input	wire [NS*C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire	[NS*2-1:0]		M_AXI_RRESP
	);
	//
	//
	localparam	LGNS = $clog2(NS);
	//
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
	wire			awskid_valid, bffull, bempty, write_awskidready;
	reg			write_bvalid, write_response;
	reg			bfull, write_wready;
	wire	[AW-ADDR_LSBS-1:0]	awskid_addr;
	reg	[AW-ADDR_LSBS-1:0]	write_windex, write_bindex;
	wire	[3-1:0]		awskid_prot;
	reg	[3-1:0]		m_axi_awprot;
	wire	[LGFLEN:0]	bfill;
	reg	[LGFLEN:0]	write_count;
	reg	[1:0]		write_resp;
	reg	[NS-1:0]	m_axi_awvalid;

	skidbuffer #(.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_OUTREG(0),
			.DW((AW-ADDR_LSBS)+3))
	awskid(	.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXI_AWVALID),
			.o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWPROT, S_AXI_AWADDR[AW-1:ADDR_LSBS] }),
		.o_valid(awskid_valid), .i_ready(write_awskidready),
			.o_data({ awskid_prot, awskid_addr }));

	initial	write_wready = 0;
	initial	m_axi_awvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ write_wready, m_axi_awvalid } <= 0;
	else if (awskid_valid && write_awskidready)
	begin
		m_axi_awvalid <= 0;
		m_axi_awvalid <= (1<<awskid_addr);
		// if (awskid_addr >= NS)
		//	m_axi_awvalid[NS] <= 1'b1;

		write_wready <= 1;
	end else if (S_AXI_WVALID)
		{ write_wready, m_axi_awvalid } <= 0;

	assign	S_AXI_WREADY = write_wready;

	always @(posedge S_AXI_ACLK)
	if (awskid_valid && write_awskidready)
	begin
		m_axi_awprot <= awskid_prot;
		write_windex <= awskid_addr;
	end

	assign M_AXI_AWVALID = (S_AXI_WVALID) ? m_axi_awvalid : {(NS){1'b0}};
	assign M_AXI_AWPROT = m_axi_awprot;
	assign S_AXI_WREADY = write_wready;
	assign	M_AXI_WDATA = S_AXI_WDATA;
	assign	M_AXI_WSTRB = S_AXI_WSTRB;
		
	assign	write_awskidready = (!write_wready || S_AXI_WVALID) && !bfull;

	initial	{ write_response, write_bvalid } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ write_response, write_bvalid } <= 0;
	else
		{ write_response, write_bvalid }
			<= { write_bvalid, (S_AXI_WVALID && S_AXI_WREADY) };

	always @(posedge S_AXI_ACLK)
		write_bindex <= write_windex;

	generate if (LGNS == $clog2(NS+1))
	begin
		always @(posedge S_AXI_ACLK)
		if (write_bindex >= NS)
			write_resp <= INTERCONNECT_ERROR;
		else
			write_resp <= M_AXI_BRESP[2*write_bindex +: 2];
	end else begin
		always @(posedge S_AXI_ACLK)
			write_resp <= M_AXI_BRESP[2*write_bindex +: 2];
	end endgenerate

	initial	write_count = 0;
	initial	bfull = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		write_count <= 0;
		bfull <= 0;
	end else case({ (awskid_valid && write_awskidready),
			(S_AXI_BVALID & S_AXI_BREADY) })
	2'b01:	begin
		write_count <= write_count - 1;
		bfull <= 1'b0;
		end
	2'b10:	begin
		write_count <= write_count + 1;
		bfull <= (&write_count[LGFLEN-1:0]);
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
		assert(write_count <= { 1'b1, {(LGFLEN){1'b0}} });
	always @(*)
		assert(bfull == (write_count == { 1'b1, {(LGFLEN){1'b0}} }));
`endif

	sfifo #(.BW(2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	bfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(write_response), .i_data(write_resp), .o_full(bffull),
			.o_fill(bfill),
		.i_rd(S_AXI_BVALID && S_AXI_BREADY), .o_data(S_AXI_BRESP),
			.o_empty(bempty));

`ifdef	FORMAL
	always @(*)
		assert(write_count == bfill
			+ (write_response ? 1:0)
			+ (write_bvalid ? 1:0)
			+ (write_wready ? 1:0));

`ifdef	VERIFIC
	always @(*)
	if (bfifo.f_first_in_fifo)
		assert(bfifo.f_first_data != 2'b01);
	always @(*)
	if (bfifo.f_second_in_fifo)
		assert(bfifo.f_second_data != 2'b01);
	always @(*)
	if (!bempty && (bfifo.rd_addr != bfifo.f_first_addr)
			&&(bfifo.rd_addr != bfifo.f_second_addr))
		assume(S_AXI_BRESP != 2'b01);
`else
	always @(*)
	if (!bempty)
		assume(S_AXI_BRESP != 2'b01);
`endif
`endif

	assign	S_AXI_BVALID = !bempty;

`ifdef	FORMAL
	always @(*)
		assert(!bffull || !write_bvalid);
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire				rempty, rdfull;
	wire	[LGFLEN:0]		rfill;
	reg	[AW-ADDR_LSBS-1:0]	read_index, last_read_index;
	reg	[1:0]			read_resp;
	reg	[DW-1:0]		read_rdata;
	reg				read_rwait, read_rvalid, read_result;
	reg	[NS-1:0]		m_axi_arvalid;
	reg	[3-1:0]			m_axi_arprot;

	initial	{ m_axi_arvalid, read_rwait } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ m_axi_arvalid, read_rwait } <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY)
	begin
		m_axi_arvalid <= (1 << S_AXI_ARADDR[AW-1:ADDR_LSBS]);
		read_rwait    <= 1'b1;
	end else
		{ m_axi_arvalid, read_rwait } <= 0;

	always @(posedge S_AXI_ACLK)
	begin
		m_axi_arprot  <= S_AXI_ARPROT;
		read_index    <= S_AXI_ARADDR[AW-1:ADDR_LSBS];
	end

	assign	M_AXI_ARVALID = m_axi_arvalid;
	assign	M_AXI_ARPROT  = m_axi_arprot;

	initial	{ read_result, read_rvalid } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ read_result, read_rvalid } <= 2'b00;
	else
		{ read_result, read_rvalid } <= { read_rvalid, read_rwait };

	always @(posedge S_AXI_ACLK)
		last_read_index <= read_index;

	always @(posedge S_AXI_ACLK)
		read_rdata <= M_AXI_RDATA[DW*last_read_index +: DW];

	generate if (LGNS == $clog2(NS+1))
	begin
		always @(posedge S_AXI_ACLK)
		if (last_read_index >= NS)
			read_resp <= INTERCONNECT_ERROR;
		else
			read_resp <= M_AXI_RRESP[2*last_read_index +: 2];
	end else begin
		always @(posedge S_AXI_ACLK)
			read_resp <= M_AXI_RRESP[2*last_read_index +: 2];
	end endgenerate

	reg			read_full;
	reg	[LGFLEN:0]	read_count;

	initial	{ read_count, read_full } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ read_count, read_full } <= 0;
	else case({ S_AXI_ARVALID & S_AXI_ARREADY, S_AXI_RVALID & S_AXI_RREADY})
	2'b10: begin
		read_count <= read_count + 1;
		read_full  <= &read_count[LGFLEN-1:0];
		end
	2'b01: begin
		read_count <= read_count - 1;
		read_full <= 1'b0;
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
		assert(read_count <= { 1'b1, {(LGFLEN){1'b0}} });
	always @(*)
		assert(read_full == (read_count == { 1'b1, {(LGFLEN){1'b0}} }));
`endif
	assign	S_AXI_ARREADY = !read_full;

	sfifo #(.BW(DW+2), .OPT_ASYNC_READ(0), .LGFLEN(LGFLEN))
	rfifo ( .i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_wr(read_result), .i_data({ read_rdata, read_resp }),
			.o_full(rdfull), .o_fill(rfill),
		.i_rd(S_AXI_RVALID && S_AXI_RREADY),
			.o_data({ S_AXI_RDATA, S_AXI_RRESP }),.o_empty(rempty));

`ifdef	FORMAL
	always @(*)
		assert(read_count == rfill + read_result + read_rvalid + read_rwait);
`ifdef	VERIFIC
	always @(*)
	if (rfifo.f_first_in_fifo)
		assert(rfifo.f_first_data[1:0] != 2'b01);
	always @(*)
	if (rfifo.f_second_in_fifo)
		assert(rfifo.f_second_data[1:0] != 2'b01);
	always @(*)
	if (!rempty && (rfifo.rd_addr != rfifo.f_first_addr)
			&&(rfifo.rd_addr != rfifo.f_second_addr))
		assume(S_AXI_RRESP != 2'b01);
`else
	always @(*)
	if (!rempty)
		assume(S_AXI_RRESP != 2'b01);
`endif
`endif

	assign	S_AXI_RVALID = !rempty;

	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
			S_AXI_AWADDR[ADDR_LSBS-1:0],
			S_AXI_ARADDR[ADDR_LSBS-1:0],
			bffull, rdfull, bfill, rfill };
	// verilator lint_on  UNUSED
`ifdef	FORMAL
	localparam	F_LGDEPTH = LGFLEN+1;
	reg	f_past_valid;
	reg	[F_LGDEPTH-1:0]	count_awr_outstanding, count_wr_outstanding,
				count_rd_outstanding;


	wire	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding,
					f_axi_wr_outstanding,
					f_axi_rd_outstanding;

	wire	[1:0]	fm_axi_awr_outstanding [0:NS-1];
	wire	[1:0]	fm_axi_wr_outstanding [0:NS-1];
	wire	[1:0]	fm_axi_rd_outstanding [0:NS-1];

	reg [NS-1:0]	m_axi_rvalid, m_axi_bvalid;

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
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr(S_AXI_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot(S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata(S_AXI_WDATA),
		.i_axi_wstrb(S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp(S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr(S_AXI_ARADDR),
		.i_axi_arprot(S_AXI_ARPROT),
		.i_axi_arcache(4'h0),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata(S_AXI_RDATA),
		.i_axi_rresp(S_AXI_RRESP),
		//
		.f_axi_rd_outstanding(f_axi_rd_outstanding),
		.f_axi_wr_outstanding(f_axi_wr_outstanding),
		.f_axi_awr_outstanding(f_axi_awr_outstanding));

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	genvar	M;
	generate for(M=0; M<NS; M=M+1)
	begin : CONSTRAIN_SLAVE_INTERACTIONS

		faxil_master #(// .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
				.C_AXI_ADDR_WIDTH(1),
				.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
				// .F_OPT_NO_READS(1'b0),
				// .F_OPT_NO_WRITES(1'b0),
				.F_OPT_NO_RESET(1'b1),
				.F_LGDEPTH(2))
			properties (
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awvalid(M_AXI_AWVALID[M]),
			.i_axi_awready(1'b1),
			.i_axi_awaddr(1'b0),
			.i_axi_awcache(4'h0),
			.i_axi_awprot(M_AXI_AWPROT),
			//
			.i_axi_wvalid(M_AXI_AWVALID[M]),
			.i_axi_wready(1'b1),
			.i_axi_wdata(M_AXI_WDATA[C_AXI_DATA_WIDTH-1:0]),
			.i_axi_wstrb(M_AXI_WSTRB[C_AXI_DATA_WIDTH/8-1:0]),
			//
			.i_axi_bvalid(m_axi_bvalid[M]),
			.i_axi_bready(1'b1),
			.i_axi_bresp(M_AXI_BRESP[2*M +: 2]),
			//
			.i_axi_arvalid(M_AXI_ARVALID[M]),
			.i_axi_arready(1'b1),
			.i_axi_araddr(1'b0),
			.i_axi_arprot(M_AXI_ARPROT),
			.i_axi_arcache(4'h0),
			//
			.i_axi_rdata(M_AXI_RDATA[M*C_AXI_DATA_WIDTH +: C_AXI_DATA_WIDTH]),
			.i_axi_rresp(M_AXI_RRESP[2*M +: 2]),
			.i_axi_rvalid(m_axi_rvalid[M]),
			.i_axi_rready(1'b1),
			//
			.f_axi_rd_outstanding(fm_axi_rd_outstanding[M]),
			.f_axi_wr_outstanding(fm_axi_wr_outstanding[M]),
			.f_axi_awr_outstanding(fm_axi_awr_outstanding[M]));

		initial	m_axi_bvalid <= 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_bvalid[M] <= 1'b0;
		else
			m_axi_bvalid[M] <= M_AXI_AWVALID[M];

		initial	m_axi_rvalid[M] <= 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_rvalid[M] <= 1'b0;
		else
			m_axi_rvalid[M] <= M_AXI_ARVALID[M];

		always @(*)
			assert(fm_axi_awr_outstanding[M] == fm_axi_wr_outstanding[M]);

		always @(*)
			assert(fm_axi_wr_outstanding[M]== (m_axi_bvalid[M] ? 1:0));

		always @(*)
			assert(fm_axi_rd_outstanding[M]== (m_axi_rvalid[M] ? 1:0));
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Properties necessary to pass induction
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assert(S_AXI_WREADY == (m_axi_awvalid != 0));
`ifdef	VERIFIC
	always @(*)
		assert($onehot0(M_AXI_AWVALID));

	always @(*)
		assert($onehot0(m_axi_bvalid));

	always @(*)
		assert($onehot0(m_axi_rvalid));
`endif
	always @(*)
	if (S_AXI_WREADY)
		assert(M_AXI_AWPROT == 0);
	always @(*)
	begin
		count_awr_outstanding = 0;
		if (!S_AXI_AWREADY)
			count_awr_outstanding = count_awr_outstanding + 1;
		if (write_wready)
			count_awr_outstanding = count_awr_outstanding + 1;
		if (write_bvalid)
			count_awr_outstanding = count_awr_outstanding + 1;
		if (write_response)
			count_awr_outstanding = count_awr_outstanding + 1;
		count_awr_outstanding = count_awr_outstanding + bfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_awr_outstanding == count_awr_outstanding);

	always @(*)
	begin
		count_wr_outstanding = 0;
		if (write_bvalid)
			count_wr_outstanding = count_wr_outstanding + 1;
		if (write_response)
			count_wr_outstanding = count_wr_outstanding + 1;
		count_wr_outstanding = count_wr_outstanding + bfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_wr_outstanding == count_wr_outstanding);

	//
	//
	//
	always @(*)
	begin
		count_rd_outstanding = 0;
		if (read_rwait)
			count_rd_outstanding = count_rd_outstanding + 1;
		if (read_rvalid)
			count_rd_outstanding = count_rd_outstanding + 1;
		if (read_result)
			count_rd_outstanding = count_rd_outstanding + 1;
		count_rd_outstanding = count_rd_outstanding + rfill;
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert(f_axi_rd_outstanding == count_rd_outstanding);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_arvalids, cvr_awvalids, cvr_reads, cvr_writes;

	initial	cvr_awvalids = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_awvalids <= 0;
	else if (S_AXI_AWVALID && S_AXI_AWREADY && !(&cvr_awvalids))
		cvr_awvalids <= cvr_awvalids + 1;

	initial	cvr_arvalids = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_arvalids <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY && !(&cvr_arvalids))
		cvr_arvalids <= cvr_arvalids + 1;

	initial	cvr_writes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_writes <= 0;
	else if (S_AXI_BVALID && S_AXI_BREADY && !(&cvr_writes))
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_reads <= 0;
	else if (S_AXI_RVALID && S_AXI_RREADY && !(&cvr_arvalids))
		cvr_reads <= cvr_reads + 1;

	always @(*)
		cover(cvr_awvalids > 4);

	always @(*)
		cover(cvr_arvalids > 4);

	always @(*)
		cover(cvr_reads > 4);

	always @(*)
		cover(cvr_writes > 4);

	always @(*)
		cover((cvr_writes > 4) && (cvr_reads > 4));
`endif
endmodule
// `ifndef	YOSYS
// `default_nettype wire
// `endif
