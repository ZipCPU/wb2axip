////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xlnxdemo.v
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	To test the formal tools on an AXI-lite core that is "known"
//		to work.  (Only this one doesn't--at least that was my purpose.
//	Most of this code comes directly from Vivado's core generator--starting
//	at the end of this comment block and going down directly to the
//	`ifdef	FORMAL block at the bottom.  I have made superficial adjustments
//	to Xilinx's code: I swapped spaces for tabs, I removed any white space
//	at the ends of lines, I fixed a spelling error in the comments, added
//	the default_nettype, added initial statements (at the bottom) for things
//	that should've had them in the first place, etc.  I may have even
//	swapped an always @(somevalue) for an always @(*), but that's as far
//	as I've gone.
//
//	Since 2016, Vivado has made updates to their core.  The last time I
//	checked, however, it still failed to pass a formal verification check.
//
//	This core will fail a verification check.
//
// Creator:	Vivado, 2016 (I think it was 2016.1)
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none	// Added to the raw demo
`timescale 1 ns / 1 ps
//
module xlnxdemo #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line

		// Width of S_AXI data bus
		parameter integer C_S_AXI_DATA_WIDTH	= 32,
		// Width of S_AXI address bus
		parameter integer C_S_AXI_ADDR_WIDTH	= 7,
`ifdef	FORMAL
		parameter [0:0] OPT_ASSUME_NO_ERRORS = 1'b0
`endif
	)
	(
		// Users to add ports here

		// User ports ends
		// Do not modify the ports beyond this line

		// Global Clock Signal
		input wire  S_AXI_ACLK,
		// Global Reset Signal. This Signal is Active LOW
		input wire  S_AXI_ARESETN,
		// Write address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_AWADDR,
		// Write channel Protection type. This signal indicates the
    		// privilege and security level of the transaction, and whether
    		// the transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_AWPROT,
		// Write address valid. This signal indicates that the master signaling
    		// valid write address and control information.
		input wire  S_AXI_AWVALID,
		// Write address ready. This signal indicates that the slave is ready
    		// to accept an address and associated control signals.
		output wire  S_AXI_AWREADY,
		// Write data (issued by master, acceped by Slave)
		input wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_WDATA,
		// Write strobes. This signal indicates which byte lanes hold
    		// valid data. There is one write strobe bit for each eight
    		// bits of the write data bus.
		input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] S_AXI_WSTRB,
		// Write valid. This signal indicates that valid write
    		// data and strobes are available.
		input wire  S_AXI_WVALID,
		// Write ready. This signal indicates that the slave
    		// can accept the write data.
		output wire  S_AXI_WREADY,
		// Write response. This signal indicates the status
    		// of the write transaction.
		output wire [1 : 0] S_AXI_BRESP,
		// Write response valid. This signal indicates that the channel
    		// is signaling a valid write response.
		output wire  S_AXI_BVALID,
		// Response ready. This signal indicates that the master
    		// can accept a write response.
		input wire  S_AXI_BREADY,
		// Read address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_ARADDR,
		// Protection type. This signal indicates the privilege
    		// and security level of the transaction, and whether the
    		// transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_ARPROT,
		// Read address valid. This signal indicates that the channel
    		// is signaling valid read address and control information.
		input wire  S_AXI_ARVALID,
		// Read address ready. This signal indicates that the slave is
    		// ready to accept an address and associated control signals.
		output wire  S_AXI_ARREADY,
		// Read data (issued by slave)
		output wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_RDATA,
		// Read response. This signal indicates the status of the
    		// read transfer.
		output wire [1 : 0] S_AXI_RRESP,
		// Read valid. This signal indicates that the channel is
    		// signaling the required read data.
		output wire  S_AXI_RVALID,
		// Read ready. This signal indicates that the master can
    		// accept the read data and response information.
		input wire  S_AXI_RREADY
	);

	// AXI4LITE signals
	reg [C_S_AXI_ADDR_WIDTH-1 : 0] 	axi_awaddr;
	reg  	axi_awready;
	reg  	axi_wready;
	reg [1 : 0] 	axi_bresp;
	reg  	axi_bvalid;
	reg [C_S_AXI_ADDR_WIDTH-1 : 0] 	axi_araddr;
	reg  	axi_arready;
	reg [C_S_AXI_DATA_WIDTH-1 : 0] 	axi_rdata;
	reg [1 : 0] 	axi_rresp;
	reg  	axi_rvalid;

	// Example-specific design signals
	// local parameter for addressing 32 bit / 64 bit C_S_AXI_DATA_WIDTH
	// ADDR_LSB is used for addressing 32/64 bit registers/memories
	// ADDR_LSB = 2 for 32 bits (n downto 2)
	// ADDR_LSB = 3 for 64 bits (n downto 3)
	localparam integer ADDR_LSB = (C_S_AXI_DATA_WIDTH/32) + 1;
	localparam integer OPT_MEM_ADDR_BITS = 4;
	//----------------------------------------------
	//-- Signals for user logic register space example
	//------------------------------------------------
	//-- Number of Slave Registers 32
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg0;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg1;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg2;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg3;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg4;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg5;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg6;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg7;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg8;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg9;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg10;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg11;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg12;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg13;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg14;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg15;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg16;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg17;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg18;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg19;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg20;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg21;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg22;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg23;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg24;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg25;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg26;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg27;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg28;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg29;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg30;
	reg [C_S_AXI_DATA_WIDTH-1:0]	slv_reg31;
	wire	 slv_reg_rden;
	wire	 slv_reg_wren;
	reg [C_S_AXI_DATA_WIDTH-1:0]	 reg_data_out;
	integer	 byte_index;

	// I/O Connections assignments

	assign S_AXI_AWREADY	= axi_awready;
	assign S_AXI_WREADY	= axi_wready;
	assign S_AXI_BRESP	= axi_bresp;
	assign S_AXI_BVALID	= axi_bvalid;
	assign S_AXI_ARREADY	= axi_arready;
	assign S_AXI_RDATA	= axi_rdata;
	assign S_AXI_RRESP	= axi_rresp;
	assign S_AXI_RVALID	= axi_rvalid;
	// Implement axi_awready generation
	// axi_awready is asserted for one S_AXI_ACLK clock cycle when both
	// S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_awready is
	// de-asserted when reset is low.

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_awready <= 1'b0;
	    end
	  else
	    begin
	      if (~axi_awready && S_AXI_AWVALID && S_AXI_WVALID)
	        begin
	          // slave is ready to accept write address when
	          // there is a valid write address and write data
	          // on the write address and data bus. This design
	          // expects no outstanding transactions.
	          axi_awready <= 1'b1;
	        end
	      else
	        begin
	          axi_awready <= 1'b0;
	        end
	    end
	end

	// Implement axi_awaddr latching
	// This process is used to latch the address when both
	// S_AXI_AWVALID and S_AXI_WVALID are valid.

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_awaddr <= 0;
	    end
	  else
	    begin
	      if (~axi_awready && S_AXI_AWVALID && S_AXI_WVALID)
	        begin
	          // Write Address latching
	          axi_awaddr <= S_AXI_AWADDR;
	        end
	    end
	end

	// Implement axi_wready generation
	// axi_wready is asserted for one S_AXI_ACLK clock cycle when both
	// S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_wready is
	// de-asserted when reset is low.

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_wready <= 1'b0;
	    end
	  else
	    begin
	      if (~axi_wready && S_AXI_WVALID && S_AXI_AWVALID)
	        begin
	          // slave is ready to accept write data when
	          // there is a valid write address and write data
	          // on the write address and data bus. This design
	          // expects no outstanding transactions.
	          axi_wready <= 1'b1;
	        end
	      else
	        begin
	          axi_wready <= 1'b0;
	        end
	    end
	end

	// Implement memory mapped register select and write logic generation
	// The write data is accepted and written to memory mapped registers when
	// axi_awready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted. Write strobes are used to
	// select byte enables of slave registers while writing.
	// These registers are cleared when reset (active low) is applied.
	// Slave register write enable is asserted when valid address and data are available
	// and the slave is ready to accept the write address and write data.
	assign slv_reg_wren = axi_wready && S_AXI_WVALID && axi_awready && S_AXI_AWVALID;

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      slv_reg0 <= 0;
	      slv_reg1 <= 0;
	      slv_reg2 <= 0;
	      slv_reg3 <= 0;
	      slv_reg4 <= 0;
	      slv_reg5 <= 0;
	      slv_reg6 <= 0;
	      slv_reg7 <= 0;
	      slv_reg8 <= 0;
	      slv_reg9 <= 0;
	      slv_reg10 <= 0;
	      slv_reg11 <= 0;
	      slv_reg12 <= 0;
	      slv_reg13 <= 0;
	      slv_reg14 <= 0;
	      slv_reg15 <= 0;
	      slv_reg16 <= 0;
	      slv_reg17 <= 0;
	      slv_reg18 <= 0;
	      slv_reg19 <= 0;
	      slv_reg20 <= 0;
	      slv_reg21 <= 0;
	      slv_reg22 <= 0;
	      slv_reg23 <= 0;
	      slv_reg24 <= 0;
	      slv_reg25 <= 0;
	      slv_reg26 <= 0;
	      slv_reg27 <= 0;
	      slv_reg28 <= 0;
	      slv_reg29 <= 0;
	      slv_reg30 <= 0;
	      slv_reg31 <= 0;
	    end
	  else begin
	    if (slv_reg_wren)
	      begin
	        case ( axi_awaddr[ADDR_LSB+OPT_MEM_ADDR_BITS:ADDR_LSB] )
	          5'h00:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 0
	                slv_reg0[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h01:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 1
	                slv_reg1[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h02:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 2
	                slv_reg2[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h03:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 3
	                slv_reg3[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h04:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 4
	                slv_reg4[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h05:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 5
	                slv_reg5[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h06:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 6
	                slv_reg6[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h07:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 7
	                slv_reg7[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h08:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 8
	                slv_reg8[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h09:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 9
	                slv_reg9[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0A:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 10
	                slv_reg10[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0B:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 11
	                slv_reg11[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0C:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 12
	                slv_reg12[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0D:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 13
	                slv_reg13[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0E:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 14
	                slv_reg14[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h0F:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 15
	                slv_reg15[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h10:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 16
	                slv_reg16[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h11:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 17
	                slv_reg17[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h12:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 18
	                slv_reg18[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h13:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 19
	                slv_reg19[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h14:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 20
	                slv_reg20[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h15:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 21
	                slv_reg21[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h16:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 22
	                slv_reg22[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h17:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 23
	                slv_reg23[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h18:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 24
	                slv_reg24[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h19:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 25
	                slv_reg25[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1A:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 26
	                slv_reg26[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1B:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 27
	                slv_reg27[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1C:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 28
	                slv_reg28[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1D:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 29
	                slv_reg29[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1E:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 30
	                slv_reg30[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          5'h1F:
	            for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
	              if ( S_AXI_WSTRB[byte_index] == 1 ) begin
	                // Respective byte enables are asserted as per write strobes
	                // Slave register 31
	                slv_reg31[(byte_index*8) +: 8] <= S_AXI_WDATA[(byte_index*8) +: 8];
	              end
	          default : begin
	                      slv_reg0 <= slv_reg0;
	                      slv_reg1 <= slv_reg1;
	                      slv_reg2 <= slv_reg2;
	                      slv_reg3 <= slv_reg3;
	                      slv_reg4 <= slv_reg4;
	                      slv_reg5 <= slv_reg5;
	                      slv_reg6 <= slv_reg6;
	                      slv_reg7 <= slv_reg7;
	                      slv_reg8 <= slv_reg8;
	                      slv_reg9 <= slv_reg9;
	                      slv_reg10 <= slv_reg10;
	                      slv_reg11 <= slv_reg11;
	                      slv_reg12 <= slv_reg12;
	                      slv_reg13 <= slv_reg13;
	                      slv_reg14 <= slv_reg14;
	                      slv_reg15 <= slv_reg15;
	                      slv_reg16 <= slv_reg16;
	                      slv_reg17 <= slv_reg17;
	                      slv_reg18 <= slv_reg18;
	                      slv_reg19 <= slv_reg19;
	                      slv_reg20 <= slv_reg20;
	                      slv_reg21 <= slv_reg21;
	                      slv_reg22 <= slv_reg22;
	                      slv_reg23 <= slv_reg23;
	                      slv_reg24 <= slv_reg24;
	                      slv_reg25 <= slv_reg25;
	                      slv_reg26 <= slv_reg26;
	                      slv_reg27 <= slv_reg27;
	                      slv_reg28 <= slv_reg28;
	                      slv_reg29 <= slv_reg29;
	                      slv_reg30 <= slv_reg30;
	                      slv_reg31 <= slv_reg31;
	                    end
	        endcase
	      end
	  end
	end

	// Implement write response logic generation
	// The write response and response valid signals are asserted by the slave
	// when axi_wready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted.
	// This marks the acceptance of address and indicates the status of
	// write transaction.

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_bvalid  <= 0;
	      axi_bresp   <= 2'b0;
	    end
	  else
	    begin
	      if (axi_awready && S_AXI_AWVALID && ~axi_bvalid && axi_wready && S_AXI_WVALID)
	        begin
	          // indicates a valid write response is available
	          axi_bvalid <= 1'b1;
	          axi_bresp  <= 2'b0; // 'OKAY' response
	        end                   // work error responses in future
	      else
	        begin
	          if (S_AXI_BREADY && axi_bvalid)
	            //check if bready is asserted while bvalid is high)
	            //(there is a possibility that bready is always asserted high)
	            begin
	              axi_bvalid <= 1'b0;
	            end
	        end
	    end
	end

	// Implement axi_arready generation
	// axi_arready is asserted for one S_AXI_ACLK clock cycle when
	// S_AXI_ARVALID is asserted. axi_awready is
	// de-asserted when reset (active low) is asserted.
	// The read address is also latched when S_AXI_ARVALID is
	// asserted. axi_araddr is reset to zero on reset assertion.

	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_arready <= 1'b0;
	      axi_araddr  <= 7'b0;
	    end
	  else
	    begin
	      if (~axi_arready && S_AXI_ARVALID)
	        begin
	          // indicates that the slave has acceped the valid read address
	          axi_arready <= 1'b1;
	          // Read address latching
	          axi_araddr  <= S_AXI_ARADDR;
	        end
	      else
	        begin
	          axi_arready <= 1'b0;
	        end
	    end
	end

	// Implement axi_arvalid generation
	// axi_rvalid is asserted for one S_AXI_ACLK clock cycle when both
	// S_AXI_ARVALID and axi_arready are asserted. The slave registers
	// data are available on the axi_rdata bus at this instance. The
	// assertion of axi_rvalid marks the validity of read data on the
	// bus and axi_rresp indicates the status of read transaction.axi_rvalid
	// is deasserted on reset (active low). axi_rresp and axi_rdata are
	// cleared to zero on reset (active low).
	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_rvalid <= 0;
	      axi_rresp  <= 0;
	    end
	  else
	    begin
	      if (axi_arready && S_AXI_ARVALID && ~axi_rvalid)
	        begin
	          // Valid read data is available at the read data bus
	          axi_rvalid <= 1'b1;
	          axi_rresp  <= 2'b0; // 'OKAY' response
	        end
	      else if (axi_rvalid && S_AXI_RREADY)
	        begin
	          // Read data is accepted by the master
	          axi_rvalid <= 1'b0;
	        end
	    end
	end

	// Implement memory mapped register select and read logic generation
	// Slave register read enable is asserted when valid address is available
	// and the slave is ready to accept the read address.
	assign slv_reg_rden = axi_arready & S_AXI_ARVALID & ~axi_rvalid;
	always @(*)
	begin
	      reg_data_out = 0;
	      // Address decoding for reading registers
	      case ( axi_araddr[ADDR_LSB+OPT_MEM_ADDR_BITS:ADDR_LSB] )
	        5'h00   : reg_data_out = slv_reg0;
	        5'h01   : reg_data_out = slv_reg1;
	        5'h02   : reg_data_out = slv_reg2;
	        5'h03   : reg_data_out = slv_reg3;
	        5'h04   : reg_data_out = slv_reg4;
	        5'h05   : reg_data_out = slv_reg5;
	        5'h06   : reg_data_out = slv_reg6;
	        5'h07   : reg_data_out = slv_reg7;
	        5'h08   : reg_data_out = slv_reg8;
	        5'h09   : reg_data_out = slv_reg9;
	        5'h0A   : reg_data_out = slv_reg10;
	        5'h0B   : reg_data_out = slv_reg11;
	        5'h0C   : reg_data_out = slv_reg12;
	        5'h0D   : reg_data_out = slv_reg13;
	        5'h0E   : reg_data_out = slv_reg14;
	        5'h0F   : reg_data_out = slv_reg15;
	        5'h10   : reg_data_out = slv_reg16;
	        5'h11   : reg_data_out = slv_reg17;
	        5'h12   : reg_data_out = slv_reg18;
	        5'h13   : reg_data_out = slv_reg19;
	        5'h14   : reg_data_out = slv_reg20;
	        5'h15   : reg_data_out = slv_reg21;
	        5'h16   : reg_data_out = slv_reg22;
	        5'h17   : reg_data_out = slv_reg23;
	        5'h18   : reg_data_out = slv_reg24;
	        5'h19   : reg_data_out = slv_reg25;
	        5'h1A   : reg_data_out = slv_reg26;
	        5'h1B   : reg_data_out = slv_reg27;
	        5'h1C   : reg_data_out = slv_reg28;
	        5'h1D   : reg_data_out = slv_reg29;
	        5'h1E   : reg_data_out = slv_reg30;
	        5'h1F   : reg_data_out = slv_reg31;
	        default : reg_data_out = 0;
	      endcase
	end

	// Output register or memory read data
	always @( posedge S_AXI_ACLK )
	begin
	  if ( S_AXI_ARESETN == 1'b0 )
	    begin
	      axi_rdata  <= 0;
	    end
	  else
	    begin
	      // When there is a valid read address (S_AXI_ARVALID) with
	      // acceptance of read address by the slave (axi_arready),
	      // output the read data
	      if (slv_reg_rden)
	        begin
	          axi_rdata <= reg_data_out;     // register read data
	        end
	    end
	end

	// Add user logic here

	// User logic ends
	//
////////////////////////////////////////////////////////////////////////////////
//
// Formal Verification section begins here.
//
// The following code was not part of the original Xilinx demo.
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = 4;

	wire	[(F_LGDEPTH-1):0]	f_axi_awr_outstanding,
					f_axi_wr_outstanding,
					f_axi_rd_outstanding;

	//
	// Connect our slave to the AXI-lite property set
	//
	faxil_slave #(
		// {{{
		// .C_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
			.C_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
			.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) properties(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awaddr(S_AXI_AWADDR),
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
		.f_axi_awr_outstanding(f_axi_awr_outstanding)
		// }}}
	);

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Properties necessary to pass induction
	// --- assuming we make it that far (we won't)
	//
	//
	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(f_axi_rd_outstanding == ((S_AXI_RVALID)? 1:0));
		assert(f_axi_wr_outstanding == ((S_AXI_BVALID)? 1:0));
	end

	always @(*)
		assert(f_axi_awr_outstanding == f_axi_wr_outstanding);

	////////////////////////////////////////////////////////////////////////
	//
	//
	// Cover properties
	//
	//
	// Make sure it is possible to change our register
	always @(posedge S_AXI_ACLK)
		cover($changed(slv_reg0)&&(slv_reg0 == 32'hdeadbeef));

	always @(posedge S_AXI_ACLK)
		cover((axi_rvalid)&&(axi_rdata == 32'hdeadbeef)
			&&($past(axi_araddr[ADDR_LSB+OPT_MEM_ADDR_BITS:ADDR_LSB] == 0)));

	// Make sure it is possible to read from our register
	always @(posedge S_AXI_ACLK)
		cover($past(reg_data_out == slv_reg0)
			&&($past(axi_araddr[ADDR_LSB+OPT_MEM_ADDR_BITS:ADDR_LSB])==0)
	        	&&(axi_rdata == slv_reg0));

	// Performance test.  See if we can retire a request on every other
	// instruction
	//
	// --- This first pair of cover statements will pass as written
	//
	// First a write check
	always @(posedge S_AXI_ACLK)
		cover( ((S_AXI_BVALID)&&(S_AXI_BREADY))
			&&(!$past((S_AXI_BVALID)&&(S_AXI_BREADY),1))
			&&( $past((S_AXI_BVALID)&&(S_AXI_BREADY),2))
			&&(!$past((S_AXI_BVALID)&&(S_AXI_BREADY),3)));

	// Now a read check
	always @(posedge S_AXI_ACLK)
		cover( ((S_AXI_RVALID)&&(S_AXI_RREADY))
			&&(!$past((S_AXI_RVALID)&&(S_AXI_RREADY),1))
			&&( $past((S_AXI_RVALID)&&(S_AXI_RREADY),2))
			&&(!$past((S_AXI_RVALID)&&(S_AXI_RREADY),3)));

	// Now let's see if we can retire one value every clock tick
	//
	// --- These two cover statements will fail, even though the ones
	//     above will pass.  This is why I call the design "crippled".
	//
	// First a write check
	/*
	always @(posedge S_AXI_ACLK)
		cover( ((S_AXI_BVALID)&&(S_AXI_BREADY))
			&&($past((S_AXI_BVALID)&&(S_AXI_BREADY),1))
			&&($past((S_AXI_BVALID)&&(S_AXI_BREADY),2))
			&&($past((S_AXI_BVALID)&&(S_AXI_BREADY),3)));

	// Now a read check
	always @(posedge S_AXI_ACLK)
		cover( ((S_AXI_RVALID)&&(S_AXI_RREADY))
			&&($past((S_AXI_RVALID)&&(S_AXI_RREADY),1))
			&&($past((S_AXI_RVALID)&&(S_AXI_RREADY),2))
			&&($past((S_AXI_RVALID)&&(S_AXI_RREADY),3)));
	*/

	// Now let's spend some time to develop a more complicated read
	// trace, showing the capabilities of the core.  We'll avoid the
	// broken parts of the core, and just present ... something useful.
	//
	reg	[12:0]	fr_rdcover, fw_rdcover;

	initial	fr_rdcover = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fr_rdcover <= 0;
	else
		fr_rdcover <= fw_rdcover;

	always @(*)
	if ((!S_AXI_ARESETN)||(S_AXI_AWVALID)||(S_AXI_WVALID))
		fw_rdcover = 0;
	else begin
		//
		// A basic read request
		fw_rdcover[0] = (S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[1] = fr_rdcover[0]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[2] = fr_rdcover[1]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[3] = fr_rdcover[2]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[4] = fr_rdcover[3]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		//
		// A high speed/pipelined read request
		fw_rdcover[5] = fr_rdcover[4]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[6] = fr_rdcover[5]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[7] = fr_rdcover[6]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[8] = fr_rdcover[7]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[9] = fr_rdcover[8]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[10] = fr_rdcover[9]
				&&(S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[11] = fr_rdcover[10]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		fw_rdcover[12] = fr_rdcover[11]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
	end

	always @(*)
	begin
		cover(fw_rdcover[0]);
		cover(fw_rdcover[1]);
		cover(fw_rdcover[2]);
		cover(fw_rdcover[3]);
		cover(fw_rdcover[4]);
		cover(fw_rdcover[5]); //
		cover(fw_rdcover[6]);
		cover(fw_rdcover[7]);
		cover(fw_rdcover[8]);
		cover(fw_rdcover[9]);
		cover(fw_rdcover[10]);
		cover(fw_rdcover[11]);
		cover(fw_rdcover[12]);
	end

	//
	// Now let's repeat our complicated cover approach for the write
	// channel.
	//
	reg	[24:0]	fr_wrcover, fw_wrcover;

	initial	fr_wrcover = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fr_wrcover <= 0;
	else
		fr_wrcover <= fw_wrcover;

	always @(*)
	if ((!S_AXI_ARESETN)||(S_AXI_ARVALID)||(!S_AXI_BREADY))
		fw_wrcover = 0;
	else begin
		//
		// A basic (synchronized) write request
		fw_wrcover[0] = (S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[1] = fr_wrcover[0]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[2] = fr_wrcover[1]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[3] = fr_wrcover[2]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[4] = fr_wrcover[3]
				&&(!S_AXI_ARVALID)
				&&(S_AXI_RREADY);
		//
		// Address before data
		fw_wrcover[5] = fr_wrcover[4]
				&&(S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[6] = fr_wrcover[5]
				&&(S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[7] = fr_wrcover[6]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[8] = fr_wrcover[7]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[9] = fr_wrcover[8]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[10] = fr_wrcover[9]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		//
		// Data before address
		fw_wrcover[11] = fr_wrcover[10]
				&&(!S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[12] = fr_wrcover[11]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[13] = fr_wrcover[12]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[14] = fr_wrcover[13]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[15] = fr_wrcover[14]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		//
		// A high speed/pipelined read request
		fw_wrcover[16] = fr_wrcover[15]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[17] = fr_wrcover[16]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[18] = fr_wrcover[17]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[19] = fr_wrcover[18]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[20] = fr_wrcover[19]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[21] = fr_wrcover[20]
				&&(S_AXI_AWVALID)
				&&(S_AXI_WVALID);
		fw_wrcover[22] = fr_wrcover[21]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[23] = fr_wrcover[22]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
		fw_wrcover[24] = fr_wrcover[23]
				&&(!S_AXI_AWVALID)
				&&(!S_AXI_WVALID);
	end

	always @(*)
	begin
		cover(fw_wrcover[0]);
		cover(fw_wrcover[1]);
		cover(fw_wrcover[2]);
		cover(fw_wrcover[3]);
		cover(fw_wrcover[4]);
		cover(fw_wrcover[5]); //
		cover(fw_wrcover[6]);
		cover(fw_wrcover[7]);
		cover(fw_wrcover[8]);
		cover(fw_wrcover[9]);
		cover(fw_wrcover[11]);
		cover(fw_wrcover[12]);
		cover(fw_wrcover[13]);
		cover(fw_wrcover[14]);
		cover(fw_wrcover[15]);
		cover(fw_wrcover[16]);
		cover(fw_wrcover[17]);
		cover(fw_wrcover[18]);
		cover(fw_wrcover[19]);
		cover(fw_wrcover[20]);
		cover(fw_wrcover[21]);
		cover(fw_wrcover[22]);
		cover(fw_wrcover[23]);
		cover(fw_wrcover[24]);
	end

	//
	//
	// Bug fixes section
	//
	// The lines below contain assumptions necessary to get the design
	// to work.  They represent things Xilinx never thought of when
	// building their demo.
	//
	// The following lines are only questionable a bug
	initial	axi_arready = 1'b0;
	initial	axi_awready = 1'b0;
	initial	axi_wready  = 1'b0;
	initial	axi_bvalid  = 1'b0;
	initial	axi_rvalid  = 1'b0;

	//
	// This here is necessary to avoid the biggest bug within the design.
	//
	// If you uncomment the following two lines, the design will work as
	// intended.  Only ... the bus now has more requirements to it.
	//
	always @(posedge S_AXI_ACLK)
	if (OPT_ASSUME_NO_ERRORS && $past(S_AXI_ARESETN))
		assume((S_AXI_RREADY)&&(S_AXI_BREADY));

	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_ARPROT, S_AXI_AWPROT,
	       axi_awaddr[1:0], axi_araddr[1:0]	};
	// verilator lint_on UNUSED
`endif
endmodule
