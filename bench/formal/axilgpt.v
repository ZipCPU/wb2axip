module axilgpt (
    input wire clk,               // Clock input
    input wire resetn,            // Active low reset
    // AXI-Lite Write Address Channel
    input wire [31:0] AWADDR,     // Write Address
    input wire AWVALID,           // Write Address valid
    output wire AWREADY,          // Write Address ready
    input wire [31:0] WDATA,      // Write Data
    input wire [3:0] WSTRB,       // Write strobes
    input wire WVALID,            // Write Data valid
    output wire WREADY,           // Write Data ready
    output wire BVALID,           // Write Response valid
    input wire BREADY,            // Write Response ready
    // AXI-Lite Read Address Channel
    input wire [31:0] ARADDR,     // Read Address
    input wire ARVALID,           // Read Address valid
    output wire ARREADY,          // Read Address ready
    // AXI-Lite Read Data Channel
    output wire [31:0] RDATA,     // Read Data
    output wire RVALID,           // Read Data valid
    input wire RREADY             // Read Data ready
);

`ifdef	V1
    // Memory (8 registers of 32 bits each)
    reg [31:0] registers [7:0];  // 8 registers, each 32 bits wide
    
    // Internal signals
    reg awready_reg, arready_reg;
    reg bvalid_reg, rvalid_reg;
    reg [31:0] rdata_reg;

    // AXI-Lite Slave State Machine
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            // Reset all registers
            registers[0] <= 32'h0;
            registers[1] <= 32'h0;
            registers[2] <= 32'h0;
            registers[3] <= 32'h0;
            registers[4] <= 32'h0;
            registers[5] <= 32'h0;
            registers[6] <= 32'h0;
            registers[7] <= 32'h0;
            awready_reg <= 1'b0;
            arready_reg <= 1'b0;
            bvalid_reg <= 1'b0;
            rvalid_reg <= 1'b0;
        end else begin
            // Write Address Handshake
            if (AWVALID && !awready_reg) begin
                awready_reg <= 1'b1;
            end else if (AWVALID && AWREADY) begin
                awready_reg <= 1'b0;
            end
            
            // Write Data Handshake
            if (WVALID && AWREADY) begin
                if (WSTRB[0]) registers[AWADDR[4:2]] <= WDATA[7:0]; // byte 0
                if (WSTRB[1]) registers[AWADDR[4:2]] <= WDATA[15:8]; // byte 1
                if (WSTRB[2]) registers[AWADDR[4:2]] <= WDATA[23:16]; // byte 2
                if (WSTRB[3]) registers[AWADDR[4:2]] <= WDATA[31:24]; // byte 3
                bvalid_reg <= 1'b1;   // Write response valid
            end else begin
                bvalid_reg <= 1'b0;   // Write response invalid
            end

            // Read Address Handshake
            if (ARVALID && !arready_reg) begin
                arready_reg <= 1'b1;
            end else if (ARVALID && ARREADY) begin
                arready_reg <= 1'b0;
            end

            // Read Data Handshake
            if (ARVALID && ARREADY) begin
                rdata_reg <= registers[ARADDR[4:2]]; // Access the register based on address
                rvalid_reg <= 1'b1;
            end else begin
                rvalid_reg <= 1'b0;
            end
        end
    end

    // Output assignments
    assign AWREADY = awready_reg;
    assign WREADY = AWREADY;   // Once AWREADY is high, data can be written
    assign BVALID = bvalid_reg;
    assign ARREADY = arready_reg;
    assign RVALID = rvalid_reg;
    assign RDATA = rdata_reg;
`else

    // Memory (8 registers of 32 bits each)
    reg [31:0] registers [7:0];  // 8 registers, each 32 bits wide
    
    // Internal signals
    reg awready_reg, wready_reg;
    reg bvalid_reg;
    reg arready_reg, rvalid_reg;
    reg [31:0] rdata_reg;
    reg [31:0] awaddr_reg;  // Buffer for AWADDR
    reg [31:0] wdata_reg;   // Buffer for WDATA
    reg [31:0] araddr_reg;  // Buffer for ARADDR
    reg wvalid_reg;         // Buffered WVALID state
    reg awvalid_reg;        // Buffered AWVALID state
    reg arvalid_reg;        // Buffered ARVALID state

    // AXI-Lite Write Address Phase Logic (AWVALID / AWREADY)
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            awready_reg <= 1'b0;
            awvalid_reg <= 1'b0;
        end else begin
            if (AWVALID && !awvalid_reg) begin
                awaddr_reg <= AWADDR;  // Latch address
                awvalid_reg <= 1'b1;   // Mark address as valid
                awready_reg <= 1'b1;   // Indicate readiness for the address
            end else if (AWREADY) begin
                awready_reg <= 1'b0;   // Address processing complete
            end
        end
    end

    // AXI-Lite Write Data Phase Logic (WVALID / WREADY)
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            wready_reg <= 1'b0;
            wvalid_reg <= 1'b0;
            bvalid_reg <= 1'b0;   // Reset BVALID on reset
        end else begin
            if (awvalid_reg && WVALID && !wvalid_reg) begin
                wdata_reg <= WDATA;  // Latch write data
                registers[awaddr_reg[4:2]] <= wdata_reg;  // Write to the register
                wvalid_reg <= 1'b1;   // Mark data as valid
            end

            // Assert WREADY when the slave is ready to accept data
            if (awvalid_reg && !wvalid_reg) begin
                wready_reg <= 1'b1;  // Slave ready for data when address is valid
            end else if (wvalid_reg && BREADY) begin
                bvalid_reg <= 1'b1;   // Assert BVALID to complete write transaction
            end

            // Deassert BVALID when master signals readiness with BREADY
            if (bvalid_reg && BREADY) begin
                bvalid_reg <= 1'b0;   // Clear BVALID after the write response is acknowledged
                wvalid_reg <= 1'b0;   // Clear wvalid_reg after write completion
                wready_reg <= 1'b0;   // Clear WREADY after transaction is complete
            end
        end
    end

    // AXI-Lite Read Address Phase Logic (ARVALID / ARREADY)
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            arready_reg <= 1'b0;
            arvalid_reg <= 1'b0;
        end else begin
            if (ARVALID && !arvalid_reg) begin
                araddr_reg <= ARADDR;  // Latch read address
                arvalid_reg <= 1'b1;   // Mark read address as valid
                arready_reg <= 1'b1;   // Indicate readiness for the read address
            end else if (ARREADY) begin
                arready_reg <= 1'b0;   // Read address processing complete
            end
        end
    end

    // AXI-Lite Read Data Phase Logic (RVALID / RREADY)
    always @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            rvalid_reg <= 1'b0;
        end else begin
            // Assert RVALID and provide read data when the read address is valid
            if (arvalid_reg && !rvalid_reg) begin
                rdata_reg <= registers[araddr_reg[4:2]];  // Read data from the register
                rvalid_reg <= 1'b1;  // Assert RVALID when read data is available
            end

            // Deassert RVALID when the master acknowledges with RREADY
            if (rvalid_reg && RREADY) begin
                rvalid_reg <= 1'b0;  // Clear RVALID after read completion
            end
        end
    end

    // Output Assignments (Final connections to the interface)
    assign AWREADY = awready_reg;  // Address ready when slave is ready for address phase
    assign WREADY = awvalid_reg && !wvalid_reg;  // Data ready when address is valid, but no data accepted yet
    assign BVALID = bvalid_reg;   // Write response valid when transaction is complete
    assign ARREADY = arready_reg;  // Read address ready when slave is ready for address phase
    assign RVALID = rvalid_reg;   // Read data valid when data is available
    assign RDATA = rdata_reg;     // Read data to be sent to the master

`endif

`ifdef	FORMAL
	faxil_slave #(
		// {{{
		.C_AXI_ADDR_WIDTH(32),
		// F_OPT_BRESP: Allow any type of write response.  If set clear, then
		// error responses are disallowed.
		.F_OPT_BRESP(1'b0),
		// F_OPT_RRESP, if cleared, will disallow error responses
		.F_OPT_RRESP(1'b0),
		// F_OPT_ASSUME_RESET, if set, will cause the design to *assume* the
		// existence of a correct reset, rather than asserting it.  It is
		// appropriate anytime the reset logic is outside of the circuit being
		// examined
		// F_OPT_ASSUME_RESET = 1'b1,
		// F_OPT_NO_RESET = 1'b1,
		//
		// F_OPT_ASYNC_RESET is for those designs that will reset the channels
		// using an asynchronous reset.  In these cases, the stability
		// properties only apply when the async reset is not asserted.
		// Likewise, when F_OPT_ASYNC_RESET is set, the reset assertions are
		// applied *on the same clock cycle*, in addition to one cycle later.
		.F_OPT_ASYNC_RESET(1'b1),
		// F_OPT_COVER_BURST = 0,
		// F_LGDEPTH is the number of bits necessary to count the maximum
		// number of items in flight.
		// F_LGDEPTH	= 4,
		// F_AXI_MAXWAIT is the maximum number of clock cycles the
		// master should have to wait for a slave to raise its ready flag to
		// accept a request.  Set to zero for no limit.
		// F_AXI_MAXWAIT  = 12,
		// F_AXI_MAXRSTALL is the maximum number of clock cycles the
		// slave should have to wait with a return valid signal high, but
		// while the master's return ready signal is low.  Set to zero for no
		// limit.
		// parameter			F_AXI_MAXRSTALL= 12,
		// F_AXI_MAXDELAY is the maximum number of clock cycles between request
		// and response within the slave.  Set this to zero for no limit.
		// parameter			F_AXI_MAXDELAY = 12,
		//
		.F_OPT_INITIAL(1'b0)
		// }}}
	) faxil (
		// {{{
		.i_clk(clk),
		.i_axi_reset_n(resetn),

		// AXI write address channel signals
		// {{{
		.i_axi_awvalid(AWVALID),
		.i_axi_awready(AWREADY),
		.i_axi_awaddr(AWADDR),	// Write address
		.i_axi_awprot(3'h0),	// Protection
		// }}}
		// AXI write data channel signals
		// {{{
		.i_axi_wvalid(WVALID),
		.i_axi_wready(WREADY),
		.i_axi_wdata(WDATA),	// Write data
		.i_axi_wstrb(WSTRB),	// Write strobes
		// }}}
		// AXI write response channel signals
		// {{{
		.i_axi_bvalid(BVALID),
		.i_axi_bready(BREADY),
		.i_axi_bresp(2'b00),	// Wr response
		// }}}
		// AXI read address channel signals
		// {{{
		.i_axi_arvalid(ARVALID),
		.i_axi_arready(ARREADY),
		.i_axi_araddr(ARADDR),	// Read address
		.i_axi_arprot(3'h0),	// Protection
		// }}}
		// AXI read data channel signals
		// {{{
		.i_axi_rvalid(RVALID),
		.i_axi_rready(RREADY),
		.i_axi_rdata(RDATA),	// Read data
		.i_axi_rresp(2'b00),	// Read response
		// }}}
		// .f_axi_rd_outstanding,
		// .f_axi_wr_outstanding,
		// .f_axi_awr_outstanding
		// }}}
	);

`endif
endmodule
