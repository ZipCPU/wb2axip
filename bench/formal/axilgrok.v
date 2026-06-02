////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/formal/axilgrok.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This module was designed by Grok, upon a request that Grok
//		design an AXI-Lite interface in Verilog, with at least 4
//	user registers.
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Gisselquist Technology asserts no copyright interest in Grok's (broken
// AXI-Lite slave) output product.  Gisselquist Technology does assert
// ownership and copyright over the formal properties at the end of this file,
// under the `ifdef FORMAL` section.  This section is ...
//
// Copyright (C) 2025, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
// }}}
//	http://www.apache.org/licenses/LICENSE-2.0
// {{{
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
// }}}

// The following is the Grok design with minimal updates (i.e. name change,
// some spacing updates, etc.).

// =============================================================================
// Module: axi_lite_reg_bank
// Description:
//   AXI-Lite slave with 4 independent 32-bit control/status registers.
//   - Address map: 0x00, 0x04, 0x08, 0x0C
//   - All registers are read/write
//   - Fully compliant with AMBA AXI4-Lite specification
//   - Parameterizable base address and data width (default 32-bit)
//
// 20251110 - This was created, by Grok, in an answer to the prompt:
//
//	Grok: Generate a Verilog module containing an AXI-Lite interface,
//		controlling at least 4 separate 32b registers
//
// =============================================================================

`timescale 1ns / 1ps

module axilgrok #(	// Was axi_lite_reg_bank
    parameter integer C_S_AXI_ADDR_WIDTH = 4,   // 16-byte address space (4 registers)
    parameter integer C_S_AXI_DATA_WIDTH = 32
) (
    // AXI-Lite Slave Interface
    input  wire                               s_axi_aclk,
    input  wire                               s_axi_aresetn,

    // Write Address Channel
    input  wire [C_S_AXI_ADDR_WIDTH-1:0]      s_axi_awaddr,
    input  wire [2:0]                         s_axi_awprot,
    input  wire                               s_axi_awvalid,
    output wire                               s_axi_awready,

    // Write Data Channel
    input  wire [C_S_AXI_DATA_WIDTH-1:0]      s_axi_wdata,
    input  wire [(C_S_AXI_DATA_WIDTH/8)-1:0]  s_axi_wstrb,
    input  wire                               s_axi_wvalid,
    output wire                               s_axi_wready,

    // Write Response Channel
    output wire [1:0]                         s_axi_bresp,
    output wire                               s_axi_bvalid,
    input  wire                               s_axi_bready,

    // Read Address Channel
    input  wire [C_S_AXI_ADDR_WIDTH-1:0]      s_axi_araddr,
    input  wire [2:0]                         s_axi_arprot,
    input  wire                               s_axi_arvalid,
    output wire                               s_axi_arready,

    // Read Data Channel
    output wire [C_S_AXI_DATA_WIDTH-1:0]      s_axi_rdata,
    output wire [1:0]                         s_axi_rresp,
    output wire                               s_axi_rvalid,
    input  wire                               s_axi_rready,

    // User Register Interface
    output wire [C_S_AXI_DATA_WIDTH-1:0]      reg_0_out,
    output wire [C_S_AXI_DATA_WIDTH-1:0]      reg_1_out,
    output wire [C_S_AXI_DATA_WIDTH-1:0]      reg_2_out,
    output wire [C_S_AXI_DATA_WIDTH-1:0]      reg_3_out,
    input  wire [C_S_AXI_DATA_WIDTH-1:0]      reg_0_in,
    input  wire [C_S_AXI_DATA_WIDTH-1:0]      reg_1_in,
    input  wire [C_S_AXI_DATA_WIDTH-1:0]      reg_2_in,
    input  wire [C_S_AXI_DATA_WIDTH-1:0]      reg_3_in
);

    // -------------------------------------------------------------------------
    // Internal Signals
    // -------------------------------------------------------------------------
    localparam integer ADDR_LSB = (C_S_AXI_DATA_WIDTH/32) + 1;
    localparam integer REG_COUNT = 4;

    reg [C_S_AXI_ADDR_WIDTH-1:0]  axi_awaddr;
    reg                           axi_awready;
    reg                           axi_wready;
    reg [1:0]                     axi_bresp;
    reg                           axi_bvalid;
    reg [C_S_AXI_ADDR_WIDTH-1:0]  axi_araddr;
    reg                           axi_arready;
    reg [C_S_AXI_DATA_WIDTH-1:0]  axi_rdata;
    reg [1:0]                     axi_rresp;
    reg                           axi_rvalid;

    // Register bank
    reg [C_S_AXI_DATA_WIDTH-1:0]  reg_bank [0:REG_COUNT-1];
    integer                       i;

    // Address decoding
    wire [1:0]                    addr_offset;
    assign addr_offset = s_axi_awaddr[ADDR_LSB+:2] & {(2){s_axi_awvalid & s_axi_awready}} |
                         s_axi_araddr[ADDR_LSB+:2] & {(2){s_axi_arvalid & s_axi_arready}};

    // -------------------------------------------------------------------------
    // AXI-Lite Write Logic
    // -------------------------------------------------------------------------
    always @(posedge s_axi_aclk) begin
        if (s_axi_aresetn == 1'b0) begin
            axi_awready <= 1'b0;
        end else begin
            if (~axi_awready && s_axi_awvalid) begin
                axi_awready <= 1'b1;
                axi_awaddr  <= s_axi_awaddr;
            end else begin
                axi_awready <= 1'b0;
            end
        end
    end
    assign s_axi_awready = axi_awready;

    always @(posedge s_axi_aclk) begin
        if (s_axi_aresetn == 1'b0) begin
            axi_wready <= 1'b0;
        end else begin
            if (~axi_wready && s_axi_wvalid && axi_awready) begin
                axi_wready <= 1'b1;
            end else begin
                axi_wready <= 1'b0;
            end
        end
    end
    assign s_axi_wready = axi_wready;

//
// This is *BROKEN*.  BVALID should be set upon a *single* condition.  When
// using a skid buffer, BVALID should be set any time ...
//
//	AWVALID && WVALID && (!BVALID || BREADY).
//
// When not using a skid buffer, AWREADY must equal WREADY and be set by the
// above formula one clock later.  If done so, then only AWREADY need be
// checked below.  By checking for AWVALID, AWREADY, WVALID, and WREADY,
// we allow BVALID to (potentially) never be set (which is indeed what
// happens). -- Dan
//

    // Write response
    always @(posedge s_axi_aclk) begin
        if (s_axi_aresetn == 1'b0) begin
            axi_bvalid <= 1'b0;
            axi_bresp  <= 2'b00;
        end else begin
            if (axi_awready && s_axi_awvalid && axi_wready && s_axi_wvalid && ~axi_bvalid) begin
                axi_bvalid <= 1'b1;
                axi_bresp  <= 2'b00; // OKAY
            end else if (s_axi_bready && axi_bvalid) begin
                axi_bvalid <= 1'b0;
            end
        end
    end
    assign s_axi_bresp  = axi_bresp;
    assign s_axi_bvalid = axi_bvalid;

//
// What is this logic?  I don't think it'll do what Grok thinks it will. -- Dan
//

    // Write to register bank
    always @(posedge s_axi_aclk) begin
        if (axi_wready && s_axi_wvalid && axi_awready) begin
            case (axi_awaddr[ADDR_LSB+:2])
                2'b00: reg_bank[0] <= (reg_bank[0] & ~s_axi_wstrb[3:0]*32'hFFFFFFFF) |
                                      (s_axi_wdata & s_axi_wstrb[3:0]*32'hFFFFFFFF);
                2'b01: reg_bank[1] <= (reg_bank[1] & ~s_axi_wstrb[3:0]*32'hFFFFFFFF) |
                                      (s_axi_wdata & s_axi_wstrb[3:0]*32'hFFFFFFFF);
                2'b10: reg_bank[2] <= (reg_bank[2] & ~s_axi_wstrb[3:0]*32'hFFFFFFFF) |
                                      (s_axi_wdata & s_axi_wstrb[3:0]*32'hFFFFFFFF);
                2'b11: reg_bank[3] <= (reg_bank[3] & ~s_axi_wstrb[3:0]*32'hFFFFFFFF) |
                                      (s_axi_wdata & s_axi_wstrb[3:0]*32'hFFFFFFFF);
            endcase
        end
    end

    // -------------------------------------------------------------------------
    // AXI-Lite Read Logic
    // -------------------------------------------------------------------------
    always @(posedge s_axi_aclk) begin
        if (s_axi_aresetn == 1'b0) begin
            axi_arready <= 1'b0;
        end else begin
            if (~axi_arready && s_axi_arvalid) begin
                axi_arready <= 1'b1;
                axi_araddr  <= s_axi_araddr;
            end else begin
                axi_arready <= 1'b0;
            end
        end
    end
    assign s_axi_arready = axi_arready;

//
// rvalid below is totally broken.  The condition below, for setting both
// rvalid and rdata, should be (s_axi_arvalid && s_axi_arready) (or a similar
// valid/ready signal from a skidbuffer.  However, if ARVALID and ARREADY,
// then *EVERYTHING* should happen independent of RVALID.  The dependence
// on RVALID indicates another problem.  The "true" dependence should be
// ARREADY getting set to ARVALID && (!RVALID || RREADY).  If this signal
// is to be registered (vs a skidbuffer), then only ARREADY need be checked
// below.
//
// Likewise, checking RREADY should be sufficient for lowering RVALID with
// minimal logic.
//
// -- Dan
//

    // Read data
    always @(posedge s_axi_aclk) begin
        if (s_axi_aresetn == 1'b0) begin
            axi_rvalid <= 1'b0;
            axi_rresp  <= 2'b00;
            axi_rdata  <= {C_S_AXI_DATA_WIDTH{1'b0}};
        end else begin
            if (axi_arready && s_axi_arvalid && ~axi_rvalid) begin
                axi_rvalid <= 1'b1;
                axi_rresp  <= 2'b00; // OKAY
                case (axi_araddr[ADDR_LSB+:2])
                    2'b00: axi_rdata <= reg_bank[0];
                    2'b01: axi_rdata <= reg_bank[1];
                    2'b10: axi_rdata <= reg_bank[2];
                    2'b11: axi_rdata <= reg_bank[3];
                    default: axi_rdata <= {C_S_AXI_DATA_WIDTH{1'b0}};
                endcase
            end else if (s_axi_rready && axi_rvalid) begin
                axi_rvalid <= 1'b0;
            end
        end
    end
    assign s_axi_rdata  = axi_rdata;
    assign s_axi_rresp  = axi_rresp;
    assign s_axi_rvalid = axi_rvalid;

    // -------------------------------------------------------------------------
    // External Register Outputs (combinational for low latency)
    // -------------------------------------------------------------------------
    assign reg_0_out = reg_bank[0];
    assign reg_1_out = reg_bank[1];
    assign reg_2_out = reg_bank[2];
    assign reg_3_out = reg_bank[3];

//
// No, Grok did not truly finish this design.  I'm not quite sure what the
// block below was supposed to accomplish.  Whatever it was supposed to do,
// it ... doesn't do it.  -- Dan
//

    // Optional: Allow external read inputs (e.g., status registers)
    // Here we OR them in — user can override in top-level
    genvar g;
    generate
        for (g = 0; g < REG_COUNT; g = g + 1) begin : reg_input_merge
            always @(posedge s_axi_aclk) begin
                if (s_axi_aresetn == 1'b0) begin
                    // Reset to zero or hold value?
                end else begin
                    // Example: merge external input on bit 31
                    // reg_bank[g][31] <= reg_bank[g][31] | reg_in[g][31];
                end
            end
        end
    endgenerate

//
// Yes, Grok did generate this abomination below: reg's are being assigned via
// assign statements, rather than via always @(*) or redefining the reg_bank's
// to be "wires". -- Dan
//

    // For this example, allow external inputs to be read
    assign reg_bank[0] = reg_0_in; // Override for read-through
    assign reg_bank[1] = reg_1_in;
    assign reg_bank[2] = reg_2_in;
    assign reg_bank[3] = reg_3_in;
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
// These were added by Dan Gisselquist, to see how well Grok did.  Hint: Grok
// failed to produce a bug-free AXI-Lite design.
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam		F_LGDEPTH = 4;
	localparam	[0:0]	F_READ_ONLY=1'b0, F_WRITE_ONLY=1'b0;

	wire	[F_LGDEPTH-1:0]	faxil_rd, faxil_wr, faxil_awr;

	faxil_slave #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
		.F_OPT_WRITE_ONLY(F_WRITE_ONLY),
		.F_OPT_READ_ONLY(F_READ_ONLY),
		.F_OPT_BRESP(1'b0),	// Disallow error responses
		.F_OPT_RRESP(1'b0),	// Disallow error responses
		// F_OPT_ASSUME_RESET(1'b1),
		// F_OPT_NO_RESET(1'b1),
		.F_OPT_ASYNC_RESET(1'b0),
		// parameter 			F_OPT_COVER_BURST = 0,
		.F_LGDEPTH(F_LGDEPTH),
		// F_AXI_MAXWAIT  = 12,
		// F_AXI_MAXRSTALL= 12,
		// F_AXI_MAXDELAY = 12,
		.F_OPT_INITIAL(1'b0)	// Grok didn't use initial statements
		// }}}
	) faxil (
		// {{{
		.i_clk(s_axi_aclk),	// System clock
		.i_axi_reset_n(s_axi_aresetn),

		// AXI write address channel signals
		// {{{
		.i_axi_awvalid(s_axi_awvalid),
		.i_axi_awready(s_axi_awready),
		.i_axi_awaddr(s_axi_awaddr),	// Write address
		.i_axi_awprot(s_axi_awprot),
		// }}}

		// AXI write data channel signals
		// {{{
		.i_axi_wvalid(s_axi_wvalid),
		.i_axi_wready(s_axi_wready),
		.i_axi_wdata(s_axi_wdata),
		.i_axi_wstrb(s_axi_wstrb),
		// }}}

		// AXI write response channel signals
		// {{{
		.i_axi_bvalid(s_axi_bvalid),
		.i_axi_bready(s_axi_bready),
		.i_axi_bresp(s_axi_bresp),
		// }}}

		// Read Address Channel
		// AXI read address channel signals
		// {{{
		.i_axi_arvalid(s_axi_arvalid),
		.i_axi_arready(s_axi_arready),
		.i_axi_araddr(s_axi_araddr),
		.i_axi_arprot(s_axi_arprot),
		// }}}

		// AXI read data channel signals
		// {{{
		.i_axi_rvalid(s_axi_rvalid),
		.i_axi_rready(s_axi_rready),

		.i_axi_rdata(s_axi_rdata),
		.i_axi_rresp(s_axi_rresp),
		// }}}
		.f_axi_rd_outstanding(faxil_rd),
		.f_axi_wr_outstanding(faxil_wr),
		.f_axi_awr_outstanding(faxil_awr)
		// }}}
	);

	// Failure #1: BVALID might be true on the first clock cycle
	//	Practically, this might be more of a failure in the
	//	formal property set.  We might agree that BVALID is
	//	irrelevant during reset, as long as it becomes
	//	zero later and following the reset.
	always @(*)
	if (!s_axi_aresetn)
		assume(s_axi_bvalid == 0);

	// Failure #2: Backpressure will never lower ARREADY.  Hence,
	//	enough backpressure and reads will be dropped.
	always @(*)
		assume(faxil_rd == (s_axi_rvalid ? 1 : 0));

	// Failure #3: AWREADY may get set, yet WREADY might never be
	//	set.
	always @(*)
	if (s_axi_awready)
		assume(s_axi_wvalid);

	// Failure #4: BVALID *NEVER* gets set under any conditions
	always @(*)
    	if (s_axi_aresetn)
		cover(s_axi_bvalid);

	// There might be more failures, but ... this was sufficient to
	// prove the point that Grok had no idea what it was doing.
`endif
// }}}
endmodule
