////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xlnxstream_2018_3
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	To test the formal tools on an AXI stream master core that is
//		"known" to work.  This core was generated via the IP packager
//	in Vivado 2018.3.  Sadly, it's broken in a couple of ways, one which
//	is prominently the TLAST signal which may be set even through the
//	channel is stalled.  Feel free to try it out.
//
//	This core will fail a verification check.
//
// Creator:	Vivado, 2018.3
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
//
`timescale 1 ns / 1 ps

module xlnxstream_2018_3 #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line

		// Width of S_AXIS address bus. The slave accepts the read and write addresses of width C_M_AXIS_TDATA_WIDTH.
		parameter integer C_M_AXIS_TDATA_WIDTH	= 32,
		// Start count is the number of clock cycles the master will wait before initiating/issuing any transaction.
		parameter integer C_M_START_COUNT	= 32
	)
	(
		// Users to add ports here

		// User ports ends
		// Do not modify the ports beyond this line

		// Global ports
		input wire  M_AXIS_ACLK,
		//
		input wire  M_AXIS_ARESETN,
		// Master Stream Ports. TVALID indicates that the master
		// is driving a valid transfer, A transfer takes place
		// when both TVALID and TREADY are asserted.
		output wire  M_AXIS_TVALID,
		// TDATA is the primary payload that is used to provide the
		// data that is passing across the interface from the master.
		output wire [C_M_AXIS_TDATA_WIDTH-1 : 0] M_AXIS_TDATA,
		// TSTRB is the byte qualifier that indicates whether the
		// content of the associated byte of TDATA is processed as a
		// data byte or a position byte.
		output wire [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0] M_AXIS_TSTRB,
		// TLAST indicates the boundary of a packet.
		output wire  M_AXIS_TLAST,
		// TREADY indicates that the slave can accept a transfer in
		// the current cycle.
		input wire  M_AXIS_TREADY
	);
	// Total number of output data
	localparam NUMBER_OF_OUTPUT_WORDS = 8;

	// function called clogb2 that returns an integer which has the
	// value of the ceiling of the log base 2.
	function integer clogb2 (input integer bit_depth);
	begin
		for(clogb2=0; bit_depth>0; clogb2=clogb2+1)
			bit_depth = bit_depth >> 1;
	end endfunction

	// WAIT_COUNT_BITS is the width of the wait counter.
	localparam integer WAIT_COUNT_BITS = clogb2(C_M_START_COUNT-1);

	// bit_num gives the minimum number of bits needed to address 'depth'
	// size of FIFO.
	localparam bit_num  = clogb2(NUMBER_OF_OUTPUT_WORDS);

	// Define the states of state machine
	// The control state machine oversees the writing of input streaming
	// data to the FIFO, and outputs the streaming data from the FIFO
	parameter [1:0] IDLE = 2'b00,	// This is the initial/idle state

		INIT_COUNTER  = 2'b01,	// This state initializes the counter,
					// once the counter reaches
					// C_M_START_COUNT count, the state
					// machine changes state to SEND_STREAM
		SEND_STREAM   = 2'b10;	// In this state the
					// stream data is output through M_AXIS_TDATA
	// State variable
	reg [1:0] mst_exec_state;
	// Example design FIFO read pointer
	reg [bit_num-1:0] read_pointer;

	// AXI Stream internal signals
	// wait counter. The master waits for the user defined number of
	// clock cycles before initiating a transfer.
	reg [WAIT_COUNT_BITS-1 : 0] 	count;
	//streaming data valid
	wire  	axis_tvalid;
	//streaming data valid delayed by one clock cycle
	reg  	axis_tvalid_delay;
	//Last of the streaming data
	wire  	axis_tlast;
	//Last of the streaming data delayed by one clock cycle
	reg  	axis_tlast_delay;
	//FIFO implementation signals
	reg [C_M_AXIS_TDATA_WIDTH-1 : 0] 	stream_data_out;
	wire  	tx_en;
	//The master has issued all the streaming data stored in FIFO
	reg  	tx_done;


	// I/O Connections assignments

	assign M_AXIS_TVALID	= axis_tvalid_delay;
	assign M_AXIS_TDATA	= stream_data_out;
	assign M_AXIS_TLAST	= axis_tlast_delay;
	assign M_AXIS_TSTRB	= {(C_M_AXIS_TDATA_WIDTH/8){1'b1}};


	// Control state machine implementation
	always @(posedge M_AXIS_ACLK)
	if (!M_AXIS_ARESETN)
	// Synchronous reset (active low)
	begin
		mst_exec_state <= IDLE;
		count <= 0;
	end else case (mst_exec_state)
	IDLE:
		// The slave starts accepting tdata when
		// there tvalid is asserted to mark the
		// presence of valid streaming data
		//if ( count == 0 )
		//  begin
		mst_exec_state  <= INIT_COUNTER;
		//  end
		//else
		//  begin
		//    mst_exec_state  <= IDLE;
		//  end

	INIT_COUNTER:
		// The slave starts accepting tdata when
		// there tvalid is asserted to mark the
		// presence of valid streaming data
		if ( count == C_M_START_COUNT - 1 )
			mst_exec_state  <= SEND_STREAM;
		else begin
			count <= count + 1;
			mst_exec_state  <= INIT_COUNTER;
		end

	SEND_STREAM:
		// The example design streaming master functionality starts when
		// the master drives output tdata from the FIFO and the slave
		// has finished storing the S_AXIS_TDATA
		if (tx_done)
			mst_exec_state <= IDLE;
		else
			mst_exec_state <= SEND_STREAM;
	endcase


	//tvalid generation
	//axis_tvalid is asserted when the control state machine's state
	// is SEND_STREAM and number of output streaming data is less than
	// the NUMBER_OF_OUTPUT_WORDS.
	assign axis_tvalid = ((mst_exec_state == SEND_STREAM) && (read_pointer < NUMBER_OF_OUTPUT_WORDS));

	// AXI tlast generation
	// axis_tlast is asserted number of output streaming data
	// is NUMBER_OF_OUTPUT_WORDS-1 (0 to NUMBER_OF_OUTPUT_WORDS-1)
	assign axis_tlast = (read_pointer == NUMBER_OF_OUTPUT_WORDS-1);


	// Delay the axis_tvalid and axis_tlast signal by one clock cycle
	// to match the latency of M_AXIS_TDATA
	always @(posedge M_AXIS_ACLK)
	if (!M_AXIS_ARESETN)
	begin
		axis_tvalid_delay <= 1'b0;
		axis_tlast_delay <= 1'b0;
	end else begin
		axis_tvalid_delay <= axis_tvalid;
		axis_tlast_delay <= axis_tlast;
	end


	//read_pointer pointer
	always@(posedge M_AXIS_ACLK)
	if(!M_AXIS_ARESETN)
	begin
		read_pointer <= 0;
		tx_done <= 1'b0;
	end else if (read_pointer <= NUMBER_OF_OUTPUT_WORDS-1)
	begin
		if (tx_en)
		// read pointer is incremented after every read from the FIFO
		// when FIFO read signal is enabled.
		begin
			read_pointer <= read_pointer + 1;
			tx_done <= 1'b0;
		end
	end else if (read_pointer == NUMBER_OF_OUTPUT_WORDS)
	begin
		// tx_done is asserted when NUMBER_OF_OUTPUT_WORDS numbers
		// of streaming data has been out.
		tx_done <= 1'b1;
	end


	//FIFO read enable generation
	assign tx_en = M_AXIS_TREADY && axis_tvalid;

		// Streaming output data is read from FIFO
	always @( posedge M_AXIS_ACLK )
	if(!M_AXIS_ARESETN)
		stream_data_out <= 1;
	else if (tx_en)// && M_AXIS_TSTRB[byte_index]
		stream_data_out <= read_pointer + 32'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Add user logic here
	//
	// The below initial lines, and FORMAL section following, were not in
	// Xilinx's original demo example.
	//
	// This initial logic is used to keep the formal proof consistent
	// below.  It's not strictly needed, neither was it part of Xilinx's
	// original example demo.
	initial count = 0;
	initial mst_exec_state = IDLE;
	initial	read_pointer = 0;
	initial tx_done = 0;
	// User logic ends
`ifdef	FORMAL
	localparam	F_LGDEPTH = $clog2(NUMBER_OF_OUTPUT_WORDS+1)+2;
	localparam	AW  = 1;
	localparam	IDW = 1;

	wire	[F_LGDEPTH-1:0]	f_bytecount;
	wire	[AW+IDW-1:0]	f_routecheck;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge M_AXIS_ACLK)
		f_past_valid <= 1;

	//
	// Insist that the proof starts in reset
	//
	always @(*)
	if (!f_past_valid)
		assume(!M_AXIS_ARESETN);

	//
	// Insist on reset values
	//
	always @(posedge M_AXIS_ACLK)
	if (!f_past_valid || $past(!M_AXIS_ARESETN))
	begin
		assert(mst_exec_state == IDLE);
		assert(read_pointer == 0);
		assert(count == 0);
		assert(!tx_done);
	end

	//
	faxis_master #(
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_PACKET({NUMBER_OF_OUTPUT_WORDS, 2'b00}+4),
		.C_S_AXI_DATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
		.OPT_ASYNC_RESET(1'b0),
		.C_S_AXI_ADDR_WIDTH(AW),
		.C_S_AXI_ID_WIDTH(IDW),
		.C_S_AXI_USER_WIDTH(1))
	axi_stream_check(.i_aclk(M_AXIS_ACLK),
		.i_aresetn(M_AXIS_ARESETN),
		.i_tvalid(M_AXIS_TVALID),
		.i_tready(M_AXIS_TREADY),
		.i_tdata(M_AXIS_TDATA),
		.i_tstrb(M_AXIS_TSTRB),
		.i_tkeep(4'hf),
		.i_tid(0),
		.i_tdest(0),
		.i_tuser(0),
		.i_tlast(M_AXIS_TLAST),
		.f_bytecount(f_bytecount),
		.f_routecheck(f_routecheck));

// `define	INDUCTION_PROOF
`ifdef	INDUCTION_PROOF
	always @(*)
		assert(count <= C_M_START_COUNT-1);

	always @(*)
	if (count != C_M_START_COUNT-1)
	begin
		assert(!M_AXIS_TVALID);
		assert(read_pointer == 0);
	end

	always @(*)
	if (tx_done)
	begin
		assert(read_pointer == NUMBER_OF_OUTPUT_WORDS);
		// assert();
	end

	always @(*)
		assert(read_pointer <= NUMBER_OF_OUTPUT_WORDS);

	always @(*)
	if (tx_done)
		assert(!M_AXIS_TVALID);

	always @(*)
	if ((read_pointer > 0)&&(!tx_done))
		assert(M_AXIS_TVALID);

	always @(posedge M_AXIS_ACLK)
	if (f_past_valid)
		cover(M_AXIS_ARESETN && !M_AXIS_TVALID
			&& $past(M_AXIS_TVALID && M_AXIS_TLAST));

	always @(*)
	if (tx_done || M_AXIS_TVALID)
		assert(count == C_M_START_COUNT-1);

	always @(*)
		assert((mst_exec_state == IDLE)
			||(mst_exec_state == INIT_COUNTER)
			||(mst_exec_state == SEND_STREAM));

	// If you actually want to get induction to pass, you'll also need
	// to assume TREADY
	// always @(*)
	//	assume(M_AXIS_TREADY);
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	final_counter = 0;

	initial	final_counter = 0;
	always @(posedge M_AXIS_ACLK)
	if (!M_AXIS_ARESETN)
		final_counter <= 0;
	else if (tx_done)
		final_counter <= final_counter + 1;

	always @(*)
		cover(tx_done);

	always @(*)
		cover(&final_counter);
`endif
endmodule
