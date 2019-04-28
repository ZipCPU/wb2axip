module	axi_addr_miter(i_last_addr, i_size, i_burst, i_len);
	parameter	AW = 32,
			DW = 32;
	input	wire	[AW-1:0]	i_last_addr;
	input	wire	[2:0]		i_size; // 1b, 2b, 4b, 8b, etc
	input	wire	[1:0]		i_burst; // fixed, incr, wrap, reserved
	input	wire	[7:0]		i_len;

	localparam	DSZ = $clog2(DW)-3;

	wire	[7:0]		ref_incr;
	wire	[AW-1:0]	ref_next_addr;

	faxi_addr #(.AW(AW))
		ref(i_last_addr, i_size, i_burst, i_len,ref_incr,ref_next_addr);

	wire	[AW-1:0]	uut_next_addr;

	axi_addr #(.AW(AW), .DW(DW))
		uut(i_last_addr, i_size, i_burst, i_len, uut_next_addr);

	always @(*)
		assert(DW == (1<<(DSZ+3)));

	always @(*)
		assume(i_burst != 2'b11);

	always @(*)
		assume(i_size <= DSZ);

	always @(*)
	if (i_burst == 2'b10)
	begin
		assume((i_len == 1)
			||(i_len == 3)
			||(i_len == 7)
			||(i_len == 15));
	end

	reg	aligned;

	always @(*)
	begin
		aligned = 0;
		case(DSZ)
		3'b000: aligned = 1;
		3'b001: aligned = (i_last_addr[0] == 0);
		3'b010: aligned = (i_last_addr[1:0] == 0);
		3'b011: aligned = (i_last_addr[2:0] == 0);
		3'b100: aligned = (i_last_addr[3:0] == 0);
		3'b101: aligned = (i_last_addr[4:0] == 0);
		3'b110: aligned = (i_last_addr[5:0] == 0);
		3'b111: aligned = (i_last_addr[6:0] == 0);
		endcase
	end

	always @(*)
	if (i_burst == 2'b10)
		assume(aligned);

	always @(*)
		assert(uut_next_addr == ref_next_addr);

	always @(*)
	if (i_burst == 2'b01)
		assume(i_last_addr[AW-1:12] == ref_next_addr[AW-1:12]);

endmodule
