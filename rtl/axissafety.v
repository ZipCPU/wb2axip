////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axissafety.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	A firewall for the AXI-stream protocol.  Only handles TVALID,
//		TREADY, TDATA, TLAST and TUSER signals.
//
//	This module is designed to be a "bump in the stream" of the stream
//	protocol--a bump that can be used to detect AXI stream errors.
//	Specifically, this firewall can detect one of three errors:
//
//	1. CHANGE	The stream is stalled and something changes.  This
//			could easily be caused by a stream overflow.
//	2. PACKET LENGTH	If OPT_PACKET_LENGTH != 0, then all stream
//			packets are assumed to be OPT_PACKET_LENGTH in length.
//			Packets that are not OPT_PACKET_LENGTH in length will
//			generate a fault.
//
//			This core cannot handle dynamic packet lengths, but
//			should do just fine with detecting errors in fixed
//			length packets--such as an FFT might use.
//	3. TOO MANY STALLS
//		If OPT_MAX_STALL != 0, and the master stalls an input more than
//		OPT_MAX_STALL cycles, then a fault will be declared.
//
//	4. (Sorry--I haven't implemented a video firewall.  Video images
//		having TUSER set to start of frame will not be guaranteed
//		video stream compliant, since TUSER might still be set to the
//		wrong number.)
//
//	If a fault is detected, o_fault will be set true.  This is designed so
//	that you can trigger an ILA off of a protocol error, and then see what
//	caused the fault.
//
//	If OPT_SELF_RESET is set, then o_fault will be self clearing.  Once
//	a fault is detected, the current packet will be flushed, and the
//	firewall will become idle (holding TREADY high) until S_AXIS_TVALID
//	and S_AXIS_TLAST--marking the end of a broken packet.  This will
//	resynchronize the core, following which packets may pass through again.
//
//	If you aren't using TLAST, set it to one.
//
//	If you aren't using TUSER, set the width to 1 and the input to a
//	constant zero.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
`default_nettype none
//
// }}}
module	axissafety #(
		// {{{
`ifdef	FORMAL
		parameter [0:0]	F_OPT_FAULTLESS = 0,
`endif
		parameter	C_AXIS_DATA_WIDTH = 8,
		parameter	C_AXIS_USER_WIDTH = 1,
		parameter	OPT_MAX_STALL = 0,
		parameter	OPT_PACKET_LENGTH = 0,
		parameter [0:0]	OPT_SELF_RESET = 0
		// }}}
	) (
		// {{{
		output	reg				o_fault,
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		// AXI-stream slave (incoming) port
		// {{{
		input	wire				S_AXIS_TVALID,
		output	wire				S_AXIS_TREADY,
		input	wire	[C_AXIS_DATA_WIDTH-1:0]	S_AXIS_TDATA,
		input	wire				S_AXIS_TLAST, // = 1,
		input	wire	[C_AXIS_USER_WIDTH-1:0]	S_AXIS_TUSER, // = 0,
		// }}}
		// AXI-stream master (outgoing) port
		// {{{
		output	reg				M_AXIS_TVALID,
		input	wire				M_AXIS_TREADY,
		output	reg	[C_AXIS_DATA_WIDTH-1:0]	M_AXIS_TDATA,
		output	reg				M_AXIS_TLAST,
		output	reg	[C_AXIS_USER_WIDTH-1:0]	M_AXIS_TUSER
		// }}}
		// }}}
	);

	// Parameter/register declarations
	// {{{
	localparam	LGPKTLEN = $clog2(OPT_PACKET_LENGTH+1);
	localparam	LGSTALLCOUNT = $clog2(OPT_MAX_STALL+1);
	reg	skdr_valid, skd_valid, skd_ready;

	reg	[C_AXIS_DATA_WIDTH+1+C_AXIS_USER_WIDTH-1:0]	idata,skdr_data;
	reg	[C_AXIS_DATA_WIDTH-1:0]	skd_data;
	reg	[C_AXIS_USER_WIDTH-1:0]	skd_user;
	reg				skd_last;

	reg	r_stalled;
	reg	packet_fault, change_fault, stall_fault;
	reg	[C_AXIS_DATA_WIDTH+1+C_AXIS_USER_WIDTH-1:0]	past_data;

	reg	[LGSTALLCOUNT-1:0]	stall_count;
	reg	[LGPKTLEN-1:0]		s_packet_counter;
	reg	[LGPKTLEN-1:0]		m_packet_count;

	reg				m_end_of_packet, m_idle;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Implement a skid buffer with no assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		idata = { S_AXIS_TUSER, S_AXIS_TLAST, S_AXIS_TDATA };

	initial	skdr_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		skdr_valid <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && (skd_valid && !skd_ready))
		skdr_valid <= 1;
	else if (skd_ready)
		skdr_valid <= 0;

	initial	skdr_data = 0;	// Allow data to be optimized away if always clr
	always @(posedge S_AXI_ACLK)
	if (S_AXIS_TVALID && S_AXIS_TREADY)
		skdr_data <= idata;

	always @(*)
	if (S_AXIS_TREADY)
		{ skd_user, skd_last, skd_data } = idata;
	else
		{ skd_user, skd_last, skd_data } = skdr_data;

	always @(*)
		skd_valid = S_AXIS_TVALID || skdr_valid;

	assign	S_AXIS_TREADY = !skdr_valid;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Fault detection
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_stalled
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_stalled <= 0;
	else
		r_stalled <= (S_AXIS_TVALID && !S_AXIS_TREADY);
	// }}}

	// past_data
	// {{{
	always @(posedge S_AXI_ACLK)
		past_data <= idata;
	// }}}

	always @(*)
		change_fault = (r_stalled && (past_data != idata));

	// packet_fault
	// {{{
	generate if (OPT_PACKET_LENGTH != 0)
	begin : S_PACKET_COUNT
		// {{{

		// s_packet_counter
		// {{{
		initial	s_packet_counter = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_packet_counter <= 0;
		else if (o_fault)
			s_packet_counter <= 0;
		else if (S_AXIS_TVALID && S_AXIS_TREADY)
		begin
			s_packet_counter <= s_packet_counter + 1;
			if (S_AXIS_TLAST)
				s_packet_counter <= 0;
		end
		// }}}

		// packet_fault
		// {{{
		always @(*)
		begin
			packet_fault = (S_AXIS_TLAST
				!= (s_packet_counter == OPT_PACKET_LENGTH-1));
			if (!S_AXIS_TVALID)
				packet_fault = 0;
		end
		// }}}
		// }}}
	end else begin
		// {{{
		always @(*)
			packet_fault = 1'b0;
		always @(*)
			s_packet_counter = 0;

		// Verilator lint_off UNUSED
		wire	unused_pkt_counter;
		assign	unused_pkt_counter = &{ 1'b0, s_packet_counter };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}

	// stall_fault
	// {{{
	generate if (OPT_MAX_STALL != 0)
	begin : S_STALL_COUNT
		// {{{

		initial	stall_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			stall_count <= 0;
		else if (!S_AXIS_TVALID || S_AXIS_TREADY)
			stall_count <= 0;
		else
			stall_count <= stall_count + 1;

		always @(*)
			stall_fault = (stall_count > OPT_MAX_STALL);
		// }}}
	end else begin
		// {{{
		always @(*)
			stall_fault = 0;

		always @(*)
			stall_count = 0;
		// }}}
	end endgenerate
	// }}}

	// o_fault
	// {{{
	initial	o_fault = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_fault   <= 0;
	else if (!o_fault)
		o_fault <= change_fault || stall_fault || packet_fault;
	else if (OPT_SELF_RESET)
	begin
		if (skd_last && skd_ready && m_idle)
			o_fault <= 1'b0;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The outgoing AXI-stream port
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// skd_ready
	// {{{
	always @(*)
	if (!o_fault && !change_fault && !stall_fault && !packet_fault)
		skd_ready = !M_AXIS_TVALID || M_AXIS_TREADY;
	else if (!o_fault)
		skd_ready = 1'b0;
	else
		skd_ready = 1'b1;
	// }}}

	// m_end_of_packet, m_packet_count
	// {{{
	generate if (OPT_PACKET_LENGTH != 0)
	begin
		// {{{
		initial	m_packet_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_packet_count <= 0;
		else if (M_AXIS_TVALID && M_AXIS_TREADY)
		begin
			m_packet_count <= m_packet_count + 1;
			if (M_AXIS_TLAST)
				m_packet_count <= 0;
		end

		// initial	m_end_of_packet = 0;
		// always @(posedge S_AXI_ACLK)
		// if (!S_AXI_ARESETN)
		//	m_end_of_packet <= 0;
		// else if (M_AXIS_TVALID && M_AXIS_TREADY)
		//	m_end_of_packet <= (m_packet_count >= (OPT_PACKET_LENGTH-3));
		always @(*)
		begin
			m_end_of_packet = (m_packet_count == (OPT_PACKET_LENGTH-1));
			if (M_AXIS_TVALID)
				m_end_of_packet = (m_packet_count == (OPT_PACKET_LENGTH-2));
		end
		// }}}
	end else begin
		// {{{
		always @(*)
			m_end_of_packet = 1'b1;
		always @(*)
			m_packet_count = 0;
		// Verilator lint_off UNUSED
		wire	unused_mpkt_counter;
		assign	unused_mpkt_counter = &{ 1'b0, m_packet_count };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	initial	m_idle = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_idle <= 1;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		if (M_AXIS_TVALID && M_AXIS_TLAST)
			m_idle <= o_fault || (!skd_valid || !skd_ready);
		else if (m_idle && !o_fault)
			m_idle <= (!skd_valid || !skd_ready);
	end
	// }}}

	// M_AXIS_TVALID
	// {{{
	initial	M_AXIS_TVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_TVALID <= 1'b0;
	else if (!M_AXIS_TVALID || M_AXIS_TREADY)
	begin
		M_AXIS_TVALID <= 1'b0;
		if (!o_fault && skd_ready)
			M_AXIS_TVALID <= skd_valid;
		else if (o_fault)
		begin
			if (m_idle)
				M_AXIS_TVALID <= 1'b0;
			else if (!M_AXIS_TVALID || M_AXIS_TLAST)
				M_AXIS_TVALID <= 1'b0;
			else
				M_AXIS_TVALID <= 1'b1;
		end
	end
	// }}}

	// M_AXIS_TUSER, M_AXIS_TLAST, M_AXIS_TDATA
	// {{{
	initial	{ M_AXIS_TUSER, M_AXIS_TLAST, M_AXIS_TDATA } <= 0;
	always @(posedge S_AXI_ACLK)
	begin
		if (!M_AXIS_TVALID || M_AXIS_TREADY)
		begin
			if (o_fault || change_fault || packet_fault)
			begin
				{ M_AXIS_TUSER, M_AXIS_TLAST, M_AXIS_TDATA } <= 0;
				// if (!M_AXIS_TLAST)
				//	M_AXIS_TLAST <= m_end_of_packet;
			end else
				{ M_AXIS_TUSER, M_AXIS_TLAST, M_AXIS_TDATA }
					<= { skd_user, skd_last, skd_data };

			if (OPT_PACKET_LENGTH != 0)
				M_AXIS_TLAST <= m_end_of_packet;
			else if (o_fault && !m_idle)
				M_AXIS_TLAST <= 1'b1;
		end

		if (!S_AXI_ARESETN)
			M_AXIS_TLAST <= 0;
	end
	// }}}
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	reg	[LGPKTLEN-1:0]		fm_packet_counter;
	reg	[LGSTALLCOUNT-1:0]	fm_stall_count;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	// Stability
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!M_AXIS_TVALID);
	else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
		assert($stable(M_AXIS_TUSER));
	end
	// }}}

	// Packet counter, assertions on the output
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fm_packet_counter <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		fm_packet_counter <= fm_packet_counter + 1;
		if (M_AXIS_TLAST)
			fm_packet_counter <= 0;
	end

	always @(*)
	if (S_AXI_ARESETN && OPT_PACKET_LENGTH != 0)
	begin
		assert(fm_packet_counter < OPT_PACKET_LENGTH);
		assert(M_AXIS_TLAST == (fm_packet_counter == OPT_PACKET_LENGTH-1));

		assert(m_packet_count == fm_packet_counter);
		if (!o_fault)
		begin
			if (skdr_valid && skd_last)
			begin
				assert(s_packet_counter == 0);
				assert(m_packet_count == OPT_PACKET_LENGTH-2);
			end else if (M_AXIS_TVALID && M_AXIS_TLAST)
			begin
				assert(s_packet_counter == (skdr_valid ? 1:0));
				assert(m_packet_count == OPT_PACKET_LENGTH-1);
			end else
				assert(s_packet_counter == m_packet_count
					+ (skdr_valid ? 1:0)
					+ (M_AXIS_TVALID ? 1:0));
		end
	end

	always @(*)
	if (S_AXI_ARESETN && !o_fault && OPT_PACKET_LENGTH > 0)
		assert(s_packet_counter < OPT_PACKET_LENGTH);

	always @(*)
	if (S_AXI_ARESETN && OPT_PACKET_LENGTH > 0)
		assert(m_idle == (m_packet_count == 0 && !M_AXIS_TVALID));
	// }}}

	// Input stall counting
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fm_stall_count <= 0;
	else if (!S_AXIS_TVALID || S_AXIS_TREADY)
		fm_stall_count <= 0;

	always @(*)
	if (S_AXI_ARESETN && OPT_MAX_STALL > 0)
		assert(fm_stall_count < OPT_MAX_STALL);
	// }}}
	
	generate if (F_OPT_FAULTLESS)
	begin
		// {{{
		// Stall and stability properties
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || !$past(S_AXI_ARESETN))
			assume(!S_AXIS_TVALID);
		else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
		begin
			assume(S_AXIS_TVALID);
			assume($stable(S_AXIS_TDATA));
			assume($stable(S_AXIS_TLAST));
			assume($stable(S_AXIS_TUSER));
		end
		// }}}

		// f_packet_counter
		// {{{
		if (OPT_PACKET_LENGTH != 0)
		begin
			// {{{
			reg	[LGPKTLEN-1:0]	fs_packet_counter;

			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				fs_packet_counter <= 0;
			else if (S_AXIS_TVALID && S_AXIS_TREADY)
			begin
				fs_packet_counter <= fs_packet_counter + 1;
				if (S_AXIS_TLAST)
					fs_packet_counter <= 0;
			end

			always @(*)
			if (S_AXI_ARESETN)
			begin
				assert(s_packet_counter == fs_packet_counter);
				if (skdr_valid && skd_last)
					assert(s_packet_counter == 0);
				else if (M_AXIS_TVALID && M_AXIS_TLAST)
					assert(s_packet_counter == (skdr_valid ? 1:0));
				else // if (!M_AXIS_TVALID && !M_AXIS_TLAST)
					assert(s_packet_counter
						== fm_packet_counter
						+ (skdr_valid ? 1:0)
						+ (M_AXIS_TVALID ? 1:0));
			end

			always @(*)
			if (S_AXI_ARESETN && S_AXIS_TVALID)
				assume(S_AXIS_TLAST == (fs_packet_counter == OPT_PACKET_LENGTH-1));
			// }}}
		end
		// }}}

		// f_stall_count
		// {{{
		if (OPT_MAX_STALL != 0)
		begin
		// {{{
			reg	[LGSTALLCOUNT-1:0]	f_stall_count;

			initial	stall_count = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				f_stall_count <= 0;
			else if (!S_AXIS_TVALID || S_AXIS_TREADY)
				f_stall_count <= 0;
			else
				f_stall_count <= f_stall_count + 1;

			always @(*)
			if (S_AXI_ARESETN)
				assert(stall_count == f_stall_count);

			always @(*)
				assume(f_stall_count <= OPT_MAX_STALL);
		// }}}
		end
		// }}}

		always @(*)
			assert(!o_fault);
		// }}}
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	generate if (F_OPT_FAULTLESS)
	begin
	end else begin

		reg	cvr_stall_fault, cvr_packet_fault, cvr_change_fault,
			cvr_last;

		initial	cvr_last = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_last <= 1'b0;
		else if (o_fault && $stable(o_fault)
				&& $rose(M_AXIS_TVALID && M_AXIS_TLAST))
			cvr_last <= 1'b1;

		initial	cvr_change_fault = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_change_fault <= 1'b0;
		else if (!o_fault && change_fault && !packet_fault && !stall_fault)
			cvr_change_fault <= 1'b1;
		else if (!o_fault)
			cvr_change_fault <= 1'b0;

		if (OPT_PACKET_LENGTH > 0)
		begin
			initial	cvr_packet_fault = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				cvr_packet_fault <= 1'b0;
			else if (!o_fault && !change_fault && packet_fault && !stall_fault)
				cvr_packet_fault <= 1'b1;
			else if (!o_fault)
				cvr_packet_fault <= 1'b0;

			always @(posedge S_AXI_ACLK)
			if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
			begin
				cover($fell(o_fault) && cvr_packet_fault);
				cover($fell(o_fault) && cvr_packet_fault && cvr_last);
			end
		end

		if (OPT_MAX_STALL > 0)
		begin
			initial	cvr_stall_fault = 0;
			always @(posedge S_AXI_ACLK)
			if (!S_AXI_ARESETN)
				cvr_stall_fault <= 1'b0;
			else if (!o_fault && !change_fault && !packet_fault && stall_fault)
				cvr_stall_fault <= 1'b1;
			else if (!o_fault)
				cvr_stall_fault <= 1'b0;

			always @(posedge S_AXI_ACLK)
			if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
			begin
				cover($fell(o_fault) && cvr_stall_fault);
				cover($fell(o_fault) && cvr_stall_fault && cvr_last);
			end
		end

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		begin
			cover($fell(o_fault));
			cover($fell(o_fault) && cvr_change_fault);
			cover($fell(o_fault) && cvr_change_fault && cvr_last);
		end

	end endgenerate
	// }}}
`endif
// }}}
endmodule
