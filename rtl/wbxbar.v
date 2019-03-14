`default_nettype none
//
module	wbxbar(i_clk, i_reset,
	i_mcyc, i_mstb, i_mwe, i_maddr, i_mdata, i_msel,
		o_mstall, o_mack, o_mdata, o_merr, o_macc,
	o_scyc, o_sstb, o_swe, o_saddr, o_sdata, o_ssel,
		i_sstall, i_sack, i_sdata, i_serr, o_sacc
`ifdef	FORMAL
	, o_timeout, o_dblbuffer, o_lowpower, o_starvation
`endif
	);
	parameter	NM = 4, NS=8;
	parameter	AW = 20, DW=32;
	parameter	[NS*AW-1:0]	SADDR = {
				3'b111, 17'h0,
				3'b110, 17'h0,
				3'b101, 17'h0,
				3'b100, 17'h0,
				3'b011, 17'h0,
				3'b010, 17'h0,
				4'b0010, 16'h0,
				4'b0000, 16'h0 };
	parameter	[NS*AW-1:0]	SMASK = { {(NS-2){ 3'b111, 17'h0 }},
				{(2){ 4'b1111, 16'h0 }} };
	// parameter	[AW-1:0]	SADDR = 0;
	// parameter	[AW-1:0]	SMASK = 0;
	parameter	LGMAXBURST=6;
	parameter	OPT_TIMEOUT = 0; // 1023;
	parameter [0:0]	OPT_STARVATION_TIMEOUT = 1'b0 && (OPT_TIMEOUT > 0);
	localparam	TIMEOUT_WIDTH = $clog2(OPT_TIMEOUT);
	parameter [0:0]	OPT_DBLBUFFER = 1'b1;
	parameter [0:0]	OPT_LOWPOWER = 1'b1;
	localparam	LGNM = $clog2(NM);
	localparam	LGNS = $clog2(NS+1);
	//
	//
	input	wire			i_clk, i_reset;
	input	wire	[NM-1:0]	i_mcyc, i_mstb, i_mwe;
	input	wire	[NM*AW-1:0]	i_maddr;
	input	wire	[NM*DW-1:0]	i_mdata;
	input	wire	[NM*DW/8-1:0]	i_msel;
	//
	output	reg	[NM-1:0]	o_mstall, o_mack, o_merr;
	output	reg	[NM*DW-1:0]	o_mdata;
	//
	//
	output	reg	[NS-1:0]	o_scyc, o_sstb, o_swe;
	output	reg	[NS*AW-1:0]	o_saddr;
	output	reg	[NS*DW-1:0]	o_sdata;
	output	reg	[NS*DW/8-1:0]	o_ssel;
	//
	input	wire	[NS-1:0]	i_sstall, i_sack, i_serr;
	input	wire	[NS*DW-1:0]	i_sdata;
	//
	//
	output	wire	[NM-1:0]	o_macc;
	output	wire	[NS-1:0]	o_sacc;
`ifdef	FORMAL
	output	wire	o_dblbuffer, o_lowpower, o_starvation;
	output	wire	[(OPT_TIMEOUT == 0)?0:TIMEOUT_WIDTH-1:0] o_timeout;

	assign	o_dblbuffer  = OPT_DBLBUFFER;
	assign	o_lowpower   = OPT_LOWPOWER;
	assign	o_starvation = OPT_STARVATION_TIMEOUT;
	assign	o_timeout    = OPT_TIMEOUT;
`endif

	assign	o_macc = (i_mstb & ~o_mstall);
	assign	o_sacc = (o_sstb & ~i_sstall);
	//
	// These definitions work with Verilator, just not with Yosys
	// reg	[NM-1:0][NS:0]		request;
	// reg	[NM-1:0][NS-1:0]	requested;
	// reg	[NM-1:0][NS:0]		grant;
	//
	// These definitions work with both
	reg	[NS:0]			request		[0:NM-1];
	reg	[NS-1:0]		requested	[0:NM-1];
	reg	[NS:0]			grant		[0:NM-1];
	// reg	[NM-1:0]		mgrant; // mrequest;
	reg				mgrant [0:NM-1]; // mrequest;
	reg	[NS-1:0]		sgrant; // srequest;

	wire	[LGMAXBURST-1:0]	w_mpending [0:NM-1];
	reg	[0:0]			mfull		[0:NM-1];
	reg	[0:0]			mnearfull	[0:NM-1];
	reg	[NM-1:0]		mempty, timed_out;

	reg	[0:0]		r_stb		[0:(1<<LGNM)-1];
	reg	[0:0]		r_we		[0:(1<<LGNM)-1];
	reg	[AW-1:0]	r_addr		[0:(1<<LGNM)-1];
	reg	[DW-1:0]	r_data		[0:(1<<LGNM)-1];
	reg	[DW/8-1:0]	r_sel		[0:(1<<LGNM)-1];
	wire	[TIMEOUT_WIDTH-1:0]	w_deadlock_timer [0:NM-1];


	reg	[LGNS-1:0]	mindex		[0:(1<<LGNM)-1];
	reg	[LGNM-1:0]	sindex		[0:(1<<LGNS)-1];

	reg	[0:0]		m_cyc		[0:(1<<LGNM)-1];
	reg	[0:0]		m_stb		[0:(1<<LGNM)-1];
	reg	[0:0]		m_we		[0:(1<<LGNM)-1];
	reg	[AW-1:0]	m_addr		[0:(1<<LGNM)-1];
	reg	[DW-1:0]	m_data		[0:(1<<LGNM)-1];
	reg	[DW/8-1:0]	m_sel		[0:(1<<LGNM)-1];
	//
	reg	[0:0]		s_stall		[0:(1<<LGNS)-1];
	reg	[DW-1:0]	s_data		[0:(1<<LGNS)-1];
	reg	[0:0]		s_ack		[0:(1<<LGNS)-1];
	reg	[0:0]		s_err		[0:(1<<LGNS)-1];

`ifdef	FORMAL
	reg	f_past_valid;
`endif

	genvar	N, M;
	integer	iN, iM;
	generate for(N=0; N<NM; N=N+1)
	begin : DECODE_REQUEST
		reg	none_sel;

		always @(*)
		begin
			none_sel = !m_stb[N];
			for(iM=0; iM<NS; iM=iM+1)
			begin

				none_sel = none_sel
					|| (((m_addr[N] ^ SADDR[iM*AW +: AW])
						&SMASK[iM*AW +: AW])==0);
			end


			none_sel = !none_sel;
		end

		always @(*)
		begin
			for(iM=0; iM<NS; iM=iM+1)
				request[N][iM] = m_stb[N]
					&&(((m_addr[N] ^ SADDR[iM*AW +: AW])
						&SMASK[iM*AW +: AW])==0);

			// Is this address non-existant?
			request[N][NS] = m_stb[N] && none_sel;
		end

		always @(*)
			m_cyc[N] = i_mcyc[N];
		always @(*)
		if (mfull[N])
			m_stb[N] = 1'b0;
		else if (mnearfull[N])
			m_stb[N] = i_mstb[N] && !r_stb[N];
		else
			m_stb[N] = i_mstb[N] || (i_mcyc[N] && r_stb[N]);
		always @(*)
			m_we[N]   = r_stb[N] ? r_we[N] : i_mwe[N];
		always @(*)
			m_addr[N] = r_stb[N] ? r_addr[N] : i_maddr[N*AW +: AW];
		always @(*)
			m_data[N] = r_stb[N] ? r_data[N] : i_mdata[N*DW +: DW];
		always @(*)
			m_sel[N]  = r_stb[N] ? r_sel[N]: i_msel[N*DW/8 +: DW/8];

	end for(N=NM; N<(1<<LGNM); N=N+1)
	begin
		// in case NM isn't one less than a power of two, complete
		// the set
		always @(*)
			m_cyc[N] = 0;
		always @(*)
			m_stb[N] = 0;
		always @(*)
			m_we[N]   = 0;
		always @(*)
			m_addr[N] = 0;
		always @(*)
			m_data[N] = 0;
		always @(*)
			m_sel[N]  = 0;

	end endgenerate

	always @(*)
	begin
		for(iM=0; iM<NS; iM=iM+1)
		begin
			requested[0][iM] = 0;
			for(iN=1; iN<NM; iN=iN+1)
			requested[iN][iM]
				= (request[iN-1][iM] || requested[iN-1][iM]);
		end
	end

	generate for(M=0; M<NS; M=M+1)
	begin

		always @(*)
		begin
			sgrant[M] = 0;
			for(iN=0; iN<NM; iN=iN+1)
				if (grant[iN][M])
					sgrant[M] = 1;
		end

		always @(*)
			s_data[M]  = i_sdata[M*DW +: DW];
		always @(*)
			s_stall[M] = o_sstb[M] && i_sstall[M];
		always @(*)
			s_ack[M]   = o_scyc[M] && i_sack[M];
		always @(*)
			s_err[M]   = o_scyc[M] && i_serr[M];
	end for(M=NS; M<(1<<LGNS); M=M+1)
	begin

		always @(*)
			s_data[M]  = 0;
		always @(*)
			s_stall[M] = 1;
		always @(*)
			s_ack[M]   = 0;
		always @(*)
			s_err[M]   = 1;
		// always @(*) sgrant[M]  = 0;

	end endgenerate

	//
	// Arbitrate
	generate for(N=0; N<NM; N=N+1)
	begin

		reg	stay_on_channel;

		always @(*)
		begin
			stay_on_channel = 0;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (request[N][iM] && grant[N][iM])
					stay_on_channel = 1;
			end
		end

		reg	requested_channel_is_available;

		always @(*)
		begin
			requested_channel_is_available = 0;
			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (request[N][iM] && !sgrant[iM]
						&& !requested[N][iM])
					requested_channel_is_available = 1;
			end
		end

		initial	grant[N] = 0;
		initial	mgrant[N] = 0;
		always @(posedge i_clk)
		if (i_reset || !i_mcyc[N])
		begin
			grant[N] <= 0;
			mgrant[N] <= 0;
		end else if (!mgrant[N] || mempty[N])
		begin
			if (stay_on_channel)
				mgrant[N] <= 1'b1;
			else if (requested_channel_is_available)
				mgrant[N] <= 1'b1;
			else if (i_mstb[N] || r_stb[N])
				mgrant[N] <= 1'b0;

			for(iM=0; iM<NS; iM=iM+1)
			begin
				if (request[N][iM] && grant[N][iM])
				begin
					// Maintain any open channels
					grant[N][iM] <= 1;
					// mgrant[N] <= 1'b1;
					mindex[N] <= iM;
				end else if (request[N][iM] && !sgrant[iM]
						&& !requested[N][iM])
				begin
					// Open a new channel if necessary
					grant[N][iM] <= 1;
					// mgrant[N] <= 1'b1;
					mindex[N] <= iM;
				end else if (i_mstb[N] || r_stb[N])
				begin
					// mgrant[N] <= 1'b0;
					grant[N][iM] <= 0;
				end
			end
			if (request[N][NS])
			begin
				grant[N][NS] <= 1'b1;
				mgrant[N] <= 1'b1;
			end else begin
				grant[N][NS] <= 1'b0;
				if (grant[N][NS])
					mgrant[N] <= 1'b1;
			end
		end

		// assign	grant[N] = r_grant[N*(NS+1)+:(NS+1)];
`ifdef	FORMAL
`ifdef	VERIFIC
		always @(*)
		if (!f_past_valid)
		begin
			assume(grant[N] == 0);
			assume(mgrant[N] == 0);
		end
`endif

		for(M=0; M<NS; M=M+1)
		begin
			always @(*)
			if ((f_past_valid)&&grant[N][M])
			begin
				assert(mgrant[N]);
				assert(mindex[N] == M);
				assert(sindex[M] == N);
			end
		end
`endif
	end endgenerate

`ifdef	FORMAL
`ifdef	VERIFIC
		always @(*)
		if (!f_past_valid)
			assume(sgrant == 0);
`endif
`endif
	generate for(M=0; M<NS; M=M+1)
	begin

		always @(posedge i_clk)
		for (iN=0; iN<NM; iN=iN+1)
		begin
			if (!mgrant[iN] || mempty[iN])
			begin
				if (request[iN][M] && grant[iN][M])
				begin
					sindex[M] <= iN;
				end else if (request[iN][M] && !sgrant[M]
						&& !requested[iN][M])
				begin
					sindex[M] <= iN;
				end
			end
		end

	end endgenerate


	//
	// Assign outputs to the slaves
	generate for(M=0; M<NS; M=M+1)
	begin
`ifdef	FORMAL
`ifdef	VERIFIC
		always @(*)
		if (!f_past_valid)
		begin
			assume(o_scyc[M] == 0);
			assume(o_sstb[M] == 0);
		end
`endif
`endif
		initial	o_scyc[M] = 0;
		initial	o_sstb[M] = 0;
		always @(posedge i_clk)
		begin
			if (sgrant[M])
			begin

				if (!i_mcyc[sindex[M]])
				begin
					o_scyc[M] <= 1'b0;
					o_sstb[M] <= 1'b0;
				end else begin
					o_scyc[M] <= 1'b1;

					if (!s_stall[M])
						o_sstb[M] <= m_stb[sindex[M]]
						  && request[sindex[M]][M]
						  && !mnearfull[sindex[M]];
				end
			end else begin
				o_scyc[M]  <= 1'b0;
				o_sstb[M]  <= 1'b0;
			end

			if (i_reset || s_err[M])
			begin
				o_scyc[M] <= 1'b0;
				o_sstb[M] <= 1'b0;
			end
		end
	end endgenerate

	//
	// Assign outputs to the slaves
	generate if ((NM == 1) && (!OPT_LOWPOWER))
	begin
		//
		// This is the low logic version of our bus data outputs.
		// It only works if we only have one master.
		//
		// The basic idea here is that we share all of our bus outputs
		// between all of the various slaves.  Since we only have one
		// bus master, this works.
		//
		always @(posedge i_clk)
		begin
			o_swe[0]        <= o_swe[0];
			o_saddr[0+: AW] <= o_saddr[0+:AW];
			o_sdata[0+: DW] <= o_sdata[0+:DW];
			o_ssel[0+:DW/8] <=o_ssel[0+:DW/8];

			if (sgrant[mindex[0]] && !s_stall[mindex[0]])
			begin
				o_swe[0]        <= m_we[0];
				o_saddr[0+: AW] <= m_addr[0];
				o_sdata[0+: DW] <= m_data[0];
				o_ssel[0+:DW/8] <= m_sel[0];
			end
		end

		for(M=1; M<NS; M=M+1)
		always @(*)
		begin
			o_swe[M]            = o_swe[0];
			o_saddr[M*AW +: AW] = o_saddr[0 +: AW];
			o_sdata[M*DW +: DW] = o_sdata[0 +: DW];
			o_ssel[M*DW/8+:DW/8]= o_ssel[0 +: DW/8];
		end

	end else for(M=0; M<NS; M=M+1)
	begin
		always @(posedge i_clk)
		begin
			if (OPT_LOWPOWER && !sgrant[M])
			begin
				o_swe[M]              <= 1'b0;
				o_saddr[M*AW   +: AW] <= 0;
				o_sdata[M*DW   +: DW] <= 0;
				o_ssel[M*(DW/8)+:DW/8]<= 0;
			end else begin
				o_swe[M]              <= o_swe[M];
				o_saddr[M*AW   +: AW] <= o_saddr[M*AW+:AW];
				o_sdata[M*DW   +: DW] <= o_sdata[M*DW+:DW];
				o_ssel[M*(DW/8)+:DW/8]<= o_ssel[M*(DW/8)+:DW/8];
			end

			if (sgrant[M] && !s_stall[M])
			begin
				o_swe[M]              <= m_we[  sindex[M]];
				o_saddr[M*AW +: AW]   <= m_addr[sindex[M]];
				o_sdata[M*DW +: DW]   <= m_data[sindex[M]];
				o_ssel[M*DW/8 +:DW/8] <= m_sel[ sindex[M]];
			end
		end
	end endgenerate

	//
	// Assign return values to the masters
	generate if (OPT_DBLBUFFER)
	begin : DOUBLE_BUFFERRED_STALL

		for(N=0; N<NM; N=N+1)
		begin
			initial	o_mstall[N] = 0;
			initial	o_mack[N]   = 0;
			initial	o_merr[N]   = 0;
			always @(posedge i_clk)
			begin
				iM = mindex[N];
				o_mstall[N] <= o_mstall[N]
						|| (i_mstb[N] && !o_mstall[N]);
				o_mack[N]   <= mgrant[N] && s_ack[mindex[N]];
				o_merr[N]   <= mgrant[N] && s_err[mindex[N]];
				if (OPT_LOWPOWER && !mgrant[N])
					o_mdata[N*DW +: DW] <= 0;
				else
					o_mdata[N*DW +: DW] <= s_data[mindex[N]];

				if (mgrant[N])
				begin
					if ((i_mstb[N]||o_mstall[N])
								&& mnearfull[N])
						o_mstall[N] <= 1'b1;
					else if ((i_mstb[N] || o_mstall[N])
							&& !request[N][iM])
						// Requesting another channel
						o_mstall[N] <= 1'b1;
					else if (!s_stall[iM])
						// Downstream channel is clear
						o_mstall[N] <= 1'b0;
					else // if (o_sstb[mindex[N]]
						//   && i_sstall[mindex[N]])
						// Downstream channel is stalled
						o_mstall[N] <= i_mstb[N];
				end

				if (mnearfull[N] && i_mstb[N])
					o_mstall[N] <= 1'b1;

				if ((o_mstall[N] && grant[N][NS])
					||(timed_out[N] && !o_mack[N]))
				begin
					o_mstall[N] <= 1'b0;
					o_mack[N]   <= 1'b0;
					o_merr[N]   <= 1'b1;
				end

				if (i_reset || !i_mcyc[N])
				begin
					o_mstall[N] <= 1'b0;
					o_mack[N]   <= 1'b0;
					o_merr[N]   <= 1'b0;
				end
			end

			always @(*)
				r_stb[N] = o_mstall[N];

			always @(posedge i_clk)
			if (OPT_LOWPOWER && !i_mcyc[N])
			begin
				r_we[N]   <= 0;
				r_addr[N] <= 0;
				r_data[N] <= 0;
				r_sel[N]  <= 0;
			end else if ((!OPT_LOWPOWER || i_mstb[N]) && !o_mstall[N])
			begin
				r_we[N]   <= i_mwe[N];
				r_addr[N] <= i_maddr[N*AW +: AW];
				r_data[N] <= i_mdata[N*DW +: DW];
				r_sel[N]  <= i_msel[N*(DW/8) +: DW/8];
			end
		end

	end else if (NS == 1) // && !OPT_DBLBUFFER
	begin : SINGLE_SLAVE

		for(N=0; N<NM; N=N+1)
		begin
			always @(*)
			begin
				o_mstall[N] = !mgrant[N] || s_stall[0]
					|| (i_mstb[N] && !request[N][0]);
				o_mack[N]   =  mgrant[N] && i_sack[0];
				o_merr[N]   =  mgrant[N] && i_serr[0];
				o_mdata[N]  = (!mgrant[N] && OPT_LOWPOWER)
					? 0 : i_sdata;

				if (mnearfull[N])
					o_mstall[N] = 1'b1;

				if (timed_out[N]&&!o_mack[0])
				begin
					o_mstall[N] = 1'b0;
					o_mack[N]   = 1'b0;
					o_merr[N]   = 1'b1;
				end

				if (grant[N][NS] && m_stb[N])
				begin
					o_mstall[N] = 1'b0;
					o_mack[N]   = 1'b0;
					o_merr[N]   = 1'b1;
				end

				if (!m_cyc[N])
				begin
					o_mack[N] = 1'b0;
					o_merr[N] = 1'b0;
				end
			end

			always @(*)
				r_stb[N] <= 1'b0;

			always @(*)
			begin
				r_we[N]   = 0;
				r_addr[N] = 0;
				r_data[N] = 0;
				r_sel[N]  = 0;
			end
		end

	end else begin : SINGLE_BUFFER_STALL
		for(N=0; N<NM; N=N+1)
		begin
			// initial	o_mstall[N] = 0;
			// initial	o_mack[N]   = 0;
			always @(*)
			begin
				o_mstall[N] = 1;
				o_mack[N]   = mgrant[N] && s_ack[mindex[N]];
				o_merr[N]   = mgrant[N] && s_err[mindex[N]];
				if (OPT_LOWPOWER && !mgrant[N])
					o_mdata[N*DW +: DW] = 0;
				else
					o_mdata[N*DW +: DW] = s_data[mindex[N]];

				if (mgrant[N])
				begin
					iM = mindex[N];
					o_mstall[N]       = (s_stall[mindex[N]])
					    || (i_mstb[N] && !request[N][iM]);
				end

				if (mnearfull[N])
					o_mstall[N] = 1'b1;

				if (grant[N][NS] ||(timed_out[N]&&!o_mack[0]))
				begin
					o_mstall[N] = 1'b0;
					o_mack[N]   = 1'b0;
					o_merr[N]   = 1'b1;
				end

				if (!m_cyc[N])
				begin
					o_mack[N] = 1'b0;
					o_merr[N] = 1'b0;
				end
			end

			always @(*)
				r_stb[N] <= 1'b0;

			always @(*)
			begin
				r_we[N]   = 0;
				r_addr[N] = 0;
				r_data[N] = 0;
				r_sel[N]  = 0;
			end
		end

	end endgenerate

	//
	// Count the pending transactions per master
	generate for(N=0; N<NM; N=N+1)
	begin
		reg	[LGMAXBURST-1:0]	lclpending;
		initial	lclpending  = 0;
		initial	mempty[N]    = 1;
		initial	mnearfull[N] = 0;
		initial	mfull[N]     = 0;
		always @(posedge i_clk)
		if (i_reset || !i_mcyc[N] || o_merr[N])
		begin
			lclpending <= 0;
			mfull[N]    <= 0;
			mempty[N]   <= 1'b1;
			mnearfull[N]<= 0;
		end else case({ (i_mstb[N] && !o_mstall[N]), o_mack[N] })
		2'b01: begin
			lclpending <= lclpending - 1'b1;
			mnearfull[N]<= mfull[N];
			mfull[N]    <= 1'b0;
			mempty[N]   <= (lclpending == 1);
			end
		2'b10: begin
			lclpending <= lclpending + 1'b1;
			mnearfull[N]<= (&lclpending[LGMAXBURST-1:2])&&(lclpending[1:0] != 0);
			mfull[N]    <= mnearfull[N];
			mempty[N]   <= 1'b0;
			end
		default: begin end
		endcase

		assign w_mpending[N] = lclpending;

`ifdef	FORMAL
		always @(*)
		if (f_past_valid)
		begin
			assert(mempty[N] == (lclpending == 0));
			assert(mnearfull[N]==(&lclpending[LGMAXBURST-1:1]));
			assert(mfull[N] == (&lclpending));
		end
`endif
	end endgenerate


	generate if (OPT_TIMEOUT > 0)
	begin : CHECK_TIMEOUT

		for(N=0; N<NM; N=N+1)
		begin

			reg	[TIMEOUT_WIDTH-1:0]	deadlock_timer;

			initial	deadlock_timer = OPT_TIMEOUT;
			initial	timed_out[N] = 1'b0;
			always @(posedge i_clk)
			if (i_reset || !i_mcyc[N]
					||((w_mpending[N] == 0)
						&&(!i_mstb[N] && !r_stb[N]))
					||((i_mstb[N] || r_stb[N])
						&&(!o_mstall[N]))
					||(o_mack[N] || o_merr[N])
					||(!OPT_STARVATION_TIMEOUT&&!mgrant[N]))
			begin
				deadlock_timer <= OPT_TIMEOUT;
				timed_out[N] <= 0;
			end else if (deadlock_timer > 0)
			begin
				deadlock_timer <= deadlock_timer - 1;
				timed_out[N] <= (deadlock_timer <= 1);
			end

			assign	w_deadlock_timer[N] = deadlock_timer;
		end

	end else begin

		always @(*)
			timed_out = 0;
		
	end endgenerate

`ifdef	FORMAL
	localparam	F_MAX_DELAY = 4;
	localparam	F_LGDEPTH = LGMAXBURST;
	wire	[F_LGDEPTH-1:0]	f_mreqs		[0:NM-1];
	wire	[F_LGDEPTH-1:0]	f_macks		[0:NM-1];
	wire	[F_LGDEPTH-1:0]	f_moutstanding	[0:NM-1];

	wire	[F_LGDEPTH-1:0]	f_sreqs		[0:NS-1];
	wire	[F_LGDEPTH-1:0]	f_sacks		[0:NS-1];
	wire	[F_LGDEPTH-1:0]	f_soutstanding	[0:NS-1];

	initial	assert(!OPT_STARVATION_TIMEOUT || OPT_TIMEOUT > 0);

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	generate for(N=0; N<NM; N=N+1)
	begin
		always @(*)
		if (f_past_valid)
		for(iN=N+1; iN<NM; iN=iN+1)
			// Can't grant the same channel to two separate
			// masters.  This applies to all but the error or
			// no-slave-selected channel
			assert((grant[N][NS-1:0] & grant[iN][NS-1:0])==0);

		for(M=1; M<=NS; M=M+1)
		begin
			// Can't grant two channels to the same master
			always @(*)
			if (f_past_valid && grant[N][M])
				assert(grant[N][M-1:0] == 0);
		end


		always @(*)
		if (&w_mpending[N])
			assert(o_merr[N] || o_mstall[N]);

		reg	checkgrant;
		always @(*)
		if (f_past_valid)
		begin
			checkgrant = 0;
			for(iM=0; iM<NS; iM=iM+1)
				if (grant[N][iM])
					checkgrant = 1;
			if (grant[N][NS])
				checkgrant = 1;

			assert(checkgrant == mgrant[N]);
		end

	end endgenerate
	
	generate for(N=0; N<NM; N=N+1)
	begin : WB_SLAVE_CHECK

		fwb_slave #(
			.AW(AW), .DW(DW),
			.F_LGDEPTH(LGMAXBURST),
			.F_MAX_ACK_DELAY(0),
			.F_MAX_STALL(0)
			) slvi(i_clk, i_reset,
				i_mcyc[N], i_mstb[N], i_mwe[N],
				i_maddr[N*AW +: AW], i_mdata[N*DW +: DW],					i_msel[N*(DW/8) +: (DW/8)],
			o_mack[N], o_mstall[N], o_mdata[N*DW +: DW], o_merr[N],
			f_mreqs[N], f_macks[N], f_moutstanding[N]);

		always @(*)
		if ((f_past_valid)&&(grant[N][NS]))
			assert(f_moutstanding[N] <= 1);

		always @(*)
		if ((f_past_valid)&&(grant[N][NS] && i_mcyc[N]))
			assert(o_mstall[N] || o_merr[N]);

	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : WB_MASTER_CHECK
		fwb_master #(
			.AW(AW), .DW(DW),
			.F_LGDEPTH(LGMAXBURST),
			.F_MAX_ACK_DELAY(F_MAX_DELAY),
			.F_MAX_STALL(2)
			) mstri(i_clk, i_reset,
				o_scyc[M], o_sstb[M], o_swe[M],
				o_saddr[M*AW +: AW], o_sdata[M*DW +: DW],
				o_ssel[M*(DW/8) +: (DW/8)],
			i_sack[M], i_sstall[M], s_data[M], i_serr[M],
			f_sreqs[M], f_sacks[M], f_soutstanding[M]);
	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin : CHECK_OUTSTANDING

		always @(posedge i_clk)
		if (i_mcyc[N])
			assert(f_moutstanding[N] == w_mpending[N]);

		reg	[LGMAXBURST:0]	n_outstanding;
		always @(*)
		if (i_mcyc[N])
			assert(f_moutstanding[N] >=
				(o_mstall[N] && OPT_DBLBUFFER) ? 1:0
				+ (o_mack[N] && OPT_DBLBUFFER) ? 1:0);

		always @(*)
			n_outstanding = f_moutstanding[N]
				- ((o_mstall[N] && OPT_DBLBUFFER) ? 1:0)
				- ((o_mack[N] && OPT_DBLBUFFER) ? 1:0);
		always @(posedge i_clk)
		if (i_mcyc[N] && !mgrant[N] && !o_merr[N])
			assert(f_moutstanding[N]
					== (o_mstall[N]&&OPT_DBLBUFFER ? 1:0));
		else if (i_mcyc[N] && mgrant[N])
		for(iM=0; iM<NS; iM=iM+1)
		if (grant[N][iM] && o_scyc[iM] && !i_serr[iM] && !o_merr[N])
			assert(n_outstanding
				== {1'b0,f_soutstanding[iM]}+(o_sstb[iM] ? 1:0));

		always @(*)
		if (i_mcyc[N] && r_stb[N] && OPT_DBLBUFFER)
			assume(i_mwe[N] == r_we[N]);

		always @(*)
		if (!OPT_DBLBUFFER && !mnearfull[N])
			assert(i_mstb[N] == m_stb[N]);

		always @(*)
		if (!OPT_DBLBUFFER)
			assert(i_mwe[N] == m_we[N]);

		always @(*)
		for(iM=0; iM<NS; iM=iM+1)
		if (grant[N][iM] && i_mcyc[N])
		begin
			if (f_soutstanding[iM] > 0)
				assert(i_mwe[N] == o_swe[iM]);
			if (o_sstb[iM])
				assert(i_mwe[N] == o_swe[iM]);
			if (o_mack[N])
				assert(i_mwe[N] == o_swe[iM]);
			if (o_scyc[iM] && i_sack[iM])
				assert(i_mwe[N] == o_swe[iM]);
			if (o_merr[N] && !timed_out[N])
				assert(i_mwe[N] == o_swe[iM]);
			if (o_scyc[iM] && i_serr[iM])
				assert(i_mwe[N] == o_swe[iM]);
		end
			
	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin
		always @(posedge i_clk)
		if (!$past(sgrant[M]))
			assert(!o_scyc[M]);
	end endgenerate

`endif
endmodule
