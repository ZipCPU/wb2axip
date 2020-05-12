////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axi_tb.cpp
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	To provide a fairly generic interface wrapper to an AXI bus,
//		that can then be used to create a test-bench class.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2020, Gisselquist Technology, LLC
//
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
//
#include <stdio.h>
#include <stdlib.h>

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "testb.h"
#include "devbus.h"

const int	BOMBCOUNT = 32;

template <class TB>	class	AXI_TB : public DEVBUS {
	bool	m_buserr;
#ifdef	INTERRUPTWIRE
	bool	m_interrupt;
#endif
	VerilatedVcdC	*m_trace;
public:
	TB		*m_tb;
	typedef	uint32_t	BUSW;
	
	bool	m_bomb;

	AXI_TB(void) {
		m_tb = new TB;
		Verilated::traceEverOn(true);

		m_bomb = false;

		m_tb->m_core->S_AXI_AWVALID = 0;
		m_tb->m_core->S_AXI_WVALID = 0;
		m_tb->m_core->S_AXI_BREADY = 0;

		m_tb->m_core->S_AXI_ARVALID = 0;
		m_tb->m_core->S_AXI_RREADY = 0;
		m_buserr = false;
#ifdef	INTERRUPTWIRE
		m_interrupt = false;
#endif
	}

	virtual	~AXI_TB(void) {
		delete m_tb;
	}

	virtual	void	opentrace(const char *vcdname) {
		m_tb->opentrace(vcdname);
	}

	virtual	void	closetrace(void) {
		m_tb->closetrace();
	}

	virtual	void	close(void) {
		// m_tb->close();
	}

	virtual	void	kill(void) {
		close();
	}

	virtual	void	eval(void) {
		m_tb->m_core->eval();
	}

#define	TICK	m_tb->tick
	void	tick(void) {
		m_tb->tick();
#ifdef	INTERRUPTWIRE
		if (m_tb->m_core->INTERRUPTWIRE)
			m_interrupt = true;
#endif
	}

	virtual	void	reset(void) {
		// m_tb->m_core->S_AXI_ARESETN = 0;
		m_tb->m_core->S_AXI_ARESETN = 0;
		m_tb->m_core->S_AXI_AWVALID = 0;
		m_tb->m_core->S_AXI_WVALID  = 0;
		m_tb->m_core->S_AXI_ARVALID = 0;

		for(int k=0; k<16; k++)
			tick();

		m_tb->m_core->S_AXI_ARESETN = 1;
		tick();
	}

	unsigned long	tickcount(void) {
		return m_tb->m_time_ps / 10000l;
	}

	void	idle(const unsigned counts = 1) {
		m_tb->m_core->S_AXI_AWVALID = 0;
		m_tb->m_core->S_AXI_WVALID  = 0;
		m_tb->m_core->S_AXI_BREADY  = 0;
		m_tb->m_core->S_AXI_ARVALID = 0;
		m_tb->m_core->S_AXI_RREADY  = 0;
		for(unsigned k=0; k<counts; k++) {
			tick();
			assert(!m_tb->m_core->S_AXI_RVALID);
			assert(!m_tb->m_core->S_AXI_BVALID);
		}
	}

	BUSW readio(BUSW a) {
		BUSW		result;
		uint32_t	delay_count = 0;

		// printf("AXI-READM(%08x)\n", a);

		m_tb->m_core->S_AXI_ARVALID = 1;
		m_tb->m_core->S_AXI_ARADDR  = a;
		m_tb->m_core->S_AXI_RREADY  = 1;

		while(!m_tb->m_core->S_AXI_ARREADY) {
			tick();
			assert(delay_count++ < BOMBCOUNT);
		}

		tick();

		m_tb->m_core->S_AXI_ARVALID = 0;
		delay_count = 0;

		while(!m_tb->m_core->S_AXI_RVALID) { // || !RVALID
			tick();
			assert(delay_count++ < BOMBCOUNT);
		}

		result = m_tb->m_core->S_AXI_RDATA;
		if (m_tb->m_core->S_AXI_RRESP & 2)
			m_buserr = true;
		assert(m_tb->m_core->S_AXI_RRESP == 0);

		tick();

		return result;
	}

	uint64_t read64(BUSW a) {
		uint64_t	result;
		int32_t		buf[2];

		readv(a, 2, buf);
		result = buf[1];
		result = (result << 32) | (uint64_t)buf[0];
		return result;
	}

	void	readv(const BUSW a, int len, BUSW *buf, const int inc=1) {
		int		cnt, rdidx, delay_count = 0;

		printf("AXI-READM(%08x, %d)\n", a, len);
		m_tb->m_core->S_AXI_ARVALID = 1;
		m_tb->m_core->S_AXI_ARADDR  = a & -4;
		//
		m_tb->m_core->S_AXI_RREADY = 1;

		rdidx =0; cnt = 0;

		do {
			int	s;

			m_tb->m_core->S_AXI_ARVALID = 1;
			s = ((m_tb->m_core->S_AXI_ARVALID)
				&&(m_tb->m_core->S_AXI_ARREADY==0))?0:1;
			tick();
			m_tb->m_core->S_AXI_ARADDR += (inc&(s^1))?4:0;
			cnt += (s^1);
			if (m_tb->m_core->S_AXI_RVALID) {
				buf[rdidx++] = m_tb->m_core->S_AXI_RDATA;
				delay_count = 0;
			}
			if (m_tb->m_core->S_AXI_RVALID
					&& m_tb->m_core->S_AXI_RRESP != 0)
				m_buserr = true;
			assert(delay_count++ < BOMBCOUNT);
		} while(cnt < len);

		m_tb->m_core->S_AXI_ARVALID = 0;
		delay_count = 0;

		while(rdidx < len) {
			tick();
			if ((m_tb->m_core->S_AXI_RVALID)&&(m_tb->m_core->S_AXI_RREADY))
				buf[rdidx++] = m_tb->m_core->S_AXI_RDATA;
			if (m_tb->m_core->S_AXI_RVALID && m_tb->m_core->S_AXI_RRESP != 0)
				m_buserr = true;
			assert(delay_count++ < BOMBCOUNT);
		}

		tick();
		m_tb->m_core->S_AXI_RREADY = 0;
		assert(!m_tb->m_core->S_AXI_BVALID);
		assert(!m_tb->m_core->S_AXI_RVALID);
	}

	void	readi(const BUSW a, const int len, BUSW *buf) {
		readv(a, len, buf, 1);
	}

	void	readz(const BUSW a, const int len, BUSW *buf) {
		readv(a, len, buf, 0);
	}

	void	writeio(const BUSW a, const BUSW v) {
		int	delay_count = 0;

		// printf("AXI-WRITEM(%08x) <= %08x\n", a, v);
		m_tb->m_core->S_AXI_ARVALID = 0;
		m_tb->m_core->S_AXI_RREADY  = 0;

		m_tb->m_core->S_AXI_AWVALID = 1;
		m_tb->m_core->S_AXI_WVALID  = 1;
		m_tb->m_core->S_AXI_AWADDR  = a & (-4);
		m_tb->m_core->S_AXI_WDATA   = v;
		m_tb->m_core->S_AXI_WSTRB   = 0x0f;

		while((m_tb->m_core->S_AXI_AWVALID)
			&&(m_tb->m_core->S_AXI_WVALID)) {
			int	awready = m_tb->m_core->S_AXI_AWREADY;
			int	wready = m_tb->m_core->S_AXI_WREADY;

			tick();

			if (awready)
				m_tb->m_core->S_AXI_AWVALID = 0;
			if (wready)
				m_tb->m_core->S_AXI_WVALID = 0;
			assert(delay_count++ < BOMBCOUNT);
		}

		m_tb->m_core->S_AXI_BREADY = 1;
		delay_count = 0;

		while(!m_tb->m_core->S_AXI_BVALID) {
			tick();
			assert(delay_count++ < BOMBCOUNT);
		}

		if (m_tb->m_core->S_AXI_BRESP & 2)
			m_buserr = true;
		tick();
	}

	void	write64(const BUSW a, const uint64_t v) {
		uint32_t	buf[2];
		// printf("AXI-WRITE64(%08x) <= %016lx\n", a, v);
		buf[0] = (uint32_t)v;
		buf[1] = (uint32_t)(v >> 32);
		writei(a, 2, buf);
	}

	void	writev(const BUSW a, const int ln, const BUSW *buf, const int inc=1) {
		unsigned nacks = 0, awcnt = 0, wcnt = 0, delay_count = 0;

		// printf("AXI-WRITEM(%08x, %d, ...)\n", a, ln);
		m_tb->m_core->S_AXI_AWVALID = 1;
		m_tb->m_core->S_AXI_AWADDR  = a & -4;
		m_tb->m_core->S_AXI_WVALID = 1;
		m_tb->m_core->S_AXI_WSTRB  = 0x0f;
		m_tb->m_core->S_AXI_WDATA  = buf[0];
		m_tb->m_core->S_AXI_BREADY = 1;
		m_tb->m_core->S_AXI_RREADY = 0;

		do {
			int	awready, wready;

			m_tb->m_core->S_AXI_WDATA   = buf[wcnt];

			m_tb->m_core->S_AXI_AWVALID = (awcnt < (unsigned)ln);
			m_tb->m_core->S_AXI_WVALID  = (wcnt < (unsigned)ln);

			awready = m_tb->m_core->S_AXI_AWREADY;
			wready  = m_tb->m_core->S_AXI_WREADY;

			tick();
			if (m_tb->m_core->S_AXI_AWVALID && awready) {
				delay_count = 0;
				awcnt++;
				// Update the address
				m_tb->m_core->S_AXI_AWADDR += (inc)?4:0;
			}

			if (m_tb->m_core->S_AXI_WVALID && wready) {
				delay_count = 0;
				wcnt++;
			}

			if (m_tb->m_core->S_AXI_BVALID) {
				nacks++;

				// Check for any bus errors
				if (m_tb->m_core->S_AXI_BRESP & 2)
					m_buserr = true;
			}

			assert(delay_count++ < BOMBCOUNT);
		} while((awcnt<(unsigned)ln)||(wcnt<(unsigned)ln));

		m_tb->m_core->S_AXI_AWVALID = 0;
		m_tb->m_core->S_AXI_WVALID  = 0;
		while(nacks < (unsigned)ln) {
			tick();
			if (m_tb->m_core->S_AXI_BVALID) {
				nacks++;
				delay_count = 0;
				if (m_tb->m_core->S_AXI_BRESP & 2)
					m_buserr = true;
			}
			assert(delay_count++ < BOMBCOUNT);
		}

		tick();

		// Release the bus
		m_tb->m_core->S_AXI_BREADY = 0;
		m_tb->m_core->S_AXI_RREADY = 0;

		assert(!m_tb->m_core->S_AXI_BVALID);
		assert(!m_tb->m_core->S_AXI_RVALID);
		assert(!m_tb->m_core->S_AXI_AWVALID);
		assert(!m_tb->m_core->S_AXI_WVALID);
	}

	void	writei(const BUSW a, const int ln, const BUSW *buf) {
		writev(a, ln, buf, 1);
	}

	void	writez(const BUSW a, const int ln, const BUSW *buf) {
		writev(a, ln, buf, 0);
	}


	bool	bombed(void) const { return m_bomb; }

	// bool	debug(void) const	{ return m_debug; }
	// bool	debug(bool nxtv)	{ return m_debug = nxtv; }

	bool	poll(void) {
#ifdef	INTERRUPTWIRE
		return (m_interrupt)||(m_tb->m_core->INTERRUPTWIRE != 0);
#else
		return false;
#endif
	}

	bool	bus_err(void) const {
#ifdef	AXIERR
		return m_buserr;
#else
		return false;
#endif
	}

	void	reset_err(void) {
#ifdef	AXIERR
		m_buserr = false;;
#endif
	}

	void	usleep(unsigned msec) {
#ifdef	CLKRATEHZ
		unsigned count = CLKRATEHZ / 1000 * msec;
#else
		// Assume 100MHz if no clockrate is given
		unsigned count = 1000*100 * msec;
#endif
		while(count-- != 0)
#ifdef	INTERRUPTWIRE
			if (poll()) return; else
#endif
			tick();
	}

	void	clear(void) {
#ifdef	INTERRUPTWIRE
		m_interrupt = false;
#endif
	}

	void	wait(void) {
#ifdef	INTERRUPTWIRE
		while(!poll())
			tick();
#else
		assert(("No interrupt defined",0));
#endif
	}
};

