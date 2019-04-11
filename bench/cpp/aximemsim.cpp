////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximemsim.cpp
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2019, Gisselquist Technology, LLC
//
// This file is part of the pipelined Wishbone to AXI converter project, a
// project that contains multiple bus bridging designs and formal bus property
// sets.
//
// The bus bridge designs and property sets are free RTL designs: you can
// redistribute them and/or modify any of them under the terms of the GNU
// Lesser General Public License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option) any later version.
//
// The bus bridge designs and property sets are distributed in the hope that
// they will be useful, but WITHOUT ANY WARRANTY; without even the implied
// warranty of MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with these designs.  (It's in the $(ROOT)/doc directory.  Run make
// with no target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	LGPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/lgpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <stdio.h>

#include "aximemsim.h"

class	ADRFIFO {
	typedef	{
		int id; unsigned addr;
	} ADRFIFOELEMENT;
	int	m_head, m_tail, m_len;
	int	*m_mem;
public:
	ADRFIFO(int ln) {
		m_mem = new ADRFIFOELEMENT[ln];
		m_head = m_tail = 0;
		m_len = ln;
	}

	void	push(int id, unsigned addr) {
		int nhead = m_head + 1;
		if (nhead >= m_len)
			nhead = 0;
		assert(nhead != m_tail);
		m_mem[m_head].id   = id;
		m_mem[m_head].addr = addr;
		m_head = nhead;
	}

	bool	full(void) {
		int nhead = m_head + 1;
		if (nhead >= m_len)
			nhead = 0;
		return (nhead == m_tail);
	}

	bool	valid(void) {
		return (m_head != m_tail);
	}

	int	id(void)	{ return m_mem[m_tail].id; }
	int	addr(void)	{ return m_mem[m_tail].addr; }
	int	pop(void)	{
		if (m_tail == m_head)
			return;
		m_tail++;
		if (m_tail >= m_len)
			m_tail = 0;
	}
};

class	DATFIFO {
	typedef	{
		unsigned data[4];
		int	strb;
	} DATAFIFOELEMENT;
	int	m_head, m_tail, m_len;
	int	*m_mem;
public:
	DATAFIFO(int ln) {
		m_mem = new DATAFIFOELEMENT[ln];
		m_head = m_tail = 0;
		m_len = ln;
	}

	void	push(int strb, unsigned dat0, unsigned dat1,
			unsigned dat, unsigned dat3) {
		int nhead = m_head + 1;
		if (nhead >= m_len)
			nhead = 0;
		assert(nhead != m_tail);
		m_mem[m_head].strb   = id;
		m_mem[m_head].data[0] = dat0;
		m_mem[m_head].data[1] = dat1;
		m_mem[m_head].data[2] = dat2;
		m_mem[m_head].data[3] = dat3;
		m_head = nhead;
	}

	bool	full(void) {
		int nhead = m_head + 1;
		if (nhead >= m_len)
			nhead = 0;
		return (nhead == m_tail);
	}

	bool	valid(void) {
		return (m_head != m_tail);
	}

	int	strb(void)	{ return m_mem[m_tail].strb; }
	unsigned *data(void)	{ return &m_mem[m_tail].data[0]; }
	int	pop(void)	{
		if (m_tail == m_head)
			return;
		m_tail++;
		if (m_tail >= m_len)
			m_tail = 0;
	}
};

AXIMEMSIM::AXIMEMSIM(unsigned abits) {
	// abits is the number of bits in a memory address, referencing 8-bit
	// bytes, therefore we can size our memory properly.
	assert(abits>2);
	m_len = (1<<(abits-2));
	m_mask= m_len-1;
	m_mem = new unsigned[(1<<(abits-2))];

	memset(m_mem, 0, sizeof(unsigned)<<(abits-2));
}

void AXIMEMSIM::apply(AXIBUS &bus) {
	// First, let's validate our inputs ..., and queue up our outputs
	bus.ar.ready = (!m_readfifo.full());
	bus.aw.ready = (!m_writefifo.full());
	bus.w.ready  = (!m_wdata.full());
	if (bus.r.ready)
		bus.r.valid = false;
	if (bus.b.ready)
		bus.b.valid = false;

	if ((bus.ar.ready)&&(!m_readfifo.full())) {
		assert(bus.ar.len  == 0);
		assert(bus.ar.size  == 5);
		assert(bus.ar.burst == 1);
		assert(bus.ar.lock  == 0);
		assert(bus.ar.cache == 2);
		assert(bus.ar.prot  == 2);
		assert(bus.ar.qos   == 0);

		m_readfifo.push(bus.ar.id, bus.ar.addr);
	}

	if ((bus.aw.ready)&&(!m_writefifo.full())) {
		assert(bus.aw.len   == 0);
		assert(bus.aw.size  == 5);
		assert(bus.aw.burst == 1);
		assert(bus.aw.lock  == 0);
		assert(bus.aw.cache == 2);
		assert(bus.aw.prot  == 2);
		assert(bus.aw.qos   == 0);

		m_awfifo.push(bus.aw.id, bus.aw.addr);
	}

	if ((bus.w.ready)&&(!m_writedata.full())) {
		m_writefifo.push(bus.aw.strb, bus.aw.data[0], bus.aw.data[1],
			bus.aw.data[2], bus.aw.data[3]);

	if (m_respfifo[m_now].valid) {
		if (m_respfifo[m_now].read) {
			if ((!bus.r.valid)||(bus.r.ready)) {
				bus.r.data[0] = m_respfifo[m_now].data[0];
				bus.r.data[1] = m_respfifo[m_now].data[1];
				bus.r.data[2] = m_respfifo[m_now].data[2];
				bus.r.data[3] = m_respfifo[m_now].data[3];
				bus.r.valid = true;
				m_now++;
			}
		} else if ((!bus.b.valid)||(bus.b.ready)) {
			bus.b.resp = m_respfifo[m_now].resp;
			bus.b.id = m_respfifo[m_now].id;
			bus.b.valid = true;
			m_now++;
		}
	}
}

