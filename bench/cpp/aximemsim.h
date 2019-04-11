////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	aximemsim.h
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	To attempt to emulate how the MIG responds to AXI requests.
//		Of course, this is written with no knowledge of how MIG actually
//	responds, just a touch of knowledge regarding how a DDR3 memory works,
//	so ... your mileage might vary.
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
#ifndef	AXIMEMSIM_H
#define	AXIMEMSIM_H

typedef	struct {
	unsigned	addr;
	int		id, len, size, burst, lock, cache, prot, qos;
	bool		ready, valid;
} AXI_AWBUS;

typedef	struct {
	unsigned	addr;
	int		id, len, size, burst, lock, cache, prot, qos;
	bool		ready, valid;
} AXI_ARBUS;

typedef	struct {
	int		strb;
	unsigned	data[4];	// 128 bits
	int		ready, valid, last;
} AXI_WBUS;

typedef	struct {
	int		id, resp;
	int		ready, valid;
} AXI_WRESP;

typedef	struct {
	int		id, resp;
	unsigned	data[4];	// 128 bits
	int		ready, valid, last;
} AXI_RDATA;

typedef	struct	{
	AXI_AWBUS	aw;
	AXI_ARBUS	ar;
	AXI_WBUS	w;
	AXI_WRESP	b;
	AXI_RDATA	r;
} AXIBUS;

class	AXIMEMSIM {
	unsigned	*m_mem;
public:
	AXIMEMSIM(unsigned abits);
	void	apply(AXIBUS &bus);
};

#endif
