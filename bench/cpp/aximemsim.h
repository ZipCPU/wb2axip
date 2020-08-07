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
// Copyright (C) 2016-2020, Gisselquist Technology, LLC
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
