////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/mcy/easyaxil/easyaxil_tb.cpp
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	This is an automatic test-bench script for the EasyAXIL
//		core.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2025, Gisselquist Technology, LLC
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
//
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
// }}}
#include "verilated.h"
#include "Veasyaxil.h"

#include "testb.h"
#include "axi_tb.h"

typedef	AXI_TB<TESTB<Veasyaxil> >	EASYAXIL_TB;

bool	checkreg(EASYAXIL_TB *tb, int reg) {
	// Convert to an address
	unsigned addr = reg * 4;

	// Check that we can write to each individual bit
	for(int b=0; b<32; b++) {
		uint32_t	v, c;

		v = (1<<b);
		tb->writeio(addr, v);
		c = tb->readio(addr);

		if (v != c)
			return false;
printf("CHECK-bit %d: 0x%08x == 0x%08x\n", b, v, c);
	}

	// Let's try writing some random data
	for(int b=0; b<32; b++) {
		uint32_t	v, c;

		v = rand();
		tb->writeio(addr, v);
		c = tb->readio(addr);

		if (v != c)
			return false;
printf("CHECK-rand %d: 0x%08x == 0x%08x\n", b, v, c);
	}

	// Success
	return true;
}

void	usage(void) {
	fprintf(stderr, "USAGE: easyaxil_tb <index>\n");
	fprintf(stderr, "\t<index>\tControls which mutation we examin\n");
}

int	main(int argc, char **argv) {
	const	char *trace_file = NULL; // "trace.vcd";
	Verilated::commandArgs(argc, argv);
	EASYAXIL_TB	*tb = new EASYAXIL_TB;
	bool		failed = false;

	if (argc > 2) {
		fprintf(stderr, "ERR: Too many arguments\n");
		usage();
		exit(EXIT_FAILURE);
	}

	int	index = 0;
	if (argc > 1)
		index = atoi(argv[1]);

	if (trace_file)
		tb->opentrace(trace_file);

	tb->m_tb->m_core->mutsel = index;
	tb->reset();

	if (!failed) failed = !checkreg(tb, 0);
	if (!failed) failed = !checkreg(tb, 1);
	if (!failed) failed = !checkreg(tb, 2);
	if (!failed) failed = !checkreg(tb, 3);

	if (failed) {
		printf("TEST FAIL!\n");
		return EXIT_FAILURE;
	}
	printf("SUCCESS!\n");
	return	EXIT_SUCCESS;
}

