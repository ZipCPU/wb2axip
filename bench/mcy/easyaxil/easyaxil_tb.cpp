////////////////////////////////////////////////////////////////////////////////
//
// Filename:	easyaxil_tb.cpp
//
// Project:	AXI DMA Check: A utility to measure AXI DMA speeds
//
// Purpose:	This is an automatic test-bench script for the EasyAXIL
//		core.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2020, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

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

