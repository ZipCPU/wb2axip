////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./testb.h
//
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	
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
#ifndef	TESTB_H
#define	TESTB_H

// #define TRACE_FST

#include <stdio.h>
#include <stdint.h>
#ifdef	TRACE_FST
#define	TRACECLASS	VerilatedFstC
#include <verilated_fst_c.h>
#else // TRACE_FST
#define	TRACECLASS	VerilatedVcdC
#include <verilated_vcd_c.h>
#endif

	//
	// The TESTB class is a useful wrapper for interacting with a Verilator
	// based design.  Key to its capabilities are the tick() method for
	// advancing the simulation timestep, and the opentrace() and
	// closetrace() methods for handling VCD tracefile generation.  To
	// use a non-VCD trace, redefine TRACECLASS before calling this
	// function to the trace class you wish to use.
//
template <class VA>	class TESTB {
public:
	VA	*m_core;
	bool		m_changed;
	TRACECLASS*	m_trace;
	bool		m_done, m_paused_trace;
	uint64_t	m_time_ps;

	//
	// Since design has only one clock within it, we won't need to use the
	// multiclock techniques, and so those aren't included here at this time.
	//

	TESTB(void) {
		m_core = new VA;
		m_time_ps  = 0ul;
		m_trace    = NULL;
		m_done     = false;
		m_paused_trace = false;
		Verilated::traceEverOn(true);
	}
	virtual ~TESTB(void) {
		if (m_trace) m_trace->close();
		delete m_core;
		m_core = NULL;
	}

	//
	// opentrace()
	//
	// Useful for beginning a (VCD) trace.  To open such a trace, just call
	// opentrace() with the name of the VCD file you'd like to trace
	// everything into
	virtual	void	opentrace(const char *vcdname, int depth=99) {
		if (!m_trace) {
			m_trace = new TRACECLASS;
			m_core->trace(m_trace, 99);
			m_trace->spTrace()->set_time_resolution("ps");
			m_trace->spTrace()->set_time_unit("ps");
			m_trace->open(vcdname);
			m_paused_trace = false;
		}
	}

	//
	// trace()
	//
	// A synonym for opentrace() above.
	//
	void	trace(const char *vcdname) {
		opentrace(vcdname);
	}

	//
	// pausetrace(pause)
	//
	// Set/clear a flag telling us whether or not to write to the VCD trace
	// file.  The default is to write to the file, but this can be changed
	// by calling pausetrace.  pausetrace(false) will resume tracing,
	// whereas pausetrace(true) will stop all calls to Verilator's trace()
	// function
	//
	virtual	bool	pausetrace(bool pausetrace) {
		m_paused_trace = pausetrace;
		return m_paused_trace;
	}

	//
	// pausetrace()
	//
	// Like pausetrace(bool) above, except that pausetrace() will return
	// the current status of the pausetrace flag above.  Specifically, it
	// will return true if the trace has been paused or false otherwise.
	virtual	bool	pausetrace(void) {
		return m_paused_trace;
	}

	//
	// closetrace()
	//
	// Closes the open trace file.  No more information will be written
	// to it
	virtual	void	closetrace(void) {
		if (m_trace) {
			m_trace->close();
			delete m_trace;
			m_trace = NULL;
		}
	}

	//
	// eval()
	//
	// This is a synonym for Verilator's eval() function.  It evaluates all
	// of the logic within the design.  AutoFPGA based designs shouldn't
	// need to be calling this, they should call tick() instead.  However,
	// in the off chance that your design inputs depend upon combinatorial
	// expressions that would be output based upon other input expressions,
	// you might need to call this function.
	virtual	void	eval(void) {
		m_core->eval();
	}

	//
	// tick()
	//
	// tick() is the main entry point into this helper core.  In general,
	// tick() will advance the clock by one clock tick.  In a multiple clock
	// design, this will advance the clocks up until the nearest clock
	// transition.
	virtual	void	tick(void) {
		// Pre-evaluate, to give verilator a chance
		// to settle any combinatorial logic that
		// that may have changed since the last clock
		// evaluation, and then record that in the
		// trace.
		eval();
		if (m_trace && !m_paused_trace) m_trace->dump(m_time_ps+2500);

		// Advance the one simulation clock, clk
		m_time_ps+= 5000;
		m_core->S_AXI_ACLK = 1;
		eval();
		// If we are keeping a trace, dump the current state to that
		// trace now
		if (m_trace && !m_paused_trace) {
			m_trace->dump(m_time_ps);
			m_trace->flush();
		}

		// <SINGLE CLOCK ONLY>:
		// Advance the clock again, so that it has its negative edge
		m_core->S_AXI_ACLK = 0;
		m_time_ps+= 5000;
		eval();
		if (m_trace && !m_paused_trace) m_trace->dump(m_time_ps);

		// Call to see if any simulation components need
		// to advance their inputs based upon this clock
		sim_clk_tick();
	}

	virtual	void	sim_clk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual bool	done(void) {
		if (m_done)
			return true;

		if (Verilated::gotFinish())
			m_done = true;

		return m_done;
	}

	//
	// reset()
	//
	// Sets the i_reset input for one clock tick.  It's really just a
	// function for the capabilies shown below.  You'll want to reset any
	// external input values before calling this though.
	virtual	void	reset(void) {
		m_core->S_AXI_ARESETN = 0;
		tick();
		m_core->S_AXI_ARESETN = 1;
		// printf("RESET\n");
	}
};

#endif	// TESTB

