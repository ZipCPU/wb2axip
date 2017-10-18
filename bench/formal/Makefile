################################################################################
##
## Filename:	Makefile
##
## Project:	Pipelined Wishbone to AXI converter
##
## Purpose:	To direct the formal verification of the bus bridge
##		sources.
##
## Targets:	The default target, all, tests all of the components defined
##		within this module.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
##
TESTS := wbm2axisp
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl
SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
# SOLVER  := -s yices
SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER)
# BMCARGS := $(SOLVER)
INDARGS := $(SOLVER) -i

WB2AXI    := wbm2axisp
WB2AXIBMC := $(WB2AXI)_bmc
WB2AXIIND := $(WB2AXI)_ind

$(WB2AXI).smt2: $(RTL)/$(WB2AXI).v
	yosys -ql $(WB2AXI).yslog -s $(WB2AXI).ys

$(WB2AXI) : $(WB2AXI).check
$(WB2AXI).check: $(WB2AXI).smt2
	$(SMTBMC) $(BMCARGS) -t 24 --dump-smt2 $(WB2AXIBMC).smt2 --dump-vcd $(WB2AXIBMC).vcd $(WB2AXI).smt2
	$(SMTBMC) $(INDARGS) -t 24 --dump-smt2 $(WB2AXIIND).smt2 --dump-vcd $(WB2AXIIND).vcd $(WB2AXI).smt2
	touch $@

.PHONY: clean
clean:
	rm -f  $(WB2AXI).smt2  $(WB2AXIBMC).smt2  $(WB2AXIIND).smt2  $(WB2AXI)*.vcd
	rm -f *.check
