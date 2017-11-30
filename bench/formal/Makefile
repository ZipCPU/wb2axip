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
TESTS := wbm2axisp wbarbiter # axim2wbsp
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl
SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
# SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER)
# BMCARGS := $(SOLVER)
INDARGS := $(SOLVER) -i

WBARB    := wbarbiter
WB2AXI   := wbm2axisp
AXI2WB   := axim2wbsp

$(WBARB).smt2: $(RTL)/$(WBARB).v fwb_master.v fwb_slave.v $(WBARB).ys
	yosys -ql $(WBARB).yslog -s $(WBARB).ys

$(WB2AXI).smt2: $(RTL)/$(WB2AXI).v $(WB2AXI).ys fwb_slave.v faxi_master.v
	yosys -ql $(WB2AXI).yslog -s $(WB2AXI).ys

$(AXI2WB).smt2: $(RTL)/$(AXI2WB).v $(AXI2WB).ys fwb_master.v faxi_slave.v
$(AXI2WB).smt2: $(RTL)/$(AXI2WB).v $(RTL)/aximwr2wbsp.v $(RTL)/aximrd2wbsp.v
	yosys -ql $(AXI2WB).yslog -s $(AXI2WB).ys

$(WBARB) : $(WBARB).check
$(WBARB).check: $(WBARB).smt2
	rm -f $@
	$(SMTBMC) $(BMCARGS) -t 36 --dump-vcd $(WBARB).vcd $(WBARB).smt2
	$(SMTBMC) $(INDARGS) -t 32 --dump-vcd $(WBARB).vcd $(WBARB).smt2
	touch $@

$(WB2AXI) : $(WB2AXI).check
$(WB2AXI).check: $(WB2AXI).smt2
	rm -f $@
	$(SMTBMC) $(BMCARGS) -t 36 --dump-vcd $(WB2AXI).vcd $(WB2AXI).smt2
	$(SMTBMC) $(INDARGS) -t 32 --dump-vcd $(WB2AXI).vcd $(WB2AXI).smt2
	touch $@

$(AXI2WB) : $(AXI2WB).check
$(AXI2WB).check: $(AXI2WB).smt2
	rm -f $@
	$(SMTBMC) $(BMCARGS) -t 36 --dump-vcd $(AXI2WB).vcd $(AXI2WB).smt2
	$(SMTBMC) $(INDARGS) -t 32 --dump-vcd $(AXI2WB).vcd $(AXI2WB).smt2
	touch $@

.PHONY: clean
clean:
	rm -f  $(WBARB).smt2  $(WBARB).yslog   $(WBARB)*.vcd
	rm -f  $(WB2AXI).smt2 $(WB2AXI).yslog  $(WB2AXI)*.vcd
	rm -f  $(AXI2WB).smt2 $(AXI2WB).yslog  $(AXI2WB)*.vcd
	rm -f *.check
