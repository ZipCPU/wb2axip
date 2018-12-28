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
## Copyright (C) 2017-2018, Gisselquist Technology, LLC
##
## This file is part of the pipelined Wishbone to AXI converter project, a
## project that contains multiple bus bridging designs and formal bus property
## sets.
##
## The bus bridge designs and property sets are free RTL designs: you can
## redistribute them and/or modify any of them under the terms of the GNU
## Lesser General Public License as published by the Free Software Foundation,
## either version 3 of the License, or (at your option) any later version.
##
## The bus bridge designs and property sets are distributed in the hope that
## they will be useful, but WITHOUT ANY WARRANTY; without even the implied
## warranty of MERCHANTIBILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU Lesser General Public License for more details.
##
## You should have received a copy of the GNU Lesser General Public License
## along with these designs.  (It's in the $(ROOT)/doc directory.  Run make
## with no target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	LGPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/lgpl.html
##
################################################################################
##
##
TESTS := wbm2axisp wbarbiter wbm2axilite axilrd2wbsp axilwr2wbsp demoaxi axlite2wbsp # axim2wbsp
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

DEMOAXI    := demoaxi
WBARB      := wbarbiter
WB2AXI     := wbm2axisp
AXI2WB     := axim2wbsp
WB2LITE    := wbm2axilite
RDLITE     := axilrd2wbsp
WRLITE     := axilwr2wbsp
AXLITE     := axlite2wbsp
XILINXDEMO := xlnxdemo

.PHONY: $(WBARB) $(WB2AXI) $(RDLITE) $(WRLITE) $(AXLITE) $(WB2LITE) $(DEMOAXI)

$(WBARB): $(WBARB)_prf/PASS $(WBARB)_cvr/PASS
$(WBARB)_prf/PASS: $(RTL)/$(WBARB).v $(WBARB).sby fwb_master.v fwb_slave.v
	sby -f $(WBARB).sby
$(WBARB)_cvr/PASS: $(RTL)/$(WBARB).v $(WBARB).sby fwb_master.v fwb_slave.v
	sby -f $(WBARB).sby

.PHONY: $(WB2AXI)
$(WB2AXI): $(WB2AXI)/PASS
$(WB2AXI)/PASS: $(RTL)/$(WB2AXI).v $(WB2AXI).sby fwb_slave.v faxi_master.v
	sby -f $(WB2AXI).sby

$(RDLITE): $(RDLITE)_prf/PASS $(RDLITE)_cvr/PASS
$(RDLITE)_prf/PASS: $(RDLITE).sby $(RTL)/$(RDLITE).v fwb_master.v faxil_slave.v
	sby -f $(RDLITE).sby prf
$(RDLITE)_cvr/PASS: $(RDLITE).sby $(RTL)/$(RDLITE).v fwb_master.v faxil_slave.v
	sby -f $(RDLITE).sby cvr

$(WRLITE): $(WRLITE)_prf/PASS $(WRLITE)_cvr/PASS
$(WRLITE)_prf/PASS: $(WRLITE).sby $(RTL)/$(WRLITE).v fwb_master.v faxil_slave.v
	sby -f $(WRLITE).sby prf
$(WRLITE)_cvr/PASS: $(WRLITE).sby $(RTL)/$(WRLITE).v fwb_master.v faxil_slave.v
	sby -f $(WRLITE).sby cvr

$(AXLITE): $(AXLITE)_prf/PASS $(AXLITE)_cvr/PASS
AXLITE_DEPS := $(RTL)/$(RDLITE).v $(RTL)/$(WRLITE).v \
	$(RTL)/$(WBARB).v fwb_master.v faxil_slave.v			\
	$(AXLITE).sby $(RTL)/$(AXLITE).v				\
	$(RDLITE)_prf/PASS $(RDLITE)_cvr/PASS				\
	$(WRLITE)_prf/PASS $(WRLITE)_cvr/PASS

$(AXLITE)_prf/PASS: $(AXLITE_DEPS)
	sby -f $(AXLITE).sby prf

$(AXLITE)_cvr/PASS: $(AXLITE_DEPS)
	sby -f $(AXLITE).sby cvr

.PHONY: $(WB2LITE)
$(WB2LITE): $(WB2LITE)_cvr/PASS $(WB2LITE)_prf/PASS
$(WB2LITE)_prf/PASS: $(RTL)/$(WB2LITE).v $(WB2LITE).ys
$(WB2LITE)_prf/PASS: $(WB2LITE).sby fwb_slave.v faxil_master.v
	sby -f $(WB2LITE).sby prf

$(WB2LITE)_cvr/PASS: $(RTL)/$(WB2LITE).v $(WB2LITE).ys
$(WB2LITE)_cvr/PASS: $(WB2LITE).sby fwb_slave.v faxil_master.v
	sby -f $(WB2LITE).sby cvr

$(DEMOAXI): $(DEMOAXI)_prf/PASS $(DEMOAXI)_cvr/PASS
$(DEMOAXI)_prf/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby faxil_slave.v
	sby -f $(DEMOAXI).sby prf
$(DEMOAXI)_cvr/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby faxil_slave.v
	sby -f $(DEMOAXI).sby cvr

.PHONY: $(XILINXDEMO)
$(XILINXDEMO): $(XILINXDEMO)_prf/PASS $(XILINXDEMO)_cvr/PASS
$(XILINXDEMO)_prf/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby faxil_slave.v
	sby -f $(XILINXDEMO).sby prf
$(XILINXDEMO)_cvr/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby faxil_slave.v
	sby -f $(XILINXDEMO).sby cvr


.PHONY: $(AXI2WB)
$(AXI2WB)/PASS: $(RTL)/$(AXI2WB).v $(AXI2WB).ys
$(AXI2WB)/PASS: fwb_slave.v
$(AXI2WB)/PASS: fwb_master.v
$(AXI2WB)/PASS: faxi_slave.v
$(AXI2WB)/PASS: f_order.v
$(AXI2WB)/PASS: $(RTL)/aximwr2wbsp.v $(RTL)/aximrd2wbsp.v
$(AXI2WB)/PASS: $(RTL)/wbarbiter.v
	echo "The AXI2WB bridge does not work yet, so I do not expect this one to pass"
	echo sby -f $(AXI2WB).sby

.PHONY: clean
clean:
	rm -rf  $(WBARB)_prf/ $(WBARB)_cvr/
	rm -rf  $(WB2LITE)_cvr/ $(WB2LITE)_prf/
	rm -rf  $(RDLITE)_cvr/  $(RDLITE)_prf
	rm -rf  $(WRLITE)_cvr/  $(WRLITE)_prf
	rm -rf  $(AXLITE)_cvr/  $(AXLITE)_prf
	rm -rf  $(DEMOAXI)_cvr/ $(DEMOAXI)_prf
	@# The three broken cores, to include Xilinx's
	rm -rf  $(WB2AXI)/
	rm -rf  $(AXI2WB)/
	rm -rf  $(XILINXDEMO)_cvr/ $(XILINXDEMO)_prf
	# rm -f *.check
