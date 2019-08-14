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
## Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
HELPERS   := sfifo addrdecode wbarbiter skidbuffer
CROSSBARS := axilxbar wbxbar # axixbar
BRIDGES   := wbm2axilite axlite2wbsp wbp2classic wbc2pipeline # wbm2axisp axi2axilite axilite2axi
AXISLAVES := demoaxi # demofull xlnxfull axisafety
TESTS := $(HELPERS) $(BRIDGES) $(CROSSBARS) $(AXISLAVES)
.PHONY: $(TESTS)
all: $(TESTS)
RTL        := ../../rtl
SMTBMC     := yosys-smtbmc

#
# Helpers
WBARB      := wbarbiter
DECODER    := addrdecode
SFIFO      := sfifo
SKIDBUFFER := skidbuffer
XBAR := $(RTL)/$(DECODER).v $(RTL)/$(SFIFO).v $(RTL)/$(SKIDBUFFER).v
#
# Slaves
DEMOAXI    := demoaxi
XILINXDEMO := xlnxdemo
XLNXSTREAM := xlnxstream_2018_3
#
# Bridges
WB2AXI     := wbm2axisp
WB2LITE    := wbm2axilite
RDLITE     := axilrd2wbsp
WRLITE     := axilwr2wbsp
AXLITE     := axlite2wbsp
WBP2CLASSIC:= wbp2classic
WBC2PIPELIN:= wbc2pipeline
#
# Crossbars
AXILXBAR   := axilxbar
WBXBAR     := wbxbar
WBXBAR4x8  := wbxbar4x8
WBXBAR1x8  := wbxbar1x8
WBXBAR4x1  := wbxbar4x1
# AXIXBAR    := axixbar
#
# Bus property sets
AXIL       := faxil_master.v faxil_slave.v
WB         := fwb_master.v   fwb_slave.v
WBC        := fwbc_master.v  fwbc_slave.v
AXIS       := faxis_master.v faxis_slave.v

.PHONY: $(WBARB) $(WB2AXI) $(RDLITE) $(WRLITE) $(AXLITE) $(WB2LITE) $(DEMOAXI)

$(WBARB): $(WBARB)_prf/PASS $(WBARB)_cvr/PASS
$(WBARB)_prf/PASS: $(RTL)/$(WBARB).v $(WBARB).sby $(WB)
	sby -f $(WBARB).sby prf
$(WBARB)_cvr/PASS: $(RTL)/$(WBARB).v $(WBARB).sby $(WB)
	sby -f $(WBARB).sby cvr

#
# This WB to AXI proof is contained elsewhere
#
# .PHONY: $(WB2AXI)
# $(WB2AXI): $(WB2AXI)/PASS
# $(WB2AXI)/PASS: $(RTL)/$(WB2AXI).v $(WB2AXI).sby $(WB)
#	sby -f $(WB2AXI).sby

$(RDLITE): $(RDLITE)_prf/PASS $(RDLITE)_cvr/PASS
$(RDLITE)_prf/PASS: $(RDLITE).sby $(RTL)/$(RDLITE).v $(WB) $(AXIL)
	sby -f $(RDLITE).sby prf
$(RDLITE)_cvr/PASS: $(RDLITE).sby $(RTL)/$(RDLITE).v $(WB) $(AXIL)
	sby -f $(RDLITE).sby cvr

$(WRLITE): $(WRLITE)_prf/PASS $(WRLITE)_cvr/PASS
$(WRLITE)_prf/PASS: $(WRLITE).sby $(RTL)/$(WRLITE).v $(WB) $(AXIL)
	sby -f $(WRLITE).sby prf
$(WRLITE)_cvr/PASS: $(WRLITE).sby $(RTL)/$(WRLITE).v $(WB) $(AXIL)
	sby -f $(WRLITE).sby cvr

.PHONY: $(AXLITE)
$(AXLITE): $(AXLITE)_prf/PASS $(AXLITE)_cvr/PASS
AXLITE_DEPS := $(RTL)/$(RDLITE).v $(RTL)/$(WRLITE).v $(AXIL) $(WB)	\
	$(RTL)/$(WBARB).v $(AXLITE).sby $(RTL)/$(AXLITE).v		\
	$(RDLITE)_prf/PASS $(RDLITE)_cvr/PASS				\
	$(WRLITE)_prf/PASS $(WRLITE)_cvr/PASS

$(AXLITE)_prf/PASS: $(AXLITE_DEPS)
	sby -f $(AXLITE).sby prf

$(AXLITE)_cvr/PASS: $(AXLITE_DEPS)
	sby -f $(AXLITE).sby cvr

.PHONY: $(WB2LITE)
$(WB2LITE): $(WB2LITE)_cvr/PASS $(WB2LITE)_prf/PASS
$(WB2LITE)_prf/PASS: $(RTL)/$(WB2LITE).v $(WB) $(AXIL)
$(WB2LITE)_prf/PASS: $(WB2LITE).sby
	sby -f $(WB2LITE).sby prf

$(WB2LITE)_cvr/PASS: $(RTL)/$(WB2LITE).v $(WB) $(AXIL)
$(WB2LITE)_cvr/PASS: $(WB2LITE).sby
	sby -f $(WB2LITE).sby cvr

$(DEMOAXI): $(DEMOAXI)_prf/PASS $(DEMOAXI)_cvr/PASS
$(DEMOAXI)_prf/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby $(AXIL)
	sby -f $(DEMOAXI).sby prf
$(DEMOAXI)_cvr/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby $(AXIL)
	sby -f $(DEMOAXI).sby cvr

.PHONY: $(XILINXDEMO)
$(XILINXDEMO): $(XILINXDEMO)_prf/PASS $(XILINXDEMO)_cvr/PASS
$(XILINXDEMO)_prf/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	@echo "Expect the Xilinx demo proof to fail."
	@echo "Xilinx's code didn't work in the first place."
	sby -f $(XILINXDEMO).sby prf
$(XILINXDEMO)_cvr/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	sby -f $(XILINXDEMO).sby cvr


.PHONY: $(AXILXBAR) $(AXILXBAR)prf $(AXILXBAR)cvr
$(AXILXBAR): $(AXILXBAR)prf $(AXILXBAR)cvr
$(AXILXBAR)prf: $(AXILXBAR)_prf4x8_lp/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf1x8_lp/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x1_lp/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x8/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf1x8/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x1/PASS
$(AXILXBAR)_prf4x8/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf4x8
$(AXILXBAR)_prf1x8/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf1x8
$(AXILXBAR)_prf4x1/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf4x1
$(AXILXBAR)_prf4x8_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf4x8_lp
$(AXILXBAR)_prf1x8_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf1x8_lp
$(AXILXBAR)_prf4x1_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby prf4x1_lp
$(AXILXBAR)cvr: $(AXILXBAR)_cvr4x8_lp/PASS
$(AXILXBAR)cvr: $(AXILXBAR)_cvr4x8/PASS
$(AXILXBAR)cvr: $(AXILXBAR)_cvr1x3_lp/PASS
$(AXILXBAR)cvr: $(AXILXBAR)_cvr1x3/PASS
$(AXILXBAR)cvr: $(AXILXBAR)_cvr4x1_lp/PASS
$(AXILXBAR)cvr: $(AXILXBAR)_cvr4x1/PASS
$(AXILXBAR)_cvr4x8/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr4x8
$(AXILXBAR)_cvr1x3/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr1x3
$(AXILXBAR)_cvr4x1/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr4x1
$(AXILXBAR)_cvr4x8_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr4x8_lp
$(AXILXBAR)_cvr1x3_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr1x3_lp
$(AXILXBAR)_cvr4x1_lp/PASS: $(AXILXBAR).sby $(RTL)/$(AXILXBAR).v $(AXIL) $(XBAR)
	sby -f $(AXILXBAR).sby cvr4x1_lp


.PHONY: $(WBXBAR) $(WBXBAR4x8) $(WBXBAR1x8) $(WBXBAR4x1)
.PHONY: $(WBXBAR)_prf $(WBXBAR)_cvr
.PHONY: $(WBXBAR4x8)_prf $(WBXBAR4x8)_cvr
.PHONY: $(WBXBAR1x8)_prf $(WBXBAR1x8)_cvr
.PHONY: $(WBXBAR4x1)_prf $(WBXBAR4x1)_cvr
$(WBXBAR): $(WBXBAR4x8) $(WBXBAR1x8) $(WBXBAR4x1)
$(WBXBAR)_prf: $(WBXBAR4x8)_prf $(WBXBAR1x8)_prf $(WBXBAR4x1)_prf
$(WBXBAR)_cvr: $(WBXBAR4x8)_cvr $(WBXBAR1x8)_cvr $(WBXBAR4x1)_cvr

$(WBXBAR4x8): $(WBXBAR4x8)_prf $(WBXBAR4x8)_cvr
$(WBXBAR1x8): $(WBXBAR1x8)_prf $(WBXBAR1x8)_cvr
$(WBXBAR4x1): $(WBXBAR4x1)_prf $(WBXBAR4x1)_cvr

$(WBXBAR4x8)_prf: wbxbar_prf4x8_buflp/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_buf/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_lp/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_cheap/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_buflpko/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_bufko/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_lpko/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_cheapko/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_buflpkos/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_bufkos/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_lpkos/PASS
$(WBXBAR4x8)_prf: wbxbar_prf4x8_cheapkos/PASS

wbxbar_prf4x8_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_buflp
wbxbar_prf4x8_buf/PASS:      $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_buf
wbxbar_prf4x8_lp/PASS:       $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_lp
wbxbar_prf4x8_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_cheap
#
wbxbar_prf4x8_buflpko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_buflpko
wbxbar_prf4x8_bufko/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_bufko
wbxbar_prf4x8_lpko/PASS:     $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_lpko
wbxbar_prf4x8_cheapko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_cheapko
wbxbar_prf4x8_buflpkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_buflpkos
wbxbar_prf4x8_bufkos/PASS:   $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_bufkos
wbxbar_prf4x8_lpkos/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_lpkos
wbxbar_prf4x8_cheapkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x8_cheapkos
#
#
$(WBXBAR4x8)_cvr: wbxbar_cvr4x8_buflp/PASS
$(WBXBAR4x8)_cvr: wbxbar_cvr4x8_buf/PASS
$(WBXBAR4x8)_cvr: wbxbar_cvr4x8_lp/PASS
$(WBXBAR4x8)_cvr: wbxbar_cvr4x8_cheap/PASS
#
wbxbar_cvr4x8_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x8_buflp
wbxbar_cvr4x8_buf/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x8_buf
wbxbar_cvr4x8_lp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x8_lp
wbxbar_cvr4x8_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x8_cheap
#
#
$(WBXBAR1x8)_prf: wbxbar_prf1x8_buflp/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_buf/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_lp/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_cheap/PASS
#

wbxbar_prf1x8_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_buflp
wbxbar_prf1x8_buf/PASS:      $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_buf
wbxbar_prf1x8_lp/PASS:       $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_lp
wbxbar_prf1x8_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_cheap
#
#
$(WBXBAR1x8)_cvr: wbxbar_cvr1x3_buflp/PASS
$(WBXBAR1x8)_cvr: wbxbar_cvr1x3_buf/PASS
$(WBXBAR1x8)_cvr: wbxbar_cvr1x3_lp/PASS
$(WBXBAR1x8)_cvr: wbxbar_cvr1x3_cheap/PASS
#
#
wbxbar_cvr1x3_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr1x3_buflp
wbxbar_cvr1x3_buf/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr1x3_buf
wbxbar_cvr1x3_lp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr1x3_lp
wbxbar_cvr1x3_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr1x3_cheap
#
#
$(WBXBAR1x8)_prf: wbxbar_prf1x8_buflpko/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_bufko/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_lpko/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_cheapko/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_buflpkos/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_bufkos/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_lpkos/PASS
$(WBXBAR1x8)_prf: wbxbar_prf1x8_cheapkos/PASS
#

#
wbxbar_prf1x8_buflpko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_buflpko
wbxbar_prf1x8_bufko/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_bufko
wbxbar_prf1x8_lpko/PASS:     $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_lpko
wbxbar_prf1x8_cheapko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_cheapko
wbxbar_prf1x8_buflpkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_buflpkos
wbxbar_prf1x8_bufkos/PASS:   $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_bufkos
wbxbar_prf1x8_lpkos/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_lpkos
wbxbar_prf1x8_cheapkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf1x8_cheapkos
#
#
$(WBXBAR4x1)_prf: wbxbar_prf4x1_buflp/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_buf/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_lp/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_cheap/PASS
#
wbxbar_prf4x1_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_buflp
wbxbar_prf4x1_buf/PASS:      $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_buf
wbxbar_prf4x1_lp/PASS:       $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_lp
wbxbar_prf4x1_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_cheap
#
$(WBXBAR4x1)_prf: wbxbar_prf4x1_buflpko/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_bufko/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_lpko/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_cheapko/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_buflpkos/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_bufkos/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_lpkos/PASS
$(WBXBAR4x1)_prf: wbxbar_prf4x1_cheapkos/PASS
#
wbxbar_prf4x1_buflpko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_buflpko
wbxbar_prf4x1_bufko/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_bufko
wbxbar_prf4x1_lpko/PASS:     $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_lpko
wbxbar_prf4x1_cheapko/PASS:  $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_cheapko
wbxbar_prf4x1_buflpkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_buflpkos
wbxbar_prf4x1_bufkos/PASS:   $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_bufkos
wbxbar_prf4x1_lpkos/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_lpkos
wbxbar_prf4x1_cheapkos/PASS: $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby prf4x1_cheapkos
#
$(WBXBAR4x1)_cvr: wbxbar_cvr4x1_buflp/PASS
$(WBXBAR4x1)_cvr: wbxbar_cvr4x1_buf/PASS
$(WBXBAR4x1)_cvr: wbxbar_cvr4x1_lp/PASS
$(WBXBAR4x1)_cvr: wbxbar_cvr4x1_cheap/PASS
#
wbxbar_cvr4x1_buflp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x1_buflp
wbxbar_cvr4x1_buf/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x1_buf
wbxbar_cvr4x1_lp/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x1_lp
wbxbar_cvr4x1_cheap/PASS:    $(WBXBAR).sby $(RTL)/$(WBXBAR).v $(WB) $(XBAR)
	sby -f $(WBXBAR).sby cvr4x1_cheap
#
#


.PHONY: $(WBP2CLASSIC)
$(WBP2CLASSIC): $(WBP2CLASSIC)_prf/PASS $(WBP2CLASSIC)_cvr/PASS
$(WBP2CLASSIC)_prf/PASS: $(RTL)/$(WBP2CLASSIC).v $(WB) $(WBC)
	sby -f $(WBP2CLASSIC).sby prf
$(WBP2CLASSIC)_cvr/PASS: $(RTL)/$(WBP2CLASSIC).v $(WB) $(WBC)
	sby -f $(WBP2CLASSIC).sby cvr

.PHONY: $(WBC2PIPELIN)
$(WBC2PIPELIN): $(WBC2PIPELIN)_prf/PASS $(WBC2PIPELIN)_cvr/PASS
$(WBC2PIPELIN)_prf/PASS: $(RTL)/$(WBC2PIPELIN).v $(WB) $(WBC)
	sby -f $(WBC2PIPELIN).sby prf
$(WBC2PIPELIN)_cvr/PASS: $(RTL)/$(WBC2PIPELIN).v $(WB) $(WBC)
	sby -f $(WBC2PIPELIN).sby cvr

.PHONY: $(SFIFO)
$(SFIFO): $(SFIFO)_prf/PASS $(SFIFO)_cvr/PASS
$(SFIFO)_prf/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf
$(SFIFO)_cvr/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby cvr

.PHONY: $(DECODER)
$(DECODER): $(DECODER)_prfrlp/PASS $(DECODER)_cvrrlp/PASS
$(DECODER): $(DECODER)_prfr/PASS   $(DECODER)_cvrr/PASS
$(DECODER): $(DECODER)_prfc/PASS   $(DECODER)_cvrc/PASS
$(DECODER)_prfrlp/PASS: $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby prfrlp
$(DECODER)_prfr/PASS:   $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby prfr
$(DECODER)_prfc/PASS:   $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby prfc
$(DECODER)_cvrrlp/PASS: $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby cvrrlp
$(DECODER)_cvrr/PASS:   $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby cvrr
$(DECODER)_cvrc/PASS:   $(DECODER).sby $(RTL)/$(DECODER).v
	sby -f $(DECODER).sby cvrc

.PHONY: $(SKIDBUFFER)
$(SKIDBUFFER): $(SKIDBUFFER)_prfc/PASS $(SKIDBUFFER)_prfo/PASS
$(SKIDBUFFER): $(SKIDBUFFER)_lpc/PASS  $(SKIDBUFFER)_lpo/PASS
$(SKIDBUFFER): $(SKIDBUFFER)_cvr/PASS
$(SKIDBUFFER)_prfc/PASS: $(SKIDBUFFER).sby $(RTL)/$(SKIDBUFFER).v
	sby -f $(SKIDBUFFER).sby prfc
$(SKIDBUFFER)_prfo/PASS: $(SKIDBUFFER).sby $(RTL)/$(SKIDBUFFER).v
	sby -f $(SKIDBUFFER).sby prfo
$(SKIDBUFFER)_lpc/PASS:  $(SKIDBUFFER).sby $(RTL)/$(SKIDBUFFER).v
	sby -f $(SKIDBUFFER).sby lpc
$(SKIDBUFFER)_lpo/PASS:  $(SKIDBUFFER).sby $(RTL)/$(SKIDBUFFER).v
	sby -f $(SKIDBUFFER).sby lpo
$(SKIDBUFFER)_cvr/PASS:  $(SKIDBUFFER).sby $(RTL)/$(SKIDBUFFER).v
	sby -f $(SKIDBUFFER).sby cvr




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
	rm -rf  $(XLNXSTREAM)_cvr/ $(XLNXSTREAM)_prf
	# rm -f *.check
