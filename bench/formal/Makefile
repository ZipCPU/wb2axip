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
## Copyright (C) 2017-2020, Gisselquist Technology, LLC
##
## This file is part of the WB2AXIP project.
##
## The WB2AXIP project contains free software and gateware, licensed under the
## Apache License, Version 2.0 (the "License").  You may not use this project,
## or this file, except in compliance with the License.  You may obtain a copy
## of the License at
##
##	http://www.apache.org/licenses/LICENSE-2.0
##
## Unless required by applicable law or agreed to in writing, software
## distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
## WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
## License for the specific language governing permissions and limitations
## under the License.
##
################################################################################
##
##
HELPERS   := sfifo addrdecode wbarbiter skidbuffer
CROSSBARS := axilxbar wbxbar # axixbar
BRIDGES   := wbm2axilite axlite2wbsp wbp2classic wbc2pipeline axilsingle axildouble # wbm2axisp axi2axilite axilite2axi
AXISLAVES := demoaxi easyaxil # demofull xlnxfull axisafety
FIREWALLS := wbsafety # axisafety
TESTS := $(HELPERS) $(AXISLAVES) $(FIREWALLS) $(BRIDGES) $(CROSSBARS)
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
XBAR := $(RTL)/$(DECODER).v $(RTL)/$(SKIDBUFFER).v
#
# Slaves
DEMOAXI    := demoaxi
EASYAXIL   := easyaxil
XILINXDEMO := xlnxdemo
XLNXSTREAM := xlnxstream_2018_3
#
# Bridges
WB2AXI     := wbm2axisp
WB2LITE    := wbm2axilite
RDLITE     := axilrd2wbsp
WRLITE     := axilwr2wbsp
AXLITE     := axlite2wbsp
AXILSINGLE := axilsingle
AXILDOUBLE := axildouble
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
# Firewalls
WBSAFETY   := wbsafety
#
# Bus property sets
AXIL       := faxil_master.v faxil_slave.v
WB         := fwb_master.v   fwb_slave.v
WBC        := fwbc_master.v  fwbc_slave.v
AXIS       := faxis_master.v faxis_slave.v

.PHONY: $(WBARB) $(WB2AXI) $(RDLITE) $(WRLITE) $(AXLITE) $(WB2LITE) $(DEMOAXI)
.PHONY: $(EASYAXIL)

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

.PHONY: $(DEMOAXI)
$(DEMOAXI): $(DEMOAXI)_prf/PASS $(DEMOAXI)_cvr/PASS
$(DEMOAXI)_prf/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby $(AXIL)
	sby -f $(DEMOAXI).sby prf
$(DEMOAXI)_cvr/PASS: $(RTL)/$(DEMOAXI).v $(DEMOAXI).sby $(AXIL)
	sby -f $(DEMOAXI).sby cvr

.PHONY: $(EASYAXIL)
$(EASYAXIL): $(EASYAXIL)_prfreg/PASS $(EASYAXIL)_prfreglp/PASS $(EASYAXIL)_cvrreg/PASS
$(EASYAXIL): $(EASYAXIL)_prfskd/PASS $(EASYAXIL)_prfskdlp/PASS $(EASYAXIL)_cvrskd/PASS
$(EASYAXIL)_prfreg/PASS: $(RTL)/$(EASYAXIL).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby prfreg
$(EASYAXIL)_prfreglp/PASS: $(RTL)/$(EASYAXIL).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby prfreglp
$(EASYAXIL)_cvrreg/PASS: $(RTL)/$(EASYAXIL).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby cvrreg
$(EASYAXIL)_prfskd/PASS: $(RTL)/$(EASYAXIL).v $(RTL)/$(SKIDBUFFER).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby prfskd
$(EASYAXIL)_prfskdlp/PASS: $(RTL)/$(EASYAXIL).v $(RTL)/$(SKIDBUFFER).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby prfskdlp
$(EASYAXIL)_cvrskd/PASS: $(RTL)/$(EASYAXIL).v $(RTL)/$(SKIDBUFFER).v $(EASYAXIL).sby $(AXIL)
	sby -f $(EASYAXIL).sby cvrskd

.PHONY: $(XILINXDEMO)
$(XILINXDEMO): $(XILINXDEMO)_prf/FAIL $(XILINXDEMO)_cvr/PASS
$(XILINXDEMO)_prf/FAIL: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	@echo "Expect the Xilinx demo proof to fail."
	@echo "Xilinx's code didn't work in the first place."
	sby -f $(XILINXDEMO).sby prf
$(XILINXDEMO)_cvr/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	sby -f $(XILINXDEMO).sby cvr


.PHONY: $(AXILXBAR) $(AXILXBAR)prf $(AXILXBAR)cvr $(AXILXBAR)_prf
$(AXILXBAR): $(AXILXBAR)prf $(AXILXBAR)cvr
$(AXILXBAR)_prf: $(AXILXBAR)prf
$(AXILXBAR)prf: $(AXILXBAR)_prf1x8_lp/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x1_lp/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf1x8/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x1/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x8/PASS
$(AXILXBAR)prf: $(AXILXBAR)_prf4x8_lp/PASS
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
$(WBXBAR): $(WBXBAR4x1)_prf
$(WBXBAR): $(WBXBAR1x8)_prf
$(WBXBAR): $(WBXBAR4x8)_prf
$(WBXBAR): $(WBXBAR4x1)_cvr
$(WBXBAR): $(WBXBAR1x8)_cvr
$(WBXBAR): $(WBXBAR4x8)_cvr
$(WBXBAR)_prf: $(WBXBAR4x1)_prf $(WBXBAR1x8)_prf $(WBXBAR4x8)_prf
$(WBXBAR)_cvr: $(WBXBAR4x1)_cvr $(WBXBAR1x8)_cvr $(WBXBAR4x8)_cvr

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

.PHONY: $(AXILSINGLE)
$(AXILSINGLE): $(AXILSINGLE)_prf/PASS $(AXILSINGLE)_cvr/PASS
$(AXILSINGLE)_prf/PASS: $(RTL)/$(AXILSINGLE).v $(RTL)/$(SFIFO).v $(AXILSINGLE).sby $(AXIL)
	sby -f $(AXILSINGLE).sby prf
$(AXILSINGLE)_cvr/PASS: $(RTL)/$(AXILSINGLE).v $(RTL)/$(SFIFO).v $(AXILSINGLE).sby $(AXIL)
	sby -f $(AXILSINGLE).sby cvr

.PHONY: $(AXILDOUBLE)
$(AXILDOUBLE): $(AXILDOUBLE)_prf/PASS $(AXILDOUBLE)_cvr/PASS
$(AXILDOUBLE)_prf/PASS: $(RTL)/$(AXILDOUBLE).v $(RTL)/$(SFIFO).v $(AXILDOUBLE).sby $(AXIL)
	sby -f $(AXILDOUBLE).sby prf
$(AXILDOUBLE)_cvr/PASS: $(RTL)/$(AXILDOUBLE).v $(RTL)/$(SFIFO).v $(AXILDOUBLE).sby $(AXIL)
	sby -f $(AXILDOUBLE).sby cvr

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

.PHONY: $(WBSAFETY)
$(WBSAFETY): $(WBSAFETY)_prf/PASS   $(WBSAFETY)_prfr/PASS
$(WBSAFETY): $(WBSAFETY)_fault/PASS $(WBSAFETY)_faultr/PASS
$(WBSAFETY): $(WBSAFETY)_cvr/PASS   $(SKIDBUFFER)
WBSAFETYDEP := $(WBSAFETY).sby $(RTL)/$(WBSAFETY).v $(RTL)/$(SKIDBUFFER).v $(WB)
$(WBSAFETY)_prf/PASS: $(WBSAFETYDEP)
	sby -f $(WBSAFETY).sby prf
$(WBSAFETY)_prfr/PASS: $(WBSAFETYDEP)
	sby -f $(WBSAFETY).sby prfr
$(WBSAFETY)_fault/PASS: $(WBSAFETYDEP)
	sby -f $(WBSAFETY).sby fault
$(WBSAFETY)_faultr/PASS: $(WBSAFETYDEP)
	sby -f $(WBSAFETY).sby faultr
$(WBSAFETY)_cvr/PASS: $(WBSAFETYDEP)
	sby -f $(WBSAFETY).sby cvr



.PHONY: clean
clean:
	rm -rf  $(DEMOAXI)_*/
	rm -rf  $(WBARB)_*/
	rm -rf  $(WB2LITE)_*/
	rm -rf  $(RDLITE)_*/     $(WRLITE)_*/
	rm -rf  $(WBC2PIPELIN)_*/ $(WBP2CLASSIC)_*/
	rm -rf  $(AXLITE)_*/     $(SFIFO)_*/
	rm -rf  $(SKIDBUFFER)_*/ $(DECODER)_*/
	rm -rf  $(WBXBAR)_*/     $(AXILXBAR)_*/
	rm -rf  $(AXILSINGLE)_*/ $(AXILDOUBLE)_*/
	rm -rf  $(WBSAFETY)_*/   $(EASYAXIL)_*/
	@# The three broken cores, to include Xilinx's
	rm -rf  $(XILINXDEMO)_*/
	rm -rf  $(XLNXSTREAM)_*/
