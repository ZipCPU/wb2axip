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
HELPERS   := sfifo afifo addrdecode wbarbiter skidbuffer
CROSSBARS := axilxbar wbxbar # axixbar
CROSSCLOCK:= wbxclk
BRIDGES   := wbm2axilite axlite2wbsp wbp2classic wbc2pipeline axilsingle axildouble axil2apb # wbm2axisp axi2axilite axilite2axi
AXISTREAM := xlnxstream_2018_3 axisswitch.v axisrandom.v
AXISLAVES := demoaxi easyaxil axil2axis axiperf # demofull xlnxfull
AXIMASTERS :=
FIREWALLS := wbsafety axilsafety axissafety # axisafety
TESTS := $(HELPERS) $(AXISLAVES) $(AXISTREAM) $(FIREWALLS) $(BRIDGES) $(CROSSCLOCK) $(CROSSBARS) $(AXIMASTERS) apbslave
.PHONY: $(TESTS)
all: $(TESTS)
RTL        := ../../rtl
SMTBMC     := yosys-smtbmc

#
# Helpers
WBARB      := wbarbiter
DECODER    := addrdecode
SFIFO      := sfifo
AFIFO      := afifo
SKIDBUFFER := skidbuffer
XBAR := $(RTL)/$(DECODER).v $(RTL)/$(SKIDBUFFER).v
#
# Slaves
AXIL2AXIS  := axil2axis
AXIPERF    := axiperf
APBSLAVE   := apbslave
DEMOAXI    := demoaxi
EASYAXIL   := easyaxil
XILINXDEMO := xlnxdemo
#
# AXI Stream cores
XLNXSTREAM := xlnxstream_2018_3
AXISRANDOM := axisrandom
AXISSWITCH := axisswitch
AXISSWITCH := axisswitch
#
# Bridges
AXIL2APB   := axil2apb
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
# Cross clock
WBXCLK     := wbxclk
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
AXILSAFETY := axilsafety
AXISSAFETY := axissafety
#
# Bus property sets
AXIL       := faxil_master.v faxil_slave.v
WB         := fwb_master.v   fwb_slave.v
WBC        := fwbc_master.v  fwbc_slave.v
AXIS       := faxis_master.v faxis_slave.v
APB        := fapb_master.v   fapb_slave.v

.PHONY: $(WBARB) $(WB2AXI) $(RDLITE) $(WRLITE) $(AXLITE) $(WB2LITE) $(DEMOAXI)
.PHONY: $(EASYAXIL) $(AXIPERF)

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

.PHONY: $(AXIPERF)
$(AXIPERF): $(AXIPERF)_prf/PASS $(AXIPERF)_cvr/PASS
$(AXIPERF)_prf/PASS: $(RTL)/$(AXIPERF).v $(RTL)/$(SKIDBUFFER).v $(AXIPERF).sby $(AXIL)
	sby -f $(AXIPERF).sby prf
$(AXIPERF)_cvr/PASS: $(RTL)/$(AXIPERF).v $(RTL)/$(SKIDBUFFER).v $(AXIPERF).sby $(AXIL)
	sby -f $(AXIPERF).sby cvr

.PHONY: $(XILINXDEMO)
$(XILINXDEMO): $(XILINXDEMO)_prf/FAIL $(XILINXDEMO)_cvr/PASS
$(XILINXDEMO)_prf/FAIL: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	@echo "Expect the Xilinx demo proof to fail."
	@echo "Xilinx's code didn't work in the first place."
	sby -f $(XILINXDEMO).sby prf
$(XILINXDEMO)_cvr/PASS: $(XILINXDEMO).v $(XILINXDEMO).sby $(AXIL)
	sby -f $(XILINXDEMO).sby cvr


.PHONY: $(XLNXSTREAM)
$(XLNXSTREAM): $(XLNXSTREAM)_prf/FAIL $(XLNXSTREAM)_cvr/PASS
$(XLNXSTREAM)_prf/FAIL: $(XLNXSTREAM).v $(XLNXSTREAM).sby $(AXIS)
	@echo "Expect the Xilinx stream master demo proof to fail."
	@echo "Xilinx's code didn't work in the first place."
	sby -f $(XLNXSTREAM).sby prf
$(XLNXSTREAM)_cvr/PASS: $(XLNXSTREAM).v $(XLNXSTREAM).sby $(AXIS)
	sby -f $(XLNXSTREAM).sby cvr

#
# Cross clock
.PHONY: $(WBXCLK)
$(WBXCLK): $(WBXCLK)_prf/PASS $(WBXCLK)_cvr/PASS
$(WBXCLK)_prf/PASS: $(RTL)/$(WBXCLK).v $(RTL)/afifo.v $(WBXCLK).sby $(WB)
	sby -f $(WBXCLK).sby prf
$(WBXCLK)_cvr/PASS: $(RTL)/$(WBXCLK).v $(RTL)/afifo.v $(WBXCLK).sby $(WB)
	sby -f $(WBXCLK).sby cvr

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
$(SFIFO): $(SFIFO)_prf/PASS    $(SFIFO)_prf_a/PASS  $(SFIFO)_cvr/PASS
$(SFIFO): $(SFIFO)_prf_r/PASS  $(SFIFO)_prf_w/PASS  $(SFIFO)_prf_wr/PASS
$(SFIFO): $(SFIFO)_prf_ar/PASS $(SFIFO)_prf_aw/PASS $(SFIFO)_prf_awr/PASS
$(SFIFO)_prf/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf
$(SFIFO)_prf_r/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_r
$(SFIFO)_prf_w/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_w
$(SFIFO)_prf_wr/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_wr
$(SFIFO)_prf_a/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_a
$(SFIFO)_prf_ar/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_ar
$(SFIFO)_prf_aw/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_aw
$(SFIFO)_prf_awr/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby prf_awr
$(SFIFO)_cvr/PASS: $(RTL)/$(SFIFO).v $(SFIFO).sby
	sby -f $(SFIFO).sby cvr

.PHONY: $(AFIFO)
$(AFIFO): $(AFIFO)_prf/PASS    $(AFIFO)_cvr/PASS
$(AFIFO)_prf/PASS: $(RTL)/$(AFIFO).v $(AFIFO).sby
	sby -f $(AFIFO).sby prf
$(AFIFO)_cvr/PASS: $(RTL)/$(AFIFO).v $(AFIFO).sby
	sby -f $(AFIFO).sby cvr

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

.PHONY: $(AXILSAFETY)
$(AXILSAFETY): $(AXILSAFETY)_prf/PASS    $(AXILSAFETY)_prfr/PASS
$(AXILSAFETY): $(AXILSAFETY)_fault/PASS  $(AXILSAFETY)_faultr/PASS
$(AXILSAFETY): $(AXILSAFETY)_prlong/PASS $(AXILSAFETY)_longr/PASS
$(AXILSAFETY): $(AXILSAFETY)_cvr/PASS   $(SKIDBUFFER)
AXILSAFETYDEP := $(AXILSAFETY).sby $(RTL)/$(AXILSAFETY).v $(RTL)/$(SKIDBUFFER).v $(WB)
$(AXILSAFETY)_prf/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby prf
$(AXILSAFETY)_prfr/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby prfr
$(AXILSAFETY)_fault/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby fault
$(AXILSAFETY)_faultr/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby faultr
$(AXILSAFETY)_longr/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby longr
$(AXILSAFETY)_prlong/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby prlong
$(AXILSAFETY)_cvr/PASS: $(AXILSAFETYDEP)
	sby -f $(AXILSAFETY).sby cvr

.PHONY: $(AXIL2AXIS)
$(AXIL2AXIS): $(AXIL2AXIS)_prf/PASS       $(AXIL2AXIS)_prflps/PASS
$(AXIL2AXIS): $(AXIL2AXIS)_prflpu/PASS    $(AXIL2AXIS)_prfsink/PASS
$(AXIL2AXIS): $(AXIL2AXIS)_prfsource/PASS $(AXIL2AXIS)_cvr/PASS
AXIL2AXISDEPS := $(AXIL2AXIS).sby $(RTL)/sfifo.v $(RTL)/skidbuffer.v	\
		$(RTL)/$(AXIL2AXIS).v $(AXIL)
$(AXIL2AXIS)_prf/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby prf
$(AXIL2AXIS)_prflpu/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby prflpu
$(AXIL2AXIS)_prflps/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby prflps
$(AXIL2AXIS)_prfsink/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby prfsink
$(AXIL2AXIS)_prfsource/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby prfsource
$(AXIL2AXIS)_cvr/PASS: $(AXIL2AXISDEPS)
	sby -f $(AXIL2AXIS).sby cvr

.PHONY: $(APBSLAVE)
$(APBSLAVE): $(APBSLAVE)_prf/PASS       $(APBSLAVE)_cvr/PASS
APBSLAVEDEPS := $(APBSLAVE).sby $(RTL)/$(APBSLAVE).v $(APB)
$(APBSLAVE)_prf/PASS: $(APBSLAVEDEPS)
	sby -f $(APBSLAVE).sby prf
$(APBSLAVE)_cvr/PASS: $(APBSLAVEDEPS)
	sby -f $(APBSLAVE).sby cvr

.PHONY: $(AXIL2APB)
$(AXIL2APB): $(AXIL2APB)_prf/PASS       $(AXIL2APB)_prfskd/PASS
$(AXIL2APB): $(AXIL2APB)_cvr/PASS
AXIL2APBDEPS := $(AXIL2APB).sby $(RTL)/$(AXIL2APB).v $(APB)
$(AXIL2APB)_prf/PASS: $(AXIL2APBDEPS)
	sby -f $(AXIL2APB).sby prf
$(AXIL2APB)_prfskd/PASS: $(AXIL2APBDEPS)
	sby -f $(AXIL2APB).sby prfskd
$(AXIL2APB)_cvr/PASS: $(AXIL2APBDEPS)
	sby -f $(AXIL2APB).sby cvr

.PHONY: $(AXISRANDOM)
$(AXISRANDOM): $(AXISRANDOM)_prf/PASS
$(AXISRANDOM)_prf/PASS: $(AXISRANDOM).sby $(RTL)/$(AXISRANDOM).v
	sby -f $(AXISRANDOM).sby prf

.PHONY: $(AXISSWITCH)
$(AXISSWITCH): $(AXISSWITCH)_prf/PASS
$(AXISSWITCH)_prf/PASS: $(AXISSWITCH).sby $(RTL)/$(AXISSWITCH).v
	sby -f $(AXISSWITCH).sby prf

.PHONY: $(AXISSAFETY)
$(AXISSAFETY): $(AXISSAFETY)_prf/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfr/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfrpkt/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfpkt/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfs/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfrs/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfrpkts/PASS
$(AXISSAFETY): $(AXISSAFETY)_prfpkts/PASS
$(AXISSAFETY): $(AXISSAFETY)_fault/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultr/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultrpkt/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultpkt/PASS
$(AXISSAFETY): $(AXISSAFETY)_faults/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultrs/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultrpkts/PASS
$(AXISSAFETY): $(AXISSAFETY)_faultpkts/PASS
$(AXISSAFETY): $(AXISSAFETY)_cvr/PASS
$(AXISSAFETY): $(AXISSAFETY)_cvrnopkt/PASS
$(AXISSAFETY)_prf/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prf
$(AXISSAFETY)_prfr/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfr
$(AXISSAFETY)_prfrpkt/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfrpkt
$(AXISSAFETY)_prfpkt/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfpkt
$(AXISSAFETY)_prfs/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfs
$(AXISSAFETY)_prfrs/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfrs
$(AXISSAFETY)_prfrpkts/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfrpkts
$(AXISSAFETY)_prfpkts/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby prfpkts
$(AXISSAFETY)_fault/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby fault
$(AXISSAFETY)_faultr/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultr
$(AXISSAFETY)_faultrpkt/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultrpkt
$(AXISSAFETY)_faultpkt/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultpkt
$(AXISSAFETY)_faults/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faults
$(AXISSAFETY)_faultrs/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultrs
$(AXISSAFETY)_faultrpkts/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultrpkts
$(AXISSAFETY)_faultpkts/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby faultpkts
$(AXISSAFETY)_cvr/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby cvr
$(AXISSAFETY)_cvrnopkt/PASS: $(AXISSAFETY).sby $(RTL)/$(AXISSAFETY).v
	sby -f $(AXISSAFETY).sby cvrnopkt

.PHONY: clean
clean:
	rm -rf  $(DEMOAXI)_*/
	rm -rf  $(WBARB)_*/
	rm -rf  $(WB2LITE)_*/
	rm -rf  $(RDLITE)_*/     $(WRLITE)_*/
	rm -rf  $(WBC2PIPELIN)_*/ $(WBP2CLASSIC)_*/
	rm -rf  $(AXLITE)_*/     $(WBXCLK)_*/
	rm -rf  $(SFIFO)_*/      $(AFIFO)_*/
	rm -rf  $(SKIDBUFFER)_*/ $(DECODER)_*/
	rm -rf  $(WBXBAR)_*/     $(AXILXBAR)_*/
	rm -rf  $(AXILSINGLE)_*/ $(AXILDOUBLE)_*/
	rm -rf  $(EASYAXIL)_*/
	rm -rf  $(WBSAFETY)_*/   $(AXILSAFETY)_*/
	rm -rf  $(AXIPERF)_*/    $(AXIL2AXIS)_*/
	rm -rf  $(AXIL2APB)_*/   $(APBSLAVE)_*/
	rm -rf	$(AXISRANDOM)_*/ $(AXISSWITCH)_*/
	@# The three broken cores, to include Xilinx's
	rm -rf  $(XILINXDEMO)_*/
	rm -rf  $(XLNXSTREAM)_*/
