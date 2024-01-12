################################################################################
##
## Filename:	Makefile
## {{{
## Project:	WB2AXIPSP: bus bridges and other odds and ends
##
## Purpose:	To describe how to build the Verilator libraries from the
##		RTL, for the purposes of trying to discover if they work.
##	Any actual testing will be done from the code within the bench/cpp
##	directory.
##
## Targets:	The default target, all, builds the target test, which includes
##		the libraries necessary for Verilator testing.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2016-2023, Gisselquist Technology, LLC
## {{{
## This file is part of the WB2AXIP project.
##
## The WB2AXIP project contains free software and gateware, licensed under the
## Apache License, Version 2.0 (the "License").  You may not use this project,
## or this file, except in compliance with the License.  You may obtain a copy
## of the License at
## }}}
##	http://www.apache.org/licenses/LICENSE-2.0
## {{{
## Unless required by applicable law or agreed to in writing, software
## distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
## WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
## License for the specific language governing permissions and limitations
## under the License.
##
################################################################################
##
## }}}
all:	test
YYMMDD=`date +%Y%m%d`
CXX   := g++
IVCHECK  := ivcheck
IVERILOG := iverilog
FBDIR := .
VDIRFB:= $(FBDIR)/obj_dir
VERILATOR := verilator
VFLAGS    := -MMD -O3 -Wall -Wpedantic -cc
.DELETE_ON_ERROR:
.PHONY: test
test: testwb testaxi testaxil testapb testaxis

.PHONY: testwb testaxi testaxil testapb testaxis

.PHONY: axim2wbsp axim2wbsp wbm2axilite axilrd2wbsp axilwr2wbsp axlite2wbsp
.PHONY: axixbar axilxbar wbxbar axis2mm aximm2s axidma axim2wbsp aximrd2wbsp
.PHONY: aximwr2wbsp axixclk axiperf demoaxi demofull easyaxil sfifo skidbuffer
.PHONY: axilgpio
.PHONY: axilsafety axisafety wbsafety axivfifo axil2apb apbslave
.PHONY: axisrandom axisswitch axisbroadcast axispacker

axim2wbsp:   $(VDIRFB)/Vwbm2axisp__ALL.a    $(IVCHECK)/axim2wbsp
axim2wbsp:   $(VDIRFB)/Vaxim2wbsp__ALL.a
wbm2axilite: $(VDIRFB)/Vwbm2axilite__ALL.a  $(IVCHECK)/wbm2axilite
axilrd2wbsp: $(VDIRFB)/Vaxilrd2wbsp__ALL.a  $(IVCHECK)/axilrd2wbsp
axilwr2wbsp: $(VDIRFB)/Vaxilwr2wbsp__ALL.a  $(IVCHECK)/axilwr2wbsp
axlite2wbsp: $(VDIRFB)/Vaxlite2wbsp__ALL.a  $(IVCHECK)/axlite2wbsp
axiempty:    $(VDIRFB)/Vaxiempty__ALL.a     $(IVCHECK)/axiempty
axilempty:   $(VDIRFB)/Vaxilempty__ALL.a    $(IVCHECK)/axilempty
axilgpio:    $(VDIRFB)/Vaxilgpio__ALL.a     $(IVCHECK)/axilgpio
axivcamera:  $(VDIRFB)/Vaxivcamera__ALL.a   $(IVCHECK)/axivcamera
axivdisplay: $(VDIRFB)/Vaxivdisplay__ALL.a  $(IVCHECK)/axivdisplay
axivfifo:    $(VDIRFB)/Vaxivfifo__ALL.a     $(IVCHECK)/axivfifo
axixbar:     $(VDIRFB)/Vaxixbar__ALL.a      $(IVCHECK)/axixbar
axilxbar:    $(VDIRFB)/Vaxilxbar__ALL.a     $(IVCHECK)/axilxbar
wbxbar:      $(VDIRFB)/Vwbxbar__ALL.a       $(IVCHECK)/wbxbar
axis2mm:     $(VDIRFB)/Vaxis2mm__ALL.a      $(IVCHECK)/axis2mm
aximm2s:     $(VDIRFB)/Vaximm2s__ALL.a      $(IVCHECK)/aximm2s
axidma:      $(VDIRFB)/Vaxidma__ALL.a       $(IVCHECK)/axidma
axim2wbsp:   $(VDIRFB)/Vaxim2wbsp__ALL.a    $(IVCHECK)/axim2wbsp
aximrd2wbsp: $(VDIRFB)/Vaximrd2wbsp__ALL.a  $(IVCHECK)/aximrd2wbsp
aximwr2wbsp: $(VDIRFB)/Vaximwr2wbsp__ALL.a  $(IVCHECK)/aximwr2wbsp
axiperf:     $(VDIRFB)/Vaxiperf__ALL.a      $(IVCHECK)/axiperf
axixclk:     $(VDIRFB)/Vaxixclk__ALL.a      $(IVCHECK)/axixclk
demoaxi:     $(VDIRFB)/Vdemoaxi__ALL.a      $(IVCHECK)/demoaxi
demofull:    $(VDIRFB)/Vdemofull__ALL.a     $(IVCHECK)/demofull
easyaxil:    $(VDIRFB)/Veasyaxil__ALL.a     $(IVCHECK)/easyaxil
sfifo:       $(VDIRFB)/Vsfifo__ALL.a        $(IVCHECK)/sfifo
skidbuffer:  $(VDIRFB)/Vskidbuffer__ALL.a   $(IVCHECK)/skidbuffer
axisafety:   $(VDIRFB)/Vaxisafety__ALL.a    $(IVCHECK)/axisafety
axilsafety:  $(VDIRFB)/Vaxilsafety__ALL.a   $(IVCHECK)/axilsafety
wbsafety:    $(VDIRFB)/Vwbsafety__ALL.a     $(IVCHECK)/wbsafety
axil2apb:    $(VDIRFB)/Vaxil2apb__ALL.a     $(IVCHECK)/axil2apb
apbslave:    $(VDIRFB)/Vapbslave__ALL.a     $(IVCHECK)/apbslave
axisbroadcast: $(VDIRFB)/Vaxisbroadcast__ALL.a $(IVCHECK)/axisbroadcast
axispacker:  $(VDIRFB)/Vaxispacker__ALL.a   $(IVCHECK)/axispacker
axisrandom:  $(VDIRFB)/Vaxisrandom__ALL.a   $(IVCHECK)/axisrandom
axisswitch:  $(VDIRFB)/Vaxisswitch__ALL.a   $(IVCHECK)/axisswitch

testwb: wbsafety wbm2axilite wbxbar sfifo wbsafety wbxbar wbsafety
testaxi: axim2wbsp axixbar axixclk demofull axiempty
testaxi: aximrd2wbsp axim2wbsp aximwr2wbsp axisafety
testaxi: axis2mm aximm2s axidma axivfifo axivdisplay axivcamera
testaxil: axilrd2wbsp axilwr2wbsp axlite2wbsp axilxbar demoaxi easyaxil
testaxil: skidbuffer axiperf axilempty axilgpio
testapb: axil2apb apbslave
testaxis: axisbroadcast axisswitch axisrandom axispacker

.PHONY: wbm2axisp
wbm2axisp: $(VDIRFB)/Vwbm2axisp__ALL.a
$(VDIRFB)/Vwbm2axisp__ALL.a: $(VDIRFB)/Vwbm2axisp.h $(VDIRFB)/Vwbm2axisp.cpp
$(VDIRFB)/Vwbm2axisp__ALL.a: $(VDIRFB)/Vwbm2axisp.mk
$(VDIRFB)/Vwbm2axisp.h $(VDIRFB)/Vwbm2axisp.cpp $(VDIRFB)/Vwbm2axisp.mk: wbm2axisp.v

.PHONY: wbm2axilite
wbm2axilite: $(VDIRFB)/Vwbm2axilite__ALL.a
$(VDIRFB)/Vwbm2axilite__ALL.a: $(VDIRFB)/Vwbm2axilite.h $(VDIRFB)/Vwbm2axilite.cpp
$(VDIRFB)/Vwbm2axilite__ALL.a: $(VDIRFB)/Vwbm2axilite.mk
$(VDIRFB)/Vwbm2axilite.h $(VDIRFB)/Vwbm2axilite.cpp $(VDIRFB)/Vwbm2axilite.mk: wbm2axilite.v

.PHONY: axilrd2wbsp
axilrd2wbsp: $(VDIRFB)/Vaxilrd2wbsp__ALL.a
$(VDIRFB)/Vaxilrd2wbsp__ALL.a: $(VDIRFB)/Vaxilrd2wbsp.h $(VDIRFB)/Vaxilrd2wbsp.cpp
$(VDIRFB)/Vaxilrd2wbsp__ALL.a: $(VDIRFB)/Vaxilrd2wbsp.mk
$(VDIRFB)/Vaxilrd2wbsp.h $(VDIRFB)/Vaxilrd2wbsp.cpp $(VDIRFB)/Vaxilrd2wbsp.mk: axilrd2wbsp.v

.PHONY: axilwr2wbsp
axilwr2wbsp: $(VDIRFB)/Vaxilwr2wbsp__ALL.a
$(VDIRFB)/Vaxilwr2wbsp__ALL.a: $(VDIRFB)/Vaxilwr2wbsp.h $(VDIRFB)/Vaxilwr2wbsp.cpp
$(VDIRFB)/Vaxilwr2wbsp__ALL.a: $(VDIRFB)/Vaxilwr2wbsp.mk
$(VDIRFB)/Vaxilwr2wbsp.h $(VDIRFB)/Vaxilwr2wbsp.cpp $(VDIRFB)/Vaxilwr2wbsp.mk: axilwr2wbsp.v

$(VDIRFB)/Vaxlite2wbsp__ALL.a: $(VDIRFB)/Vaxlite2wbsp.h $(VDIRFB)/Vaxlite2wbsp.cpp
$(VDIRFB)/Vaxlite2wbsp__ALL.a: $(VDIRFB)/Vaxlite2wbsp.mk
$(VDIRFB)/Vaxlite2wbsp.h $(VDIRFB)/Vaxlite2wbsp.cpp $(VDIRFB)/Vaxlite2wbsp.mk: axlite2wbsp.v

$(VDIRFB)/Vaxiempty__ALL.a: $(VDIRFB)/Vaxiempty.h $(VDIRFB)/Vaxiempty.cpp
$(VDIRFB)/Vaxiempty__ALL.a: $(VDIRFB)/Vaxiempty.mk
$(VDIRFB)/Vaxiempty.h $(VDIRFB)/Vaxiempty.cpp $(VDIRFB)/Vaxiempty.mk: axiempty.v skidbuffer.v

$(VDIRFB)/Vaxilempty__ALL.a: $(VDIRFB)/Vaxilempty.h $(VDIRFB)/Vaxilempty.cpp
$(VDIRFB)/Vaxilempty__ALL.a: $(VDIRFB)/Vaxilempty.mk
$(VDIRFB)/Vaxilempty.h $(VDIRFB)/Vaxilempty.cpp $(VDIRFB)/Vaxilempty.mk: axilempty.v skidbuffer.v

$(VDIRFB)/Vaxilgpio__ALL.a: $(VDIRFB)/Vaxilgpio.h $(VDIRFB)/Vaxilgpio.cpp
$(VDIRFB)/Vaxilgpio__ALL.a: $(VDIRFB)/Vaxilgpio.mk
$(VDIRFB)/Vaxilgpio.h $(VDIRFB)/Vaxilgpio.cpp $(VDIRFB)/Vaxilgpio.mk: axilgpio.v skidbuffer.v

$(VDIRFB)/Vaxim2wbsp__ALL.a: $(VDIRFB)/Vaxim2wbsp.h $(VDIRFB)/Vaxim2wbsp.cpp
$(VDIRFB)/Vaxim2wbsp__ALL.a: $(VDIRFB)/Vaxim2wbsp.mk
$(VDIRFB)/Vaxim2wbsp.h $(VDIRFB)/Vaxim2wbsp.cpp $(VDIRFB)/Vaxim2wbsp.mk: \
	axim2wbsp.v aximrd2wbsp.v aximwr2wbsp.v wbarbiter.v

$(VDIRFB)/Vaxivfifo__ALL.a: $(VDIRFB)/Vaxivfifo.h $(VDIRFB)/Vaxivfifo.cpp
$(VDIRFB)/Vaxivfifo__ALL.a: $(VDIRFB)/Vaxivfifo.mk
$(VDIRFB)/Vaxivfifo.h $(VDIRFB)/Vaxivfifo.cpp $(VDIRFB)/Vaxivfifo.mk: \
	axivfifo.v skidbuffer.v sfifo.v

$(VDIRFB)/Vaxivcamera__ALL.a: $(VDIRFB)/Vaxivcamera.h $(VDIRFB)/Vaxivcamera.cpp
$(VDIRFB)/Vaxivcamera__ALL.a: $(VDIRFB)/Vaxivcamera.mk
$(VDIRFB)/Vaxivcamera.h $(VDIRFB)/Vaxivcamera.cpp $(VDIRFB)/Vaxivcamera.mk: \
	axivcamera.v skidbuffer.v sfifo.v

$(VDIRFB)/Vaxivdisplay__ALL.a: $(VDIRFB)/Vaxivdisplay.h $(VDIRFB)/Vaxivdisplay.cpp
$(VDIRFB)/Vaxivdisplay__ALL.a: $(VDIRFB)/Vaxivdisplay.mk
$(VDIRFB)/Vaxivdisplay.h $(VDIRFB)/Vaxivdisplay.cpp $(VDIRFB)/Vaxivdisplay.mk: \
	axivdisplay.v skidbuffer.v sfifo.v

$(VDIRFB)/V%.cpp $(VDIRFB)/V%.h $(VDIRFB)/V%.mk: $(FBDIR)/%.v
	$(VERILATOR) $(VFLAGS) $*.v

$(VDIRFB)/V%__ALL.a: $(VDIRFB)/V%.mk
	cd $(VDIRFB); make -f V$*.mk

##
## Run Icarus Verilog (iverilog) on each of these cores for a lint check
##
$(IVCHECK)/axi2axilite: axi2axilite.v sfifo.v skidbuffer.v axi_addr.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axil2axis: axil2axis.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axildouble: axildouble.v sfifo.v skidbuffer.v addrdecode.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilrd2wbsp: axilrd2wbsp.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilsafety: axilsafety.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilsingle: axilsingle.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilwr2wbsp: axilwr2wbsp.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilxbar: axilxbar.v skidbuffer.v addrdecode.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axidma: axidma.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/aximm2s: aximm2s.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axim2wbsp: axim2wbsp.v sfifo.v skidbuffer.v aximrd2wbsp.v aximwr2wbsp.v axi_addr.v wbarbiter.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/aximrd2wbsp: aximrd2wbsp.v sfifo.v skidbuffer.v axi_addr.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/aximwr2wbsp: aximwr2wbsp.v sfifo.v skidbuffer.v axi_addr.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axiperf: axiperf.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axisafety: axisafety.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axis2mm: axis2mm.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axivcamera: axivcamera.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axivdisplay: axivdisplay.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axivfifo: axivfifo.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axixbar: axixbar.v skidbuffer.v addrdecode.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axixclk: axixclk.v afifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axlite2wbsp: axlite2wbsp.v axilrd2wbsp.v axilwr2wbsp.v wbarbiter.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axiempty: axiempty.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilempty: axilempty.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axilgpio: axilgpio.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/demoaxi: demoaxi.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/demofull: demofull.v axi_addr.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/easyaxil: easyaxil.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/sfifo: sfifo.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/skidbuffer: skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/wbm2axilite: wbm2axilite.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/wbsafety: wbsafety.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/wbxbar: wbxbar.v skidbuffer.v addrdecode.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axil2apb: axil2apb.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/apbslave: apbslave.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axisbroadcast: axisbroadcast.v sfifo.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axispacker: axispacker.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axisrandom: axisrandom.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

$(IVCHECK)/axisswitch: axisswitch.v skidbuffer.v
	$(mk-ivcheck)
	$(IVERILOG) -g2012 $^ -o $@

define	mk-ivcheck
	@bash -c "if [ ! -e $(IVCHECK) ]; then mkdir -p $(IVCHECK); fi"
endef

.PHONY: clean
clean:
	rm -rf $(VDIRFB)/*.mk
	rm -rf $(VDIRFB)/*.cpp
	rm -rf $(VDIRFB)/*.h
	rm -rf $(VDIRFB)/
	rm -rf $(IVCHECK)/
