################################################################################
##
## Filename:	Makefile
##
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
##
## Copyright (C) 2016-2020, Gisselquist Technology, LLC
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
all:	test
YYMMDD=`date +%Y%m%d`
CXX   := g++
FBDIR := .
VDIRFB:= $(FBDIR)/obj_dir
VERILATOR := verilator
VFLAGS    := -MMD -Wall -cc
.DELETE_ON_ERROR:
.PHONY: test
test: testwb testaxi testaxil

.PHONY: testwb testaxi testaxil

.PHONY: axim2wbsp axim2wbsp wbm2axilite axilrd2wbsp axilwr2wbsp axlite2wbsp
.PHONY: axixbar axilxbar wbxbar axis2mm aximm2s axidma axim2wbsp aximrd2wbsp
.PHONY: aximwr2wbsp axixclk axiperf demoaxi demofull easyaxil sfifo skidbuffer
.PHONY: axilsafety axisafety wbsafety

axim2wbsp:   $(VDIRFB)/Vwbm2axisp__ALL.a
axim2wbsp:   $(VDIRFB)/Vaxim2wbsp__ALL.a
wbm2axilite: $(VDIRFB)/Vwbm2axilite__ALL.a
axilrd2wbsp: $(VDIRFB)/Vaxilrd2wbsp__ALL.a
axilwr2wbsp: $(VDIRFB)/Vaxilwr2wbsp__ALL.a
axlite2wbsp: $(VDIRFB)/Vaxlite2wbsp__ALL.a
axixbar:     $(VDIRFB)/Vaxixbar__ALL.a
axilxbar:    $(VDIRFB)/Vaxilxbar__ALL.a
wbxbar:      $(VDIRFB)/Vwbxbar__ALL.a
axis2mm:     $(VDIRFB)/Vaxis2mm__ALL.a
aximm2s:     $(VDIRFB)/Vaximm2s__ALL.a
axidma:      $(VDIRFB)/Vaxidma__ALL.a
axim2wbsp:   $(VDIRFB)/Vaxim2wbsp__ALL.a
aximrd2wbsp: $(VDIRFB)/Vaximrd2wbsp__ALL.a
aximwr2wbsp: $(VDIRFB)/Vaximwr2wbsp__ALL.a
axiperf:     $(VDIRFB)/Vaxiperf__ALL.a
axixclk:     $(VDIRFB)/Vaxixclk__ALL.a
demoaxi:     $(VDIRFB)/Vdemoaxi__ALL.a
demofull:    $(VDIRFB)/Vdemofull__ALL.a
easyaxil:    $(VDIRFB)/Veasyaxil__ALL.a
sfifo:       $(VDIRFB)/Vsfifo__ALL.a
skidbuffer:  $(VDIRFB)/Vskidbuffer__ALL.a
axisafety:   $(VDIRFB)/Vaxisafety__ALL.a
axilsafety:  $(VDIRFB)/Vaxilsafety__ALL.a
wbsafety:    $(VDIRFB)/Vwbsafety__ALL.a

testwb: wbsafety wbm2axilite wbxbar sfifo wbsafety wbxbar wbsafety
testaxi: axim2wbsp axixbar axixclk demofull
testaxi: aximrd2wbsp axim2wbsp aximwr2wbsp axisafety
testaxi: axis2mm aximm2s axidma
testaxil: axilrd2wbsp axilwr2wbsp axlite2wbsp axilxbar demoaxi easyaxil
testaxil: skidbuffer axiperf

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

.PHONY: axlite2wbsp
axlite2wbsp: $(VDIRFB)/Vaxlite2wbsp__ALL.a
$(VDIRFB)/Vaxlite2wbsp__ALL.a: $(VDIRFB)/Vaxlite2wbsp.h $(VDIRFB)/Vaxlite2wbsp.cpp
$(VDIRFB)/Vaxlite2wbsp__ALL.a: $(VDIRFB)/Vaxlite2wbsp.mk
$(VDIRFB)/Vaxlite2wbsp.h $(VDIRFB)/Vaxlite2wbsp.cpp $(VDIRFB)/Vaxlite2wbsp.mk: axlite2wbsp.v

$(VDIRFB)/Vaxim2wbsp__ALL.a: $(VDIRFB)/Vaxim2wbsp.h $(VDIRFB)/Vaxim2wbsp.cpp
$(VDIRFB)/Vaxim2wbsp__ALL.a: $(VDIRFB)/Vaxim2wbsp.mk
$(VDIRFB)/Vaxim2wbsp.h $(VDIRFB)/Vaxim2wbsp.cpp $(VDIRFB)/Vaxim2wbsp.mk: \
	axim2wbsp.v aximrd2wbsp.v aximwr2wbsp.v wbarbiter.v

$(VDIRFB)/V%.cpp $(VDIRFB)/V%.h $(VDIRFB)/V%.mk: $(FBDIR)/%.v
	$(VERILATOR) $(VFLAGS) $*.v 

$(VDIRFB)/V%__ALL.a: $(VDIRFB)/V%.mk
	cd $(VDIRFB); make -f V$*.mk

.PHONY: clean
clean:
	rm -rf $(VDIRFB)/*.mk
	rm -rf $(VDIRFB)/*.cpp
	rm -rf $(VDIRFB)/*.h
	rm -rf $(VDIRFB)/
