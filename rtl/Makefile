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

.PHONY: test
test: testwb

.PHONY: testwb
.PHONY: testaxi

.PHONY: wbm2axisp
wbm2axisp: testwb

.PHONY: axim2wbsp
axim2wbsp: testaxi

.PHONY: axilite

testwb:  $(VDIRFB)/Vwbm2axisp__ALL.a
testaxi: $(VDIRFB)/Vaxim2wbsp__ALL.a
axilite: $(VDIRFB)/Vwbm2axilite__ALL.a
axilite: $(VDIRFB)/Vaxilrd2wbsp__ALL.a
axilite: $(VDIRFB)/Vaxilwr2wbsp__ALL.a
axilite: $(VDIRFB)/Vaxlite2wbsp__ALL.a

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
	verilator -cc $*.v 

$(VDIRFB)/V%__ALL.a: $(VDIRFB)/V%.mk
	cd $(VDIRFB); make -f V$*.mk

.PHONY: clean
clean:
	rm -rf $(VDIRFB)/*.mk
	rm -rf $(VDIRFB)/*.cpp
	rm -rf $(VDIRFB)/*.h
	rm -rf $(VDIRFB)/
