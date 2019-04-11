################################################################################
##
## Filename:	Makefile
##
## Project:	Pipelined Wishbone to AXI converter
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
## Copyright (C) 2016,2018-2019, Gisselquist Technology, LLC
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
