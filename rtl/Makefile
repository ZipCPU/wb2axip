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
## Copyright (C) 2016, Gisselquist Technology, LLC
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
all:	test
YYMMDD=`date +%Y%m%d`
CXX   := g++
FBDIR := .
VDIRFB:= $(FBDIR)/obj_dir

.PHONY: test
test: testwb testaxi

.PHONY: testwb
.PHONY: testaxi

.PHONY: wbm2axisp
wbm2axisp: testwb

.PHONY: axim2wbsp
axim2wbsp: testaxi

testwb:  $(VDIRFB)/Vwbm2axisp__ALL.a
testaxi: $(VDIRFB)/Vaxim2wbsp__ALL.a

$(VDIRFB)/Vwbm2axisp__ALL.a: $(VDIRFB)/Vwbm2axisp.h $(VDIRFB)/Vwbm2axisp.cpp
$(VDIRFB)/Vwbm2axisp__ALL.a: $(VDIRFB)/Vwbm2axisp.mk
$(VDIRFB)/Vwbm2axisp.h $(VDIRFB)/Vwbm2axisp.cpp $(VDIRFB)/Vwbm2axisp.mk: wbm2axisp.v

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

