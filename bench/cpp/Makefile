################################################################################
##
## Filename: 	Makefile
##
## Project:	Pipelined Wishbone to AXI converter
##
## Purpose:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
## with this program.  (It's in the $(ROOT)/doc directory, run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
CXX	:= g++
FLAGS	:= -Wall -Og -g
OBJDIR  := obj-pc
RTLD	:= ../verilog
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT| head -1 | sed -e " s/^.*=\s*//"')
INCS	:= -I$(RTLD)/obj_dir/ -I$(VROOT)/include
SOURCES := # testset.cpp
VOBJDR	:= $(RTLD)/obj_dir
VLIB	:= $(VROOT)/include/verilated.cpp
SIMSRCS := aximemsim.cpp # testset.cpp
SIMOBJ := $(subst .cpp,.o,$(SIMSRCS))
SIMOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ))
all:	$(OBJDIR)/ testset

$(OBJDIR)/:
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"

$(OBJDIR)/aximemsim.o: aximemsim.cpp aximemsim.h

$(OBJDIR)/%.o: %.cpp
	$(CXX) $(FLAGS) $(INCS) -c $< -o $@

# testset: $(OBJDIR)/testset.o $(OBJDIR)/aximemsim.o $(VOBJDR)/Vtestset__ALL.a
#	$(CXX) $(FLAGS) $(INCS) $^ $(VLIB) -o $@
.PHONY: testset
testset:
	@echo
	@echo "I seem to have lost the testset.cpp file that this test suite"
	@echo "was based off of.  Hence, the suite is incomplete."
	@echo

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/
	# rm -f  ./testset

