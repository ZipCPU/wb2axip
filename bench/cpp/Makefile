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
## Copyright (C) 2015-2020, Gisselquist Technology, LLC
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

