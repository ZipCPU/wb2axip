################################################################################
##
## Filename:	Makefile
##
## Project:	Pipelined Wishbone to AXI converter
##
## Purpose:	A master project makefile.  It tries to build all targets
##		within the project, mostly by directing subdirectory makes.
##
## Targets:	
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
.PHONY: all
all:	archive rtl formal
# all:	verilated sw bench bit
#
# Could also depend upon load, if desired, but not necessary
BENCH := `find bench -name Makefile` `find bench -name "*.cpp"` `find bench -name "*.h"`
RTL   := `find rtl -name "*.v"` `find rtl -name Makefile`
NOTES := `find . -name "*.txt"` `find . -name "*.html"`
YYMMDD:=`date +%Y%m%d`

.PHONY: archive
archive:
	tar --transform s,^,$(YYMMDD)-wb2axi/, -chjf $(YYMMDD)-wb2axi.tjz $(BENCH) $(RTL) $(NOTES)

.PHONY: verilated
verilated:
	cd rtl ; $(MAKE) --no-print-directory

.PHONY: rtl
rtl: verilated

.PHONY: bench
bench: rtl
	cd bench/cpp ; $(MAKE) --no-print-directory

.PHONY: formal
formal:
	$(MAKE) --no-print-directory -C bench/formal

.PHONY: doc
doc:
	cd doc ; $(MAKE) --no-print-directory


