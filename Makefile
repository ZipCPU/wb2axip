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
## Copyright (C) 2015-2016,2019, Gisselquist Technology, LLC
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
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http:##www.gnu.org/licenses/gpl.html
##
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


