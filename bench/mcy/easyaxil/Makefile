################################################################################
##
## Filename: 	bench/mcy/easyaxil/Makefile
##
## Project:	WB2AXIPSP: bus bridges and other odds and ends
##
## Purpose:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2019-2020, Gisselquist Technology, LLC
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
YYMMDD:= `date +%Y%m%d`
.PHONY: archive
# archive:	$(YYMMDD)-easyaxil.tgz

FILES := $(wildcard *.sv) $(wildcard *.v) $(wildcard *.cpp) $(wildcard *.h) $(wildcard *.sh) $(wildcard *.mcy) test_fm.sby

archive: $(FILES)
	tar -cvzhf $(YYMMDD)-easyaxil.tgz --exclude tasks --exclude database  --transform "sm^m./$(YYMMDD)-easyaxil/m" $(FILES)

easyaxil.v:
	@bash -c "if [ ! -e easyaxil.v ]; then ln -s ../../../rtl/easyaxil.v .; fi"

faxil_slave.v:
	@bash -c "if [ ! -e faxil_slave.v ]; then ln -s ../../../bench/formal/faxil_slave.v; fi"

.PHONY: mcy
mcy: config.mcy easyaxil.v faxil_slave.v test_eq.sh test_sim.sh test_fm.sh test_fm.sby easyaxil_tb.cpp easyaxil_tb.sv
	rm -rf database/
	rm -rf tasks/
	mcy init
	mcy run -j4

.PHONY: clean
clean:
	rm -rf easyaxil.v faxil_slave.v
	rm -rf database/ tasks/
