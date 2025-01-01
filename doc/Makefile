################################################################################
##
## Filename:	doc/Makefile
## {{{
## Project:	WB2AXIPSP: bus bridges and other odds and ends
##
## Purpose:	To coordinate the build of documentation PDFs from their
##		LaTeX sources.
##
##	Targets include:
##		all		Builds all documents
##
##		spec.pdf	Builds the specification for the SDSPI
##					controller.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
##
all:
	echo "See the comments internal to the various RTL files for any documentation"

pdf:	spec
DSRC := src
## }}}

.PHONY: spec
## {{{
spec: spec.pdf

spec.pdf: $(DSRC)/spec.tex $(DSRC)/gqtekspec.cls $(DSRC)/GT.eps
	cd $(DSRC)/; latex spec.tex
	cd $(DSRC)/; latex spec.tex
	cd $(DSRC)/; dvips -q -z -t letter -P pdf -o ../spec.ps spec.dvi
	ps2pdf -dAutoRotatePages=/All spec.ps spec.pdf
	-grep -i warning $(DSRC)/spec.log
	@rm -f $(DSRC)/spec.dvi $(DSRC)/spec.log
	@rm -f $(DSRC)/spec.aux $(DSRC)/spec.toc
	@rm -f $(DSRC)/spec.lot $(DSRC)/spec.lof
	@rm -f $(DSRC)/spec.out spec.ps
## }}}

.PHONY: clean
## {{{
clean:
	rm -f $(DSRC)/spec.dvi $(DSRC)/spec.log
	rm -f $(DSRC)/spec.aux $(DSRC)/spec.toc
	rm -f $(DSRC)/spec.lot $(DSRC)/spec.lof
	rm -f $(DSRC)/spec.out spec.ps spec.pdf
	rm -f $(LICENSE).pdf
## }}}
