################################################################################
##
## Filename: 	Makefile
##
## Project:	Pipelined Wishbone to AXI converter
##
## Purpose:	To coordinate the build of documentation PDFs from their
##		LaTeX sources.
##
##	Targets include:
##		all		Builds all documents
##
##		lgpl-3.0.pdf	Builds the LGPL license these files are released
##					under.
##
##		spec.pdf	Builds the specification for the SDSPI
##					controller.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2016,2018-2019 Gisselquist Technology, LLC
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
all:	lgpl
pdf:	lgpl spec
DSRC := src

.PHONY: lgpl
LICENSE := lgpl-3.0
lgpl: $(LICENSE).pdf

$(LICENSE).pdf: $(DSRC)/$(LICENSE).tex
	latex $(DSRC)/$(LICENSE).tex
	latex $(DSRC)/$(LICENSE).tex
	dvips -q -z -t letter -P pdf -o $(LICENSE).ps $(LICENSE).dvi
	ps2pdf -dAutoRotatePages=/All $(LICENSE).ps $(LICENSE).pdf
	rm $(LICENSE).dvi $(LICENSE).log $(LICENSE).aux $(LICENSE).ps

.PHONY: spec
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

.PHONY: clean
clean:
	rm -f $(DSRC)/spec.dvi $(DSRC)/spec.log
	rm -f $(DSRC)/spec.aux $(DSRC)/spec.toc
	rm -f $(DSRC)/spec.lot $(DSRC)/spec.lof
	rm -f $(DSRC)/spec.out spec.ps spec.pdf
	rm -f $(LICENSE).pdf
