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
##		gpl-3.0.pdf	Builds the GPL license these files are released
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
## Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
all:	gpl spec
pdf:	gpl spec
DSRC := src

.PHONY: gpl
gpl: gpl-3.0.pdf

gpl-3.0.pdf: $(DSRC)/gpl-3.0.tex
	latex $(DSRC)/gpl-3.0.tex
	latex $(DSRC)/gpl-3.0.tex
	dvips -q -z -t letter -P pdf -o gpl-3.0.ps gpl-3.0.dvi
	ps2pdf -dAutoRotatePages=/All gpl-3.0.ps gpl-3.0.pdf
	rm gpl-3.0.dvi gpl-3.0.log gpl-3.0.aux gpl-3.0.ps

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
	rm -f gpl-3.0.pdf

