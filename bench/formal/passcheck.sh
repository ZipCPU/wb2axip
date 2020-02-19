#!/bin/bash
################################################################################
##
## Filename: 	passcheck.sh
##
## Project:	WB2AXIPSP: bus bridges and other odds and ends
##
## Purpose:	This script simply checks for failing proofs of any type,
##		printing out the files associated with any such failing proofs.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## This simple bash script is herein donated to the public domain
##
################################################################################
##
##
find . -name FAIL
find . -name UNKNOWN
find . -name ERROR
