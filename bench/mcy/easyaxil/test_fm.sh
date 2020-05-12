#!/bin/bash

exec 2>&1
set -ex

export SCRIPT=/home/dan/work/rnd/opencores/tools/mcy/scripts/create_mutated.sh
# create_mutated.sh
. ${SCRIPT}

## create yosys script with instructions how to export the mutated design
# {
#	# read synthesized design
#	echo "read_ilang ../../database/design.il"
#	# apply mutation
#	# First line is numbered one, two, etc.
#	# This cust off the '1' in the beginning, keeps the rest of the
#	# mutate command
#	cut -f2- -d' ' input.txt
#	# export design to RTLIL
#	echo "write_ilang mutated.il"
#	echo "write_verilog mutated.v"
#} > mutate.ys

## run the above script to create mutated.il
yosys -ql mutate.log mutate.ys

## run formal property check
ln -s ../../test_fm.sby    .
ln -s ../../faxil_slave.v  .
ln -s ../../easyprops.sv .

sby -f test_fm.sby prf

## obtain result
gawk "{ print 1, \$1; }" test_fm_prf/status | sed -e "s/UNKNOWN/FAIL/" >> output.txt

exit 0
