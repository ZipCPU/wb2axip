#!/bin/bash

exec 2>&1
set -ex

export SCRIPT=/home/dan/work/rnd/opencores/tools/mcy/scripts/create_mutated.sh
# create_mutated.sh -c
. ${SCRIPT} -c
## create yosys script with instructions how to export the mutated design
# {
#	# read synthesized design
#	echo "read_ilang ../../database/design.il"
#	while read -r idx mut; do
#		# add mutation to the design, to be enabled by value ${idx} on 8-bit input `mutsel` added to the module
#		echo "mutate -ctrl mutsel 8 ${idx} ${mut#* }"
#	done < input.txt
#	# export design to RTLIL
#	echo "write_ilang mutated.il"
#	echo "write_verilog mutated.v"
#} > mutate.ys

## run the above script to create mutated.il
yosys -ql mutate.log mutate.ys

## run formal property check
ln -s ../../test_eq.sv     .
ln -s ../../test_fm.sby    .
ln -s ../../faxil_slave.v  .
ln -s ../../easyaxil_tb.sv .
# sed -e '1,$s/easyaxil/goldenaxil/' < ../../easyaxil.v > goldenaxil.v

sby -f test_fm.sby bmc

## obtain result
gawk "{ print 1, \$1; }" test_fm_bmc/status >> output.txt

exit 0
