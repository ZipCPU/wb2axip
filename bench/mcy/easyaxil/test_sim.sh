#!/bin/bash

# Pipe standard error stream to stdout
exec 2>&1

# Exit on any non-zero error code along the way
set -ex

export SCRIPT=${HOME}/work/rnd/opencores/tools/mcy/scripts/create_mutated.sh
. ${SCRIPT} -c

VROOT=/usr/local/share/verilator
VINC=${VROOT}/include
INCFILES="-I${VROOT}/include -Iobj_dir"
CFLAGS="-Wall -O3"
# CPPDIR="../../../cpp"
CPPDIR="../.."
OBJ=obj_dir

# {
#	echo "read_ilang ../../database/design.il"
#	while read -r idx mut; do
#		echo "mutate -ctrl mutsel 8 ${idx} ${mut#* }"
#	# One line goes into input.txt
#	done < input.txt
#	echo "write_verilog -attr2comment mutated.v"
#} > mutate.ys

yosys -ql mutate.log mutate.ys
cp ${CPPDIR}/easyaxil_tb.cpp  .
cp ${CPPDIR}/axi_tb.h         .
cp ${CPPDIR}/devbus.h         .
cp ${CPPDIR}/testb.h          .

cp mutated.v easyaxil.v
verilator -O3 --trace -Wno-UNOPTFLAT -Wno-CASEOVERLAP -Wno-WIDTH -cc easyaxil.v
g++ ${CFLAGS} ${INCFILES} -DMCY -c easyaxil_tb.cpp -o ${OBJ}/easyaxil.o
g++ ${CFLAGS} ${INCFILES} -c ${VINC}/verilated.cpp -o ${OBJ}/verilated.o
g++ ${CFLAGS} ${INCFILES} -c ${VINC}/verilated_vcd_c.cpp -o ${OBJ}/verilated_vcd.o
cd obj_dir
make -f Veasyaxil.mk
g++ easyaxil.o verilated.o verilated_vcd.o Veasyaxil__ALL.a -o ../easyaxil_tb
cd ..

./easyaxil_tb 0 > goodsim.out || true
good_sum=$(md5sum goodsim.out | awk '{ print $1; }')
while read idx mut; do

	./easyaxil_tb ${idx} > sim_${idx}.out || true
	this_sum=$(md5sum sim_${idx}.out | awk '{ print $1; }')
	echo "SUM " $this_sum
	if [ $good_sum = $this_sum ]; then
		echo "$idx PASS" >> output.txt
	else
		echo "$idx FAIL" >> output.txt
	fi
done < input.txt
exit 0
