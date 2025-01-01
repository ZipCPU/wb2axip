#!/usr/bin/perl
################################################################################
##
## Filename:	bench/formal/genreport.pl
## {{{
## Project:	WB2AXIPSP: bus bridges and other odds and ends
##
## Purpose:	Generates an HTML report file which can be used to evaluate the
##		current status of specific named proofs.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2017-2025, Gisselquist Technology, LLC
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
## }}}

## Variable declarations
## {{{
$dir = ".";
@proofs = (
	"addrdecode",
	"afifo",
	"apbslave",
	"apbxclk",
	"axi2axilite",
	"axi2axilsub",
	"axidma",
	"axidouble",
	"axiempty",
	"axil2apb",
	"axil2axis",
	"axildouble",
	"axilempty",
	"axilgpio",
	"axilite2axi",
	"axilrd2wbsp",
	"axilsafety",
	"axilsingle",
	"axilupsz",
	"axilwr2wbsp",
	"axilxbar",
	"aximm2s",
	"aximrd2wbsp",
	"aximwr2wbsp",
	"axiperf",
	"axis2mm",
	"axisafety",
	"axisbroadcast",
	"axisgfsm",
	"axispacker",
	"axisrandom",
	"axissafety",
	"axisswitch",
	"axivcamera",
	"axivdisplay",
	"axivfifo",
	"axixbar",
	"axlite2wbsp",
	"demoaxi",
	"demofull",
	"easyaxil",
	"sfifo",
	"skidbuffer",
	"wbarbiter",
	"wbc2pipeline",
	"wbm2axilite",
	"wbm2axisp",
	"wbp2classic",
	"wbsafety",
	"wbxbar",
	"wbxclk",
	"xlnxdemo_2018_3",
	"xlnxdemo"
	# "xlnxaxil_2020_1",
	# "xlnxfull_2018_3",
	# "xlnxstream_2018_3"
	);

%desc = (
	"addrdecode"	=> "Address decoder, used in bus crossbars",
	"afifo"		=> "Asynchronous FIFO",
	"apbslave"	=> "APB Slave",
	"apbxclk"	=> "APB Clock crossing bridge",
	"axi2axilite"	=> "AXI to AXI-Lite bridge",
	"axi2axilsub"	=> "Wide AXI to smaller AXI-Lite bridge",
	"axidma"	=> "AXI DMA (memory copy function)",
	"axidouble"	=> "AXI to simplified DOUBLE interface bridge",
	"axiempty"	=> "Empty AXI slave implementation, returns bus errs",
	"axil2apb"	=> "AXI-Lite to APB bridge",
	"axil2axis"	=> "AXI-Lite to AXI stream bridge",
	"axildouble"	=> "AXI-Lite to DOUBLE interface bridge",
	"axilempty"	=> "Empty AXI-Lite slave implementation",
	"axilgpio"	=> "AXI-Lite slave, controlling GPIO peripheral",
	"axilite2axi"	=> "AXI-Lite to AXI bridge",
	"axilrd2wbsp"	=> "AXI-Lite (read-only) to Wishbone bridge",
	"axilsafety"	=> "AXI-Lite firewall",
	"axilsingle"	=> "AXI-Lite to SINGLE interface bridge",
	"axilupsz"	=> "AXI-Lite to larger bus bridge",
	"axilwr2wbsp"	=> "AXI-Lite (write-only) to Wishbone bridge",
	"axilxbar"	=> "AXI-Lite Crossbar",
	"aximm2s"	=> "AXI memory to stream DMA",
	"aximrd2wbsp"	=> "AXI (read-only) to Wishbone bridge",
	"aximwr2wbsp"	=> "AXI (write-only) to Wishbone bridge",
	"axiperf"	=> "AXI Performance monitor",
	"axis2mm"	=> "AXI stream to memory DMA",
	"axisafety"	=> "AXI firewall",
	"axisbroadcast"	=> "AXI stream broadcaster",
	"axisgfsm"	=> "AXI Scatter-gather demonstrator",
	"axispacker"	=> "AXI Stream byte packer",
	"axisrandom"	=> "AXI stream random number generator",
	"axissafety"	=> "AXI Stream firewall",
	"axisswitch"	=> "AXI Stream switch",
	"axivcamera"	=> "AXI Video stream input to memory",
	"axivdisplay"	=> "Memory to AXI Video stream",
	"axivfifo"	=> "AXI Virtual FIFO",
	"axixbar"	=> "AXI Crossbar",
	"axlite2wbsp"	=> "AXI-Lite to Wishbone (pipelined) bridge",
	"demoaxi"	=> "AXI-Lite demonstrator",
	"demofull"	=> "AXI (full) demonstrator",
	"easyaxil"	=> "Simple AXI-Lite demonstrator",
	"sfifo"		=> "A Basic synchronous FIFO",
	"skidbuffer"	=> "Skidbuffer",
	"wbarbiter"	=> "A basic Wishbone 2-way arbiter",
	"wbc2pipeline"	=> "Wishbone classic to pipeline bridge",
	"wbm2axilite"	=> "Wishbone to AXI-Lite bridge",
	"wbm2axisp"	=> "Wishbone to AXI (pipelined) bridge",
	"wbp2classic"	=> "Wishbone pipeline to classic bridge",
	"wbsafety"	=> "Wishbone firewall",
	"wbxbar"	=> "Wishbone crossbar",
	"wbxclk"	=> "Wishbone clock domain crossing bridge",
	"xlnxdemo"		=> "Xilinx\'s (broken) AXI-Lite slave template"
	# "xlnxaxil_2020_1",
	# "xlnxfull_2018_3",
	# "xlnxstream_2018_3"
	);
## }}}

## getstatus subroutine
## {{{
# This subroutine runs make, to see if a proof is up to date, or otherwise
# checks the logfile to see what the status was the last time the proof was
# run.
sub getstatus($) {
	my $based = shift;
	my $log = "$based/logfile.txt";

	my $bmc = 0;
	my $ind = 0;
	my $cvr = 0;
	my $ncvr = 0;

	my $PASS = 0;
	my $FAIL = 0;
	my $UNK = 0;
	my $ERR = 0;
	my $terminated = 0;
	my $current = 1;
	my $nreached = 0;

	# print "<TR><TD>Checking make $based/PASS</TD></TR>\n";

	if (open(MAK, "make -n $based/PASS |")) {
		while($line = <MAK>) {
			if ($line =~ /sby/) {
				$current = 0;
			}
		} close(MAK);
	}

	# print "<TR><TD>Opening log, $log</TD></TR>\n";

	open (LOG, "< $log") or return "No log";
	while($line = <LOG>) {
		# print "<TR><TD>LINE=$line</TD></TR>\n";
		if ($line =~ /DONE.*FAIL/) {
			$FAIL = 1;
			# print "<TR><TD>FAIL match</TD></TR>\n";
		} if ($line =~ /DONE.*PASS/) {
			$PASS = 1;
			# print "<TR><TD>PASS match</TD></TR>\n";
		} if ($line =~ /DONE.*UNKNOWN/) {
			$UNK = 1;
			# print "<TR><TD>UNKNOWN match</TD></TR>\n";
		} if ($line =~ /DONE.*ERROR/) {
			$ERR = 1;
			# print "<TR><TD>ERROR match</TD></TR>\n";
		} if ($line =~ /terminating process/) {
			$terminated = 1;
		} if ($line =~ /Reached cover statement/) {
			$nreached = $nreached + 1;
		} if ($line =~ /Checking cover/) {
			$cvr = 1;
		} if ($line =~ /engine_\d.induction/) {
			$ind = 1;
			# print "<TR><TD>induction match</TD></TR>\n";
		} if ($line =~ /engine_\d.basecase.*Checking assertions in step\s+(\d+)/) {
			if ($1 > $bmc) {
				$bmc = $1;
				# print "<TR><TD>basecase $bmc match</TD></TR>\n";
			}
		} if ($line =~ /engine_\d:.*Writing trace to VCD.*trace(\d+).vcd/) {
			if ($1 > $ncvr) {
				$ncvr = $1+1;
			}
		}
	}
	close(LOG);

	if ($PASS) {
		if ($current == 0) {
			"Out of date";
		} elsif ($cvr) {
			"Cover $ncvr";
		} else {
			"PASS";
		}
	} elsif ($FAIL) {
		"FAIL";
	} elsif ($ERR) {
		"ERROR";
	} elsif (($ind == 0 || $UNK != 0) && $bmc > 0) {
		"BMC $bmc";
	} elsif ($terminated) {
		"Terminated";
	} elsif ($nreached > 0) {
		"Reached $nreached";
	} else {
		"Unknown";
	}
}
## }}}

## Start the HTML output
## {{{
print <<"EOM";
<HTML><HEAD><TITLE>Formal Verification Report</TITLE></HEAD>
<BODY>
<TABLE border>
<TR><TH>Status</TH><TH>Component</TD><TH>Proof</TH><TH>Component description</TH></TR>
EOM
## }}}

## Look up all directory entries
## {{{
# We'll use this result to look for subdirectories that might contain
# log files.
opendir(DIR, $dir) or die "Cannot open directory for reading";
my @dirent = readdir(DIR);
closedir(DIR);

# print "@dirent";
## }}}

# Lookup each components proof
foreach $prf (sort @proofs) {
	my $ndirs=0;
	foreach $dent (@dirent) {
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /$prf(_\S+)/);
			$subprf = $1;

		$ndirs = $ndirs+1;
	}

	my $firstd = 1;

	# Find each subproof of the component
	foreach $dent (@dirent) {
		## Filter out the wrong directories
		## {{{
		# print("<TR><TD>DIR $dent</TD></TR>\n");
		# Only look at subdirectories
		next if (! -d $dent);
		next if ($dent =~ /^\./);
		next if ($dent !~ /$prf(_\S+)/);
			$subprf = $1;
		# print("<TR><TD>$dent matches $prf</TD></TR>\n");
		## }}}

		## Get the resulting status
		$st = getstatus($dent);
		# print("<TR><TD>STATUS = $st</TD></TR>\n");

		## Fill out one entry of our table
		## {{{
		my $tail;
		if ($firstd) {
			print "<TR></TR>\n";
			$tail = "</TD><TD>$prf</TD><TD>$subprf</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
			$firstd = 0;
		} else {
			$tail = "</TD><TD>$prf</TD><TD>$subprf</TD></TR>\n";
		}
		if ($st =~ /PASS/) {
			print "<TR><TD bgcolor=#caeec8>Pass$tail";
		} elsif ($st =~ /Cover\s+(\d+)/) {
			print "<TR><TD bgcolor=#caeec8>$1 Cover points$tail";
		} elsif ($st =~ /FAIL/) {
			print "<TR><TD bgcolor=#ffa4a4>FAIL$tail";
		} elsif ($st =~ /Terminated/) {
			print "<TR><TD bgcolor=#ffa4a4>Terminated$tail";
		} elsif ($st =~ /ERROR/) {
			print "<TR><TD bgcolor=#ffa4a4>ERROR$tail";
		} elsif ($st =~ /Out of date/) {
			print "<TR><TD bgcolor=#ffffca>Out of date$tail";
		} elsif ($st =~ /BMC\s+(\d)+/) {
			print "<TR><TD bgcolor=#ffffca>$1 steps of BMC$tail";
		} elsif ($st =~ /Reached\s+(\d+)/) {
			print "<TR><TD bgcolor=#ffffca>$1 cover points$tail";
		} elsif ($st =~ /No log/) {
			print "<TR><TD bgcolor=#e5e5e5>No log file found$tail";
		} else {
			print "<TR><TD bgcolor=#e5e5e5>Unknown$tail";
		}
		## }}}
	} if ($myfirstd != 0) {
		print "<TR><TD bgcolor=#e5e5e5>Not found</TD><TD>$prf</TD><TD>&nbsp;</TD><TD rowspan=$ndirs>$desc{$prf}</TD></TR>\n";
	}
}

## Finish the HTML log file
## {{{
print <<"EOM";
</TABLE>
</BODY></HTML>
EOM
## }}}
