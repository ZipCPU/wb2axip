Every IP component in the [rtl](../../rtl) directory should have a respective
SymbiYosys script here.  (A .sby file.)  Many of the AXI scripts remain
proprietary and so get published elsewhere, but the AXI-lite and Wishbone
scripts can be found here.

In addition to the formal verification scripts found in this directory,
you'll also find a series of bus properties for various interface standards.
In general, these property sets are found in pairs--one property set for the
slave, and a second property set for verifying the bus master.  I routinely
compare these sets against each other using [meld](https://meldmerge.org),
so you shouldn't find any really substantial differences between them.

## Wishbone (Pipelined)

[Master](fwb_master.v) and [Slave](fwb_slave.v) properties.

My properties insist on two clarifications to the WB specification: 1) any
bus cycle may be aborted by dropping the CYC line, and 2) the CYC line will
drop and all bus cycles will be aborted following any bus error.  I've also
dropped the retry signal from the standard.

## Wishbone (Classic)

[Master](fwbc_master.v) and [Slave](fwbc_slave.v) properties.

## AXI4-Lite

[Master](faxil_master.v) and [Slave](faxil_slave.v) properties.  These may
be the easiest AXI4-lite property sets to use.

## AXI4

These properties are kept in a separate repository.  You can see some of what
they contain in the [master](faxi_master.v) and [slave](faxi_slave.v) properties
contained in this directory.  The full properties, however, will allow you to
do a proper induction (unbounded) proof.  Those full properties can also handle
out-of-order packet returns, such as AXI permits, to make certain that a
core is fully/properly functional.  The difficulty of checking these out of
order properties using induction is one of the reasons these properties may be
purchased rather than downloaded for free.

## AXI Stream

[Master](faxis_master.v) and [slave](faxis_slave.v) properties.

I rarely use these properties, however.  I've found that every AXI stream
slave is unique, especially input or output slaves that operate at a fixed
rate.  These properties also rely upon default portlist properties for
the rarely used signals, `TID`, `TKEEP`, `TDEST`, and `TUSER`, something
Yosys didn't yet support when they were first written.

That said, the properties are currently good enough as is to prove that
[Xilinx's AXI-Stream master](xlnxstream_2018_3.v) demonstration IP is broken.

## Avalon

It's been a while since I've worked with Avalon, but the [slave
properties](fav_slave.v) found here saved my bacon in a
[Cyclone-V design](https://zipcpu.com/blog/2018/02/09/first-cyclonev.html)
more than once.  These properties only use a subset of the Avalon signals
as well, and don't support any of the burst signaling capabilities of Avalon.

## APB

[Master](fapb_master.v) and [slave](fapb_slave.v) properties.
