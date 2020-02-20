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
do a proper induction (unbounded) proof.

## AXI Stream

[Master](faxis_master.v) and [slave](faxis_slave.v) properties.

I rarely use these properties, however.  I've found that every AXI stream
slave is unique, especially input or output slaves that operate at a fixed
rate.  These properties also rely upon default portlist properties for
the rarely used signals, `TID`, `TKEEP`, `TDEST`, and `TUSER`, something
Yosys didn't yet support when they were first written.

## Avalon

It's been a while since I've worked with Avalon, but the [slave
properties](fav_slave.v) found here saved my bacon in a
[Cyclone-V design](https://zipcpu.com/blog/2018/02/09/first-cyclonev.html)
more than once.  These properties only use a subset of the Avalon signals
as well, and don't support any of the burst signaling capabilities of Avalon.

## APB

[Slave](fapb_slave.v) properties.  These haven't really been tested well,
so your mileage with them might vary.
