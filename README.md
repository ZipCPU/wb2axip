# WB2AXIP: A Pipelined Wishbone B4 to AXI4 bridge

Built out of necessity, [this core](rtl/wbm2axisp.v) is designed to provide
a conversion from a [wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI bus.
Primarily, the core is designed to connect a
[wishbone bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html),
either 32- or 128-bits wide, to a 128-bit wide AXI bus, which is the natural
width of a DDR3 transaction (with 16-bit lanes).  Hence, if the
Memory Interface Generator DDR3 controller is running at a 4:1 clock rate,
memory clocks to AXI system clocks, then it should be possible to accomplish
one transaction per clock at a sustained or pipelined rate.  This
[bus translator](rtl/wbm2axisp.v) is designed to be able to handle one
transaction per clock (pipelined), although [(due to Xilinx's MIG design)
the delay may be up to 27 clocks](http://opencores.org/project,wbddr3).  (Ouch!)

Since the initial build of the core, I've added the
[WB to AXI lite](rtl/wbm2axilite.v) bridge.  This is also a pipelined bridge,
and like the original one it has also been formally verified.

# AXI to Wishbone conversion

As of 20181228, the project now contains an
[AXI4 lite read channel to wishbone interface](rtl/axilrd2wbsp.v), and also an
[AXI4 lite write channel to wishbone interface](rtl/axilwr2wbsp.v).  
A third core, the [AXI-lite to WB core](rtl/axlite2wbsp.v) combines these
two together using a  [Wishbone arbiter](rtl/wbartbiter.v).  All four of these
designs have been *formally verified*, and should be reliable to use.

As of 20190101, [this AXI-lite to WB bridge](rtl/axlite2wbsp.v) has been
FPGA proven.

The full AXI to WB bridge, however, remains a work in progress.  This includes
the [write half](rtl/aximwr2wbsp.v), [read half](rtl/aximrd2wbsp.v), and the
[read/write wrapper](rtl/axim2wbsp.v).

# Wishbone pipeline to WB Classic

As of 20190424, there's now a [Wishbone (pipelined, master) to Wishbone
(classic, slave)](rtl/wbp2classic.v) bridge, as well as the reverse
[Wishbone (classic, master) to Wishbone (pipelined, slave)](rtl/wbc2pipeline.v)
bridge.  It's recent as of this writing, but it has passed its formal tests.
As written, it can only support Classic transactions.

# Formal Verification

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone
(classic)](bench/formal/fwbc_slave.v), [Wishbone
(pipelined)](bench/formal/fwb_slave.v), and
[AXI-lite](bench/formal/faxil_slave.v) buses.  There's also a formal
property specification for an [AXI (full) bus](bench/formal/faxi_slave.v), but
the one in the master branch is known to have issues.  (I actually have a
good set of formal properties for verifying full AXI4 transactions.  Those
will be available as part of the [SymbioticEDA
Suite](https://www.symbioticeda.com/seda-suite).
Previews are available to my [sponsors](http://www.patreon.com/ZipCPU).)

# Cross-bars and AXI demonstrators

This repository has since become a repository for all kinds of bus-based
odds and ends in addition to the bus translators mentioned above.  Some of
these odds and ends include crossbar switches and AXI demonstrator cores.

- [WBXBAR](rtl/wbxbar.v) is a fully function N master to M slave Wishbone
  crossbar.  Unlike my typical WB interconnects, this one guarantees that the
  ACK responses won't get crossed, and that misbehaving slave accesses will
  be timed out.  The core also has options for checking for starvation
  (where a master's request is not granted in a particular period of time),
  double-buffering all outputs (i.e. with skid buffers), and forcing idle
  channel values to zero in order to reduce power.

  *This core has been formally verified.*

- [AXILXBAR](rtl/axilxbar.v) is a fully functional, formally verified, `N`
  master to `M` slave AXI-lite crossbar interconnect.  As such, it permits
  `min(N,M)` active channel connections between masters and slaves all at once.
  This core also has options for low power, whereby unused outputs are forced
  to zero, and lingering.  Since the AXI protocol doesn't specify exactly
  when to close a channel, there's an `OPT_LINGER` allowing you to specify
  how many cycles the channel should be idle for in order for the channel
  to be closed.  If the channel is not closed, a clock can be spared when
  reusing it.  Otherwise, two clocks will be required to access a given channel.

  *This core has been formally verified.*

  While I haven't tested Xilinx's interconnect to know, if the quality of
  [their demonstration AXI-lite slave core](bench/formal/xlnxdemo.v) is any
  indication, then this cross-bar should easily outperform anything they have.
  The key unusual feature?  The ability to maintain one transaction per clock
  over an extended period of time across any channel pair.

- [AXIXBAR](rtl/axixbar.v) is a fun project to develop a full `NxM`
  configurable cross bar using the full AXI protocol.

  Unique to this (full) AXI core is the ability to have multiple ongoing
  transactions on each of the master-to-slave channels.  Were Xilinx's
  crossbar to do this, it would've broken their [demonstration AXI4 slave
  core](bench/formal/xlnxfull_2018_3.v).

  *This core has been formally verified.*

- [DEMOAXI](rtl/demoaxi.v) is a demonstration AXI-lite slave core with more
  power and capability than Xilinx's demonstration AXI-lite slave core.
  Particular differences include 1) this one passes a formal verification check
  (Xilinx's core has bugs), and 2) this one can handle a maximum throughput of
  one transaction per clock.  (Theirs did at best one transactions every other
  clock period.) You can read more about this [demonstration AXI-lite slave
  core](rtl/demoaxi.v) on [ZipCPU.com](http://zipcpu.com) in
  [this article](http://zipcpu.com/blog/2019/01/12/demoaxilite.html).

  *This core has been formally verified.*

- [DEMOFULL](rtl/demofull.v) is a fully capable AXI4 demonstration slave core,
  rather than just the AXI-lite protocol.  Well, okay, it doesn't do anything
  with the PROT, QOS, CACHE, and LOCK flags, so perhaps it isn't truly the
  *full* AXI protocol.  Still, it's sufficient for most needs.

  Unlike [Xilinx's demonstration AXI4 slave
  core](bench/formal/xlnxfull_2018_3.v), [this one](rtl/demofull.v) can handle
  100% loading on both read and write channels.  That is, it can handle one
  read or write data beat per channel per clock with no stalls between bursts.

  *This core has been formally verified.*

- [AXISAFETY](rtl/axisafety.v) is a bus fault isolator AXI translator,
  designed to support a connection to a trusted AXI master, and an untrusted
  AXI slave.  Should the slave attempt to return an illegal response, or
  perhaps a response beyond the internal timeouts within the core, then the
  untrusted slave will be "disconnected" from the bus, and a bus error will be
  return for both the errant transaction and any following.

  [AXISAFETY](rtl/axisafety.v) also has a mode where, once a fault has been
  detected, the slave is reset and allowed to return to the bus infrastructure
  until its next fault.

  *This core has been formally verified.*

# Commercial Applications

Should you find the [GPLv3 license](doc/gpl-3.0.pdf) insufficient for your
needs, other licenses can be purchased from Gisselquist Technology, LLC.
Likewise the AXI4 (full) properties are available to
[sponsors](https://www.patreon.com/ZipCPU) of the [ZipCPU
blog](http://zipcpu.com).

# Thanks

I'd like to thank @wallento for his initial work on a
[Wishbone to AXI converter](https://github.com/wallento/wb2axi), and his
encouragement to improve upon it.  While this isn't a fork of his work, the
[pipelined wishbone to AXI bridge](rtl/wbm2axisp.v) took its initial
motivation from his work.

Many of the rest of these projects have been motivated by the desire to learn
and develop my formal verification skills.
