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
designs have been formally verified, and should be reliable to use.

As of 20190101, [this AXI-lite to WB bridge](rtl/axlite2wbsp.v) has been
FPGA proven.

The full AXI4 protocol, however, is rather complicated--especially when
[compared to WB](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html).  As a
result, while there is a full-fledged
[AXI4 to Wishbone bridge](rtl/axim2wbsp.v) within this project,
this bridge is still not ready for prime time.  It is designed to
synchronize the write channels, turning AXI read/write requests into pipeline
wishbone requests, maintaining the AXI ID fields, handle burst transactions,
etc.  As designed, it ignores the AXI xSIZE, xLOCK, xCACHE, xPROT, and xQOS
fields, while supporting xBURST types of FIXED (2'b00) and INCR (2'b01)
but not WRAP (2'b10) or reserved (2'b11).  The design supports bridging
between buses of different widths.  The only problem is ...
this full AXI4 to WB converter _doesn't work_ (yet).  I know this because it
doesn't yet pass formal verification.

# Wishbone pipeline to WB Classic

As of 20190424, there's now a [Wishbone (pipelined, master) to Wishbone
(classic, slave)](rtl/wbp2classic.v) bridge, as well as the reverse
[Wishbone (classic, master) to Wishbone (pipelined, slave)](rtl/wbc2pipeline.v)
bridge.  It's recent as of this writing, but it has passed its formal tests.

# Formal Verification

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone
(classic)](bench/formal/fwbc_slave.v), [Wishbone
(pipelined)](bench/formal/fwb_slave.v), and
[AXI-lite](bench/formal/faxil_slave.v) buses.  There's also a formal
property specification for an [AXI (full) bus](bench/formal/faxi_slave.v), but
the one in the master branch is known to have issues.  (I actually have a
good set of formal properties for verifying AXI transactions, they just aren't
part of this repository at this time.)

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

- [AXIXBAR](rtl/axixbar.v) is a fun (but ongoing, work-in-progress) project to
  develop a full `NxM` configurable cross bar using the full AXI protocol.

  Unique to this (full) AXI core is the ability to have multiple ongoing
  transactions on each of the master-to-slave channels.  Were Xilinx's
  crossbar to do this, it would've broken their [demonstration AXI-full slave
  core](bench/formal/xlnxfull_2018_3.v).

- [DEMOAXI](rtl/demoaxi.v) is a demonstration AXI-lite slave core with more
  power and capability than Xilinx's demonstration AXI-lite slave core.
  Particular differences include 1) this one passes a formal verification check
  (Xilinx's core has bugs), and 2) this one can handle a maximum throughput of
  one transaction per clock.  (There's did at best two transactions per clock.)
  You can read more about this [demonstration AXI-lite slave
  core](rtl/demoaxi.v) on [ZipCPU.com](http://zipcpu.com) in
  [this article](http://zipcpu.com/blog/2019/01/12/demoaxilite.html).
  *This core has been formally verified.*

- [DEMOFULL](rtl/demofull.v) is a new core recently added to this collection.
  This is also a demonstration slave core, but this demonstration slave core
  implements the full AXI protocol, rather than just the AXI-lite protocol.
  Well, okay, it ignores QOS, CACHE, and LOCK flags, so perhaps it isn't
  truly the *full* AXI protocol, but neither did [Xilinx's demonstration full
  AXI slave core](bench/formal/xlnxfull_2018_3.v).

  *This core has been formally verified.*

# Commercial Applications

Should you find the GPLv3 license insufficient for your needs, other licenses
can be purchased from Gisselquist Technology, LLc.

# Thanks

I'd like to thank @wallento for his initial work on a
[Wishbone to AXI converter](https://github.com/wallento/wb2axi), and his
encouragement to improve upon it.  While this isn't a fork of his work, the
[pipelined wishbone to AXI bridge](rtl/wbm2axisp.v) took its initial
motivation from his work.

Many of the rest of these projects have been motivated by the desire to learn
and develop my formal verification skills.
