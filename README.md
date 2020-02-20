# WB2AXIP: Bus interconnects, bridges, and other components

The bus components and bridges within this repository are unique in that they
are all designed for 100% throughput with no throughput overhead.  They are also
unique in that the vast majority of the cores within have all been formally
verified.

Where the protocol allows it, such as with AXI4, AXI-lite, and Wishbone B4
pipelined, multiple transactions may be in flight at a time so that
protocol handling doesn't stall the bus.

This is uncommon among AXI4 implementations and almost unheard of in the
AXI-lite implementations I have examined.

Most AXI4 implementations will process a single burst transaction packet at
a time and require some overhead to make this happen.  Xilinx's AXI-lite
implementations, both interconnect and slave implementations, only handle one
request at a time.  Other buses, such as Wishbone Classic, AHB, or APB, will
only ever process one transaction word at a time.

If you are coming from AXI4, AXI-lite, or any one of these other bus
implementations to the AXI4 or even AXI-lite components supported here, then
you should expect to see a throughput increase by using one (or more) of these
cores--given of course that you have a bus master capable of issuing multiple
requests at a time.

This performance improvement may be as significant as a [16x speedup when
toggling an I/O](https://zipcpu.com/zipcpu/2019/02/09/cpu-blinky.html), a 4x
speedup in when comparing [this slave](rtl/demofull.v) against Xilinx's block
RAM memory controller (when processing single beat transactions), or as
insignificant as 2% improvement from using the AXI4 MM to Slave converters
(according to Xilinx's data sheets---I haven't yet run the test myself).  This
increased performance extends to the crossbar implementations contained within
this repository as well, and so you may notice the improvement only increases
when using these crossbars.

# A Pipelined Wishbone B4 to AXI4 bridge

Built out of necessity, this repository was originally built around [a Wishbone
(WB) to AXI4 bridge](rtl/wbm2axisp.v), which is designed to provide a
conversion from a [pipelined wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI4 bus for the
purposes of driving memory transactions through Xilinx SDRAM controllers.  [The
WB->AXI bridge](rtl/wbm2axisp.v) is designed to connect a [wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI bus which
may be wider--such as from a 32-bit WB bus to a 128-bit AXI bus.  Hence, if
the Memory Interface Generator DDR3 controller is running at a 4:1 clock rate,
memory clocks to AXI system clocks, then this [bus translator](rtl/wbm2axisp.v)
should be able to accomplish one transaction per clock at a sustained or
pipelined rate.

Since the initial build of [the core](rtl/wbm2axisp.v), I've added the
[WB to AXI lite](rtl/wbm2axilite.v) bridge.  This is also a pipelined bridge,
and like the original one it has also been formally verified.

# AXI to Wishbone conversion

While not the original purpose of the project, it now has both
[AXI-lite to WB](rtl/axlite2wbsp.v)
and [AXI to WB](rtl/axim2wbsp.v) bridges.  Each of these bridges comes in
two parts, a read and write half.  These halves can be used either independently
, generating separate inputs to a [WB crossbar](rtl/wbxbar.v),
or combined through a [WB arbiter](rtl/wbarbiter.v).

[The AXI-lite to WB bridge](rtl/axlite2wbsp.v) has been both formally
verified and FPGA proven.  This includes both the [write
half](rtl/axilwr2wbsp.v) as well as the [read half](rtl/axilrd2wbsp.v).
Given the reluctance of the major vendors to support high speed AXI-lite
interfaces, you aren't likely to find this kind of performance elsewhere.

[The AXI to WB bridge](rtl/axim2wbsp.v) [write](rtl/aximwr2wbsp.v) and
[read](aximrd2wbsp.v) components have only been formally verified through
about a dozen steps or so.  This proof is deep enough to
verify most of the bus interactions, but not nearly deep enough to verify
any issues associated with internal FIFO overflows.

# Wishbone pipeline to WB Classic

There's also a [Wishbone (pipelined, master) to Wishbone
(classic, slave)](rtl/wbp2classic.v) bridge, as well as the reverse
[Wishbone (classic, master) to Wishbone (pipelined, slave)](rtl/wbc2pipeline.v)
bridge.  Both of these have passed their formal tests.  They are accompanied
by a set of formal properties for Wishbone classic, both for
[slaves](bench/formal/fwbc_slave.v) as well as
[masters](bench/formal/fwbc_master.v).

# Formal Verification

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone
(classic)](bench/formal/fwbc_slave.v), [Wishbone
(pipelined)](bench/formal/fwb_slave.v), and
[AXI-lite](bench/formal/faxil_slave.v) buses.  There's also a formal
property specification for an [AXI (full) bus](bench/formal/faxi_slave.v), but
the one in the master branch is incomplete.  The complete set of AXI
properties are maintained elsewhere.

# Xilinx Cores

The formal properties were first tested on a pair of Xilinx AXI demonstration
cores.  These cores failed formal verification.  You can read about them
on [my blog, at zipcpu.com](https://zipcpu.com), [here for
AXI-lite](http://zipcpu.com/formal/2018/12/28/axilite.html) and
[here for AXI](http://zipcpu.com/formal/2019/05/13/axifull.html).
You can find the Xilinx cores referenced in those articles
[here](bench/formal/xlnxdemo.v) and [here](bench/formal/xlnxfull_2018_3.v) for
reference, for those who wish to repeat or examine my proofs.

# Cross-bars and AXI demonstrators

This repository has since become a repository for all kinds of bus-based
odds and ends in addition to the bus translators mentioned above.  Some of
these odds and ends include crossbar switches and AXI demonstrator cores.
As mentioned above, these cores are unique in their 100% throughput
capabilities.

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
  [their demonstration AXI-lite slave
  core](http://zipcpu.com/formal/2018/12/28/axilite.html) is any
  indication, then this cross-bar should easily outperform anything they have.
  The key unusual feature?  The ability to maintain one transaction per clock
  over an extended period of time across any channel pair.

- [AXILSINGLE](rtl/axilsingle.v) is designed to be a companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI-lite support.  It's
  purpose is to simplify connectivity logic when supporting multiple AXI-lite
  registers.  This core takes a generic AXI-lite interface, and simplifies
  the interface so that multiple single-register cores can be connected to
  it.  The single-register cores can either be full AXI-lite cores in their
  own respect, subject to simplification rules, or even simplified from that.
  They must never stall the bus, and must always return responses within one
  clock cycle.  The [AXILSINGLE](rtl/axilsingle.v) handles all backpressure
  issues.  If done right, the backpressure logic from the slave core will be
  removed by the synthesis tool, allowing all backpressure logic to be
  condensed into a few shared wires.

  *This core has been formally verified.*

- [AXILDOUBLE](rtl/axildouble.v) is the second AXI-lite companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI-lite support.  It's
  purpose is to simplify connectivity logic when supporting multiple AXI-lite
  slaves.  This core takes a generic AXI-lite interface, and simplifies
  the interface so that peripherals can be connected to it.  These
  peripherals cores can either be full AXI-lite cores in their own respect,
  subject to simplification rules discussed within, or even simplified from
  that.  They must never stall the bus, and must always return responses
  within one clock cycle.  The [AXILDOUBLE](rtl/axildouble.v) core handles all
  backpressure issues, address selection, and invalid address returns.

  *This core has been formally verified.*

- [AXIXBAR](rtl/axixbar.v) is a fun project to develop a full `NxM`
  configurable cross bar using the full AXI protocol.

  Unique to this (full) AXI core is the ability to have multiple ongoing
  transactions on each of the master-to-slave channels.  Were Xilinx's
  crossbar to do this, it would've broken their [demonstration AXI-full slave
  core](http://zipcpu.com/formal/2019/05/13/axifull.html).

  *This core has been formally verified.*

- [DEMOAXI](rtl/demoaxi.v) is a demonstration AXI-lite slave core with more
  power and capability than Xilinx's demonstration AXI-lite slave core.
  Particular differences include 1) this one passes a formal verification check
  (Xilinx's core has bugs), and 2) this one can handle a maximum throughput of
  one transaction per clock.  (Theirs did at best one transaction every other
  clock period.)  You can read more about this [demonstration AXI-lite slave
  core](rtl/demoaxi.v) on [ZipCPU.com](http://zipcpu.com) in
  [this article](http://zipcpu.com/blog/2019/01/12/demoaxilite.html).

  *This core has been formally verified.*

- [DEMOFULL](rtl/demofull.v) is a fully capable AXI4 demonstration slave core,
  rather than just the AXI-lite protocol.  Well, okay, it doesn't do anything
  with the PROT, QOS, CACHE, and LOCK flags, so perhaps it isn't truly the
  *full* AXI protocol.  Still, it's sufficient for most needs.

  Unlike [Xilinx's demonstration AXI4 slave
  core](http://zipcpu.com/formal/2019/05/13/axifull.html),
  [this one](rtl/demofull.v) can handle 100% loading on both read and write
  channels simultaneously.  That is, it can handle one read and one write beat
  per channel per clock with no stalls between bursts if the environment will
  allow it.

  *This core has been formally verified.*

- [AXISAFETY](rtl/axisafety.v) is a bus fault isolator AXI translator,
  designed to support a connection to a trusted AXI master, and an untrusted
  AXI slave.  Should the slave attempt to return an illegal response, or
  perhaps a response beyond the internal timeouts within the core, then the
  untrusted slave will be "disconnected" from the bus, and a bus error will be
  return for both the errant transaction and any following.

  *This core has been formally verified.*

  [AXISAFETY](rtl/axisafety.v) also has a mode where, once a fault has been
  detected, the slave is reset and allowed to return to the bus infrastructure
  until its next fault.

  *This core has been formally verified.*

- [AXI2AXILITE](rtl/axi2axilite.v) converts incoming AXI4 (full) requests
  for an AXI-lite slave.  This conversion is fully pipelined, and capable of
  sending back to back AXI-lite requests on both channels.

  *This core has been formally verified.*

- [AXIS2MM](rtl/axis2mm.v) converts an incoming stream signal into outgoinng
  AXI (full) requests.  Supports bursting and aborted transactions.  Also
  supports writes to a constant address, and continuous writes to concurrent
  addresses.  This core depends upon all stream addresses being aligned.

  *This core has been formally verified.*

- [AXIMM2S](rtl/aximm2s.v) reads from a given address, and writes it to
  a FIFO buffer and then to an eventual AXI stream.  Read requests are not
  issued unless room already exists in the FIFO, yet for a sufficiently fast
  stream the read requests may maintain 100% bus utilization--but only if
  the rest of the bus does as well.  Supports continuous, fixed address or
  incrementing, and aborted transactions.

  Both this core and the one above it depend upon all stream addresses being
  aligned.

  *This core has been formally verified.*

- [AXIDMA](rtl/axidma.v) is a hardware assisted memory copy.  Given a source
  address, read address, and length, this core reads from the source address
  into a FIFO, and then writes the data from the FIFO to memory.  As an
  optimization, memory address requests are not made unless the core is able
  to transfer at a 100% throughput rate.

  This particular version can only handle bus aligned transfers.  A separate
  version that can handle unaligned transfers is available for purchase.

  *This core has been formally verified.*

- AXISINGLE is a (to be written) core that will also be an
  [AutoFPGA](https://github.com/ZipCPU/autofpga) companion core.  Slave's of
  type "SINGLE" (one register, one clock to generate a response) can be ganged
  together using it.  This core will then essentially turn an AXI core into
  an AXI-lite core, with the same interface as [AXILSINGLE](rtl/axilsingle.v) 
  above.  When implemented, it will look very similar to the [AXIDOUBLE](rtl/axidouble.v)
  core mentioned below.

- [AXIDOUBLE](rtl/axidouble.v) is the second AXI4 (full) companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI4 (full) support.  It's
  purpose is to simplify connectivity logic when supporting multiple AXI4 (full)
  slaves.  This core takes a generic AXI4 (full) interface, and simplifies
  the interface so that peripherals can be connected to it with a minimal amount
  of logic.  These peripherals cores can either be full AXI4 (full) cores in
  their own respect, subject to simplification rules discussed within,
  simplified AXI-lite slave as one might use with
  [AXILDOUBLE](rtl/axildouble.v), or even simpler than that.  Key to this
  simplification is the assumption that the simplified slaves must never stall
  the bus, and that they must always return responses within one clock cycle.
  The [AXIDOUBLE](rtl/axidouble.v) core handles all backpressure issues, ID
  logic, burst logic, address selection, invalid address return and exclusive
  access logic.

  *This core has been formally verified.*

- [AXIXCLK](rtl/axixclk.v) can be used to cross clock domains in an AXI
  context.  As implemented, it is little more than a set of asynchronous FIFOs
  applied to each of the AXI channels.  The asynchronous FIFOs have been
  formally verified,

- [WBSAFETY](rtl/wbsafety.v) is a firewall, very similar to the
  [AXISAFETY](rtl/axisafety.v) firewall above, only for the Wishbone bus.
  Unlike many other firewall implementations, this one is able to reset
  the downstream core following any error.

# Licensing

This repository is licensed under the [Apache 2
license](https://www.apache.org/licenses/LICENSE-2.0.html).

# Thanks

I'd like to thank @wallento for his initial work on a
[Wishbone to AXI converter](https://github.com/wallento/wb2axi), and his
encouragement to improve upon it.  While this isn't a fork of his work, the
initial [pipelined wishbone to AXI bridge](rtl/wbm2axisp.v) which formed
the core seed for this project took its initial motivation from his work.

Many of the rest of these projects have been motivated by the desire to learn
and develop my formal verification skills.  For that, I would thank the staff
of Symbiotic EDA for their tools and their encouragement.
