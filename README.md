# WB2AXIP: Bus interconnects, bridges, and other components

The bus components and bridges within this repository are unique in that they
are all designed for 100% throughput with no throughput overhead.  They are also
unique in that the vast majority of the cores within have all been formally
verified.

Where the protocol allows it, such as with [AXI4](https://zipcpu.com/blog/2019/05/29/demoaxi.html),
[AXI-lite](https://zipcpu.com/formal/2018/12/28/axilite.html), and [Wishbone B4
pipelined](https://zipcpu.com/zipcpu/2017/11/07/wb-formal.html), multiple transactions
may be in flight at a time so that protocol handling doesn't stall the bus.

This is [uncommon among AXI4 implementations](https://zipcpu.com/formal/2019/05/13/axifull.html) and almost unheard of in the example AXI-lite implementations I have examined.

Most AXI4 implementations will process a single burst transaction packet at
a time and require some overhead to make this happen.  Xilinx's AXI-lite
implementations, both interconnect and [slave implementations](https://zipcpu.com/formal/2018/12/28/axilite.html), only handle one
request at a time.  Other buses, such as Wishbone Classic, AHB, or APB, will
only ever process one transaction word at a time.

If you are coming from AXI4, AXI-lite, or any one of these other bus
implementations to the AXI4 or even AXI-lite components supported here, then
you should expect to see a throughput increase by using one (or more) of the
cores listed here--given of course that you have a bus master capable of
issuing multiple requests at a time.

This performance improvement may be as significant as a [16x speedup when
toggling an I/O](https://zipcpu.com/zipcpu/2019/02/09/cpu-blinky.html), a 4x
speedup when comparing [this slave](rtl/demofull.v) against [Xilinx's block
RAM memory controller (when processing single beat transactions)](https://zipcpu.com/blog/2020/03/23/wbm2axisp.html), or as
insignificant as 2% improvement from using the AXI4 MM to Slave converters
(according to Xilinx's data sheets---I haven't yet run the test myself).  This
increased performance extends to the [crossbar implementations](https://zipcpu.com/blog/2019/07/17/crossbar.html) contained within
this repository as well, and so you may notice the improvement only increases
when using [these crossbars](https://zipcpu.com/blog/2019/07/17/crossbar.html).

# A Pipelined Wishbone B4 to AXI4 bridge

Built out of necessity, this repository was originally built around [a Wishbone
(WB) to AXI4 bridge](https://zipcpu.com/blog/2020/03/23/wbm2axisp.html),
which is designed to provide a conversion from a (simpler) [pipelined wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI4 bus for the
purposes of driving memory transactions through Xilinx's SDRAM controllers.
[The WB->AXI bridge](rtl/wbm2axisp.v) is designed to connect a [wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI bus which
may be wider--such as from a 32-bit WB bus to a 128-bit AXI bus.  Hence, if
the Memory Interface Generator DDR3 controller is running at a 4:1 clock rate,
memory clocks to AXI system clocks, then this [bus translator](rtl/wbm2axisp.v)
should be able to accomplish one transaction per clock at a sustained
(pipelined) rate (neglecting any stalls due to refresh cycles).

Since the initial build of [the core](rtl/wbm2axisp.v), I've added the
[WB to AXI lite](rtl/wbm2axilite.v) bridge.  This is also a pipelined bridge,
and like the original one it has also been formally verified.

# AXI to Wishbone conversion

While not the original purpose of the project, it now has both [AXI-lite to
WB](rtl/axlite2wbsp.v) and [AXI to WB](rtl/axim2wbsp.v) bridges.  Each of these
bridges comes in two parts, a read and write half.  These halves can be used
either independently, generating separate inputs to a
[WB crossbar](rtl/wbxbar.v), or combined through a [WB
arbiter](rtl/wbarbiter.v).

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

# AXI3 bridging

I'm now in the process of adding AXI3 bridges to this repository.  These
will be necessary for working with the Zynq chips, and others, that are still
using AXI3.  While the work is ongoing, I do have an [AXI3 to
AXI4](rtl/axi32axi.v) bridge available that's undergoing testing.  The bridge
supports two algorithms for `W*` reordering, and should be suitable for most
applications.

# Formal Verification

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone
(classic)](bench/formal/fwbc_slave.v), [Wishbone
(pipelined)](bench/formal/fwb_slave.v),
[APB](bench/formal/fapb_slave.v), and
[AXI-lite](bench/formal/faxil_slave.v) buses.  There's also a (partial) formal
property specification for an [AXI (full) bus](bench/formal/faxi_slave.v), but
the one in the master branch is incomplete.  The complete set of AXI
properties are maintained elsewhere.  These properties, and the cores they've
been used to verify, have all been tested and verified using SymbiYosys.

# Xilinx Cores

The formal properties were first tested on a pair of Xilinx AXI demonstration
cores.  These cores failed formal verification.  You can read about them
on [my blog, at zipcpu.com](https://zipcpu.com), [here for
AXI-lite](http://zipcpu.com/formal/2018/12/28/axilite.html) and
[here for AXI](http://zipcpu.com/formal/2019/05/13/axifull.html).
You can find the Xilinx cores referenced in those articles
[here](bench/formal/xlnxdemo.v) and [here](bench/formal/xlnxfull_2018_3.v) for
reference, for those who wish to repeat or examine my proofs.

# Firewalls

A [firewall](https://zipcpu.com/formal/2020/05/16/firewall.html)
is a guarantor: given an interface, of which only one side is trusted, the
[firewall](https://zipcpu.com/formal/2020/05/16/firewall.html)
guarantees the other side can trust the interface.  More than that, a
[firewall](https://zipcpu.com/formal/2020/05/16/firewall.html) can be used
to trigger an in-circuit logic analyzer: if ever the interface rules are
violated, the [firewall](https://zipcpu.com/formal/2020/05/16/firewall.html)
will set an ouput fault indicator, which can then be used to trigger the logic
analyzer.  On top of that, the
[firewalls](https://zipcpu.com/formal/2020/05/16/firewall.html) below are also
built with an optional reset, allowing the design to safely return to
functionality after triggering.  In many cases, this requires resetting the
downstream (untrusted) component.

- [AXILSAFETY](rtl/axilsafety.v) is a bus fault isolator AXI-lite translator,
  sometimes called a firewall, designed to support a connection to a trusted
  AXI-lite master, and an untrusted AXI-lite slave.  Should the slave attempt
  to return an illegal response, or perhaps a response beyond the user
  parameterized timeouts, then the untrusted slave will be "disconnected" from
  the bus, and a bus error will be returned for both the errant transaction
  and any following.

  [AXILSAFETY](rtl/axisafety.v) also has a mode where, once a fault has been
  detected, the slave is reset and then allowed to return to the bus
  infrastructure again until its next fault.

  *This core has been formally verified.*

- [AXISAFETY](rtl/axisafety.v) is a bus fault isolator/firewall very similar
  to the [AXILSAFETY](rtl/axilsafety.v) bus fault isolator above with many of
  the same options.  The difference is that the [AXISAFETY](rtl/axisafety.v)
  core works with the full AXI4 specification, whereas the
  [AXILSAFETY](rtl/axilsafety.v) core works only with AXI4-lite.

  As with the [AXILSAFETY](rtl/axilsafety.v) example, the [AXISAFETY](rtl/axisafety.v)
  firewall also has a mode where, once a fault has been detected, the slave is
  reset and allowed to return to the bus infrastructure until its next fault.
  Unliike the [AXILSAFETY](rtl/axilsafety.v) example, this one will only ever
  process a single AXI4 burst at a time.

  *This core has been formally verified.*

- [AXISSAFETY](rtl/axissafety.v) is a firewall for the AXI stream protocol.
  It guarantees the stream protocol, and optionally that the incoming stream
  will never be stalled for too long a period or that all packets downstream
  have the same length.

  *This core has been formally verified.*

- [WBSAFETY](rtl/wbsafety.v) is a bus fault isolator/firewall, very similar
  to the [AXILSAFETY](rtl/axilsafety.v) firewall above, only for the Wishbone
  bus.  Unlike many vendor firewall implementations, this one is able to reset
  the downstream core following any error without impacting it's ability to
  respond to the bus in a protocol compliant fashion.

  *This core has been formally verified.*

# Cross-bars and AXI demonstrators

This repository has since become a repository for all kinds of bus-based
odds and ends in addition to the bus translators mentioned above.  Some of
these odds and ends include [crossbar
switches](https://zipcpu.com/blog/2019/07/17/crossbar.html) and AXI
demonstrator cores.  As mentioned above, these cores are unique in their 100%
throughput capabilities.

- [WBXBAR](rtl/wbxbar.v) is a fully function N master to M slave Wishbone
  [crossbar](https://zipcpu.com/blog/2019/07/17/crossbar.html).  Unlike my
  Unlike my [earlier WB interconnects](https://zipcpu.com/blog/2017/06/22/simple-wb-interconnect.html), this one guarantees that the
  ACK responses won't get crossed, and that misbehaving slave accesses will
  be timed out.  The core also has options for checking for starvation
  (where a master's request is not granted in a particular period of time),
  double-buffering all outputs (i.e. with [skid
  buffers](https://zipcpu.com/blog/2019/05/22/skidbuffer.html), and forcing idle
  channel values to zero in order to reduce power.

  *This core has been formally verified and used in several designs.*

- [AXILXBAR](rtl/axilxbar.v) is a fully functional, formally verified, `N`
  master to `M` slave AXI-lite [crossbar interconnect](https://zipcpu.com/blog/2019/07/17/crossbar.html).  As such, it permits
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
  over an extended period of time across any channel pair.  (Their crossbar
  artificially limits AXI-lite interfaces to one transaction at a time.)

- [AXIL2AXIS](rtl/axil2axis.v) [converts from AXI-lite to AXI stream and back
  again](https://zipcpu.com/dsp/2020/04/20/axil2axis.html).  It's primary
  purpose is for testing AXI stream components at low speed, to make certain
  that they work before increasing the speed of the stream to the system clock
  rate.  As such, writes to the core will generate writes to the AXI stream on
  the master side, and reads from the core will accept AXI stream reads on the
  slave side.

  While this isn't really intended to be a high performance core, it can still
  handle 100% throughput like most of my IP here.  Therefore, anything less
  than 100% throughput through this core will be a test of and reflection
  of how the rest of your system works.

  *This core has been formally verified.*

- [AXIEMPTY](rtl/axiempty.v) is a cross bar helper.  It's the simplest, most
  basic slave I could come up with that obeyed all the rules of AXI while
  returning a bus error for every request.  It's designed to be used by the
  interconnect generator for those cases where there are no slaves on a given
  AXI bus.

  *This core has been formally verified.*

- [AXILEMPTY](rtl/axilempty.v) is a cross bar helper along the same lines as
  the [AXIEMPTY](rtl/axiempty.v) core above.  It has an nearly identical
  purpose, save only that [AXILEMPTY](rtl/axilempty.v) is built to be the
  empty slave on an AXI-lite bus, not an AXI one.

  *This core has been formally verified.*

- [AXILSINGLE](rtl/axilsingle.v) is designed to be a companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI-lite support.  It's
  purpose is to [simplify connectivity logic when supporting multiple AXI-lite
  registers](https://zipcpu.com/zipcpu/2019/08/30/subbus.html).  This core
  takes a generic AXI-lite interface, and simplifies the interface so that
  multiple single-register cores can be connected to it at no loss in
  throughput.  The single-register cores can either be full AXI-lite cores in
  their own respect, subject to simplification rules ([listed
  within](rtl/axilsingle.v)), or even further simplified from that.
  They must never stall the bus, and must always return responses within one
  clock cycle.  The [AXILSINGLE](rtl/axilsingle.v) handles all backpressure
  issues.  If done right, the backpressure logic from any downstream slave
  core will be removed by the synthesis tool, allowing all backpressure logic
  to be condensed into a few shared wires.

  *This core has been formally verified.*

- [AXILDOUBLE](rtl/axildouble.v) is the second AXI-lite companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI-lite support.  It's
  purpose is to [simplify connectivity logic when supporting multiple AXI-lite
  slaves](https://zipcpu.com/zipcpu/2019/08/30/subbus.html) while imposing
  no throughput penalty.  This core takes a generic AXI-lite interface, and
  simplifies the interface so that multiple peripherals can be connected to
  it.  These peripheral cores can either be full AXI-lite cores in their own
  respect, subject to simplification rules discussed within, or even simplified 
  from that.  They must never stall the bus, and must always return responses
  within one clock cycle.  The [AXILDOUBLE](rtl/axildouble.v) core handles all
  backpressure issues, address selection, and invalid address returns.

  *This core has been formally verified.*

- [AXIXBAR](rtl/axixbar.v) is a fun project to develop a full `NxM`
  configurable [crossbar](https://zipcpu.com/blog/2019/07/17/crossbar.html)
  using the full AXI protocol.

  Unique to [this (full) AXI crossbar](rtl/axixbar.v) is the ability to have
  multiple ongoing transactions on each of the master-to-slave channels.  Were
  Xilinx's crossbar to do this, it would've broken their [demonstration
  AXI-full slave core](http://zipcpu.com/formal/2019/05/13/axifull.html).

- [DEMOAXI](rtl/demoaxi.v) is a demonstration AXI-lite slave core with more
  power and capability than Xilinx's demonstration AXI-lite slave core.
  Particular differences include 1) this one passes a formal verification check
  ([Xilinx's core has bugs](http://zipcpu.com/formal/2018/12/28/axilite.html)),
  and 2) this one can handle a maximum throughput of one transaction per clock.
  (Theirs did at best one transaction every other clock period.)  You can read
  more about this [demonstration AXI-lite slave core](rtl/demoaxi.v) on
  [ZipCPU.com](http://zipcpu.com) in [this article](http://zipcpu.com/blog/2019/01/12/demoaxilite.html).

  *This core has been formally verified.*

- [AXISSWITCH](rtl/axisswitch.v) is a quick switch for AXI streams.  Given
  `N` stream inputs, select from among them to produce a stream output.
   Guarantees that the switch takes place at packet boundaries.  Provides an
   AXI-lite interface for controlling which AXI stream gets forwarded
   downstream.

  *This core has been formally verified.*

- [EASYAXIL](rtl/easyaxil.v) is a [second demonstration AXI-lite slave core,
  only this time re-engineered to look and feel
  simpler](https://zipcpu.com/blog/2020/03/08/easyaxil.html) than the
  [DEMOAXI](rtl/demoaxi.v) core above.  It's also designed to use internal
  registers, vice a memory, so that it can be more easily extended.  The
  core can either use [skidbuffers](https://zipcpu.com/blog/2019/05/22/skidbuffer.html), in which case its performance matches the
  [DEMOAXI](rtl/demoaxi.v) core above, or not, in which case it has only half
  the throughput.  The real key difference is that the [skid
  buffers](https://zipcpu.com/blog/2019/05/22/skidbuffer.html) have been
  separated into an external module.

  *This core has been formally verified.  While not used in any designs per se
  it has formed the basis for many AXI-lite designs.*

- [DEMOFULL](rtl/demofull.v) is a [fully capable AXI4 demonstration slave
  core](https://zipcpu.com/blog/2019/05/29/demoaxi.html)
  rather than just the AXI-lite protocol.  Well, okay, it doesn't do anything
  with the PROT, QOS, CACHE, and LOCK flags, so perhaps it isn't truly the
  *full* AXI protocol.  Still, it's sufficient for most needs.

  Unlike [Xilinx's demonstration AXI4 slave
  core](http://zipcpu.com/formal/2019/05/13/axifull.html),
  [this one](rtl/demofull.v) can handle 100% loading on both read and write
  channels simultaneously.  That is, it can handle one read and one write beat
  per channel per clock with no stalls between bursts if the environment will
  allow it.

  *This core has been formally verified and used in several designs.*

- [AXI2AXILITE](rtl/axi2axilite.v) converts incoming AXI4 (full) requests
  for an AXI-lite slave.  This conversion is fully pipelined, and capable of
  sending back to back AXI-lite requests on both channels.

  *This core has been formally verified and used in several designs.*

- [AXIS2MM](rtl/axis2mm.v) converts an incoming stream signal into outgoinng
  AXI (full) requests.  Supports bursting and aborted transactions.  Also
  supports writes to a constant address, and continuous writes to concurrent
  addresses.  This core depends upon all stream addresses being aligned.

  *This core has been formally verified and checked in simulation.*

- [AXIMM2S](rtl/aximm2s.v) reads from a given address, and writes it to
  a FIFO buffer and then to an eventual AXI stream.  Read requests are not
  issued unless room already exists in the FIFO, yet for a sufficiently fast
  stream the read requests may maintain 100% bus utilization--but only if
  the rest of the bus does as well.  Supports continuous, fixed address or
  incrementing, and aborted transactions.

  Both this core and the one above it depend upon all stream words being
  aligned to the stream.

  *This core has been both formally verified and checked in simulation.*

- [AXIDMA](rtl/axidma.v) is a hardware assisted memory copy.  Given a source
  address, read address, and length, this core reads from the source address
  into a FIFO, and then writes the data from the FIFO to memory.  As an
  optimization, memory address requests are not made unless the core is able
  to transfer at a 100% throughput rate.

  *This core has been formally verified and used in several designs.*

- [AXISGDMA](rtl/axisgdma.v) is a brand new scatter-gather/vector-io based
  DMA controller.  Give it a pointer to a table of DMA descriptors, and it
  will issue commands to the DMA until the table is complete.

  This core has not yet been verified in any manner, and is likely to still
  contain many bugs within it until that time.  Use it at your own risk.

- [AXIVCAMERA](rtl/axivcamera.v) is a AXI-based frame-buffer writer.  Given
  an AXI-stream video source, a frame start address, the number of lines in the
  image and the number of bytes per line, this core will copy one (or more)
  frames of video to memory.

  *This core has been formally verified, and used successfully in a simulation
  based demonstration.*

- [AXIVDISPLAY](rtl/axivdisplay.v) is a AXI-based frame-buffer source.  Given
  a frame start address in memory, the number of lines in an image and the
  number of bytes per line, this core will perpetually read a video image
  from memory and produce it on an outgoing stream interface.

  This particular version can only handle bus aligned transfers.

  *This core has been formally verified.*

  You can find a demonstration of this core being used in my [VGA
  simulator](https://github.com/ZipCPU/vgasim)--supporting both VGA and HDMI
  outputs.

- AXISINGLE is a (to be written) bus simplifier core along the lines of the
  [AXILSINGLE](rtl/axilsingle.v), [AXILDOUBLE](rtl/axildouble.v) and
  [AXIDOUBLE](rtl/axidouble.v) cores, in that it can [handle all of the bus
  logic for multiple AXI slaves while simplifying the bus
  interactions for each](https://zipcpu.com/zipcpu/2019/08/30/subbus.html)
  but at no throughput penalty.  Once built, this will also be an
  [AutoFPGA](https://github.com/ZipCPU/autofpga) companion core.  Slave's of
  type "SINGLE" (one register, one clock to generate a response) can be ganged
  together using it.  This core will then essentially turn an AXI core into
  an AXI-lite core, with the same interface as [AXILSINGLE](rtl/axilsingle.v) 
  above.  When implemented, it will look very similar to the [AXIDOUBLE](rtl/axidouble.v)
  core mentioned below.

- [AXIDOUBLE](rtl/axidouble.v) is the second AXI4 (full) companion to
  [AutoFPGA](https://github.com/ZipCPU/autofpga)'s AXI4 (full) support.  It's
  purpose is to [simplify connectivity logic when supporting multiple AXI4
  (full) slaves](https://zipcpu.com/zipcpu/2019/08/30/subbus.html).
  This core takes a generic AXI4 (full) interface, and simplifies
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

- [WBXCLK](rtl/wbxclk.v) can be used to cross clock domains on a pipelined
  Wishbone bus.  It's conceptually an asynchronous request FIFO coupled with
  an asynchronous acknowledgment FIFO to cross clock domains.  A counter in
  the original clock domain guarantees that the number of outstanding
  transactions remains smaller than the FIFO size.  The design is complicated
  by the masters ability to arbitrarily lower CYC at any time mid-cycle and
  reliably be able to cancel any outgoing transactions in the downstream
  channel direction.

  *This core has been formally verified.*

- [AXIVFIFO](rtl/axivfifo.v) implements a virtual FIFO.  A virtual FIFO is
  basically a memory backed FIFO.  Hence, after data gets written to this
  core it is then burst across an AXI bus to the whatever memory device is
  connected to the bus.  This allows you to build FIFOs of arbitrarily large
  length for ... whatever task.

  *This core has been formally verified.*

- [AXIXCLK](rtl/axixclk.v) can be used to cross clock domains in an AXI
  context.  As implemented, it is little more than a set of asynchronous FIFOs
  applied to each of the AXI channels.  The asynchronous FIFOs have been
  formally verified,

- [AXISRANDOM](rtl/axisrandom.v) is a quick AXI stream source generating random
  numbers via a linear feedback shift register.

# APB

There are now two APB cores in this repository:

- [APBSLAVE](rtl/apbslave.v) is a demonstration APB slave.

  *This core has been formally verified.*

- [AXIL2APB](rtl/axil2apb.v) -- a high throughput AXI-lite to APB bridge.
  Unlike other bridges, this one bridges to a single APB slave only.  It can
  also maintain PSEL high across multiple bursts, achieving a maximum
  throughput rate of 50%.

  *This core has been formally verified.*


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
