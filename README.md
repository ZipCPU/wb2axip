# WB2AXIP: A Pipelind Wishbone B4 to AXI4 bridge

Built out of necessity, [this core](rtl/wbm2axisp.v) is designed to provide
a conversion from a [wishbone
bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html) to an AXI bus.
Primarily, the core is designed to connect a
[wishbone bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html),
either 32- or 128-bits wide, to a 128-bit wide AXI bus, which is the natural
width of a DDR3 transaction (with 16-bit lanes).  Hence, if the
Memory Interface Generator DDR3 controller is running at a 4:1 clock rate,
memory clocks to AXI system clocks, then it should be possible to accomplish
one transaction clock at a sustained or pipelined rate.  This
[bus translator](rtl/wbm2axisp.v) is designed to be able to handle one
transaction per clock (pipelined), although [(due to Xilinx's MIG design)
the delay may be up to 27 clocks](http://opencores.org/project,wbddr3).  (Ouch!)

Since the initial build of the core, I've added the
[WB to AXI lite](rtl/wbm2axilite.v) bridge.  This is also a pipelined bridge,
and like the original one it is also formally verified.

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
between busses of different widths.  The only problem is ...
this full AXI4 to WB converter _doesn't work_ (yet).  I know this because it
doesn't yet pass formal verification.

# Formal Verification

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone](bench/formal/fwb_slave.v), and
[AXI](bench/formal/faxi_slave.v) busses.

# Commercial Applications

Should you find the GPLv3 license insufficient for your needs, other licenses
can be purchased from Gisselquist Technology, LLc.

# Thanks

I'd like to thank @wallento for his initial work on a
[Wishbone to AXI converter](https://github.com/wallento/wb2axi), and his
encouragement to improve upon it.  While this isn't a fork of his work, the
[pipelined wishbone to AXI bridge](rtl/wbm2axisp.v) took its initial
motivation from his work.
