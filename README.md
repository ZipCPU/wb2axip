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

# AXI to Wishbone conversion

Since the project began, a full-fledged [AXI4 to Wishbone bridge](rtl/axim2wbsp.v) has been added to the project.
This converter handles synchronizing the write channels, turning AXI read/write
requests into pipeline wishbone requests, maintaining the AXI ID fields, etc.
It ignores the AXI xSIZE, xLOCK, xCACHE, xPROT, and xQOS fields.  It supports
xBURST types of FIXED (2'b00) and INCR (2'b01), but not WRAP (2'b10) or
reserved (2'b11).  It does not (yet) support bridging between busses of
different widths, so both the AXI and the WB bus must have the same width.

AXI4 is a complicated protocol, however, especially when
[compared to WB](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html).

_Finally, whereas the [bridge](rtl/axim2wbsp.v) has been written, it has yet
to be significantly tested or formally proven.  If you are interested in
helping to test it, please contact me at (zipcpu (at) gmail.com).  Until
that time, it must be said that the result is subject to change._

# Formal Verification

This particular version of the tools includes an initial attempt at
formally proving that the core(s) work.

Currently, the project contains formal specifications for
[Avalon](bench/formal/fav_slave.v), [Wishbone](bench/formal/fwb_slave.v), and
[AXI](bench/formal/faxi_slave.v) busses.  Components with working proofs
include the [WB to AXI](rtl/wbm2axisp.v) bridge as well as the
[WB arbiter](rtl/wbarbiter.v) needed for the [AXI to WB](rtl/axim2wbsp.v).
I also have a working proof for an Avalon to WB bridge that isn't posted
here.

The [AXI4 to Wishbone bridge](rtl/axim2wbsp.v) remains a work in progress
that isn't getting a lot of attention.

# Commercial Applications

Should you find the GPLv3 license insufficient for your needs, other licenses
can be purchased from Gisselquist Technology, LLc.

# Thanks

I'd like to thank @wallento for his initial work on a
[Wishbone to AXI converter](https://github.com/wallento/wb2axi), and his
encouragement to improve upon it.  While this isn't a fork of his work, it
takes its motivation from his work.
