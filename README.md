# WB2AXIP: A Pipelind Wishbone B4 to AXI4 bridge

Built out of necessity, this core is designed to provide a conversion from a 
wishbone bus to an AXI bus.  Primarily, the core is designed to connect a 
wishbone bus, either 32- or 128-bits wide, to a 128-bit wide AXI bus, which is
the natural width of a DDR3 transaction (with 16-bit lanes).  Hence, if the
Memory Interface Generator DDR3 controller is running at a 4:1 clock rate,
memory clocks to AXI system clocks, then it should be possible to accomplish
one transaction clock at a sustained or pipelined rate.  This bus translator
is designed to be able to handle one transaction per clock (pipelined),
although (due to Xilinx's design) the delay may be up to 27 clocks.  (Ouch!)

# AXI to Wishbone conversion

Since the project began, a full-fledged AXI4 to Wishbone bridge has been 
added to the project.  Check out the core
[here](https:wb2axip/blob/master/rtl/axim2wbsp.v).
This converter handles synchronizing the write channels, turning AXI read/write
requests into pipeline wishbone requests, maintaining the AXI ID fields, etc.
It ignores the AXI xSIZE, xLOCK, xCACHE, xPROT, and xQOS fields.  It supports
xBURST types of FIXED (2'b00) and INCR (2'b01), but not WRAP (2'b10) or
reserved (2'b11).  It does not (yet) support bridging between busses of
different widths, so both the AXI and the WB bus must have the same width.

AXI4 is a complicated protocol, however, especially when compared to WB.

_Finally, whereas the bridge has been written, it has yet to be significantly
tested.  If you are interested in helping to test it, please contact me at
(dgisselq (at) yahoo.com).  Until that time, it must be said that the result
is subject to change._

# Thanks

I'd like to thank @wallento for his initial work on a Wishbone to AXI converter (https://github.com/wallento/wb2axi), and his encouragement to improve upon it.  While this isn't a fork of his work, it takes its motivation from his work.
