## Demo designs

- [Demonstration AXI4-lite slave](demoaxi.v)
- [Demonstration APB slave](apbslave.v)
- [Demonstration AXI4(Full) slave](demofull.v)
  -- [AXI Addr](axi_addr.v) is a helper core used for calculating the "next" address in a burst sequence.  It's based upon [the algorithm discussed here](https://zipcpu.com/blog/2019/04/27/axi-addr.html).
- [A simplified AXI-lite slave](easyaxil.v)
- [A basic AXI-lite GPIO controller](axilgpio.v)

- [Skidbuffer](skidbuffer.v)

## Demo AXI-stream designs

- [AXIS Broadcast](axisbroadcast.v): Accepts one stream input, duplicates that
	stream to an arbitrary number of output streams
- [AXISPACKER](axispacker.v): Removes NULL bytes from an AXI Stream
- [AXISRANDOM](axisrandom.v): Generates a pseudorandom AXI-Stream output
- [AXISSWITCH](axisswitch.v): Switches a stream from among many input streams,
	with an AXI-lite control input for switching between them.

## Crossbars

See [this post for a discussion of these
crossbars](https://zipcpu.com/blog/2019/07/17/crossbars.html).

- [AXI4](axixbar.v)
- [AXI4-Lite](axilxbar.v)
- [Wishbone](wbxbar.v)

These cores rely not only on the [skidbuffer](skidbuffer.v) listed above, but
also upon a separate [address decoder](addrdecode.v) that is common to all of
them.

All three cores are supported by the (dev branch of)
[AutoFPGA](https://github.com/ZipCPU/autofpga).

## Data movers/DMA engines

- [AXIMM2S](aximm2s.v).  Supports unaligned transfers, but only fully aligned
  stream words.
- [AXIS2MM](axis2mm.v).  Doesn't yet support unaligned transfers.  It may
  eventually, but it will also only ever support full word transfers
  through the stream.
- [AXIDMA](axidma.v).  Supports unaligned transfers.
- [AXISGDMA](axisgdma.v).  A scatter-gather DMA implementation.  Performs DMA
  operations based upon an external, bus-fetched, table containing the details
  of multiple DMA operations to be done.
  -- [AXILFETCH](axilfetch.v)--A ZipCPU instruction fetch module required by the Scatter-Gather engine to fetch tables from memory.
  -- [AXISGFSM](axisgfsm.v)--The FSM that reads instructions (i.e. table entries) from the fetch routine, and issues instructions to the [AXIDMA](axidma.v).
- [AXIVFIFO](axivfifo.v).  A virtual FIFO, using an external AXI device for
  memory backing--perhaps even an SDRAM.  It doesn't really matter--it just
  needs to be AXI.
- [AXIVCAMERA](axivcamera.v).  Writes a video stream to a memory frame buffer.
- [AXIVDISPLAY](axivdisplay.v).  Reads a frame buffer from memory to generate
  a continuous AXI-stream video source output.

- [Synchronous FIFO](sfifo.v)
- [Synchronous FIFO with threshold](sfifothresh.v)

## Bus Bridges

- [AXI to AXI-lite](axi2axilite.v).  Supports 100% throughput even across burst
  boundaries, unlike other (similar) bridges of this type you might come across.

- [AXI-lite to AXI](axilite2axi.v).  A "no-cost" bridge.

- [AXI-lite to AXI stream](axil2axis.v)

- [AXI-Lite to Wishbone](axlite2wbsp.v)

  -- [Read side](axilrd2wbsp.v)

  -- [Write side](axilwr2wbsp.v)

  -- A following (optional) [arbiter](wbarbiter.v) will connect read and write sides together into the same WB bus.  Alternatively, each of the two sides can be submitted separately into a [WB Crossbar](wbxbar.v).

- [AXI-Lite to APB](axil2apb.v)

- [AXI4 Master to Wishbone](axim2wbsp.v)

  -- [Read side](aximrd2wbsp.v)

  -- [AXI4 Master to Wishbone](aximwr2wbsp.v)

- [Wishbone classic to pipelined](wbc2pipeline.v)

- [Wishbone pipelined to classic](wbp2classic.v)

- [Wishbone master to AXI4-Litejk slave](wbm2axilite.v)

- [Wishbone master to AXI4 slave](wbm2axisp.v)

  This core, together with its sister core, [migsdram](migsdram.v), form the
  basis for my approach to accessing DDR3 SDRAM memory through an AXI
  interface using Xilinx's MIG controller.  Other than the lag in going
  through the bridge, this solution works quite well--achieving full (nearly
  100%) bus throughput when loaded.

- [AXI3 to AXI4](axi32axi.v).  See the internal documentation of the
  [AXI3 write deinterleaver](axi3reorder.v) for the details of the write
  deinterleaving algorithm.

- The AXI4 to AXI3 bridge is still missing.
  This will be more difficult than its [AXI3 to AXI4 sister](axi32axi.v) above,
  since it will need to break apart large AXI4 burst requests into smaller AXI3
  bursts, sort of like the [AXI4 to AXI4-lite bridge](axi2axilite.v) does.

## AXI Simplifiers

These follow from the discussion in [this article about how to simplify
a bus interconnect](https://zipcpu.com/zipcpu/2019/08/30/subbus.html) into
something allowing easier integration of multiple slaves into a design.  They
work by aggregating the signaling logic across many slaves together.  See the
headers for each of the cores for the specifics of the standard subsets
they support.

- AXI Single, the companion to the [AXI Double](axidouble.v) core has not yet
  been written.  The design for it should be nearly identical.  The big
  difference between single and double AXI slaves is that single slaves can have
  only one address, and that address must always be available for reading.

- [AXI Double](axidouble.v).

- [AXI-Lite Single](axilsingle.v)

- [AXI-Lite Double](axildouble.v)

## Firewalls

The goal of these firewall(s) is to create a core that, when placed between the
bus master and slave, will guarantee that the slave responds appropriately to
the bus master---even in the presence of a broken slave.  If the slave is
broken, the firewall will raise a flag that can then be used to trigger a
logic analyzer of some type so you can dig deeper into what's going on.

As a bonus, the firewall may also have the capability of resetting the
downstream core upon any error, so that it might be reintegrated later into
the rest of the design for additional testing.

- [AXI-lite](axilsafety.v)

- [AXI4](axisafety.v)

- [AXI-stream](axissafety.v)

- [Wishbone](wbsafety.v)

## Performance Measurement

- [AXIPERF](axiperf.v) -- Useful for measuring Latency and Throughput in an
AXI bus.  Has an AXI-lite interface, and an AXI4 monitor interface.  Monitors
the AXI4 bus, and measures key performance statistics.  Statistics may be read
and cleared via the AXI-lite interface.

## Empty slaves

These are used to simplify interconnect generation.  When there are no slaves
connected to an interconnect, the interconnect generator can automatically
connect one of these slaves (depending on the protocol) and be guaranteed
that the protocol will still be followed.  All requests, however, will return
bus errors.

- [AXIEMPTY](axiempty.v) - the AXI4 empty slave

- [AXILEMPTY](axilempty.v) - the AXI4-lite empty slave

## Clock domain crossing bridges

- [Wishbone cross-clock domains](wbxclk.v)

- [AXI4 cross-clock domains](axixclk.v)

- [APB cross-clock domains](apbxclk.v)

- [Asynchronous FIFO](afifo.v) -- support function
