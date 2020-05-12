This repository contains three types of bench testing information.

1. [Formal scripts and properties](formal) for the use in formal proofs using
   SymbiYosys.  To be complete, each formal script will produce a full proof
   (with induction), together with a series of cover traces demonstrating
   all of what the design should/could do, and at high speed.  You can find
   many of these cover results posted in the [../doc](../doc/gfx) directory.

2. [CPP scripts](cpp) for use with Verilator.  These aren't very well developed,
   and were not used to verify anything here.

3. [MCY information](mcy).  [MCY](https://github.com/YosysHQ/mcy) is a new
   program built by SymbioticEDA for the purpose of testing whether or not
   a test bench is sufficient for determining if a design truly works.  My
   [mcy directory](mcy) contains my attempts and efforts at using this program.
