BlueCheck
=========

(Inspired by the QuickCheck tool for testing Haskell programs.)

BlueCheck is a *generic* test-bench written in the Bluespec HDL.  It
is generic in the sense that it can be used to test *any* design.

To use it, the developer simply provides a specification of
correctness: a set of properties, written in Bluespec, about the
design under test.

BlueCheck then automatically tests these properties, reporting any
counter-examples found.

It's main features are:

  * *Automatic test-sequence generation*, with support for definining
    custom generators when the default one doesn't suffice.

  * *Iterative-deepening*: the lengths of test-sequences are increased
    gradually over time with aim of finding simple failures first.

  * *Shrinking*: once a failing test-sequence is found, BlueCheck tries
    to make it shorter by repeatedly ommitting possibly-unneeded
    elements.  This helps find simple failures quickly.

  * *Fully synthesisable*: it can run on FPGA as well as in simulation,
    allowing thorough testing.  Counter-examples found on FPGA are
    automatically trasferred to a host PC to be viewed or replayed
    in simulation.

  * *Ease of use*: rigourous HDL-level test frameworks can be
    constructed by writing a very small amount of code.

A good place to start learning about BlueCheck is [this
report](https://github.com/CTSRD-CHERI/bluecheck/raw/master/bluecheck.pdf)
(Copyright IEEE).
Also, take a look at the examples in
[SimpleExamples.bsv](SimpleExamples.bsv) and
[StackExample.bsv](StackExample.bsv).  These can be built using
[make.sh](make.sh).

Acknowlegements
---------------

BlueCheck is inspired by the influential QuickCheck tool by Koen
Claessen and John Hughes.

For numerous vital suggestions, thanks to Alex Horsman, Alexandre
Joannou, Theo Markettos, Simon Moore, Peter Sewell, Robert Watson, and
Jon Woodruff.
