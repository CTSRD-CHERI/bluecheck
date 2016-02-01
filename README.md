BlueCheck
=========

(Inspired by the QuickCheck tool for testing Haskell programs.)

BlueCheck is a *generic* test-bench written in the Bluespec HDL.  It
is generic in the sense that it can be applied to *any* Bluespec module.

To use it, the developer simply provides a specification of
correctness: a set of properties, written in Bluespec, about the
module under test.

BlueCheck then automatically tests these properties, reporting any
counter-examples found.

It's main features are:

  * *Automatic test-sequence generation*, with support for defining
    custom generators when the default one doesn't suffice.

  * *Iterative-deepening*: the lengths of test-sequences are increased
    gradually over time with aim of finding simple failures first.

  * *Shrinking*: once a failing test-sequence is found, BlueCheck tries
    to make it shorter by repeatedly omitting possibly-unneeded
    elements.  This helps find simple failures quickly.

  * *Fully synthesisable*: it can run on FPGA as well as in simulation,
    allowing thorough testing.  Counter-examples found on FPGA are
    automatically transferred to a host PC to be viewed or replayed
    in simulation.

  * *Ease of use*: rigorous HDL-level test frameworks can be
    constructed by writing a very small amount of code.

There is various documentation about BlueCheck:

* MEMOCODE 2015 paper, Copyright IEEE: [pdf](https://github.com/CTSRD-CHERI/bluecheck/raw/master/bluecheck.pdf);

* MEMOCODE 2015 slides: [pdf](https://github.com/CTSRD-CHERI/bluecheck/raw/master/slides.pdf);

* Examples in
[SimpleExamples.bsv](SimpleExamples.bsv) and
[StackExample.bsv](StackExample.bsv): these can be built using
[make.sh](make.sh);

* Frequently Asked Questions: [pdf](https://github.com/CTSRD-CHERI/bluecheck/raw/master/FAQ.pdf)

Acknowledgements
---------------

BlueCheck is inspired by QuickCheck by Koen Claessen and John Hughes.

For helpful suggestions, thanks to Nirav Dave, Alex Horsman, Alexandre
Joannou, Theo Markettos, Simon Moore, Peter Sewell, Robert Watson, Jon
Woodruff, and Andy Wright.

For code contributions, thanks to Nirav Dave and Andy Wright.
