BlueCheck
=========

BlueCheck is a generic test-bench written in the Bluespec HDL.  It is
generic in the sense that it can be used to test any design.

To use it, the developer simply provides specification of correctness:
a set of properties, written in Bluespec, about the design under test.

BlueCheck then automatically tests these properties, reporting any
counter-examples found.

It's main features are:

  * Automatic test-sequence generation, with support for definining
    custom generators when the default one doesn't suffice.

  * Iterative-deepening: the length of test-sequences are increased
    gradually over time with aim of finding simple failures first.

  * Shrinking: once a failing test-sequence is found, we try to make
    it smaller by ommitting possibly-unneeded elements.  This helps
    find simple failures quickly.

  * Fully synthesisable: it can run on FPGA as well as in simulation,
    allowing thorough testing.  Counter-examples found on FPGA can be
    trasferred to a host PC to be viewed or replayed in simulation.

  * Ease of use: rigourous test frameworks can be constructed by
    writing a very small amount of code.

Technical documentation will appear here shortly.  For now, take a
look at the examples in SimpleExamples.bsv and StackExample.bsv.
