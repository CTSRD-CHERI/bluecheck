================================================================
BlueCheck: A library for specification-based testing in Bluespec
Matthew N, 4 Oct 2012
Updated 5 Nov 2012
Updated 6 Dec 2014
================================================================

BlueCheck is a library supporting specification-based testing in
Bluespec, inspired by Haskell's QuickCheck [1].

Scenario
========

I developed a block RAM based stack module in Bluespec with the
following interface.

  /* A stack with a capacity of 2^n elements of type a */
  interface Stack#(numeric type n, type a);
    method Action push(a x);
    method Action pop;
    method a top;
    method Bool isEmpty;
    method Action clear;
  endinterface

My implementation (46 lines) can be found in Appendix A.

But is it correct?  And if so, what is a convincing way to demonstrate it?

Option 1: Unit testing
======================

Initially I used the StmtFSM and Assert packages to make a simple unit
test.

  seq
    stk.push(1);
    stk.push(2);
    dynamicAssert(stk.top == 2, "Failed check 1");
    stk.pop;
    dynamicAssert(stk.top == 1, "Failed check 2");
    $display("Testing completed successfully.");
  endseq

A successfull run of this test is reassuring, but I need more unit
tests to be sure. Do I have to write them all out by hand?  And what
if I forget a corner case?

Option 2: Model-based testing
=============================

A second implementation (31 lines) of the stack module can be found in
Appendix B.  It's much simpler than the first, using registers instead
of a block RAM to store the elements.  It's hard to see anything that
could be wrong with it.  Unlike the first, it contains no assumptions
about the RAM access protocol.  This second implementation could be
viewed as an "executable specification" or a "reference
implementation".

Now testing is a case of showing that the two modules behave
identically.  How can I test that property in Bluespec?

Using BlueCheck I write:

  module [BlueCheck] checkBRAMStack ();
    /* Implementation instance (Appendix A) */
    Stack#(8, UInt#(8)) imp <- mkBRAMStack();

    /* Specification instance (Appendix B) */
    Stack#(8, UInt#(8)) spec <- mkStackSpec();

    equiv("pop"    , spec.pop    , imp.pop);
    equiv("push"   , spec.push   , imp.push);
    equiv("isEmpty", spec.isEmpty, imp.isEmpty);
    equiv("top"    , spec.top    , imp.top);
  endmodule

This is a BlueCheck module, signified by the "[BlueCheck]" qualifier
after the "module" keyword.  Like a normal Bluespec module, it may
instantiate other modules and contain rules.  But it may also contain
equivalence declarations, specified by the "equiv" function.  To make
a synthesisable test bench out of a BlueCheck module, we write:

  module mkTestBRAMStack ();
    blueCheck(checkBRAMStack);
  endmodule

BlueCheck will generate hardware to invoke random sequences of methods
applied to random arguments, and will raise an error if the
implementation ever differs from the spec.  For a taste of what's
required without BlueCheck, see Appendix C.

Running the test bench
======================

What happens when I run it?

  4: push('h4)
  6: pop
  9: push('h3)
  10: push('h9)
  11: push('h6)
  12: push('hd)
  13: pop
  14: pop
  15: top failed: 'h9 v 'h6
  15: push('h5)
  FAILED: counter-example found.

A bug! BlueCheck says that, after executing the above sequence of
methods at the given times, the top stack element should be 9
(according to the spec) but it is actually 6 (according to the
implementation).  In Appendix A, the line

  ram.put(False, sp-1, ?);

should be

  ram.put(False, sp-2, ?);

The above counter-example is not minimal, i.e. there exists a shorter
sequence of instructions that reveals the bug.  BlueCheck has a
feature called shrinking that allows smaller counter-examples to
produced from larger ones.  This is discussed below.

Thorough testing
================

BlueCheck testbenches are synthesisable.  They may invoke one method
per clock cycle (if the methods allow it) so can in principle check
hundreds of millions of method calls per second in a design clocking
at 100Mhz.

Type classes
============

To use BlueCheck, the type of any argument or result of a method
passed to equiv must be an instance of the following type classes.

  Bits, Eq, Bounded, FShow

Easily done.  Just write

  deriving (Bits, Eq, Bounded, FShow);

after your data type declarations.

BlueCheck needs Eq to check for equivalence; Bits and Bounded to
generate random values; and FShow to display them.

Method frequencies
==================

Notice that the BlueCheck code above does not test the "clear" method.
In fact, if "clear" is added to the test then the chances of finding
the above bug are somewhat reduced.  The problem is that "clear" is
invoked with equal probability to "push", so only stacks consisting of
1 or 2 elements are likely to be constructed.

BlueCheck therefore allows the probability of invoking each method to
be controlled using the "equivf" function.

  module [BlueCheck] checkBRAMStack ();
    /* Implementation instance (Appendix A) */
    Stack#(8, UInt#(8)) imp <- mkBRAMStack();

    /* Specification instance (Appendix B) */
    Stack#(8, UInt#(8)) spec <- mkStackSpec();

    equivf(2, "pop"    , spec.pop    , imp.pop);
    equivf(4, "push"   , spec.push   , imp.push);
    equiv(    "isEmpty", spec.isEmpty, imp.isEmpty);
    equiv(    "top"    , spec.top    , imp.top);
    equiv(    "clear"  , spec.clear  , imp.clear);
  endmodule

Here "push" has a frequency of 4, "pop" of 2, and "clear" of 1 (the
default frequency is 1).  This means that, on average, "push" will be
invoked twice as often as "pop" and "pop" twice as often as "clear".
Pure methods such as "isEmpty" and "top" are invoked and checked on
every step.

Option 3: Algebraic testing
===========================

Unlike model-based specification, algebraic specification does not
require a reference implementation.  Instead we specify correctness by
giving equations between code fragments involving the module methods.
For example, here are four equivalences that should hold for any stack
"s", where ";" is to be interpreted as sequential composition.

  s.clear ; v <= s.isEmpty     =   s.clear ; v = True

  s.push(x) ; v <= s.isEmpty   =   s.push(x) ; v = False

  s.push(x) ; s.pop            =   /* No-op */

  s.push(x) ; v <= s.top       =   s.push(x) ; v = x

This specification is complete in the sense that it defines the
behaviour of every sequence of stack operations (provided the sequence
contains a single "clear" as the first operation).  Using the
equations as left-to-right rewrite rules, any such sequence of stack
operations can be transformed to a normal form consisting of a clear
operation followed by any number of pushes followed by any number of
variable bindings.

  s.clear;
  s.push(x1);
  ...
  s.push(xm);
  v1 = y1;
  ...
  vn = yn

In other words, the equations can be used to deduce exactly the items
on the stack after execution, along with the results of all stack
queries.

We can formulate these properties in BlueCheck as follows.

  module [BlueCheck] checkBRAMStack ();
    /* Make two stack instances */
    Stack#(8, UInt#(8)) s1 <- mkBRAMStack();
    Stack#(8, UInt#(8)) s2 <- mkBRAMStack();

    /* This function allows us to make assertions in the properties */
    Ensure ensure <- getEnsure;

    Stmt prop1 =
      seq
        s1.clear;               s2.clear;
        ensure(s1.isEmpty);
      endseq;

    function Stmt prop2(UInt#(8) x) =
      seq
        s1.push(x);             s2.push(x);
        ensure(!s1.isEmpty);
      endseq;

    function Stmt prop3(UInt#(8) x) =
      seq
        s1.push(x);
        s1.pop;
      endseq;

    function Stmt prop4(UInt#(8) x) =
      seq
        s1.push(x);          s2.push(x);
        ensure(s1.top == x);
      endseq;

    /* Properties */
    prop("prop1", prop1);
    prop("prop2", prop2);
    prop("prop3", prop3);
    prop("prop4", prop4);

    /* Equivalences */
    equiv("pop"    , s1.pop    , s2.pop);
    equiv("push"   , s1.push   , s2.push);
    equiv("isEmpty", s1.isEmpty, s2.isEmpty);
    equiv("top"    , s1.top    , s2.top);
  endmodule

Note that properties are just functions whose arguments represent
universally quantified variables.

Running the test bench
======================

What happens when I test the algebraic specification?

  3: prop2( 93)
  8: prop4( 65)
  13: prop4( 24)
  18: prop1
  23: prop3(100)
  27: prop4( 36)
  32: prop4(186)
  37: prop1
  42: prop2( 59)
  47: prop1
  52: prop4(163)
  57: prop4(236)
  62: push( 52)
  63: prop3(246)
  68: push( 37)
  70: prop3( 87)
  74: prop4(250)
  79: prop3(124)
  85: prop3(218)
  90: pop
  91: top failed: 250 v  37
  91: pop
  FAILED: counter-example found.

We find the bug, again.

Shrinking
=========

BlueCheck supports a feature known as 'shrinking' whereby
counter-examples consisting of long sequences of method/property
invocations can be reduced in size while still revealing a bug.
Shrinking is not enabled by default because it requires an extra piece
of information from the programmer, namely a reset signal that when
asserted resets all modules under test (excluding, of course, the
BlueCheck module itself).

Stack example revisited
=======================

To support shrinking, the equivalance checker is now written as
follows:

  module [BlueCheck] checkBRAMStack (Reset r);
    /* Implementation instance (Appendix A) */
    Stack#(8, UInt#(8)) imp <- mkBRAMStack(reset_by r);

    /* Specification instance (Appendix B) */
    Stack#(8, UInt#(8)) spec <- mkStackSpec(reset_by r);

    equiv("pop"    , spec.pop    , imp.pop);
    equiv("push"   , spec.push   , imp.push);
    equiv("isEmpty", spec.isEmpty, imp.isEmpty);
    equiv("top"    , spec.top    , imp.top);
  endmodule

The only difference is the addtional reset parameter "Reset r" and the
two "reset_by r" arguments passed to each module under test.

To make a synthesisable test bench, we now write:

  module mkTestBRAMStack ();
    Clock clk <- exposeCurrentClock;
    MakeResetIfc r <- mkReset(0, True, clk);
    blueCheckID(checkBRAMStack(r.new_rst), r);
  endmodule

Running the test bench now gives a smaller counter-example:

  === Depth 20, Test 1/10000 ===
  6: push('h9)
  7: push('h6)
  8: push('hd)
  9: pop
  10: pop
  11: top failed: 'h9 v 'h6
  Saving counter-example to 'CounterExample.bin'
  Continue searching?
  Press ENTER to continue or Ctrl-D to stop: 

Notice that the above counter-example has been saved to a file during
simulation.  (In future we hope to send it over the UART when running
on FPGA.)

Replaying counter-examples
==========================

We can replay the counter-example in isolation (perhaps with debugging
enabled) by passing "+replay" as an argument the generated BlueSim
executable.

  # testStackID +replay
  Loading counter-example from 'CounterExample.bin'
  6: push('h9)
  7: push('h6)
  8: push('hd)
  9: pop
  10: pop
  11: top failed: 'h9 v 'h6

Iterative deepening
===================

When supplied with a reset signal, BlueCheck operates in 'iterative
deepening' mode whereby it generates lots of short test sequences,
gradually increasting the depth (i.e. the size of these sequences).
In the above example, BlueCheck started at depth 20 and found a
counter-example (of length no larger than 20) and shrunk it to a
counter example of length 6.  In 'iterative deepening' mode, the user
has the option to continue testing with the possibility of finding a
simpler counter-example.

Future work
===========

If a method can fire in either the specification OR the implementation
(but not both) then a problem can never be reported.

Currently, the generated testbench will not explore the possibility of
different methods being invoked in parallel.

Exploring exhaustive testing as an alternative to random testing is
also a possibility for future work.

Acknowledgements
================

Thanks to Alex Horsman for showing me Bluespec's ModuleCollect
library, used in the implmentation of BlueCheck.

Appendix A: Implementation
==========================

/* A stack with a capacity of 2^n elements of type a */
module mkBRAMStack (Stack#(n, a))
         provisos(Bits#(a, b));

  /* Create the block RAM */
  BRAM_PORT#(UInt#(n), a) ram <- mkBRAMCore1(2**valueOf(n), False);

  /* Create the stack pointer */
  Reg#(UInt#(n)) sp <- mkReg(0);

  /* The top stack element is stored in a register */
  Reg#(a) topReg <- mkRegU;

  method Action push(a x);
    /* Update top of stack */
    topReg <= x;

    /* Push the old top of stack to block RAM and speculate next pop */
    ram.put(True, sp, topReg);

    /* Increment stack pointer */
    sp <= sp+1;
  endmethod

  method Action pop if (sp > 0);
    /* Update top of stack */
    topReg <= ram.read;

    /* Speculate that another pop is coming soon */
    ram.put(False, sp-1, ?);

    /* Decrement stack pointer */
    sp <= sp-1;
  endmethod

  method a top if (sp > 0);
    return topReg;
  endmethod

  method Bool isEmpty;
    return (sp == 0);
  endmethod

  method Action clear;
    sp <= 0;
  endmethod
endmodule: mkBRAMStack

Appendix B: Specification
=========================

/* A stack with a capacity of 2^n elements of type a */
module mkStackSpec (Stack#(n, a))
         provisos(Bits#(a, b), Add#(1, m, TExp#(n)));

  /* Represent the stack with a vector of size n */
  Reg#(Vector#(TExp#(n), a)) stk <- mkReg(newVector());

  /* Needed to keep track of emptiness */
  Reg#(UInt#(n)) size <- mkReg(0);

  method Action push(a x);
    size <= size+1;
    stk <= cons(x, init(stk));
  endmethod

  method Action pop if (size > 0);
    size <= size-1;
    stk <= append(tail(stk), cons(?, nil));
  endmethod

  method a top if (size > 0);
    return head(stk);
  endmethod

  method Bool isEmpty;
    return (size==0);
  endmethod

  method Action clear;
    size <= 0;
  endmethod
endmodule

Appedix C: Equivalence checking without BlueCheck
=================================================

Without BlueCheck, my solution was to create a state machine where
there is one state for each module method (plus an extra state for a
no-op).

  typedef enum { Pop, Push, Top, IsEmpty, Clear, Nop } State
    deriving (Bits, Eq, Bounded);

The idea is that in a state (say Push) the method (push) associated
with that state is called with random arguments in both the
specification and the implementation.  The state machine can make
random transitions, and look for any observable difference in
behaviour.

Here's how I do it.  In a new testbench module, I instantiate the
implementation and the spec, along with some random generators:

  /* Current state */
  Reg#(State) state <- mkReg(Nop);

  /* Implementation: 2^8 element stack of 6-bit integers */
  Stack#(8, UInt#(6)) imp <- mkBRAMStack();

  /* Specification of same shape */
  Stack#(8, UInt#(6)) spec <- mkStackSpec();

  /* A random state generator */
  Randomize#(State) randomState <- mkGenericRandomizer;

  /* A random stack element generator */
  Randomize#(UInt#(6)) randomElem <- mkGenericRandomizer;

I also keep track of the number of state transitions, so that testing
does not go on for ever.

  /* Count the number of state transitions */
  Reg#(UInt#(16)) count <- mkReg(0);

Now I have a rule for each state, and make the associated method call
in the imp and spec.

  rule do_pop (state == Pop);
    $display("pop");
    spec.pop;
    imp.pop;
  endrule

  rule do_push (state == Push);
    UInt#(6) x <- randomElem.next;
    $display("push ", x);
    spec.push(x);
    imp.push(x);
  endrule

  rule do_top (state == Top);
    $display("top");
    if (spec.top != imp.top)
      begin
        $display("Not equivalent: ", spec.top, " v ", imp.top);
        $finish(0);
      end
  endrule

  rule do_isEmpty (state == IsEmpty);
    $display("isEmpty");
    if (spec.isEmpty != imp.isEmpty)
      begin
        $display("Not equivalent!");
        $finish(0);
      end
  endrule

  rule do_nop (state == Nop);
    $display("No-op");
  endrule

  rule do_nop (state == Clear);
    $display("clear");
    spec.clear;
    imp.clear;
  endrule

Finally, some rules to drive the state machine, exploring random
interleavings of method invocations.

  /* Initialise the random generators */
  rule initialise (count == 0);
    count <= count+1;
    randomElem.cntrl.init;
    randomState.cntrl.init;
  endrule

  rule explore_random_interleavings (count > 0);
    count <= count+1;
    if (count < 100)
      begin
        State nextState <- randomState.next;
        state <= nextState;
      end
    else
      begin
        $display("Testing completed sucessfully.");
        $finish(0);
      end
  endrule

References
==========

[1] Claessen and Hughes, Testing monadic code with QuickCheck.
