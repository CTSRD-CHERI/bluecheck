import Vector    :: *;
import BRAMCore  :: *;
import BlueCheck :: *;
import StmtFSM   :: *;
import Clocks    :: *;

///////////////
// Interface //
///////////////

interface Stack#(numeric type n, type a);
  method Action push(a x);
  method Action pop;
  method a top;
  method Bool isEmpty;
  method Action clear;
  method Bit#(n) size;
endinterface

//////////////////
// Specfication //
//////////////////

/* Make a stack with space for 2^n elements of type a */
module mkStackSpec (Stack#(n, a))
  provisos(Bits#(a, b), Add#(1, m, TExp#(n)));

  Reg#(Vector#(TExp#(n), a)) stk <- mkReg(newVector());

  Reg#(Bit#(n)) num <- mkReg(0);

  method Action push(a x);
    num <= num+1;
    stk <= cons(x, init(stk));
  endmethod

  method Action pop if (num > 0);
    num <= num-1;
    stk <= append(tail(stk), cons(?, nil));
  endmethod

  method a top if (num > 0);
    return head(stk);
  endmethod

  method Bool isEmpty;
    return (num==0);
  endmethod

  method Action clear;
    num <= 0;
  endmethod

  method Bit#(n) size = num;
endmodule

////////////////////
// Implementation //
////////////////////

/*

A block RAM based stack implementation.  

We want push and pop to be single-cycle operations.  In the case of
pop, we cannot get the value out of memory until the next cycle so
must fetch it speculatively:

  * when popping, we speculatively read the next item from block RAM
    so that it's ready on the data bus for the next pop;

  * when pushing, we request the value we are writing (using the
    WRITE_FIRST semantics of block RAMs) so that it's also ready
    on the data bus for the next pop.

We assume the block RAMs have a WRITE_FIRST semantics even though this
is not stated in the documentation!  (I can see it in the Verilog
though.)

Simultaneous pushing and popping (with a pop before push semantics) is
useful but not supported by this module.  Could be easily done using
DWires though.

*/


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
    ram.put(False, sp-1, ?); // INCORRECT
    //ram.put(False, sp-2, ?); // CORRECT

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
endmodule

/////////////////////////
// Equivalence testing //
/////////////////////////

module [BlueCheck] checkStack ();
  /* Specification instance */
  Stack#(8, Bit#(4)) spec <- mkStackSpec();

  /* Implmentation instance */
  Stack#(8, Bit#(4)) imp <- mkBRAMStack();

  equiv("pop"    , spec.pop    , imp.pop);
  equiv("push"   , spec.push   , imp.push);
  equiv("isEmpty", spec.isEmpty, imp.isEmpty);
  equiv("top"    , spec.top    , imp.top);
endmodule

// Reset version, for iterative deepening
module [BlueCheck] checkStackWithReset#(Reset r) ();
  /* Specification instance */
  Stack#(8, Bit#(4)) spec <- mkStackSpec(reset_by r);

  /* Implmentation instance */
  Stack#(8, Bit#(4)) imp <- mkBRAMStack(reset_by r);

  equiv("clear"  , spec.clear  , imp.clear);
  equiv("pop"    , spec.pop    , imp.pop);
  equiv("push"   , spec.push   , imp.push);
  equiv("isEmpty", spec.isEmpty, imp.isEmpty);
  equiv("top"    , spec.top    , imp.top);
endmodule

// Similar to above, but with classification
module [BlueCheck] checkStackWithResetAndClassify#(Reset r) ();
  /* Specification instance */
  Stack#(8, Bit#(4)) spec <- mkStackSpec(reset_by r);

  /* Implmentation instance */
  Stack#(8, Bit#(4)) imp <- mkBRAMStack(reset_by r);

  /* Test data classifier */
  Classifier classifySmall <- mkClassifier("small");

  /* Monitor max stack size */
  Reg#(Bit#(8)) maxSize <- mkReg(0);
  PulseWire resetMaxSize <- mkPulseWire;
  rule updateMaxSize;
    if (resetMaxSize) maxSize <= 0;
    else maxSize <= max(maxSize, spec.size);
  endrule

  pre("", resetMaxSize.send);

  equiv("pop"    , spec.pop    , imp.pop);
  equiv("push"   , spec.push   , imp.push);
  equiv("isEmpty", spec.isEmpty, imp.isEmpty);
  equiv("top"    , spec.top    , imp.top);
  equiv("clear"  , spec.clear  , imp.clear);

  post("", classifySmall(maxSize <= 3));
endmodule

module [Module] testStack ();
  blueCheck(checkStack);
endmodule

// Synthesisable version
module [Module] testStackSynth (JtagUart);
  let uart <- blueCheckSynth(checkStack);
  return uart;
endmodule

// Iterative deepening version
module [Module] testStackID ();
  Clock clk <- exposeCurrentClock;
  MakeResetIfc r <- mkReset(0, True, clk);
  blueCheckID(checkStackWithReset(r.new_rst), r);
endmodule

// Iterative deepening version & classification
module [Module] testStackIDClassify ();
  Clock clk <- exposeCurrentClock;
  MakeResetIfc r <- mkReset(0, True, clk);
  blueCheckID(checkStackWithResetAndClassify(r.new_rst), r);
endmodule

// Synthesisable & iterative deepening version
module [Module] testStackIDSynth (JtagUart);
  Clock clk <- exposeCurrentClock;
  MakeResetIfc r <- mkReset(0, True, clk);
  let uart <- blueCheckIDSynth(checkStackWithReset(r.new_rst), r);
  return uart;
endmodule

///////////////////////
// Algebraic testing //
///////////////////////

/* A block RAM based stack: test against algebraic specification. */

module [BlueCheck] checkStackAlgWithReset#(Reset r) ();
  /* Instances */
  Stack#(8, UInt#(8)) s1 <- mkBRAMStack(reset_by r);
  Stack#(8, UInt#(8)) s2 <- mkBRAMStack(reset_by r);

  /* This function allows us to make assertions in the properties */
  Ensure ensure <- getEnsure;

  Stmt prop1 =
    seq
      s1.clear;            s2.clear;
      ensure(s1.isEmpty);
    endseq;

  function Stmt prop2(UInt#(8) x) =
    seq
      s1.push(x);          s2.push(x);
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

  /* Equivalences */
  equiv("pop", s1.pop, s2.pop);
  equiv("push", s1.push, s2.push);
  equiv("isEmpty", s1.isEmpty, s2.isEmpty);
  equiv("top", s1.top, s2.top);

  /* Properties */
  prop("prop1", prop1);
  prop("prop2", prop2);
  prop("prop3", prop3);
  prop("prop4", prop4);

endmodule

module [Module] testStackAlgID ();
  Clock clk <- exposeCurrentClock;
  MakeResetIfc r <- mkReset(0, True, clk);
  blueCheckID(checkStackAlgWithReset(r.new_rst), r);
endmodule

module [Module] testStackAlg ();
  blueCheck(checkStackAlgWithReset(noReset));
endmodule
