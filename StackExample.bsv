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
endinterface

//////////////////
// Specfication //
//////////////////

/* Make a stack with space for 2^n elements of type a */
module mkStackSpec (Stack#(n, a))
  provisos(Bits#(a, b), Add#(1, m, TExp#(n)));

  Reg#(Vector#(TExp#(n), a)) stk <- mkReg(newVector());

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
    //ram.put(False, sp-1, ?); // INCORRECT
    ram.put(False, sp-2, ?); // CORRECT

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

  equiv("pop"    , spec.pop    , imp.pop);
  equiv("push"   , spec.push   , imp.push);
  equiv("isEmpty", spec.isEmpty, imp.isEmpty);
  equiv("top"    , spec.top    , imp.top);
endmodule

module [Module] testStack ();
  blueCheck(checkStack);
endmodule

// Iterative deepening version
module [Module] testStackID ();
  Clock clk <- exposeCurrentClock;
  MakeResetIfc r <- mkReset(0, True, clk);
  blueCheckID(checkStackWithReset(r.new_rst), r);
endmodule

///////////////////////
// Algebraic testing //
///////////////////////

/* A block RAM based stack: test against algebraic specification. */

module [BlueCheck] checkStackAlgWithReset#(Reset r) ();
  /* Instances */
  Stack#(8, UInt#(8)) s1 <- mkBRAMStack(reset_by r);
  Stack#(8, UInt#(8)) s2 <- mkBRAMStack(reset_by r);

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
