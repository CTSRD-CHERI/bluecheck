// BlueCheck 0.12, M Naylor.

// Change log
// ==========
//
// 5  Nov 2012: Version 0.1
// 20 Nov 2014: Support for Action and ActionValue props
// 21 Nov 2014: Added iterative deepening capability

package BlueCheck;

import Randomizable  :: *;
import ModuleCollect :: *;
import StmtFSM       :: *;
import List          :: *;
import Clocks        :: *;

// BlueCheck parameters
typedef struct {
  // Display message when a chosen state does not fire
  Bool showNonFire;

  // Display message when a chosen state is a no-op
  Bool showNoOp;

  // Generate a checker based on an iterative deepening strategy
  // (If 'Invalid', a single random state walk is performed)
  Maybe#(ID_Params) iterativeDeepening;

  // Number of testing iterations to perform. For iterative deepening,
  // this is the number of times to increase the depth before stopping
  // Otherwise, the it's the length of the random state walk
  Bit#(32) numIterations;
} BlueCheck_Params;

// Sub-parameters for iterative deepening
typedef struct {
  // Iterative deepening requires ability to reset the circuit under test
  MakeResetIfc rst;

  // The number of states to be explored in a single 'test'
  Bit#(32) initialDepth;

  // The number of tests to perform at each depth
  Bit#(32) testsPerDepth;

  // A function to increase the depth
  (function Bit#(32) f(Bit#(32) currentDepth)) incDepth;
} ID_Params;

// The maximum number of states in the equivalance checker.
// You will get a compile-time error message if this parameter
// is not big enough, but it's not likely, unless you use very
// large method frequencies.
typedef 16 LogMaxStates;
typedef UInt#(LogMaxStates) State;

// The frequency that the checker will move to particular state.
typedef Integer Frequency; // Range: 1 to 100.

// A BlueCheck module implicitly collects actions, statements,
// invariants and random generators, an allowing automatic creation of
// an equivalance checker.
typedef ModuleCollect#(Item) BlueCheck;

typedef union tagged {
  Tuple3#(Frequency, Fmt, Action) ActionItem;
  Tuple3#(Frequency, Fmt, Stmt) StmtItem;
  Tuple2#(Bool, Action) RandomGenItem;
  Tuple2#(Fmt, Bool) InvariantItem;
} Item;

// Turn an item into a singleton action if it is an ActionItem.
function List#(Tuple3#(Frequency, Fmt, Action)) getActionItem(Item item) =
  case (item) matches
    tagged ActionItem .a: return cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton action if it is an RandomGenItem.
function List#(Tuple2#(Bool, Action)) getRandomGenItem(Item item) =
  case (item) matches
    tagged RandomGenItem .a: return cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton pair if it is an InvariantItem.
function List#(Tuple2#(Fmt, Bool)) getInvariantItem(Item item) =
  case (item) matches
    tagged InvariantItem .a: return cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is an StmtItem.
function List#(Tuple3#(Frequency, Fmt, Stmt)) getStmtItem(Item item) =
  case (item) matches
    tagged StmtItem .a: return cons(a, Nil);
    default: return Nil;
  endcase;

// Display a function application, where function and
// arguments are available as Fmt items of a list.
function Fmt formatApp(List#(Fmt) app);
  if (tail(app) matches tagged Nil)
    return head(app);
  else 
    return (head(app) + fshow("(") + formatArgs(tail(app)) + fshow(")"));
endfunction

function Fmt formatArgs(List#(Fmt) args);
  if (tail(args) matches tagged Nil)
    return head(args);
  else
    return (head(args) + fshow(",") + formatArgs(tail(args)));
endfunction

// The following type class allows two functions of the same type to
// be applied to random inputs.  If the return values differ, the
// behaviour is to terminate with an error message (a counter-example
// has been found).  The probability that the equivalence will be
// checked on any given step can be specified.
typeclass Equiv#(type a);
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr, a f, a g) ();
endtypeclass

module [BlueCheck] equiv#(String name, a f, a g) ()
    provisos(Equiv#(a));
  eq(cons(fshow(name), nil), 1, f, g);
endmodule

module [BlueCheck] equivf#(Frequency fr, String name, a f, a g) ()
    provisos(Equiv#(a));
  eq(cons(fshow(name), nil), fr, f, g);
endmodule

// Base case 1: execute two actions.
instance Equiv#(Action);
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr, Action a, Action b) ();
    Action executeTwo =
      action
        a; b;
      endaction;
    addToCollection(tagged ActionItem
      (tuple3(fr, formatApp(app), executeTwo)));
  endmodule
endinstance

// Base case 2: execute two action-values,
// and check equivalance of results.
instance Equiv#(ActionValue#(t))
  provisos(Eq#(t), Bits#(t, n));
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr
                                       , ActionValue#(t) a
                                       , ActionValue#(t) b) ();
    Action executeTwoAndCheck =
      action
        t aVal <- a;
        t bVal <- b;
        if (aVal != bVal)
          begin
            $display("Not equal:", aVal, " versus ", bVal);
            $finish(0);
          end
      endaction;
      addToCollection(tagged ActionItem
        (tuple3(fr, formatApp(app), executeTwoAndCheck)));
  endmodule
endinstance

// Base case 3: execute two statements.
instance Equiv#(Stmt);
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr, Stmt a, Stmt b) ();
    Stmt s = par a; b; endpar;
    addToCollection(tagged StmtItem (tuple3(fr, formatApp(app), s)));
  endmodule
endinstance

// Recursive case: generate a random input,
// apply it to each function, and
// recurse on the resulting applications.
instance Equiv#(function b f(a x))
  provisos(Equiv#(b), Bits#(a, n), Bounded#(a), FShow#(a));
    module [BlueCheck] eq#(List#(Fmt) app, Frequency fr
                                         , function b f(a x)
                                         , function b g(a y))();
      Reg#(Bool) init <- mkReg(True);
      Reg#(a) aReg <- mkRegU;
      Randomize#(a) aRandom <- mkGenericRandomizer;

      Action genRandom =
        action
          let a <- aRandom.next;
          aReg <= a;
        endaction;

      rule initialise (init);
        aRandom.cntrl.init;
        init <= False;
      endrule

      addToCollection(tagged RandomGenItem (tuple2(!init, genRandom)));

      eq(append(app, cons(fshow(aReg), nil)), fr, f(aReg), g(aReg));
    endmodule
endinstance

// Base case 4 (fall through): check that two values are equal.
instance Equiv#(a) provisos(Eq#(a), FShow#(a));
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr, a x, a y) ();
    Fmt fmt = formatApp(app) + fshow(" failed: ")
            + fshow(x) + fshow(" v ") + fshow(y);
    addToCollection(tagged InvariantItem (tuple2(fmt, x == y)));
  endmodule
endinstance

// Like the Equiv type-class, except for a single method.
typeclass Prop#(type a);
  module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, a f) ();
endtypeclass

// Base case 1: execute statement.
instance Prop#(Stmt);
  module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, Stmt a) ();
    addToCollection(tagged StmtItem (tuple3(fr, formatApp(app), a)));
  endmodule
endinstance

// Base case 2: execute action.
instance Prop#(Action);
  module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, Action a) ();
    addToCollection(tagged ActionItem (tuple3(fr, formatApp(app), a)));
  endmodule
endinstance

// Base case 3: execute action-value
instance Prop#(ActionValue#(t))
  provisos(Eq#(t), Bits#(t, n));
  module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, ActionValue#(t) a) ();
    Action act =
      action
        t aVal <- a;
        $display("   (Returned ", aVal, ")");
      endaction;
      addToCollection(tagged ActionItem (tuple3(fr, formatApp(app), act)));
  endmodule
endinstance

// Recursive case.
instance Prop#(function b f(a x))
  provisos(Prop#(b), Bits#(a, n), Bounded#(a), FShow#(a));
    module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, function b f(a x))();
      Reg#(Bool) init <- mkReg(True);
      Reg#(a) aReg <- mkRegU;
      Randomize#(a) aRandom <- mkGenericRandomizer;

      Action genRandom =
        action
          let a <- aRandom.next;
          aReg <= a;
        endaction;

      rule initialise (init);
        aRandom.cntrl.init;
        init <= False;
      endrule

      addToCollection(tagged RandomGenItem (tuple2(!init, genRandom)));

      pr(append(app, cons(fshow(aReg), nil)), fr, f(aReg));
    endmodule
endinstance

module [BlueCheck] prop#(String name, a f) ()
    provisos(Prop#(a));
  pr(cons(fshow(name), nil), 1, f);
endmodule

module [BlueCheck] propf#(Frequency fr, String name, a f) ()
    provisos(Prop#(a));
  pr(cons(fshow(name), nil), fr, f);
endmodule

function Action ensure(Bool b) =
    action
      if (!b)
        begin
          $display("'ensure' statement failed");
          $finish(0);
        end
    endaction;

// Compute the condition for being in each state of the equivalance
// checker. Some states are visited more frequently than others.
function List#(Bool) stateConds(Reg#(State) s, Integer start,
                                         List#(Frequency) freqs);
  if (freqs matches tagged Nil) return Nil;
  else
    begin
      Frequency f = head(freqs);
      return (cons(s >= fromInteger(start) && s < fromInteger(start+f),
        stateConds(s, start+f, tail(freqs))));
    end
endfunction

function Integer sum(List#(Integer) xs);
  if (xs matches tagged Nil) return 0;
  else return (head(xs) + sum(tail(xs)));
endfunction

// Turn the list of items gathered in a BlueCheck module into an
// actual equivalence checker.
module [Module] blueCheckCore#( BlueCheck#(Empty) bc
                              , BlueCheck_Params params ) (Stmt);
  // Extract items.
  let {_, items} <- getCollection(bc);
  let actionItems = concat(map(getActionItem, items));
  let stmtItems = concat(map(getStmtItem, items));
  let randomGens = concat(map(getRandomGenItem, items));
  let invariantBools = concat(map(getInvariantItem, items));
  let actionMsgs = map(tpl_2, actionItems);
  let stmtMsgs = map(tpl_2, stmtItems);
  let actions = map(tpl_3, actionItems);
  let stmts = map(tpl_3, stmtItems);

  // Setup state machine for equivalence checking.
  // Note state 0 is a no-op state.
  List#(Integer) freqs = append(map(tpl_1, actionItems),
                                map(tpl_1, stmtItems));
  Integer numStates = 1+sum(freqs);
  Randomize#(State) randomState <-
    mkConstrainedRandomizer(0, fromInteger(numStates-1));
  Reg#(State) state <- mkReg(0);
  Wire#(Bool) waitWire <- mkDWire(False);
  Wire#(Bool) didntFire <- mkDWire(False);
  Reg#(Bool) testDone <- mkReg(False);
  List#(Bool) inState = stateConds(state, 1, freqs);

  // When count is 0 the checker is disabled
  Reg#(Bit#(32)) count <- mkReg(0);
  Bool enabled = count != 0;

  // State for iterative-deepening
  Reg#(Bit#(32)) currentDepth <- mkReg(0);
  Reg#(Bit#(32)) testNum <- mkReg(0);
  Reg#(Bit#(32)) iterCount <- mkReg(0);

  // Generate rules to generate random data.
  for (Integer i = 0; i < length(randomGens); i=i+1)
    begin
      let go  = tpl_1(randomGens[i]);
      let gen = tpl_2(randomGens[i]);
      rule genRandomData (go && !waitWire);
        gen;
      endrule
    end

  // Generate rules to check invariant booleans.
  for (Integer i = 0; i < length(invariantBools); i=i+1)
    begin
      let msg = tpl_1(invariantBools[i]);
      let b   = tpl_2(invariantBools[i]);
      rule checkInvariantBool (enabled && !waitWire);
        if (!b)
          begin
            $display(msg);
            $finish(0);
          end
      endrule
    end

  // Generate rules to run actions, guarded by the current state.
  for (Integer i = 0; i < length(actions); i=i+1)
    begin
      (* preempts = "runAction, runActionNotPossible" *)
      rule runAction (enabled && inState[i] && !waitWire);
        $display("%0t: ", $time, actionMsgs[i]);
        actions[i];
      endrule
      rule runActionNotPossible (enabled && inState[i] && !waitWire);
        didntFire <= True;
        if (params.showNonFire)
          $display("%0t: [did not fire] ", $time, actionMsgs[i]);
      endrule
    end

  // Generate rules to run statements, guarded by the current state.
  // Statements may take many cycles, hence waitWire.
  for (Integer i = 0; i < length(stmts); i=i+1)
    begin
      Integer s = length(actions)+i;
      Reg#(Bool) fsmRunning <- mkReg(False);
      FSM fsm <- mkFSMWithPred(stmts[i], enabled && inState[s]);

      rule runStmt (enabled && inState[s] && !fsmRunning);
        $display("%0t: ", $time, stmtMsgs[i]);
        fsm.start;
        fsmRunning <= True;
        waitWire <= True;
      endrule

      rule assertWait (enabled && inState[s] && fsmRunning && !fsm.done);
        waitWire <= True;
      endrule

      rule finishStmt (enabled && inState[s] && fsmRunning && fsm.done);
        fsmRunning <= False;
      endrule
    end

  // No-op.
  rule noOp (enabled && state == 0);
    if (params.showNoOp)
      $display("%0t: No-op", $time);
  endrule

  // One long walk of the state space.
  Stmt singleWalk =
    seq
      randomState.cntrl.init;
      testDone <= False;
      $display("=== Depth %0d, Test %0d ===", currentDepth, testNum);
      while (! testDone)
        action
          await(!waitWire);
          let nextState <- randomState.next;
          state <= nextState;
          if (state != 0 && !didntFire)
            begin
              if (count < params.numIterations)
                count <= count+1;
              else
                begin
                  count <= 0;
                  testDone <= True;
                end
              end
        endaction
      $display("OK: passed %0d iterations", params.numIterations);
    endseq;

  // Many short walks of the state space (iterative deepening).
  Stmt iterativeDeepening =
    begin
      let idParams = fromMaybe(?, params.iterativeDeepening);

      seq
        randomState.cntrl.init;
        currentDepth <= idParams.initialDepth;
        while (iterCount < params.numIterations)
          seq
            testNum <= 0;
            while (testNum < idParams.testsPerDepth)
              seq
                testDone <= False;
                $display("=== Depth %0d, Test %0d ===", currentDepth, testNum);
                while (! testDone)
                  action
                    await(!waitWire);
                    let nextState <- randomState.next;
                    state <= nextState;
                    if (state != 0 && !didntFire)
                      begin
                        if (count < currentDepth)
                          count <= count+1;
                        else
                          begin
                            count <= 0;
                            testDone <= True;
                          end
                      end
                  endaction
                testNum <= testNum+1;
                idParams.rst.assertReset();
              endseq
            currentDepth <= idParams.incDepth(currentDepth);
            iterCount <= iterCount+1;
          endseq
        $display("OK: passed %0d test sequences",
                   params.numIterations*idParams.testsPerDepth);
      endseq;
    end;

  return isValid(params.iterativeDeepening) ?
           iterativeDeepening : singleWalk;
endmodule

// Default parameters for single state walk
BlueCheck_Params bcParamsSimple =
  BlueCheck_Params {
    showNonFire        : False
  , showNoOp           : False
  , iterativeDeepening : tagged Invalid
  , numIterations      : 1000
  };

// Default parameters for iterative deepening
function BlueCheck_Params bcParamsID(MakeResetIfc rst);
  function double(x) = x*2;

  ID_Params idParams =
    ID_Params {
      rst           : rst
    , initialDepth  : 5
    , testsPerDepth : 1000
    , incDepth      : double
    };

  BlueCheck_Params params =
    BlueCheck_Params {
      showNonFire        : False
    , showNoOp           : False
    , iterativeDeepening : tagged Valid idParams
    , numIterations      : 3
    };

  return params;
endfunction

// Simple version returning a statement
module [Module] blueCheckStmt#(BlueCheck#(Empty) bc)(Stmt);
  Stmt s <- blueCheckCore(bc, bcParamsSimple);
  return s;
endmodule

// Simple version that constructs a checker
module [Module] blueCheck#(BlueCheck#(Empty) bc)();
  Stmt s <- blueCheckStmt(bc);
  mkAutoFSM(s);
endmodule

// Iterative deepening version returning a statement
module [Module] blueCheckStmtID# (BlueCheck#(Empty) bc
                                , MakeResetIfc rst ) (Stmt);
  Stmt s <- blueCheckCore(bc, bcParamsID(rst));
  return s;
endmodule

// Iterative deepening version that constructs a checker
module [Module] blueCheckID#( BlueCheck#(Empty) bc
                            , MakeResetIfc rst ) ();
  Stmt s <- blueCheckStmtID(bc, rst);
  mkAutoFSM(s);
endmodule

endpackage
