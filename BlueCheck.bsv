// BlueCheck 0.2, Matt N.

// Change log
// ==========
//
// 5  Nov 2012: Version 0.1
// 21 Nov 2014: Support for iterative deepening
// 28 Nov 2014: Version 0.2, with support for shrinking

package BlueCheck;

import Randomizable  :: *;
import ModuleCollect :: *;
import StmtFSM       :: *;
import List          :: *;
import Clocks        :: *;
import FIFOF         :: *;
import ConfigReg     :: *;
import Vector        :: *;
import Assert        :: *;

// The max size of the log used for shrinking.  This is tricky to
// implement as a module parameter, hence it is a global parameter.
typedef 32 LogSize;
Integer logSize = valueOf(LogSize);

// BlueCheck module parameters
typedef struct {
  // Verbose output
  Bool verbose;

  // Display message when a chosen state does not fire
  Bool showNonFire;

  // Display message when a chosen state is a no-op
  Bool showNoOp;

  // Generate a checker based on an iterative deepening strategy
  // (If 'False', a single random state walk is performed)
  Bool useIterativeDeepening;
  // This must contain valid data if 'useIterativeDeepening' is 'True'
  ID_Params id; 

  // Interactive iterative deepening
  Bool interactive;

  // Attempt to shrink a counter example, if one is found
  // (This is only valid for iterative deepening)
  Bool useShrinking;

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
// invariants, random generators and loggers, an allowing automatic
// creation of an equivalance checker.
typedef ModuleCollect#(Item) BlueCheck;

typedef union tagged {
  Tuple3#(Frequency, Fmt, Action) ActionItem;
  Tuple3#(Frequency, Fmt, Stmt) StmtItem;
  Tuple2#(Bool, function Action gen(Bool replay)) RandomGenItem;
  Tuple2#(Fmt, Bool) InvariantItem;
  Tuple2#(Bool, Reg#(Bool)) EnsureItem;
  Tuple3#(Action, Action, Action) LogItem;
  Stmt PreStmtItem;
  Stmt PostStmtItem;
} Item;

// Turn an item into a singleton action if it is an ActionItem.
function List#(Tuple3#(Frequency, Fmt, Action)) getActionItem(Item item) =
  case (item) matches
    tagged ActionItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton action if it is an RandomGenItem.
function List#(Tuple2#(Bool, function Action gen(Bool replay)))
  getRandomGenItem(Item item) =
  case (item) matches
    tagged RandomGenItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton pair if it is an InvariantItem.
function List#(Tuple2#(Fmt, Bool)) getInvariantItem(Item item) =
  case (item) matches
    tagged InvariantItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is an StmtItem.
function List#(Tuple3#(Frequency, Fmt, Stmt)) getStmtItem(Item item) =
  case (item) matches
    tagged StmtItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is an EnsureItem.
function List#(Tuple2#(Bool, Reg#(Bool))) getEnsureItem(Item item) =
  case (item) matches
    tagged EnsureItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is an LogItem.
function List#(Tuple3#(Action, Action, Action))
  getLogItem(Item item) =
  case (item) matches
    tagged LogItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is a PreStmtItem.
function List#(Stmt) getPreStmtItem(Item item) =
  case (item) matches
    tagged PreStmtItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Turn an item into a singleton statement if it is a PostStmtItem.
function List#(Stmt) getPostStmtItem(Item item) =
  case (item) matches
    tagged PostStmtItem .a: return Cons(a, Nil);
    default: return Nil;
  endcase;

// Display a function application, where function and
// arguments are available as Fmt items of a list.
function Fmt formatApp(List#(Fmt) app);
  if (List::tail(app) matches tagged Nil)
    return List::head(app);
  else 
    return (List::head(app) + fshow("(") +
             formatArgs(List::tail(app)) + fshow(")"));
endfunction

function Fmt formatArgs(List#(Fmt) args);
  if (List::tail(args) matches tagged Nil)
    return List::head(args);
  else
    return (List::head(args) + fshow(",") + formatArgs(List::tail(args)));
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
  eq(Cons(fshow(name), Nil), 1, f, g);
endmodule

module [BlueCheck] equivf#(Frequency fr, String name, a f, a g) ()
    provisos(Equiv#(a));
  eq(Cons(fshow(name), Nil), fr, f, g);
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
  provisos(Eq#(t), Bits#(t, n), FShow#(t));
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr
                                       , ActionValue#(t) a
                                       , ActionValue#(t) b) ();
    Wire#(Bool) success <- mkDWire(True);
    Wire#(t) aWire      <- mkDWire(?);
    Wire#(t) bWire      <- mkDWire(?);
    Fmt msg             =  fshow("Not equal: ") + fshow(aWire)
                        +  fshow(" versus ")    + fshow(bWire);

    Action executeTwoAndCheck =
      action
        t aVal <- a; aWire <= aVal;
        t bVal <- b; bWire <= bVal;
        if (aVal != bVal) success <= False;
      endaction;
      addToCollection(tagged ActionItem
        (tuple3(fr, formatApp(app), executeTwoAndCheck)));
      addToCollection(tagged InvariantItem (tuple2(msg, success)));
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
      FIFOF#(a) aLog <- mkUGSizedFIFOF(logSize);

      function Action genRandom(Bool replay) =
        action
          let a <- aRandom.next;
          aReg <= replay ? aLog.first : a;
        endaction;

      rule initialise (init);
        aRandom.cntrl.init;
        init <= False;
      endrule

      Action logEnq   = aLog.enq(aReg);
      Action logRot   = action aLog.deq; aLog.enq(aLog.first); endaction;
      Action logClear = aLog.clear;

      addToCollection(tagged RandomGenItem (tuple2(!init, genRandom)));
      addToCollection(tagged LogItem (tuple3(logEnq, logRot, logClear)));

      eq(List::append(app, Cons(fshow(aReg), Nil)),
           fr, f(aReg), g(aReg));
    endmodule
endinstance

// Base case 4 (fall through): check that two values are equal.
instance Equiv#(a) provisos(Eq#(a), FShow#(a));
  module [BlueCheck] eq#(List#(Fmt) app, Frequency fr, a x, a y) ();
    Wire#(Bool) success <- mkDWire(True);
    Fmt fmt = formatApp(app) + fshow(" failed: ")
            + fshow(x) + fshow(" v ") + fshow(y);

    rule check;
      if (x != y) success <= False;
    endrule
     
    addToCollection(tagged InvariantItem (tuple2(fmt, success)));
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
instance Prop#(ActionValue#(Bool));
  module [BlueCheck] pr#(List#(Fmt) app,Frequency fr,ActionValue#(Bool) a) ();
    Wire#(Bool) success <- mkDWire(True);
    Fmt msg = fshow("Property failed");

    Action act =
      action
        Bool s <- a;
        if (!s) success <= False;
      endaction;
      addToCollection(tagged ActionItem (tuple3(fr, formatApp(app), act)));
      addToCollection(tagged InvariantItem (tuple2(msg, success)));
  endmodule
endinstance

// Recursive case.
instance Prop#(function b f(a x))
  provisos(Prop#(b), Bits#(a, n), Bounded#(a), FShow#(a));
    module [BlueCheck] pr#(List#(Fmt) app, Frequency fr, function b f(a x))();
      Reg#(Bool) init <- mkReg(True);
      Reg#(a) aReg <- mkRegU;
      Randomize#(a) aRandom <- mkGenericRandomizer;
      FIFOF#(a) aLog <- mkUGSizedFIFOF(logSize);

      function Action genRandom(Bool replay) =
        action
          let a <- aRandom.next;
          aReg <= replay ? aLog.first : a;
        endaction;

      rule initialise (init);
        aRandom.cntrl.init;
        init <= False;
      endrule

      Action logEnq   = aLog.enq(aReg);
      Action logRot   = action aLog.deq; aLog.enq(aLog.first); endaction;
      Action logClear = aLog.clear;

      addToCollection(tagged RandomGenItem (tuple2(!init, genRandom)));
      addToCollection(tagged LogItem (tuple3(logEnq, logRot, logClear)));

      pr(List::append(app, Cons(fshow(aReg), Nil)), fr, f(aReg));
    endmodule
endinstance

module [BlueCheck] prop#(String name, a f) ()
    provisos(Prop#(a));
  pr(Cons(fshow(name), Nil), 1, f);
endmodule

module [BlueCheck] propf#(Frequency fr, String name, a f) ()
    provisos(Prop#(a));
  pr(Cons(fshow(name), Nil), fr, f);
endmodule

// Ensure function -- for making assertions inside properties
typedef (function Action f(Bool cond)) Ensure;
typedef (function Action f(Bool cond, Fmt msg)) EnsureMsg;

module [BlueCheck] getEnsure (Ensure);
  // Create ensure function
  Wire#(Bool) ok <- mkDWire(True);
  Reg#(Bool) showMsg <- mkReg(False);
  function Action ensureFunc(Bool cond) = action ok <= cond; endaction;
  addToCollection(tagged EnsureItem (tuple2(ok, showMsg)));
  return ensureFunc;
endmodule

module [BlueCheck] getEnsureMsg (EnsureMsg);
  // Create ensure function
  Wire#(Bool) ok <- mkDWire(True);
  Reg#(Bool) showMsg <- mkReg(False);
  function Action ensureFunc(Bool cond, Fmt msg) =
    action ok <= cond; if (!cond && showMsg) $display(msg); endaction;
  addToCollection(tagged EnsureItem (tuple2(ok, showMsg)));
  return ensureFunc;
endmodule

function Action assignReg(t x, Reg#(t) r) = action r <= x; endaction;

// Allow user to add custom pre/post statements for each test
module [BlueCheck] addPreStmt#(Stmt pre) (Empty);
  addToCollection(tagged PreStmtItem pre);
endmodule

module [BlueCheck] addPostStmt#(Stmt post) (Empty);
  addToCollection(tagged PostStmtItem post);
endmodule

// Compute the condition for being in each state of the equivalance
// checker. Some states are visited more frequently than others.
function List#(Bool) stateConds(Reg#(State) s, Integer start,
                                         List#(Frequency) freqs);
  if (freqs matches tagged Nil) return Nil;
  else
    begin
      Frequency f = List::head(freqs);
      return (Cons(s >= fromInteger(start) && s < fromInteger(start+f),
        stateConds(s, start+f, List::tail(freqs))));
    end
endfunction

// Sum a list
function Integer sum(List#(Integer) xs);
  if (xs matches tagged Nil) return 0;
  else return (List::head(xs) + sum(List::tail(xs)));
endfunction

// Sequence a list of statements
function Stmt seqList(List#(Stmt) xs);
  if (xs matches tagged Nil) return (seq delay(1); endseq);
  else return (seq List::head(xs); seqList(List::tail(xs)); endseq);
endfunction

// Turn the list of items gathered in a BlueCheck module into an
// actual equivalence checker.
module [Module] blueCheckCore#( BlueCheck#(Empty) bc
                              , BlueCheck_Params params ) (Stmt);
  // Extract items.
  let concat = List::concat;
  let map    = List::map;
  let append = List::append;
  let {_, items} <- getCollection(bc);
  let actionItems    = concat(map(getActionItem, items));
  let stmtItems      = concat(map(getStmtItem, items));
  let randomGens     = concat(map(getRandomGenItem, items));
  let logItems       = concat(map(getLogItem, items));
  let ensureItems    = concat(map(getEnsureItem, items));
  let invariantBools = concat(map(getInvariantItem, items));
  let preStmt        = seqList(concat(map(getPreStmtItem, items)));
  let postStmt       = seqList(concat(map(getPostStmtItem, items)));
  let actionMsgs     = map(tpl_2, actionItems);
  let stmtMsgs       = map(tpl_2, stmtItems);
  let actions        = map(tpl_3, actionItems);
  let stmts          = map(tpl_3, stmtItems);
  let ensureBools    = map(tpl_1, ensureItems);
  let ensureShows    = map(tpl_2, ensureItems);

  // Setup state machine for equivalence checking.
  // Note state 0 is a no-op state.
  List#(Integer) freqs = append(map(tpl_1, actionItems),
                                map(tpl_1, stmtItems));
  Integer numStates = 1+sum(freqs);
  Randomize#(State) randomState <-
    mkConstrainedRandomizer(0, fromInteger(numStates-1));
  ConfigReg#(State) state <- mkConfigReg(0);
  Wire#(Bool) waitWire <- mkDWire(False);
  Wire#(Bool) didntFire <- mkDWire(False);
  Reg#(Bool) testDone <- mkReg(False);
  Reg#(Bool) doneUI <- mkReg(False);
  List#(Bool) inState = stateConds(state, 1, freqs);
  Reg#(Bool) shrinkingMode <- mkReg(False);
  Reg#(Bool) verbose <- mkReg(params.verbose);

  // When all random generators have initialised
  Reg#(Bool) randGensInitialised <- mkReg(False);

  // When count is 0, actions/statements are disabled
  ConfigReg#(Bit#(32)) count <- mkConfigReg(0);
  Bool actionsEnabled = count != 0;

  // When delayed count is 0, invariant checking is disabled
  ConfigReg#(Bit#(32)) delayedCount <- mkConfigReg(0);
  Bool checkingEnabled = delayedCount != 0;

  rule updateDelayedCount;
    delayedCount <= count;
  endrule

  // Log/replay signals
  FIFOF#(State) stateLog  <- mkSizedFIFOF(logSize);
  FIFOF#(Bit#(64)) timeLog <- mkSizedFIFOF(logSize);
  Wire#(Bool) replayWire <- mkDWire(False);
  Wire#(Bool) logEnqWire <- mkDWire(False);
  Wire#(Bool) logRotWire <- mkDWire(False);
  Wire#(Bool) logClearWire <- mkDWire(False);
  Reg#(Bit#(32)) counterExampleLength <- mkReg(0);
  Reg#(Bit#(32)) omitNum <- mkReg(0);
  Vector#(LogSize, Reg#(Bool)) omitMask <- replicateM(mkReg(False));

  // Track failures
  Reg#(Bool) failureReg    <- mkConfigReg(False);
  Wire#(Bool) resetFailure <- mkDWire(False);
  Bool ensureFailure    = List::any( \== (False), ensureBools);
  Bool invariantFailure = (waitWire || !checkingEnabled) ? False
                        : List::any( \== (False), map (tpl_2, invariantBools));
  Bool failureFound     = ensureFailure || invariantFailure || failureReg;

  rule trackFailure;
    if (resetFailure)
      failureReg <= False;
    else if (ensureFailure || invariantFailure)
      failureReg <= True;
  endrule

  // Local timer
  Reg#(Bit#(64)) timer <- mkReg(0);
  Wire#(Bool) resetTimer <- mkDWire(False);

  rule incTimer;
    if (resetTimer)
      timer <= 0;
    else
      timer <= timer+1;
  endrule

  // Generate rules to generate random data.
  for (Integer i = 0; i < length(randomGens); i=i+1)
    begin
      let go  = tpl_1(randomGens[i]);
      let gen = tpl_2(randomGens[i]);
      rule genRandomData (go && !waitWire);
        gen(replayWire);
      endrule
    end

  // Signal when all random generators have initialised
  rule initRandomGens;
    randGensInitialised <= List::all(tpl_1, randomGens);
  endrule

  // Rules to check 'ensure' assertions.
  rule checkEnsure (!failureReg && List::any( \== (False) , ensureBools));
    if (verbose)
      $display("%0t: 'ensure' statement failed", timer);
  endrule

  // Generate rules to check invariant booleans.
  for (Integer i = 0; i < length(invariantBools); i=i+1)
    begin
      let msg = tpl_1(invariantBools[i]);
      let b   = tpl_2(invariantBools[i]);
      rule checkInvariantBool (checkingEnabled && !failureReg && !waitWire);
        if (!b && verbose) $display("%0t: ", timer, msg);
      endrule
    end

  // Generate rules to run actions, guarded by the current state.
  for (Integer i = 0; i < length(actions); i=i+1)
    begin
      (* preempts = "runAction, runActionNotPossible" *)
      rule runAction (actionsEnabled && inState[i] && !waitWire);
        if (verbose)
          $display("%0t: ", timer, actionMsgs[i]);
        actions[i];
        if (!shrinkingMode)
          logEnqWire <= True;
      endrule
      rule runActionNotPossible (actionsEnabled && inState[i] && !waitWire);
        didntFire <= True;
        if (params.showNonFire && verbose)
          $display("%0t: [did not fire] ", timer, actionMsgs[i]);
      endrule
    end

  // Generate rules to run statements, guarded by the current state.
  // Statements may take many cycles, hence waitWire.
  for (Integer i = 0; i < length(stmts); i=i+1)
    begin
      Integer s = length(actions)+i;
      Reg#(Bool) fsmRunning <- mkReg(False);
      FSM fsm <- mkFSMWithPred(stmts[i], actionsEnabled && inState[s]);

      rule runStmt (actionsEnabled && inState[s] && !fsmRunning);
        if (verbose)
          $display("%0t: ", timer, stmtMsgs[i]);
        fsm.start;
        fsmRunning <= True;
        waitWire <= True;
        if (!shrinkingMode)
          logEnqWire <= True;
      endrule

      rule assertWait (actionsEnabled && inState[s] && fsmRunning && !fsm.done);
        waitWire <= True;
      endrule

      rule finishStmt (actionsEnabled && inState[s] && fsmRunning && fsm.done);
        fsmRunning <= False;
      endrule
    end

  // Generate rules to modify logs
  if (params.useIterativeDeepening && params.useShrinking)
  begin

    for (Integer i = 0; i < length(logItems); i=i+1)
      begin
        let logEnq   = tpl_1(logItems[i]);
        let logRot   = tpl_2(logItems[i]);
        let logClear = tpl_3(logItems[i]);

        // Enqueue the current state into the log
        (* mutually_exclusive = "triggerEnq,triggerRot" *)
        rule triggerEnq (logEnqWire);
          logEnq;
        endrule

        // Remove the head of the log and append it to the end
        rule triggerRot (logRotWire);
          logRot;
        endrule

        // Clear the log
        rule triggerClear (logClearWire);
          logClear;
        endrule
      end

    // Also update the state and timer logs
    (* mutually_exclusive = "enqLogs,rotLogs" *)
    rule enqLogs (logEnqWire);
      stateLog.enq(state);
      timeLog.enq(timer);
    endrule

    rule rotLogs (logRotWire);
      stateLog.enq(stateLog.first); stateLog.deq;
      timeLog.enq(timeLog.first); timeLog.deq;
    endrule

    rule clearLogs (logClearWire);
      stateLog.clear;
      timeLog.clear;
    endrule
  end

  // No-op.
  rule noOp (actionsEnabled && state == 0);
    if (params.showNoOp && verbose)
      $display("%0t: No-op", timer);
  endrule

  // Single walk of state space ===============================================

  // One long walk of the state space.
  Stmt singleWalk =
    seq
      action
        // Show ensure-failure messages?
        let _ <- List::mapM(assignReg(True), ensureShows);
      endaction

      // Initialise
      randomState.cntrl.init;
      await(randGensInitialised);
      testDone <= False;
      resetTimer <= True;
      preStmt;
      while (!testDone)
        action
          await(!waitWire);
          let nextState <- randomState.next;
          if (failureFound)
            begin
              count <= 0;
              testDone <= True;
            end
          else
            begin
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
            end
        endaction
      postStmt;
      if (failureFound)
        $display("FAILED: counter-example found.");
      else
        $display("OK: passed %0d iterations", params.numIterations);
    endseq;

  // Replaying and shrinking counter examples =================================

  Stmt shrink =
    seq
      // Initialise shrinker
      action
        omitNum <= 0;
        shrinkingMode <= True;
        for (Integer i=0; i < logSize; i=i+1) omitMask[i] <= False;
      endaction

      // Try to omit each element of the failing sequence, and if
      // it succeeds, undo the omission.
      while (omitNum <= counterExampleLength)
        seq
          action
            if (verbose) $display("=== Shrink attempt %0d ===", omitNum);
            // Display counter example even if verbose == False
            if (!verbose && omitNum == counterExampleLength)
              begin
                verbose <= True;
                let _ <- List::mapM(assignReg(True), ensureShows);
                $display("");
              end
          endaction

          omitMask[omitNum] <= True;
          // Reset circuit under test
          params.id.rst.assertReset();
          action
            // Initialise replay
            resetFailure <= True;
            resetTimer <= True;
          endaction

          // Test sequence starts here
          delay(1);
          preStmt;
          while (count < counterExampleLength)
            action
              await(!waitWire);
              if (timer+1 >= timeLog.first)
                begin
                  if (omitMask[count] == False)
                    begin
                      state <= stateLog.first;
                      replayWire <= True;
                    end
                  else
                    state <= 0;
                  logRotWire <= True;
                  count <= count+1;
                end
              else
                state <= 0;
            endaction
          count <= 0;
          postStmt;
          if (!failureFound)
            omitMask[omitNum] <= False;
          omitNum <= omitNum+1;
      endseq

      // Restore original settings
      action
        shrinkingMode <= False;
        verbose <= params.verbose;
        let _ <- List::mapM(assignReg(params.verbose), ensureShows);
      endaction
    endseq;

  // Iterative deepening ======================================================

  // State for iterative-deepening
  Reg#(Bit#(32)) currentDepth <- mkReg(0);
  Reg#(Bit#(32)) testNum <- mkReg(0);
  Reg#(Bit#(32)) iterCount <- mkReg(0);

  Stmt iterativeDeepening =
    seq
      // Initialisation
      action
        resetFailure <= True;
        iterCount <= 0;
      endaction

      // Each iteration will produce N test sequences of size 'depth'.
      // After each iteration, the depth is increased.
      currentDepth <= params.id.initialDepth;
      while (!failureFound && iterCount < params.numIterations)
        seq
          // Check that the depth is OK
          if (params.useShrinking && currentDepth >= fromInteger(logSize))
            seq
              $display("Maximum depth of %0d", logSize-1, " exceeded.");
              $display("Increase the 'logSize' parameter in BlueCheck.bsv.");
              $finish(0);
            endseq

          // Produce a test sequence of size 'currentDepth'
          testNum <= 0;
          while (!failureFound && testNum < params.id.testsPerDepth)
            seq
              // Reset the circuit under test
              params.id.rst.assertReset();

              // Initialise test
              action
                $write("=== Depth %0d, Test %0d/%0d ===%c", currentDepth,
                  testNum+1, params.id.testsPerDepth, verbose ? 10 : 13);
                testDone <= False;
                counterExampleLength <= currentDepth;
                logClearWire <= True;
                resetTimer <= True;
              endaction

              // Test sequence starts here
              delay(1);
              preStmt;   // Execute user-defined pre-statement
              while (!testDone)
                action
                  // This action only fires when not waiting for a
                  // user-defined statement to finish.
                  await(!waitWire);
                  let nextState <- randomState.next;
                  let actionFired = (state != 0 && !didntFire);
                  if (failureFound)
                    begin
                      // We found a counter example smaller than the depth
                      counterExampleLength <= actionFired ? count : count-1;
                      count <= 0;
                      testDone <= True;
                    end
                  else
                    begin
                      // Change the state for the next clock cycle
                      state <= nextState;
                      if (actionFired)
                        begin
                          // Is this the final element of the sequence?
                          if (count < currentDepth)
                            count <= count+1;
                          else
                            begin
                              // A count of '0' disables the checker
                              count <= 0;
                              testDone <= True;
                            end
                        end
                    end
                endaction
              postStmt; // Execute user-defined post-statement
              testNum <= testNum+1;
            endseq

          currentDepth <= params.id.incDepth(currentDepth);
          iterCount <= iterCount+1;
          if (!failureFound) $display("");
        endseq

      // We've reached the end of iterative deepening.  Either we
      // found a failure or performed the desired number of tests.
      if (!failureFound)
        $display("\nOK: passed %0d test sequences",
                   params.numIterations*params.id.testsPerDepth);
      else if (params.useShrinking)
        shrink;
      else
        $display("\nFAILED: counter-example found");
      
    endseq;

  // Iterative deepening (with iteraction) ====================================

  Stmt iterativeDeepeningTop =
    seq
      action
        // Show ensure-failure messages?
        let _ <- List::mapM(assignReg(params.verbose), ensureShows);
      endaction

      // Initialise the random generators
      randomState.cntrl.init;
      await(randGensInitialised);

      // Loop while user demands it
      while (! doneUI)
        seq
          iterativeDeepening;
          if (params.interactive)
            action
              $display("Continue searching?\n",
                       "Press ENTER to continue or Ctrl-D to stop: ");
              int c <- $fgetc(stdin);
              if (c < 0) doneUI <= True;
            endaction
          else
            doneUI <= True;
        endseq
    endseq;

  // Result of blueCheck module
  return params.useIterativeDeepening ?
           iterativeDeepeningTop : singleWalk;
endmodule

// Default parameters for single state walk
BlueCheck_Params bcParamsSimple =
  BlueCheck_Params {
    verbose               : True
  , showNonFire           : False
  , showNoOp              : False
  , useIterativeDeepening : False
  , interactive           : False
  , useShrinking          : False
  , id                    : ?
  , numIterations         : 1000
  };

// Default parameters for iterative deepening
function BlueCheck_Params bcParamsID(MakeResetIfc rst);
  function incDepth(x) = x+10;

  ID_Params idParams =
    ID_Params {
      rst           : rst
    , initialDepth  : 20
    , testsPerDepth : 10000
    , incDepth      : incDepth
    };

  BlueCheck_Params params =
    BlueCheck_Params {
      verbose               : False
    , showNonFire           : False
    , showNoOp              : False
    , useIterativeDeepening : True
    , interactive           : True
    , useShrinking          : True
    , id                    : idParams
    , numIterations         : 2
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
