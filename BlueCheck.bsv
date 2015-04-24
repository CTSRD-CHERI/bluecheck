// BlueCheck 0.3, Matt N

import ModuleCollect :: *;
import StmtFSM       :: *;
import List          :: *;
import Clocks        :: *;
import FIFOF         :: *;
import ConfigReg     :: *;
import Vector        :: *;

// ============================================================================
// Module parameters
// ============================================================================

typedef struct {
  // Verbose output
  Bool verbose;

  // Display message when a chosen state does not fire
  Bool showNonFire;

  // Display message when a chosen state is a no-op
  Bool showNoOp;

  // Show the time of each displayed state
  Bool showTime;

  // Is the wedge-detector enabled?
  Bool wedgeDetect;

  // Generate a checker based on an iterative deepening strategy
  // (If 'False', a single random state walk is performed)
  Bool useIterativeDeepening;
  // This must contain valid data if 'useIterativeDeepening' is true
  ID_Params id; 

  // Interactive iterative deepening (simulation only, must be
  // disabled for synthesis)
  Bool interactive;

  // Attempt to shrink a counter example, if one is found
  // (This is only valid when 'useIterativeDeepening' is true)
  Bool useShrinking;

  // Number of testing iterations to perform. For iterative deepening,
  // this is the number of times to increase the depth before stopping
  // Otherwise, the it's the length of the random state walk
  Bit#(32) numIterations;

  // For synthesis, we use a FIFO for saving the state
  // of the checker, rather than a file on the local filesystem.
  Maybe#(FIFOF#(Bit#(8))) outputFIFO;
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

// ============================================================================
// States of the BlueCheck-generated checker
// ============================================================================

// The maximum number of states in the equivalance checker.
// You will get a compile-time error message if this parameter
// is not big enough, but it's not likely, unless you use very
// large method frequencies.

typedef 16 LogMaxStates;
typedef Bit#(LogMaxStates) State;

// The frequency that the checker will move to particular state.

typedef Integer Freq;

// ============================================================================
// BlueCheck collection data type
// ============================================================================

// A BlueCheck module implicitly collects various items that allow
// automatic creation of an equivalance checker.

typedef ModuleCollect#(Item) BlueCheck;
typedef ModuleCollect#(Item) Specification;

// BlueCheck modules collect items of the following type.

typedef union tagged {
  Tuple3#(Freq, App, Action) ActionItem;
  Tuple3#(Freq, App, Stmt) StmtItem;
  Tuple2#(Freq, List#(String)) ParItem;
  Action GenItem;
  List#(PRNG16) PRNGItem;
  Tuple2#(Fmt, Bool) InvariantItem;
  Tuple2#(Bool, Reg#(Bool)) EnsureItem;
  Tuple2#(App, Stmt) PreStmtItem;
  Tuple2#(App, Stmt) PostStmtItem;
  Classification ClassifyItem;
} Item;

// Functions for extracting items.

function List#(a) single(a x) = Cons(x, Nil);

function List#(Tuple3#(Freq, App, Action)) getActionItem(Item item) =
  item matches tagged ActionItem .x ? single(x) : Nil;

function List#(Tuple3#(Freq, App, Stmt)) getStmtItem(Item item) =
  item matches tagged StmtItem .x ? single(x) : Nil;

function List#(Tuple2#(Freq, List#(String))) getParItem(Item item) =
  item matches tagged ParItem .x ? single(x) : Nil;

function List#(Action) getGenItem(Item item) =
  item matches tagged GenItem .x ? single(x) : Nil;

function List#(PRNG16) getPRNGItem(Item item) =
  item matches tagged PRNGItem .xs ? xs : Nil;

function List#(Tuple2#(Fmt, Bool)) getInvariantItem(Item item) =
  item matches tagged InvariantItem .x ? single(x) : Nil;

function List#(Tuple2#(Bool, Reg#(Bool))) getEnsureItem(Item item) =
  item matches tagged EnsureItem .x ? single(x) : Nil;

function List#(Tuple2#(App, Stmt)) getPreStmtItem(Item item) =
  item matches tagged PreStmtItem .x ? single(x) : Nil;

function List#(Tuple2#(App, Stmt)) getPostStmtItem(Item item) =
  item matches tagged PostStmtItem .x ? single(x) : Nil;

function List#(Classification) getClassifyItem(Item item) =
  item matches tagged ClassifyItem .x ? single(x) : Nil;

// ============================================================================
// For displaying function applications
// ============================================================================

typedef struct {
  String name;
  List#(Fmt) args;
} App;

function String getName(App app) = app.name;

function Fmt formatApp(App app);
  if (app.args matches tagged Nil)
    return $format("%s", app.name);
  else 
    return ($format("%s", app.name) + fshow("(") +
            formatArgs(app.args) + fshow(")"));
endfunction

function Fmt formatArgs(List#(Fmt) args);
  if (List::tail(args) matches tagged Nil)
    return List::head(args);
  else
    return (List::head(args) + fshow(",") + formatArgs(List::tail(args)));
endfunction

function App appendArg(App app, Fmt arg) =
  App { name: app.name, args: List::append(app.args, Cons(arg, Nil)) };

// ============================================================================
// Psuedo-random number generation
// ============================================================================

// This is a slight variant of a standard 16-bit LCG.  The difference
// is that it mutates the seed when the period has elapsed.  The aim
// is to avoid synchronising with other LCGs that may exist, which
// could lead to cycles.

interface PRNG16;
  method Action seed(Bit#(32) s);
  method Action next;
  method Bit#(32) value;
  method Bit#(16) out;
endinterface

module mkPRNG16 (PRNG16);
  // State of the generator
  Reg#(Bit#(31)) state <- mkReg(0);

  // Signals from the methods to the following rule
  Wire#(Maybe#(Bit#(32))) seedWire <- mkDWire(Invalid);
  PulseWire nextWire               <- mkPulseWire;

  // The rule ('seed' takes priority over 'next')
  rule step;
    if (seedWire matches tagged Valid .s)
      state <= s[30:0];
    else if (nextWire)
      state <= state*1103515245 + 12345;
  endrule

  // Set the seed
  method Action seed(Bit#(32) s);
    seedWire <= tagged Valid s;
  endmethod

  // Output to use as psuedo-random number
  method Bit#(16) out = reverseBits(state[30:15]);

  // Obtain the current state
  method Bit#(32) value = {0, state};

  // Generate a new psuedo-random number
  method Action next;
    nextWire.send;
  endmethod
endmodule

// ============================================================================
// Generators
// ============================================================================

// Generate values of a given type.

interface Gen#(type t);
  method ActionValue#(t) gen;
endinterface

// The following standard generator works for any type in Bits and
// uses PRNGs to give psuedo-random data.

module [BlueCheck] mkGenDefault (Gen#(t))
  provisos (Bits#(t, n));
 
  // Number of 16-bit PRNGs needed.
  Integer numPRNGs = (valueOf(n)+15)/16;

  // Create as many 16-bit PRNGs as needed.
  PRNG16 prngs[numPRNGs];
  List#(PRNG16) list = Nil;
  for (Integer i = 0; i < numPRNGs; i=i+1) begin
    let prng <- mkPRNG16;
    prngs[i] = prng;
    list     = Cons(prng, list);
  end

  // Expose these PRNGs to BlueCheck (which will seed them).
  addToCollection(tagged PRNGItem list);

  // Generate a value using the PRNGs.
  method ActionValue#(t) gen;
    Bit#(n) x = 0;
    for (Integer i = 0; i < numPRNGs; i=i+1)
      prngs[i].next;

    Integer outer = 0;
    Integer inner = 0;
    for (Integer i = 0; i < valueOf(n); i=i+1) begin
      x[i] = prngs[outer].out[inner];
      if (inner == 15) begin
        outer = outer+1;
        inner = 0;
      end else
        inner = inner+1; 
    end
    return unpack(x);
  endmethod
endmodule

// ============================================================================
// MkGen class (like Arbitrary in QuickCheck)
// ============================================================================

// The MkGen class defines a generator for each type.

typeclass MkGen#(type t);
  module [BlueCheck] mkGen (Gen#(t));
endtypeclass

// Standard instances

instance MkGen#(void);
  mkGen = mkGenDefault;
endinstance

instance MkGen#(Bool);
  mkGen = mkGenDefault;
endinstance

instance MkGen#(Ordering);
  mkGen = mkGenDefault;
endinstance

instance MkGen#(Bit#(n));
  mkGen = mkGenDefault;
endinstance

instance MkGen#(Int#(n));
  mkGen = mkGenDefault;
endinstance

instance MkGen#(UInt#(n));
  mkGen = mkGenDefault;
endinstance

instance MkGen#(Maybe#(t)) provisos (MkGen#(t));
  module [BlueCheck] mkGen (Gen#(Maybe#(t)));
    Gen#(Bool) boolGen <- mkGen;
    Gen#(t)    tGen    <- mkGen;
    method ActionValue#(Maybe#(t)) gen;
      let v <- boolGen.gen;
      let x <- tGen.gen;
      return (v ? Valid(x) : Nothing);
    endmethod
  endmodule
endinstance

instance MkGen#(Vector#(n, t)) provisos (MkGen#(t));
  module [BlueCheck] mkGen (Gen#(Vector#(n, t)));
    Vector#(n, Gen#(t)) gens <- replicateM(mkGen);
    method ActionValue#(Vector#(n, t)) gen;
      Vector#(n, t) v;
      for (Integer i = 0; i < valueOf(n); i=i+1) begin
        let x <- gens[i].gen;
        v[i] = x;
      end
      return v;
    endmethod
  endmodule
endinstance

instance MkGen#(Tuple2#(a, b))
  provisos (MkGen#(a), MkGen#(b));
  module [BlueCheck] mkGen (Gen#(Tuple2#(a, b)));
    Gen#(a) aGen <- mkGen;
    Gen#(b) bGen <- mkGen;
    method ActionValue#(Tuple2#(a, b)) gen;
      let x <- aGen.gen;
      let y <- bGen.gen;
      return tuple2(x, y);
    endmethod
  endmodule
endinstance

instance MkGen#(Tuple3#(a, b, c))
  provisos (MkGen#(a), MkGen#(b), MkGen#(c));
  module [BlueCheck] mkGen (Gen#(Tuple3#(a, b, c)));
    Gen#(a) aGen <- mkGen;
    Gen#(b) bGen <- mkGen;
    Gen#(c) cGen <- mkGen;
    method ActionValue#(Tuple3#(a, b, c)) gen;
      let x <- aGen.gen;
      let y <- bGen.gen;
      let z <- cGen.gen;
      return tuple3(x, y, z);
    endmethod
  endmodule
endinstance

// Default instance.  If none of the above instances match a given
// type, we use the following default instance.  This instance
// exploits the "overlapping instances" feature and I'm still unsure
// as to whether we actually want it.

instance MkGen#(t)
  provisos (Bits#(t, n));

  module [BlueCheck] mkGen (Gen#(t));
    let gen <- mkGenDefault;
    return gen;
  endmodule
endinstance

// ============================================================================
// Adding properties
// ============================================================================

// Add a property to be checked.

typeclass Prop#(type a);
  module [BlueCheck] addProp#(Freq fr, App app, a f) ();
endtypeclass

// Short-hand for a unit frequency.

module [BlueCheck] prop#(String name, a f) ()
    provisos(Prop#(a));
  addProp(1, App { name: name, args: Nil}, f);
endmodule

// Short-hand for a specified frequency.

module [BlueCheck] propf#(Freq freq, String name, a f) ()
    provisos(Prop#(a));
  addProp(freq, App { name: name, args: Nil}, f);
endmodule

// Base case 1: an action.

instance Prop#(Action);
  module [BlueCheck] addProp#(Freq freq, App app, Action a) ();
    addToCollection(tagged ActionItem (tuple3(freq, app, a)));
  endmodule
endinstance

// Base case 2: a statement.

instance Prop#(Stmt);
  module [BlueCheck] addProp#(Freq freq, App app, Stmt s) ();
    addToCollection(tagged StmtItem (tuple3(freq, app, s)));
  endmodule
endinstance

// Base case 3: a boolean.

instance Prop#(Bool);
  module [BlueCheck] addProp#(Freq freq, App app, Bool b) ();
    Fmt msg = $format(formatApp(app), "\nProperty does not hold");
    addToCollection(tagged InvariantItem (tuple2(msg, b)));
  endmodule
endinstance

// Base case 4: an action-value returning a boolean.

instance Prop#(ActionValue#(Bool));
  module [BlueCheck] addProp#(Freq freq, App app, ActionValue#(Bool) a) ();
    Wire#(Bool) success <- mkDWire(True);
    Fmt msg = $format("Property does not hold");

    Action act =
      action
        Bool s <- a;
        if (!s) success <= False;
      endaction;

    addToCollection(tagged ActionItem (tuple3(freq, app, act)));
    addToCollection(tagged InvariantItem (tuple2(msg, success)));
  endmodule
endinstance

// Base case 5: an action-value returning some other type

instance Prop#(ActionValue#(t));
  module [BlueCheck] addProp#(Freq freq, App app, ActionValue#(t) a) ();
    Action act = action t s <- a; endaction;
    addToCollection(tagged ActionItem (tuple3(freq, app, act)));
  endmodule
endinstance

// Recursive case: generate input.

instance Prop#(function b f(a x))
  provisos(Prop#(b), Bits#(a, n), MkGen#(a), FShow#(a));
    module [BlueCheck] addProp#(Freq freq, App app, function b f(a x))();
      Reg#(a) aReg    <- mkRegU;
      Gen#(a) aRandom <- mkGen;

      Action genRandom =
        action
          let a <- aRandom.gen;
          aReg <= a;
        endaction;
      
      addToCollection(tagged GenItem genRandom);
      addProp(freq, appendArg(app, fshow(aReg)), f(aReg));
    endmodule
endinstance

// ============================================================================
// Adding equivalences
// ============================================================================

// Add an equivalence to be checked.

typeclass Equiv#(type a);
  module [BlueCheck] addEquiv#(Freq freq, App app, a f, a g) ();
endtypeclass

// Short-hand for a unit frequency.

module [BlueCheck] equiv#(String name, a f, a g) ()
    provisos(Equiv#(a));
  addEquiv(1, App { name: name, args: Nil}, f, g);
endmodule

// Short-hand for a specified frequency.

module [BlueCheck] equivf#(Freq freq, String name, a f, a g) ()
    provisos(Equiv#(a));
  addEquiv(freq, App { name: name, args: Nil}, f, g);
endmodule

// Base case 1: two actions.

instance Equiv#(Action);
  module [BlueCheck] addEquiv#(Freq fr, App app, Action a, Action b) ();
    Action both = action a; b; endaction;
    addToCollection(tagged ActionItem (tuple3(fr, app, both)));
  endmodule
endinstance

// Base case 2: two statements.

instance Equiv#(Stmt);
  module [BlueCheck] addEquiv#(Freq fr, App app, Stmt a, Stmt b) ();
    Stmt s = par a; b; endpar;
    addToCollection(tagged StmtItem (tuple3(fr, app, s)));
  endmodule
endinstance

// Base case 3: two action-values

instance Equiv#(ActionValue#(t))
  provisos(Eq#(t), Bits#(t, n), FShow#(t));
  module [BlueCheck] addEquiv#(Freq fr, App app
                                , ActionValue#(t) a
                                , ActionValue#(t) b) ();
    Wire#(Bool) success <- mkDWire(True);
    Wire#(t) aWire      <- mkDWire(?);
    Wire#(t) bWire      <- mkDWire(?);
    Fmt msg             =  fshow("Not equal: ") + fshow(aWire)
                        +  fshow(" versus ")    + fshow(bWire);

    Action check =
      action
        t aVal <- a; aWire <= aVal;
        t bVal <- b; bWire <= bVal;
        if (aVal != bVal) success <= False;
      endaction;

    addToCollection(tagged ActionItem (tuple3(fr, app, check)));
    addToCollection(tagged InvariantItem (tuple2(msg, success)));
  endmodule
endinstance

// Recursive case: generate input

instance Equiv#(function b f(a x))
  provisos(Equiv#(b), Bits#(a, n), MkGen#(a), FShow#(a));
    module [BlueCheck] addEquiv#(Freq freq, App app
                                          , function b f(a x)
                                          , function b g(a y)) ();
      Reg#(a) aReg    <- mkRegU;
      Gen#(a) aRandom <- mkGen;

      Action genRandom =
        action
          let a <- aRandom.gen;
          aReg <= a;
        endaction;
      
      addToCollection(tagged GenItem genRandom);
      addEquiv(freq, appendArg(app, fshow(aReg)), f(aReg), g(aReg));
    endmodule
endinstance

// Base case 4 (fall through): check that two values are equal

instance Equiv#(a) provisos(Eq#(a), FShow#(a));
  module [BlueCheck] addEquiv#(Freq fr, App app, a x, a y) ();
    Wire#(Bool) success <- mkDWire(True);
    Fmt fmt = formatApp(app) + fshow(" failed: ")
            + fshow(x) + fshow(" v ") + fshow(y);

    rule check;
      if (x != y) success <= False;
    endrule
     
    addToCollection(tagged InvariantItem (tuple2(fmt, success)));
  endmodule
endinstance

// ============================================================================
// Adding pre/post statements
// ============================================================================

// Pre or post statement?
typedef enum { PRE, POST } PreOrPost deriving (Eq);

// Add a property to be checked.

typeclass PrePost#(type a);
  module [BlueCheck] addPrePost#(PreOrPost p, App app, a f) ();
endtypeclass

// Short-hand for pre statement.

module [BlueCheck] pre#(String name, a f) ()
    provisos(PrePost#(a));
  addPrePost(PRE, App { name: name, args: Nil}, f);
endmodule

// Short-hand for post statement.

module [BlueCheck] post#(String name, a f) ()
    provisos(PrePost#(a));
  addPrePost(POST, App { name: name, args: Nil}, f);
endmodule

// Base case 1: an action.

instance PrePost#(Action);
  module [BlueCheck] addPrePost#(PreOrPost p, App app, Action a) ();
    Stmt s = seq a; endseq;
    addPrePost(p, app, s);
  endmodule
endinstance

// Base case 2: a statement.

instance PrePost#(Stmt);
  module [BlueCheck] addPrePost#(PreOrPost p, App app, Stmt s) ();
    if (p == PRE)
      addToCollection(tagged PreStmtItem (tuple2(app, s)));
    else
      addToCollection(tagged PostStmtItem (tuple2(app, s)));
  endmodule
endinstance

// Recursive case: generate input.

instance PrePost#(function b f(a x))
  provisos(PrePost#(b), Bits#(a, n), MkGen#(a), FShow#(a));
    module [BlueCheck] addPrePost#(PreOrPost p, App app, function b f(a x))();
      Reg#(a) aReg    <- mkRegU;
      Gen#(a) aRandom <- mkGen;

      Action genRandom =
        action
          let a <- aRandom.gen;
          aReg <= a;
        endaction;
      
      addToCollection(tagged GenItem genRandom);
      addPrePost(p, appendArg(app, fshow(aReg)), f(aReg));
    endmodule
endinstance

// ============================================================================
// For classifying test data
// ============================================================================

typedef struct {
  String name;
  Reg#(Bit#(32)) positive;
  Reg#(Bit#(32)) total;
} Classification;

typedef (function Action f(Bool cond)) Classifier;

module [BlueCheck] mkClassifier#(String text) (Classifier);
  // Create classify function
  Reg#(Bit#(32)) positive <- mkReg(0);
  Reg#(Bit#(32)) total    <- mkReg(0);
  Classification c;
  c.name     = text;
  c.positive = positive;
  c.total    = total;
  function Action classifyFunc(Bool cond) = 
    action total <= total+1; if (cond) positive <= positive+1; endaction;
  addToCollection(tagged ClassifyItem c);
  return classifyFunc;
endmodule

function Action displayClassifications(List#(Classification) cs) =
  action
    function Action f(Classification c) =
      action
        $display("%0d%%", (c.positive*100)/c.total, " ", c.name);
      endaction;
    let _ <- List::mapM(f, cs);
  endaction;

// ============================================================================
// Assertions
// ============================================================================

// 'ensure' functions allow assertions to be made inside actions or
// statements of properties or equivalences.

// Obtain a function to make assertions with.

typedef (function Action f(Bool cond)) Ensure;

module [BlueCheck] getEnsure (Ensure);
  // Create ensure function
  Wire#(Bool) ok <- mkDWire(True);
  Reg#(Bool) showMsg <- mkReg(False);
  function Action ensureFunc(Bool cond) = action ok <= cond; endaction;
  addToCollection(tagged EnsureItem (tuple2(ok, showMsg)));
  return ensureFunc;
endmodule

module [BlueCheck] mkEnsure (Ensure);
  Ensure ensure <- getEnsure;
  return ensure;
endmodule

// Similar to above, but the assertion function also takes a message
// to be displayed if the assertion fails.

typedef (function Action f(Bool cond, Fmt msg)) EnsureMsg;

module [BlueCheck] getEnsureMsg (EnsureMsg);
  // Create ensure function
  Wire#(Bool) ok <- mkDWire(True);
  Reg#(Bool) showMsg <- mkReg(False);
  function Action ensureFunc(Bool cond, Fmt msg) =
    action ok <= cond; if (!cond && showMsg) $display(msg); endaction;
  addToCollection(tagged EnsureItem (tuple2(ok, showMsg)));
  return ensureFunc;
endmodule

// ============================================================================
// Parallel properties
// ============================================================================

// Specify that a list of equivalences/properties can run in parallel.

module [BlueCheck] parallel#(List#(String) names) (Empty);
  addToCollection(tagged ParItem (tuple2(1, names)));
endmodule

module [BlueCheck] parallelf#(Freq fr, List#(String) names) (Empty);
  addToCollection(tagged ParItem (tuple2(fr, names)));
endmodule

// ============================================================================
// Friendly list construction
// ============================================================================

// The following type-class allows convenient construction of lists, e.g.
//
//   List#(String) xs = list("push", "pop", "top");

typeclass MkList#(type a, type b) dependencies (a determines b);
  function a mkList(List#(b) acc);
endtypeclass

instance MkList#(List#(a), a);
  function List#(a) mkList(List#(a) acc) = List::reverse(acc);
endinstance

instance MkList#(function b f(a elem), a) provisos (MkList#(b, a));
  function mkList(acc, elem) = mkList(Cons(elem, acc));
endinstance

function b list() provisos (MkList#(b, a));
  return mkList(Nil);
endfunction

// ============================================================================
// Misc functions
// ============================================================================

// Is a list empty?

function Bool isEmpty(List#(a) xs);
  if (xs matches tagged Nil) return True; else return False;
endfunction

// Function for assigning a value to a register.

function Action assignReg(t x, Reg#(t) r) = action r <= x; endaction;

// Function to sum a list.

function Integer sum(List#(Integer) xs);
  if (xs matches tagged Nil) return 0;
  else return (List::head(xs) + sum(List::tail(xs)));
endfunction

// Sequence a list of statements.

function Stmt seqList(Bool show, List#(Tuple2#(App, Stmt)) xs);
  if (xs matches tagged Nil)
    return (seq delay(1); endseq);
  else begin
    let t   = List::head(xs);
    let app = tpl_1(t);
    Stmt s  =
      seq
        action if (show && app.name != "") $display(formatApp(app)); endaction
        tpl_2(t);
      endseq;
    return (seq s; seqList(show, List::tail(xs)); endseq);
  end
endfunction

// ============================================================================
// ASCII encoding/decoding
// ============================================================================

// For transferring data over the UART, we encode each 4-bit nibble as
// a ASCII hex digit.

function Bit#(8) hexEncode(Bit#(4) x);
  Bit#(8) y = x <= 9 ? 48 : 55;
  return y+extend(x);
endfunction

function Bit#(4) hexDecode(Bit#(8) x);
  Bit#(8) y = x >= 65 ? 55 : 48;
  return (x-y)[3:0];
endfunction

// ============================================================================
// File I/O
// ============================================================================

function Action putHalfWord(File f, Bit#(16) data) =
  action
    $fwrite(f, "%c", hexEncode(data[15:12]));
    $fwrite(f, "%c", hexEncode(data[11:8]));
    $fwrite(f, "%c", hexEncode(data[7:4]));
    $fwrite(f, "%c", hexEncode(data[3:0]));
  endaction;

function ActionValue#(Bit#(16)) getHalfWord(File f) =
  actionvalue
    Bit#(16) x;
    int c0 <- $fgetc(f);
    int c1 <- $fgetc(f);
    int c2 <- $fgetc(f);
    int c3 <- $fgetc(f);
    x[15:12] = hexDecode(pack(c0)[7:0]);
    x[11:8]  = hexDecode(pack(c1)[7:0]);
    x[7:4]   = hexDecode(pack(c2)[7:0]);
    x[3:0]   = hexDecode(pack(c3)[7:0]);
    return x;
  endactionvalue;

function Action putWord(File f, Bit#(32) data) =
  action
    putHalfWord(f, data[31:16]);
    putHalfWord(f, data[15:0]);
  endaction;

function ActionValue#(Bit#(32)) getWord(File f) =
  actionvalue
    Bit#(16) x <- getHalfWord(f);
    Bit#(16) y <- getHalfWord(f);
    return {x, y};
  endactionvalue;

// The filename used to store a counter-example on the filesystem.

String filename = "State.txt";

// ============================================================================
// Rotating Queue
// ============================================================================

// Each PRNG has a 'shadow register'.  These shadow registers can be
// used to save or restore the state of all the PRNGs.  Since we want
// to be able to easily serialise this state, for transfer to a file
// or over a UART, we using the following rotating queue structure.

// A rotating queue is a list of registers with support for:
//   * inserting (by rotation) an element at one end
//   * reading (by rotation) an element from the other end
//   * loading and storing the values of all the registers

interface RotatingQueue#(type t);
  method Action put(t in);
  method ActionValue#(t) get;
  method List#(t) load;
  method Action store(List#(t) inputs);
endinterface

module [Module] mkRotatingQueue#(Integer size) (RotatingQueue#(t))
                  provisos (Bits#(t, n));

  // Registers
  // ---------

  List#(Reg#(t)) regs <- List::replicateM(size, mkRegU);

  // Wires
  // -----

  Wire#(Bool)        rotWire  <- mkDWire(False);
  Wire#(Maybe#(t))   putWire  <- mkDWire(Invalid);
  Wire#(Bool)        loadWire <- mkDWire(False);
  List#(Wire#(t))    loadVals <- List::replicateM(size, mkDWire(?));

  // Rules
  // -----

  rule rotate (rotWire || loadWire);
    t insert;
    if (putWire matches tagged Valid .x)
      insert = x;
    else
      insert = readReg(List::last(regs));

    List#(Reg#(t))  rs = regs;
    List#(Wire#(t)) vs = loadVals;
    for (Integer i = 0; i < size; i=i+1) begin
      if (loadWire)
        rs[0] <= vs[0];
      else
        rs[0] <= insert;
      insert = rs[0];
      rs     = List::tail(rs);
      vs     = List::tail(vs);
    end
  endrule

  // Methods
  // -------

  method Action put(t x);
    putWire <= tagged Valid x;
    rotWire <= True;
  endmethod

  method ActionValue#(t) get;
    rotWire <= True;
    return readReg(List::last(regs));
  endmethod

  method List#(t) load = List::map(readReg, regs);

  method Action store(List#(t) inputs);
    function Action f(Wire#(t) w, t x) = action w <= x; endaction;
    let _ <- List::zipWithM(f, loadVals, inputs);
    loadWire <= True;
  endmethod

endmodule

// ============================================================================
// State conditions
// ============================================================================

// Compute the condition for being in each state of the equivalance
// checker. Some states are visited more frequently than others.

function List#(Bool) stateConds(Reg#(State) s, Integer start,
                                         List#(Freq) freqs);
  if (freqs matches tagged Nil) return Nil;
  else
    begin
      Freq f = List::head(freqs);
      Bool cond;
      if (f == 1) cond = s == fromInteger(start);
      else cond = s >= fromInteger(start) && s < fromInteger(start+f);
      return (Cons(cond, stateConds(s, start+f, List::tail(freqs))));
    end
endfunction

// With the presence of 'parallel' statements, it is possible to be in
// multiple states at the same time, i.e. multiple properties are
// being checked on the same cycle.  The following function will
// update the 'inState' mapping using the 'parallel' lists.

function List#(Bool) mergeConds
  ( List#(Bool) inState
  , List#(String) stateNames
  , List#(Bool) inStatePar
  , List#(List#(String)) parLists
  );

  if (inState matches tagged Nil)
    return Nil;
  else begin
    Bool cond            = List::head(inState);
    String stateName     = List::head(stateNames);
    let origInStatePar   = inStatePar;
    let origParLists     = parLists;

    while (! isEmpty(inStatePar)) begin
      let condPar = List::head(inStatePar);
      let parList = List::head(parLists);

      if (List::elem(stateName, parList))
        cond = cond || condPar;

      inStatePar = List::tail(inStatePar);
      parLists   = List::tail(parLists);
    end

    return Cons(cond, mergeConds( List::tail(inState)
                                , List::tail(stateNames)
                                , origInStatePar, origParLists ));
  end
endfunction

// ============================================================================
// Bounding psuedo-random numbers
// ============================================================================

// Bound a given number using the specified maximum value 'm'.  This
// function is cheaper to compute that modulus divide, but has a worse
// distribution: after bounding, some values are two times more likely
// to appear than others.

function Bit#(n) bound(Bit#(n) x, Integer m);
  Integer top = 2 ** log2(m+1);
  let y = x & fromInteger(top-1);
  return (y > fromInteger(m) ? y - fromInteger(m+1) : y);
endfunction

// ============================================================================
// Max sequence length
// ============================================================================

// When shrinking is enabled, the length of the sequences generated
// must be bounded.

Integer maxSeqLen = 64;

// ============================================================================
// Communication from FPGA to host PC
// ============================================================================

// For communication from FPGA to host PC, we use an Avalon
// memory-mapped interface to Altera's JTAG UART.  This section of
// code is specific to Altera FPGAs, but should be easy to port to
// other devices.

interface JtagUart;
  (* always_ready *)
  method Bit#(3)  uart_address;
  (* always_ready *)
  method Bit#(32) uart_writedata;
  (* always_ready *)
  method Bool uart_write;
  (* always_ready *)
  method Bool uart_read;
  (* always_enabled *)
  method Action uart(Bool uart_waitrequest,
                     Bit#(32) uart_readdata);
endinterface

// Given a FIFO of bytes to send to the host PC, return an interface
// to Altera's JTAG UART.

module mkJtagUart#(FIFOF#(Bit#(8)) fifo) (JtagUart);
  Reg#(Bool) reading <- mkReg(True);
  method Bit#(3)  uart_address   = reading ? 4 : 0;
  method Bit#(32) uart_writedata = extend(fifo.first);
  method Bool     uart_write     = !reading && fifo.notEmpty;
  method Bool     uart_read      = reading;
  method Action   uart(Bool     uart_waitrequest,
                       Bit#(32) uart_readdata);
    if (reading) begin
      if (!uart_waitrequest)
        if (uart_readdata[31:16] > 0) reading <= False;
    end else
      if (!uart_waitrequest && fifo.notEmpty) begin
        fifo.deq;
        reading <= True;
      end
  endmethod
endmodule

// ============================================================================
// Construct model checker
// ============================================================================

// Turn the list of items gathered in a BlueCheck module into an
// actual model checker.

module [Module] mkModelChecker#( BlueCheck#(Empty) bc
                               , BlueCheck_Params params ) (Stmt);

  // Read any flags from the command-line
  // ------------------------------------

  // Resume testing from a point specified by a file of PRNG seeds
  Reg#(Bool) resumeFlag <- mkReg(False);
  Reg#(Bool) resumed    <- mkReg(False);

  // True once command-line args have been read
  Reg#(Bool) gotPlusArgs <- mkReg(False);

  rule readPlusArgs (!gotPlusArgs);
    let b0 <- $test$plusargs("replay"); // For backwards-compatibility
    let b1 <- $test$plusargs("resume");
    resumeFlag  <= b0 || b1;
    gotPlusArgs <= True;
  endrule

  // Enable/disable display statements
  Reg#(Bool) verbose      <- mkReg(params.verbose);

  // Extract items from BlueCheck collection
  // ---------------------------------------

  let concat = List::concat;
  let map    = List::map;
  let append = List::append;
  let zip    = List::zip;
  let {_, items} <- getCollection(bc);
  let actionItems    = concat(map(getActionItem, items));
  let stmtItems      = concat(map(getStmtItem, items));
  let randomGens     = concat(map(getGenItem, items));
  let ensureItems    = concat(map(getEnsureItem, items));
  let invariantBools = concat(map(getInvariantItem, items));
  let classifyItems  = concat(map(getClassifyItem, items));
  let preStmt        = seqList(verbose, concat(map(getPreStmtItem, items)));
  let postStmt       = seqList(verbose, concat(map(getPostStmtItem, items)));
  let prngItems      = concat(map(getPRNGItem, items));
  let actionApps     = map(tpl_2, actionItems);
  let stmtApps       = map(tpl_2, stmtItems);
  let actionMsgs     = map(formatApp, actionApps);
  let stmtMsgs       = map(formatApp, stmtApps);
  let actions        = map(tpl_3, actionItems);
  let stmts          = map(tpl_3, stmtItems);
  let ensureBools    = map(tpl_1, ensureItems);
  let ensureShows    = map(tpl_2, ensureItems);
  let actionNames    = map(getName, actionApps);
  let stmtNames      = map(getName, stmtApps);
  let actionFreqs    = map(tpl_1, actionItems);
  let stmtFreqs      = map(tpl_1, stmtItems);
  let parItems       = concat(map(getParItem, items));
  let parFreqs       = map(tpl_1, parItems);
  let parLists       = map(tpl_2, parItems);

  // State machine for equivalence checking
  // (Note: state 0 is a no-op state)
  // --------------------------------------

  List#(Integer) freqs    =  append(actionFreqs, stmtFreqs);
  List#(Integer) allFreqs =  append(freqs, parFreqs);
  Integer sumFreqs        =  sum(freqs);
  Integer numStates       =  1+sumFreqs+sum(parFreqs);
  PRNG16 stateGen         <- mkPRNG16;
  List#(PRNG16) prngs     =  Cons(stateGen, prngItems);
  Integer numPRNGs        =  List::length(prngs);
  ConfigReg#(State) state <- mkConfigReg(0);
  PulseWire waitWire      <- mkPulseWireOR;
  PulseWire didFire       <- mkPulseWireOR;
  Reg#(Bool) testDone     <- mkReg(False);
  List#(Bool) inStateSeq  =  stateConds(state, 1, freqs);
  List#(Bool) inStatePar  =  stateConds(state, 1+sumFreqs, parFreqs);
  List#(Bool) inState     =  mergeConds(inStateSeq,
                               append(actionNames, stmtNames),
                               inStatePar, parLists);
  Reg#(File) seedFile     <- mkReg(InvalidFile);
  Reg#(Bit#(32)) currentDepth <- mkReg(0);
  Reg#(Bool) prePostActive <- mkReg(False);

  // Wedge detector: count consecutive non-firings
  Reg#(Bit#(16)) consecutiveNonFires <- mkReg(0);

  // When count is 0, actions/statements are disabled
  // ------------------------------------------------

  ConfigReg#(Bit#(32)) count <- mkConfigReg(0);
  Bool actionsEnabled = count != 0;

  // When delayed count is 0, invariant checking is disabled
  // -------------------------------------------------------

  ConfigReg#(Bit#(32)) delayedCount <- mkConfigReg(0);
  Bool checkingEnabled = delayedCount != 0;

  rule updateDelayedCount;
    delayedCount <= count;
  endrule

  // Keep track of failures
  // ----------------------

  Reg#(Bool) failureReg    <- mkConfigReg(False);
  Wire#(Bool) resetFailure <- mkDWire(False);
  PulseWire wedgeFailure   <- mkPulseWireOR;
  Bool ensureFailure       =  List::any( \== (False), ensureBools);
  Bool invariantFailure    = (waitWire || !checkingEnabled) ? False
                           : List::any( \== (False),
                                        map (tpl_2, invariantBools));
  Bool failureFound        = ensureFailure
                          || invariantFailure
                          || wedgeFailure
                          || failureReg;
  
  rule trackFailure;
    if (resetFailure)
      failureReg <= False;
    else if (ensureFailure || invariantFailure || wedgeFailure)
      failureReg <= True;
  endrule

  // Timer
  // -----

  Reg#(Bit#(32)) timer <- mkReg(0);
  Wire#(Bool) resetTimer <- mkDWire(False);
  Fmt timeInfo = params.showTime ? $format("%0t: ", timer) : $format("");

  rule incTimer;
    if (resetTimer)
      timer <= 0;
    else
      timer <= timer+1;
  endrule

  // Seed the random generators
  // --------------------------

  Reg#(Bool) seeded <- mkReg(False);

  rule seedPRNGs (!seeded);
    for (Integer i = 0; i < numPRNGs; i=i+1)
      prngs[i].seed(fromInteger(i+1));
    seeded <= True;
  endrule

  // Generate rules to generate random data
  // --------------------------------------

  PulseWire savePRNGs     <- mkPulseWire;
  PulseWire restorePRNGs  <- mkPulseWire;

  Integer numRandomGens = length(randomGens);
  for (Integer i = 0; i < numRandomGens; i=i+1)
    begin
      rule genRandomData (seeded && !waitWire && !prePostActive
                                 && !restorePRNGs && !savePRNGs);
        randomGens[i];
      endrule
    end

  // Rule to check 'ensure' assertions
  // ---------------------------------

  rule checkEnsure (!failureReg && List::any( \== (False) , ensureBools));
    if (verbose) $display(timeInfo, "'ensure' statement failed");
  endrule

  // Generate rules to check invariants
  // ----------------------------------

  Integer numInvBools = length(invariantBools);
  for (Integer i = 0; i < numInvBools; i=i+1)
    begin
      let msg = tpl_1(invariantBools[i]);
      let b   = tpl_2(invariantBools[i]);
      rule checkInvariantBool (checkingEnabled && !failureReg && !waitWire);
        if (!b && verbose) $display(timeInfo, msg);
      endrule
    end

  // Generate rules to run actions, guarded by the current state
  // -----------------------------------------------------------

  Integer numActions = length(actions);
  for (Integer i = 0; i < numActions; i=i+1)
    begin
      (* preempts = "runAction, runActionNotPossible" *)
      rule runAction (actionsEnabled && inState[i] && !waitWire);
        if (verbose) $display(timeInfo, actionMsgs[i]);
        actions[i];
        didFire.send;
      endrule
      rule runActionNotPossible (actionsEnabled && inState[i] && !waitWire
                                   && params.showNonFire);
        if (verbose)
          $display(timeInfo, "[did not fire] ", actionMsgs[i]);
      endrule
    end

  // Wedge detector
  // --------------

  rule wedgeDetect (params.wedgeDetect && actionsEnabled && !waitWire);
    if (didFire)
      consecutiveNonFires <= 0;
    else begin
      if (consecutiveNonFires == 10000)
        begin
          if (verbose) $display("\nWedge detected\n");
          consecutiveNonFires <= 0;
          wedgeFailure.send;
        end
     else
        consecutiveNonFires <= consecutiveNonFires+1;
    end
  endrule

  // Generate rules to run statements, guarded by the current state
  // --------------------------------------------------------------

  // Statements may take many cycles, hence 'waitWire'.

  Integer numStmts = length(stmts);
  for (Integer i = 0; i < numStmts; i=i+1)
    begin
      Integer s = length(actions)+i;
      Reg#(Bool) fsmRunning <- mkReg(False);
      FSM fsm <- mkFSMWithPred(stmts[i], actionsEnabled && inState[s]);

      rule runStmt (actionsEnabled && inState[s] && !fsmRunning);
        if (verbose) $display(timeInfo, stmtMsgs[i]);
        fsm.start;
        fsmRunning <= True;
        waitWire.send;
        consecutiveNonFires <= 0;
      endrule

      rule assertWait (actionsEnabled && inState[s] && fsmRunning && !fsm.done);
        waitWire.send;
      endrule

      rule finishStmt (actionsEnabled && inState[s] && fsmRunning && fsm.done);
        fsmRunning <= False;
        didFire.send;
      endrule
    end

  // Show classifications
  // --------------------

  Action showClassifications = displayClassifications(classifyItems);

  // No-op state
  // -----------

  rule noOp (actionsEnabled && state == 0);
    if (params.showNoOp && verbose) $display(timeInfo, "No-op");
    if (numStates == 1) didFire.send;
  endrule

  // PRNGs: loading, storing, saving, and restoring
  // ----------------------------------------------

  RotatingQueue#(Bit#(32)) shadows <- mkRotatingQueue(numPRNGs);
  Reg#(Bit#(32)) iterCount         <- mkReg(0);
  Reg#(Bool) loopDone              <- mkReg(False);

  // Copy the value of each PRNG to the corresponding shadow register

  rule ruleSavePRNGs (savePRNGs);
    function Bit#(32) f(PRNG16 x) = x.value;
    shadows.store(List::map(f, prngs));
  endrule

  // Copy the value of each shadow register the to corresponding PRNG

  rule ruleRestorePRNGs (seeded && !actionsEnabled && restorePRNGs);
    function Action f(PRNG16 x, Bit#(32) y) = x.seed(y);
    let _ <- List::zipWithM(f, prngs, shadows.load);
  endrule

  // Load a file of seeds into the shadow PRNGs

  Stmt loadFromFile = 
    seq
      action
        $display("Loading state from '%s'", filename);

        // Open file for reading
        let file <- $fopen(filename, "r");

        // Check result
        if (file == InvalidFile) begin
          $display("Can't open file '%s'", filename);
          $finish(0);
        end
        seedFile <= file;

        // Ignore first character
        let _  <- $fgetc(file);

        // Read depth
        let d <- getWord(file);
        currentDepth <= d;

        // Initialise
        loopDone <= False;
        iterCount <= 0;
      endaction

      while (!loopDone)
        action
          let x <- getWord(seedFile);
          shadows.put(x);

          // Increment loop counter
          iterCount <= iterCount+1;
          if (iterCount+1 == fromInteger(numPRNGs)) loopDone <= True;
        endaction

      // Close file
      $fclose(seedFile);
    endseq;

  // Store the values of the shadow PRNGs to a file

  function Stmt storeToFile(Bit#(32) depth) =
    seq
      action
        $write("\nSaving state to '%s'", filename);

        // Open file for writing
        let file <- $fopen(filename, "w");

        // Check result
        if (file == InvalidFile) begin
          $display("Can't open file '%s'", filename);
          $finish(0);
        end
        seedFile <= file;

        // Write single char: '1' if counter-example found; '0' otherwise
        $fwrite(file, failureFound ? "1" : "0");

        // Write depth
        putWord(file, depth);

        // Initialise
        loopDone <= False;
        iterCount <= 0;
      endaction

      while (!loopDone)
        action
          let x <- shadows.get;
          putWord(seedFile, x);

          // Increment loop counter
          iterCount <= iterCount+1;
          if (iterCount+1 == fromInteger(numPRNGs)) loopDone <= True;
        endaction

      // Close file
      $fclose(seedFile);
    endseq;

  // Store the values of the shadow PRNGs to a FIFO

  Reg#(Bit#(32)) tmpReg     <- mkReg(0);
  Reg#(Bit#(4)) nibbleCount <- mkReg(0);

  function Stmt storeToFIFO(FIFOF#(Bit#(8)) fifo, Bit#(32) depth) =
    seq
      action
        // Write single char: '1' if counter-example found; '0' otherwise
        await(fifo.notFull);
        fifo.enq(failureFound ? 49 : 48);

        // Initialise
        loopDone <= False;
        iterCount <= 0;
        nibbleCount <= 0;
        tmpReg <= depth;
      endaction

      while (nibbleCount <= 7)
        action
          await(fifo.notFull);
          fifo.enq(hexEncode(tmpReg[31:28]));
          tmpReg <= tmpReg << 4;
          nibbleCount <= nibbleCount+1;
        endaction

      while (!loopDone)
        seq
          action
            let x <- shadows.get;
            tmpReg <= {0, x};
            nibbleCount <= 0;
          endaction

          while (nibbleCount <= 7)
            action
              await(fifo.notFull);
              fifo.enq(hexEncode(tmpReg[31:28]));
              tmpReg <= tmpReg << 4;
              nibbleCount <= nibbleCount+1;
            endaction

          action
            // Increment loop counter
            iterCount <= iterCount+1;
            if (iterCount+1 == fromInteger(numPRNGs)) loopDone <= True;
          endaction
        endseq
    endseq;

  // Store the values of the shadow PRNGs to file or FIFO, depending
  // on module parameters.

  function Stmt storeToOutput(Bit#(32) depth);
    if (params.outputFIFO matches tagged Valid .fifo)
      return storeToFIFO(fifo, depth);
    else
      return storeToFile(depth);
  endfunction

  // Single walk of the state space
  // ------------------------------

  Stmt singleWalk =
    seq
      // Initialise
      action
        await(seeded);
        testDone   <= False;
        resetTimer <= True;

        // Show 'ensure' failure messages?
        let _ <- List::mapM(assignReg(True), ensureShows);
      endaction

      prePostActive <= True;
      preStmt;
      prePostActive <= False;

      count <= 1;
      while (!testDone)
        action
          await(!waitWire);
          stateGen.next;
          let nextState = bound(stateGen.out, numStates-1);
          if (failureFound)
            begin
              count <= 0;
              testDone <= True;
            end
          else
            begin
              state <= nextState;
              if (didFire)
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

      prePostActive <= True;
      postStmt;
      prePostActive <= False;

      if (!failureFound)
        action
          $display("OK: passed %0d iterations", params.numIterations);
          showClassifications;
        endaction
      action
        if (params.outputFIFO matches tagged Valid .fifo)
          fifo.enq(failureFound ? 49 : 48);
      endaction
    endseq;

  // Replay a counter-example
  // ------------------------

  Reg#(Bit#(32)) counterExampleLen  <- mkReg(0);
  FIFOF#(Maybe#(Bit#(32))) timeFIFO <- mkSizedFIFOF(maxSeqLen);
  Reg#(Bit#(32)) omitNum            <- mkReg(0);
  Reg#(Maybe#(Bit#(32))) deleteNum  <- mkReg(Invalid);

  Stmt replay =
    seq
      // Reset the circuit under test
      params.id.rst.assertReset();

      // Initialisation
      action
        resetFailure <= True;
        resetTimer   <= True;
        state        <= 0;
        restorePRNGs.send;
      endaction

      // Test sequence starts here
      delay(1);
      prePostActive <= True;
      preStmt;
      prePostActive <= False;

      delay(1);
      while (count < counterExampleLen)
        action
          await(!waitWire);
          if (timeFIFO.first matches tagged Valid .t) begin
            if (timer >= t) begin
              timeFIFO.deq;
              if (deleteNum != tagged Valid count) begin
                timeFIFO.enq(timeFIFO.first);
                if (omitNum != count)
                  state <= bound(stateGen.out, numStates-1);
                else
                  state <= 0;
              end else begin
                timeFIFO.enq(Invalid);
                state <= 0;
              end
              count <= count+1;
            end else
              state <= 0;
          end else begin
            timeFIFO.deq;
            timeFIFO.enq(Invalid);
            count <= count+1;
            state <= 0;
          end
          stateGen.next;
        endaction

      action
        await(!waitWire);
        count <= 0;
      endaction

      prePostActive <= True;
      postStmt;
      prePostActive <= False;
    endseq;

  // Shrink a counter-example
  // ------------------------

  Stmt shrink =
    seq
      // Initialise shrinker
      action
        omitNum   <= 0;
        deleteNum <= Invalid;
      endaction

      // Try to omit each element of the failing sequence, and
      // if it succeeds, undo the omission.
      while (omitNum <= counterExampleLen)
        seq
          action
            if (verbose) $display("=== Shrink attempt %0d ===", omitNum);
            // Display counter example even if verbose == False
            if (!verbose && omitNum == counterExampleLen)
              begin
                verbose <= True;
                let _ <- List::mapM(assignReg(True), ensureShows);
                $display("");
              end
          endaction

          // Replay counter-example with omission
          replay;

          // If failure remains, make omission permanenent
          if (failureFound)
            deleteNum <= tagged Valid omitNum;
          else
            deleteNum <= Invalid;
          omitNum <= omitNum+1;
        endseq

      // Restore original settings
      action
        verbose <= params.verbose;
        let _ <- List::mapM(assignReg(params.verbose), ensureShows);
      endaction
    endseq;

  // Iterative deepening
  // -------------------

  // State for iterative-deepening
  Reg#(Bit#(32)) testNum           <- mkReg(0);
  Reg#(Bit#(32)) startTime         <- mkReg(0);

  Stmt iterativeDeepening =
    seq
      // Initialisation
      action
        resetFailure <= True;
        iterCount <= 0;

        // When not using shrinking, enable output
        if (! params.useShrinking) begin
          verbose <= True;
          let _ <- List::mapM(assignReg(True), ensureShows);
        end
      endaction

      // Each iteration will produce N test sequences of size 'depth'.
      // After each iteration, the depth is increased.
      if (! resumeFlag)
        currentDepth <= params.id.initialDepth;
      while (!failureFound && iterCount < params.numIterations)
        seq
          // Check that the depth is OK
          if (params.useShrinking &&
            currentDepth >= fromInteger(maxSeqLen)) seq
            $display("Max depth of %0d", maxSeqLen-1, " exceeded.");
            $display("Increase the 'maxSeqLen' parameter in BlueCheck.bsv.");
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
                counterExampleLen <= currentDepth;
                resetTimer <= True;
                state <= 0;
                if (params.useShrinking) timeFIFO.clear;
                if (resumeFlag && !resumed)
                  begin restorePRNGs.send; resumed <= True; end
                else
                  savePRNGs.send;
              endaction

              // Test sequence starts here
              delay(1);
              prePostActive <= True;
              preStmt;   // Execute user-defined pre-statement
              prePostActive <= False;

              count <= 1;
              while (!testDone)
                action
                  // This action only fires when not waiting for a
                  // user-defined statement to finish.
                  await(!waitWire);
                  stateGen.next;
                  let nextState = bound(stateGen.out, numStates-1);
                  if (didFire && params.useShrinking)
                    timeFIFO.enq(tagged Valid (startTime));
                  if (failureFound)
                    begin
                      // We found a counter example smaller than the depth
                      counterExampleLen <= didFire ? count : count-1;
                      count <= 0;
                      testDone <= True;
                    end
                  else
                    begin
                      // Change the state for the next clock cycle
                      state <= nextState;
                      startTime <= timer;
                      if (didFire)
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

              prePostActive <= True;
              postStmt; // Execute user-defined post-statement
              prePostActive <= False;

              testNum <= testNum+1;
            endseq

          if (!failureFound) action
            $display("");
            currentDepth <= params.id.incDepth(currentDepth);
            iterCount <= iterCount+1;
          endaction
        endseq

      // Save the state of the PRNGs so we can resume testing later
      // from this point.
      storeToOutput(currentDepth);

      // We've reached the end of iterative deepening.  Either we
      // found a failure or performed the desired number of tests.
      if (!failureFound)
        action
          $display("\nOK: passed %0d test sequences",
                     params.numIterations*params.id.testsPerDepth);
          showClassifications;
        endaction
      else seq
        if (params.useShrinking)
          shrink;
        else
          $display("\nFAILED: counter-example found");
      endseq
    endseq;

  // Iterative deepening (with iteraction)
  // -------------------------------------

  Reg#(Bool) doneUI <- mkReg(False);

  Stmt iterativeDeepeningUI =
    seq
      action
        // Show ensure-failure messages?
        let _ <- List::mapM(assignReg(params.verbose), ensureShows);
      endaction

      // Initialise the random generators
      await(seeded);

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

  // Top-level iterative deepening checker for simulation
  // ----------------------------------------------------

  Stmt iterativeDeepeningTop =
    seq
      await(gotPlusArgs);
      if (resumeFlag) loadFromFile;
      iterativeDeepeningUI;
    endseq;

  // Result of module
  // ----------------

  return params.useIterativeDeepening
       ? iterativeDeepeningTop : singleWalk;
endmodule

// ============================================================================
// Default parameters for single state-space walk
// ============================================================================

BlueCheck_Params bcParams =
  BlueCheck_Params {
    verbose               : True
  , showNonFire           : False
  , showNoOp              : False
  , showTime              : False
  , wedgeDetect           : False
  , useIterativeDeepening : False
  , interactive           : False
  , useShrinking          : False
  , id                    : ?
  , numIterations         : 1000
  , outputFIFO            : Invalid
  };

// ============================================================================
// Default parameters for iterative deepening
// ============================================================================

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
    , showTime              : True
    , wedgeDetect           : False
    , useIterativeDeepening : True
    , interactive           : True
    , useShrinking          : True
    , id                    : idParams
    , numIterations         : 2
    , outputFIFO            : Invalid
    };

  return params;
endfunction

// ============================================================================
// Variants of the model-checker generator
// ============================================================================

// Simple version returning a statement
module [Module] blueCheckStmt#(BlueCheck#(Empty) bc)(Stmt);
  Stmt s <- mkModelChecker(bc, bcParams);
  return s;
endmodule

// Simple version that constructs a checker
module [Module] blueCheck#(BlueCheck#(Empty) bc)();
  Stmt s <- blueCheckStmt(bc);
  mkAutoFSM(s);
endmodule

// Simple version that constructs a synthesisable checker
module [Module] blueCheckSynth#(BlueCheck#(Empty) bc) (JtagUart);
  FIFOF#(Bit#(8)) out <- mkUGFIFOF;
  let params           = bcParams;
  params.interactive   = False;
  params.outputFIFO    = tagged Valid out;
  JtagUart uart       <- mkJtagUart(out);
  Stmt s              <- mkModelChecker(bc, params);
  mkAutoFSM(s);
  return uart;
endmodule

// Iterative deepening version returning a statement
module [Module] blueCheckStmtID# (BlueCheck#(Empty) bc
                                , MakeResetIfc rst ) (Stmt);
  Stmt s <- mkModelChecker(bc, bcParamsID(rst));
  return s;
endmodule

// Iterative deepening version that constructs a checker
module [Module] blueCheckID#( BlueCheck#(Empty) bc
                            , MakeResetIfc rst ) ();
  Stmt s <- blueCheckStmtID(bc, rst);
  mkAutoFSM(s);
endmodule

// Iterative deepening version that constructs a synthesisable checker
module [Module] blueCheckIDSynth#( BlueCheck#(Empty) bc
                                 , MakeResetIfc rst) (JtagUart);
  FIFOF#(Bit#(8)) out <- mkUGFIFOF;
  let params           = bcParamsID(rst);
  params.interactive   = False;
  params.outputFIFO    = tagged Valid out;
  params.useShrinking  = False;
  JtagUart uart       <- mkJtagUart(out);
  Stmt s              <- mkModelChecker(bc, params);
  mkAutoFSM(s);
  return uart;
endmodule
