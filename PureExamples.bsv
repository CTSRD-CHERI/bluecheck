import BlueCheck :: *;

// ============================================================================
// Basic arithmetic properties
// ============================================================================

module [BlueCheck] mkArithSpec ();
  function Bool addComm(Int#(4) x, Int#(4) y) =
    x + y == y + x;

  function Bool addAssoc(Int#(4) x, Int#(4) y, Int#(4) z) =
    x + (y + z) == (x + y) + z;

  function Bool subComm(Int#(4) x, Int#(4) y) =
    x - y == y - x;

  prop("addComm"  , addComm);
  prop("addAssoc" , addAssoc);
  prop("subComm" , subComm);
endmodule

module [Module] mkArithChecker ();
  blueCheck(mkArithSpec);
endmodule

// ============================================================================
// First-hot trick & properties
// ============================================================================

function Bit#(4) firstHot(Bit#(4) x) = x & (~x+1);

module [Specification] firstHotSpec ();
  function Bool oneIsHot(Bit#(4) x) =
    countOnes(firstHot(x)) == (x == 0 ? 0 : 1);

  function Bool hotBitCommon(Bit#(4) x) =
    (x & firstHot(x)) == firstHot(x);

  //function Bool hotBitFirst(Bit#(4) x) =
  //  (x & (firstHot(x)-1)) == 0;

  prop("oneIsHot"    , oneIsHot);
  prop("hotBitCommon", hotBitCommon);
  //prop("hotBitFirst" , hotBitFirst);
endmodule

module [Module] mkFirstHotChecker ();
  blueCheck(firstHotSpec);
endmodule
