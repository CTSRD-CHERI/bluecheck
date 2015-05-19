/* 
 * Copyright 2015 Matthew Naylor
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
 * ("CTSRD"), as part of the DARPA CRASH research programme.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-11-C-0249
 * ("MRC2"), as part of the DARPA MRC research programme.
 *
 * This software was developed by the University of Cambridge Computer
 * Laboratory as part of the Rigorous Engineering of Mainstream
 * Systems (REMS) project, funded by EPSRC grant EP/K008528/1.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

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
// First-hot example & properties
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

// ============================================================================
// Custom generator example & properties
// ============================================================================

// A custom generator for 'one-hot' values.

typedef struct { Bit#(n) value; } OneHot#(type n)
  deriving (Bits, Bounded, FShow);

module [Specification] genOneHot (Gen#(OneHot#(n)));
  Gen#(Bit#(TLog#(n))) index <- mkGen;
  method ActionValue#(OneHot#(n)) gen;
    let i <- index.gen;
    return OneHot { value: 1 << bound(i, valueOf(n)-1) };
  endmethod
endmodule

instance MkGen#(OneHot#(n));
  mkGen = genOneHot;
endinstance

// Example property

module [Specification] customGenExample ();
  function Bool oneIsHot(OneHot#(4) x) =
    countOnes(x.value) == 1;

  prop("oneIsHot", oneIsHot);
endmodule

module [Module] mkCustomGenExample ();
  blueCheck(customGenExample);
endmodule
