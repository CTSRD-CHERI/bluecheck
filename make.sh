#!/bin/bash
#
# Copyright (c) 2015 Matthew Naylor
# All rights reserved.
#
# This software was developed by SRI International and the University of
# Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
# ("CTSRD"), as part of the DARPA CRASH research programme.
#
# This software was developed by SRI International and the University of
# Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-11-C-0249
# ("MRC2"), as part of the DARPA MRC research programme.
#
# This software was developed by the University of Cambridge Computer
# Laboratory as part of the Rigorous Engineering of Mainstream
# Systems (REMS) project, funded by EPSRC grant EP/K008528/1.
#
# @BERI_LICENSE_HEADER_START@
#
# Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
# license agreements.  See the NOTICE file distributed with this work for
# additional information regarding copyright ownership.  BERI licenses this
# file to you under the BERI Hardware-Software License, Version 1.0 (the
# "License"); you may not use this file except in compliance with the
# License.  You may obtain a copy of the License at:
#
#   http://www.beri-open-systems.org/legal/license-1-0.txt
#
# Unless required by applicable law or agreed to in writing, Work distributed
# under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations under the License.
#
# @BERI_LICENSE_HEADER_END@
#

BSC="bsc"
BSCFLAGS="-keep-fires -cross-info -aggressive-conditions \
          -wait-for-license -suppress-warnings G0043 \
          -steps-warn-interval 300000"
SUFFIXES=

# UI
# ==

echo "(1) Simple arithmetic properties"
echo "(2) firstHot properties"
echo "(3) Custom generator example"
echo "(4) Stack"
echo "(5) Stack + ID"
echo "(6) Stack + ID + Classify"
echo "(7) Stack(algebraic)"
echo "(8) Stack(algebraic) + ID"
echo "(9) Stack(synthesisable)"
echo "(10) Stack(synthesisable) + ID"
echo "(11) Stack + ID + custom parameters"

read OPTION
case "$OPTION" in
  1) TOPFILE=SimpleExamples.bsv
     TOPMOD=mkArithChecker
     ;;
  2) TOPFILE=SimpleExamples.bsv
     TOPMOD=mkFirstHotChecker
     ;;
  3) TOPFILE=SimpleExamples.bsv
     TOPMOD=mkCustomGenExample
     ;;
  4) TOPFILE=StackExample.bsv
     TOPMOD=testStack
     ;;
  5) TOPFILE=StackExample.bsv
     TOPMOD=testStackID
     ;;
  6) TOPFILE=StackExample.bsv
     TOPMOD=testStackIDClassify
     ;;
  7) TOPFILE=StackExample.bsv
     TOPMOD=testStackAlg
     ;;
  8) TOPFILE=StackExample.bsv
     TOPMOD=testStackAlgID
     ;;
  9) TOPFILE=StackExample.bsv
     TOPMOD=testStack
     SYNTH=1
     ;;
 10) TOPFILE=StackExample.bsv
     TOPMOD=testStackID
     SYNTH=1
     ;;
 11) TOPFILE=StackExample.bsv
     TOPMOD=testStackIDCustom
     ;;
  *) echo "Option not recognised"
     exit
     ;;
esac
  
# Build it
# ========

echo Compiling $TOPMOD in file $TOPFILE
if [ "$SYNTH" = "1" ]
then
  bsc -suppress-warnings G0043 -u -verilog -g $TOPMOD $TOPFILE
else
  if $BSC $BSCFLAGS -sim -g $TOPMOD -u $TOPFILE
  then
    if $BSC $BSCFLAGS -sim -o $TOPMOD -e $TOPMOD  $TOPMOD.ba
    then
        ./$TOPMOD
    else
        echo Failed to generate executable simulation model
    fi
  else
    echo Failed to compile
  fi
fi
