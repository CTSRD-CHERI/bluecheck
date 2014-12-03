#!/bin/bash

BSC="bsc"
BSCFLAGS="-keep-fires -cross-info -aggressive-conditions \
          -D BLUESIM -wait-for-license -suppress-warnings G0043"
SUFFIXES=

#TOPMOD=testStack
TOPMOD=testStackID
#TOPMOD=testStackAlg
#TOPMOD=testStackAlgID
TOPFILE=StackExample.bsv

echo Compiling $TOPMOD in file $TOPFILE
if $BSC $BSCFLAGS -sim -g $TOPMOD -u $TOPFILE
then
  if $BSC $BSCFLAGS -sim -o $TOPMOD -e $TOPMOD  $TOPMOD.ba
  then
      ./$TOPMOD -m 10000000
  else
      echo Failed to generate executable simulation model
  fi
else
  echo Failed to compile
fi

