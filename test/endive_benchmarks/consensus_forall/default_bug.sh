#!/bin/sh

echo "Consensus Forall (4-4) (bug)"
time python3 ../../../verify.py Bug.tla Bug.cfg
