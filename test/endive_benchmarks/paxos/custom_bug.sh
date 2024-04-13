#!/bin/sh

echo "Paxos (2-2) (bug)"
time python3 ../../../verify.py Bug.tla Bug.cfg --cust
