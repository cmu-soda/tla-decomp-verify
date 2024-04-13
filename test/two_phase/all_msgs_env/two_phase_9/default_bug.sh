#!/bin/sh

echo "Two Phase Commit (9) (Bug)"
time python3 ../../../../verify.py Bug.tla Bug.cfg
