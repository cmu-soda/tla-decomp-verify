#!/bin/sh

echo "Two Phase Commit (10) (Bug)"
time python3 ../../../../verify.py Bug.tla Bug.cfg
