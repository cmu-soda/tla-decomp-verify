#!/bin/sh

echo "Two Phase Counter (9) (Bug)"
time python3 ../../../verify.py Bug.tla Bug.cfg --cust
