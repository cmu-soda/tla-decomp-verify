#!/bin/sh

echo "Firewall (5) (bug)"
time python3 ../../../verify.py Bug.tla Bug.cfg --cust
