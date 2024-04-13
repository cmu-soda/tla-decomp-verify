#!/bin/sh

echo "Lock Server (18) (bug)"
time python3 ../../../../verify.py Bug.tla Bug.cfg --cust
