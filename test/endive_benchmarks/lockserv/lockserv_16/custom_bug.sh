#!/bin/sh

echo "Lock Server (16) (bug)"
time python3 ../../../../verify.py Bug.tla Bug.cfg --cust
