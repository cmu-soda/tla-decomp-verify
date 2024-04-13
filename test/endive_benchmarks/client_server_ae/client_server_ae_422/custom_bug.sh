#!/bin/sh

echo "Client Server AE (4-2-2) (bug)"
time python3 ../../../../verify.py Bug.tla Bug.cfg --cust
