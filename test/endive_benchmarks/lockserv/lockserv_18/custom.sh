#!/bin/sh

echo "Lock Server (18)"
time python3 ../../../../verify.py Monolithic.tla Monolithic.cfg --cust
