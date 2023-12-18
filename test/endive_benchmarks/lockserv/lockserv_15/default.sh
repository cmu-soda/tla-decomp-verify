#!/bin/sh

echo "Lock Server (15)"
time python3 ../../../../verify.py Monolithic.tla Monolithic.cfg
