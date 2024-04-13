#!/bin/sh

echo "Paxos (2-2)"
time python3 ../../../verify.py Monolithic.tla Monolithic.cfg
