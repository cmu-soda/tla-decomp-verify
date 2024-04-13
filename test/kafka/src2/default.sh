#!/bin/sh

echo "Kafka"
time python3 ../../../verify.py Monolithic.tla Monolithic.cfg
