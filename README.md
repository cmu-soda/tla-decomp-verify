# Decomp-Verify
This repo allows you to run the Decomp-Verify model checker for TLA+.
Please note it is currently a work in progress and is not production ready yet.

## Running Decomp-Verify
There is a python script in the root directory that makes it easy to run the model checker.
```
python3 verify.py <TLA file> <Config file>
```

## Example
If you want to model check the 2PC (Two Phase Commit) protocol you can do the following:
```
$ cd test/two_phase/all_msgs_env 
$ python3 ../../../verify.py Monolithic.tla Monolithic.cfg 
# components: 3

Component 1: A1
State space gen: 6128ms
LTS gen: 306ms
# unique states: 143128 states
minimization: 1966ms
# unique states post-minimization: 6125 states
WARNING: sun.reflect.Reflection.getCallerClass is not supported. This will impact performance.

Component 2: A2
State space gen: 667ms
LTS gen: 17ms
# unique states: 2048 states
minimization: 147ms
# unique states post-minimization: 2048 states
New property gen (|| composition): 2980ms

Component 3: B2
State space gen: 91ms
LTS gen: 5ms
# unique states: 1025 states
minimization: 19ms
# unique states post-minimization: 514 states
New property gen (|| composition): 4121ms

Total # states checked: 146201
Property satisfied!
```

## Examining the Decomposed Files
The python script will put all artifacts that are created in a folder called "out".
The "out" folder will contain--among other artifacts--the decomposed specification.
The decomposition consists of every A#.tla file (where # represents a number) and the B#.tla file with the highest number.
For example, here is the contents of the "out" folder from the previous example:
```
$ ls out
A1.tla		A2.tla		B1.tla		B2.tla		Monolithic.cfg	Monolithic.tla	no_invs.cfg	states
```
In this case, the monolithic file is decomposed into A1.tla, A2.tla, and B2.tla.
The file B1.tla represents an intermediate step during the decomposition, and is NOT considered to be a part of the decomposed spec.
