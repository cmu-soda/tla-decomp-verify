---- MODULE Monolithic ----
\* benchmark: pyv-learning-switch

EXTENDS TLC, Naturals, FiniteSets

Node == {"n1","n2","n3"}

VARIABLE
    \* @type: Set(<<Str, Str, Str>>);
    table,
    \* @type: Set(<<Str, Str, Str, Str>>);
    pending

vars == <<table, pending>>

\* @type: (Str, Str) => Bool;
NewPacket(ps,pd) ==
    /\ pending' = pending \cup {<<ps,pd,ps,ps>>}
    /\ UNCHANGED table

\* @type: (Str, Str, Str, Str, Str) => Bool;
Forward(ps,pd,sw0,sw1,nondet) ==
    /\ <<ps,pd,sw0,sw1>> \in pending
    \* Remove all elements whose first element is not 'nondet',
    \* and also add elements for all d \in Node.
    /\ pending' =
        {<<psa,pda,sw1a,da>> \in pending : psa = nondet} \cup
        {<<ps,pd,sw1,d>> : d \in Node}
    /\ table' = IF ( (ps # sw1) /\ (\A w \in Node : w # sw1 => <<ps,sw1,w>> \notin table) )
                THEN  table \cup
                      {<<px,n1,n2>> \in Node \X Node \X Node :
                            /\ px = ps
                            /\ (<<ps,n1,sw1>> \in table /\ <<ps,sw0,n2>> \in table) }
                ELSE table

Next ==
    \/ \E ps,pd \in Node : NewPacket(ps,pd)
    \/ \E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet)

Init ==
    /\ table = {<<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2}
    /\ pending = {}

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ table \in SUBSET (Node \X Node \X Node)
    /\ pending \in SUBSET (Node \X Node \X Node \X Node)

Safety ==
    /\ \A t,x \in Node : <<t,x,x>> \in table
    \*/\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,y,z>> \in table) => (<<t,x,z>> \in table)
    \*/\ \A t,x,y \in Node : (<<t,x,y>> \in table /\ <<t,y,x>> \in table) => (x = y)
    \*/\ \A t,x,y,z \in Node : (<<t,x,y>> \in table /\ <<t,x,z>> \in table) => (<<t,y,z>> \in table \/ <<t,z,y>> \in table)

StateConstraint == Cardinality(pending) < 5

====
