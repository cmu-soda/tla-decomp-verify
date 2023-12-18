---- MODULE ErrTrace ----
\* benchmark: pyv-client-server-ae
EXTENDS Naturals

Node == {"n1","n2"}
Request == {"req1","req2"}
Response == {"res1","res2"}

VARIABLE match

VARIABLE request_sent
VARIABLE response_sent
VARIABLE response_received

vars == <<match,request_sent,response_sent,response_received>>

ResponseMatched(n,p) == \E r \in Request : (<<n,r>> \in request_sent) /\ <<r,p>> \in match

NewRequest(n, r) ==
    /\ request_sent' = request_sent \cup {<<n,r>>}
    /\ UNCHANGED <<response_sent,response_received,match>>

Respond(n,r,p) ==
    /\ <<n,r>> \in request_sent
    /\ <<r,p>> \in match
    /\ response_sent' = response_sent \cup {<<n,p>>}
    /\ UNCHANGED <<request_sent,response_received,match>>

ReceiveResponse(n,p) ==
    /\ <<n,p>> \in response_sent
    /\ response_received' = response_received \cup {<<n,p>>}
    /\ UNCHANGED <<request_sent,response_sent,match>>

Next ==
    \/ \E n \in Node, r \in Request : NewRequest(n,r)
    \/ \E n \in Node, r \in Request, p \in Response : Respond(n,r,p)
    \/ \E n \in Node, p \in Response : ReceiveResponse(n,p)

Init ==
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent = {}
    /\ response_sent = {}
    /\ response_received = {}

TypeOK ==
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent \in SUBSET (Node \X Request)
    /\ response_sent \in SUBSET (Node \X Response)
    /\ response_received \in SUBSET (Node \X Response)

NextUnchanged == UNCHANGED vars

Safety == \A n \in Node, p \in Response : (<<n,p>> \in response_received) => ~ResponseMatched(n,p)

VARIABLE errCounter
ErrInit ==
    /\ Init
    /\ errCounter = 0
ErrNext ==
    /\ Next
    /\ errCounter' = errCounter + 1
    /\ errCounter = 0 => NewRequest("n2","req1")
    /\ errCounter = 1 => Respond("n2","req1","res1")
    /\ errCounter = 2 => ReceiveResponse("n2","res1")
    /\ errCounter = 3 => FALSE
ErrSpec == ErrInit /\ [][ErrNext]_vars
====
