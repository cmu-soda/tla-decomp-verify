---- MODULE Monolithic ----
\* benchmark: pyv-client-server-ae

Node == {"n1","n2"}
Request == {"req1","req2"}
Response == {"res1","res2"}

VARIABLE match

VARIABLE request_sent
VARIABLE response_sent
VARIABLE response_received

vars == <<match,request_sent,response_sent,response_received>>

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
    \E n \in Node : \E r \in Request : \E p \in Response :
        \/ NewRequest(n,r)
        \/ Respond(n,r,p)
        \/ ReceiveResponse(n,p)

Init == 
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent = {}
    /\ response_sent = {}
    /\ response_received = {}

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ match \in SUBSET (Request \X Response)
    /\ request_sent \in SUBSET (Node \X Request)
    /\ response_sent \in SUBSET (Node \X Response)
    /\ response_received \in SUBSET (Node \X Response)

Safety ==
    \A n \in Node : \A p \in Response :
        (<<n,p>> \in response_received) =>
            (\E r \in Request : <<n,r>> \in request_sent /\ <<r,p>> \in match)

====
