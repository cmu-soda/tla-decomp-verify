---- MODULE Bug ----
EXTENDS TLC

Node == {"n1","n2","n3","n4","n5","n6","n7","n8","n9","n10","n11","n12","n13","n14","n15","n16","n17"}

VARIABLE lock_msg
VARIABLE grant_msg
VARIABLE unlock_msg
VARIABLE holds_lock
VARIABLE server_holds_lock

vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

SendLock(n) ==
    /\ lock_msg' = [lock_msg EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<unlock_msg, grant_msg, holds_lock, server_holds_lock>>

RecvLock(n) ==
    /\ server_holds_lock
    /\ lock_msg[n]
    /\ server_holds_lock' = FALSE
    /\ lock_msg' = [k \in Node |-> lock_msg[k] /\ k # n]
    /\ grant_msg' = [grant_msg EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<unlock_msg,holds_lock>>

RecvGrant(n) ==
    /\ grant_msg[n]
    /\ grant_msg' = [k \in Node |-> grant_msg[k] /\ k # n]
    /\ holds_lock' = [holds_lock EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<lock_msg,unlock_msg,server_holds_lock>>

Unlock(n) ==
    /\ holds_lock[n]
    /\ holds_lock' = [k \in Node |-> holds_lock[k] /\ k # n]
    /\ unlock_msg' = [unlock_msg EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<lock_msg, grant_msg, server_holds_lock>>


RecvUnlock(n) ==
    /\ unlock_msg[n]
    /\ unlock_msg' = [k \in Node |-> unlock_msg[k] /\ k # n]
    /\ server_holds_lock' = TRUE
    /\ UNCHANGED <<lock_msg, grant_msg, holds_lock>>

Next ==
    \/ \E n \in Node : SendLock(n)
    \/ \E n \in Node : RecvLock(n)
    \/ \E n \in Node : RecvGrant(n)
    \/ \E n \in Node : Unlock(n)
    \/ \E n \in Node : RecvUnlock(n)

Init ==
    /\ lock_msg = [n \in Node |-> FALSE]
    /\ unlock_msg = [n \in Node |-> FALSE]
    /\ grant_msg = [n \in Node |-> FALSE]
    /\ holds_lock = [n \in Node |-> FALSE]
    /\ server_holds_lock = TRUE

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ lock_msg \in [Node -> BOOLEAN]
    /\ grant_msg \in [Node -> BOOLEAN]
    /\ unlock_msg \in [Node -> BOOLEAN]
    /\ holds_lock \in [Node -> BOOLEAN]
    /\ server_holds_lock \in BOOLEAN

\* No two clients think they hold the lock simultaneously.
Mutex == \A x,y \in Node : (holds_lock[x] /\ holds_lock[y]) => (x # y)

====
