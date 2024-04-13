------------------------------- MODULE Monolithic ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, rmState, tmState, tmPrepared, counter

vars == <<msgs, rmState, tmState, tmPrepared, counter>>

RMs == {"rm1", "rm2", "rm3", "rm4", "rm5", "rm6", "rm7", "rm8", "rm9"}
msg == "msg"
theRM == "theRM"

Message ==
  [type : {"Prepared"}, rm : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ msgs = {}
  /\ rmState = [rm \in RMs |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ counter = 0

SndPrepare(rm) == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "prepared"]
  /\ UNCHANGED <<tmState, tmPrepared, counter>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmState, counter>>

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState, counter>>

RcvCommit(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "committed"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared, counter>>

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState, counter>>

RcvAbort(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<msgs, tmState, tmPrepared, counter>>
  
SilentAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs, counter>>
  
Increment ==
  /\ counter' = counter + 1
  /\ UNCHANGED <<rmState, tmState, tmPrepared, msgs>>


Next ==
    \E rm \in RMs :
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)
        \/ Increment

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs
  /\ counter \in Nat

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
