------------------------------- MODULE Monolithic ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, tmState, tmPrepared, rmState1, rmState2, rmState3

vars == <<msgs, tmState, tmPrepared, rmState1, rmState2, rmState3>>

RMs == {"rm1", "rm2", "rm3"}
\*RMs == {"rm1", "rm2", "rm3", "rm4", "rm5", "rm6", "rm7", "rm8", "rm9"}
msg == "msg"
theRM == "theRM"

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]


Init ==   
  /\ msgs = {}
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ rmState1 = "working"
  /\ rmState2 = "working"
  /\ rmState3 = "working"

SndPrepare_rm1 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm1"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState1 = "working"
  /\ rmState1' = "prepared"
  /\ UNCHANGED <<rmState2, rmState3>>

SndPrepare_rm2 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm2"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState2 = "working"
  /\ rmState2' = "prepared"
  /\ UNCHANGED <<rmState1, rmState3>>

SndPrepare_rm3 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm3"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState3 = "working"
  /\ rmState3' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmState1, rmState2, rmState3>>

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState1, rmState2, rmState3>>

RcvCommit_rm1 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState1' = "committed"
  /\ UNCHANGED <<rmState2, rmState3>>

RcvCommit_rm2 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState2' = "committed"
  /\ UNCHANGED <<rmState1, rmState3>>

RcvCommit_rm3 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState3' = "committed"
  /\ UNCHANGED <<rmState1, rmState2>>

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState1, rmState2, rmState3>>

RcvAbort_rm1 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState1' = "aborted"
  /\ UNCHANGED <<rmState2, rmState3>>

RcvAbort_rm2 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState2' = "aborted"
  /\ UNCHANGED <<rmState1, rmState3>>

RcvAbort_rm3 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState3' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2>>
  
SilentAbort_rm1 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState1 = "working"
  /\ rmState1' = "aborted"
  /\ UNCHANGED <<rmState2, rmState3>>
  
SilentAbort_rm2 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState2 = "working"
  /\ rmState2' = "aborted"
  /\ UNCHANGED <<rmState1, rmState3>>
  
SilentAbort_rm3 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState3 = "working"
  /\ rmState3' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2>>


Next ==
    \E rm \in RMs :
        \/ SndPrepare_rm1
        \/ SndPrepare_rm2
        \/ SndPrepare_rm3
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit_rm1
        \/ RcvCommit_rm2
        \/ RcvCommit_rm3
        \/ SndAbort(rm)
        \/ RcvAbort_rm1
        \/ RcvAbort_rm2
        \/ RcvAbort_rm3
        \/ SilentAbort_rm1
        \/ SilentAbort_rm2
        \/ SilentAbort_rm3

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ msgs \in SUBSET Message
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \in SUBSET RMs
  /\ rmState1 \in {"working", "prepared", "committed", "aborted"}
  /\ rmState2 \in {"working", "prepared", "committed", "aborted"}
  /\ rmState3 \in {"working", "prepared", "committed", "aborted"}

\*Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
Consistent == ~(rmState1 = "aborted" /\ rmState2 = "committed")

=============================================================================
