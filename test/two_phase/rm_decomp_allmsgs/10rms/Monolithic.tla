------------------------------- MODULE Monolithic ----------------------------- 

EXTENDS Sequences, Naturals, Integers

VARIABLES msgs, tmState, tmPrepared,
    rmState1, rmState2, rmState3,
    rmState4, rmState5, rmState6,
    rmState7, rmState8, rmState9,
    rmState10

vars == <<msgs, tmState, tmPrepared,
    rmState1, rmState2, rmState3,
    rmState4, rmState5, rmState6,
    rmState7, rmState8, rmState9,
    rmState10>>

\*RMs == {"rm1", "rm2", "rm3"}
RMs == {"rm1", "rm2", "rm3", "rm4", "rm5", "rm6", "rm7", "rm8", "rm9", "rm10"}
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
  /\ rmState4 = "working"
  /\ rmState5 = "working"
  /\ rmState6 = "working"
  /\ rmState7 = "working"
  /\ rmState8 = "working"
  /\ rmState9 = "working"
  /\ rmState10 = "working"

SndPrepare_rm1 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm1"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState1 = "working"
  /\ rmState1' = "prepared"
  /\ UNCHANGED <<rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm2 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm2"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState2 = "working"
  /\ rmState2' = "prepared"
  /\ UNCHANGED <<rmState1, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm3 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm3"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState3 = "working"
  /\ rmState3' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm4 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm4"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState4 = "working"
  /\ rmState4' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm5 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm5"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState5 = "working"
  /\ rmState5' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm6 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm6"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState6 = "working"
  /\ rmState6' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState7, rmState8, rmState9, rmState10>>

SndPrepare_rm7 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm7"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState7 = "working"
  /\ rmState7' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState8, rmState9, rmState10>>

SndPrepare_rm8 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm8"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState8 = "working"
  /\ rmState8' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState9, rmState10>>

SndPrepare_rm9 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm9"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState9 = "working"
  /\ rmState9' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState10>>

SndPrepare_rm10 == 
  /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> "rm10"]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  /\ rmState10 = "working"
  /\ rmState10' = "prepared"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9>>

RcvPrepare(rm) ==
  /\ [type |-> "Prepared", theRM |-> rm] \in msgs
  /\ tmState = "init"
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<msgs, tmState, rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SndCommit(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ tmState \in {"init", "commmitted"}
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ UNCHANGED <<tmPrepared, rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm1 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState1' = "committed"
  /\ UNCHANGED <<rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm2 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState2' = "committed"
  /\ UNCHANGED <<rmState1, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm3 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState3' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm4 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState4' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm5 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState5' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm6 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState6' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState7, rmState8, rmState9, rmState10>>

RcvCommit_rm7 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState7' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState8, rmState9, rmState10>>

RcvCommit_rm8 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState1' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState9, rmState10>>

RcvCommit_rm9 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState9' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState10>>

RcvCommit_rm10 ==
  /\ [type |-> "Commit"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState10' = "committed"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9>>

SndAbort(rm) ==
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ tmState \in {"init", "aborted"}
  /\ tmState' = "aborted"
  /\ UNCHANGED <<tmPrepared, rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm1 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState1' = "aborted"
  /\ UNCHANGED <<rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm2 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState2' = "aborted"
  /\ UNCHANGED <<rmState1, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm3 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState3' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm4 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState4' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm5 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState5' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState6, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm6 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState6' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState7, rmState8, rmState9, rmState10>>

RcvAbort_rm7 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState7' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState8, rmState9, rmState10>>

RcvAbort_rm8 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState8' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState9, rmState10>>

RcvAbort_rm9 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState9' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState10>>

RcvAbort_rm10 ==
  /\ [type |-> "Abort"] \in msgs
  /\ UNCHANGED <<msgs, tmState, tmPrepared>>
  /\ rmState10' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9>>

SilentAbort_rm1 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState1 = "working"
  /\ rmState1' = "aborted"
  /\ UNCHANGED <<rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>
  
SilentAbort_rm2 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState2 = "working"
  /\ rmState2' = "aborted"
  /\ UNCHANGED <<rmState1, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>
  
SilentAbort_rm3 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState3 = "working"
  /\ rmState3' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SilentAbort_rm4 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState4 = "working"
  /\ rmState4' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState5, rmState6, rmState7, rmState8, rmState9, rmState10>>

SilentAbort_rm5 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState5 = "working"
  /\ rmState5' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState6, rmState7, rmState8, rmState9, rmState10>>

SilentAbort_rm6 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState6 = "working"
  /\ rmState6' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState7, rmState8, rmState9, rmState10>>

SilentAbort_rm7 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState7 = "working"
  /\ rmState7' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState8, rmState9, rmState10>>

SilentAbort_rm8 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState8 = "working"
  /\ rmState8' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState9, rmState10>>

SilentAbort_rm9 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState9 = "working"
  /\ rmState9' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState10>>

SilentAbort_rm10 ==
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  /\ rmState10 = "working"
  /\ rmState10' = "aborted"
  /\ UNCHANGED <<rmState1, rmState2, rmState3, rmState4, rmState5, rmState6, rmState7, rmState8, rmState9>>


Next ==
    \E rm \in RMs :
        \/ SndPrepare_rm1
        \/ SndPrepare_rm2
        \/ SndPrepare_rm3
        \/ SndPrepare_rm4
        \/ SndPrepare_rm5
        \/ SndPrepare_rm6
        \/ SndPrepare_rm7
        \/ SndPrepare_rm8
        \/ SndPrepare_rm9
        \/ SndPrepare_rm10
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit_rm1
        \/ RcvCommit_rm2
        \/ RcvCommit_rm3
        \/ RcvCommit_rm4
        \/ RcvCommit_rm5
        \/ RcvCommit_rm6
        \/ RcvCommit_rm7
        \/ RcvCommit_rm8
        \/ RcvCommit_rm9
        \/ RcvCommit_rm10
        \/ SndAbort(rm)
        \/ RcvAbort_rm1
        \/ RcvAbort_rm2
        \/ RcvAbort_rm3
        \/ RcvAbort_rm4
        \/ RcvAbort_rm5
        \/ RcvAbort_rm6
        \/ RcvAbort_rm7
        \/ RcvAbort_rm8
        \/ RcvAbort_rm9
        \/ RcvAbort_rm10
        \/ SilentAbort_rm1
        \/ SilentAbort_rm2
        \/ SilentAbort_rm3
        \/ SilentAbort_rm4
        \/ SilentAbort_rm5
        \/ SilentAbort_rm6
        \/ SilentAbort_rm7
        \/ SilentAbort_rm8
        \/ SilentAbort_rm9
        \/ SilentAbort_rm10

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
\*Consistent == ~(rmState1 = "aborted" /\ rmState1 = "committed")

=============================================================================
