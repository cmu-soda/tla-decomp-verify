--------------------------- MODULE DijkstraMutex ---------------------------
\* TODO the IF-THEN-ELSE causes issues and causes an unsound result due to mis-translation
EXTENDS Integers

defaultInitValue == 0
VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

Proc == {"p1","p2","p3","p4"}
\*Proc == {"p1","p2","p3","p4","p5","p6"}
ProcSet == (Proc)

Init == (* Global variables *)
        /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        (* Process P *)
        /\ temp = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Li0"]
        \*/\ pc = [self \in ProcSet |-> CASE self \in Proc -> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Li4a"]
             /\ UNCHANGED << b, c, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li3a"]
             /\ UNCHANGED << b, k, temp >>

Li3a(self) == /\ pc[self] = "Li3a"
              /\ temp' = [temp EXCEPT ![self] = k]
              /\ pc' = [pc EXCEPT ![self] = "Li3b"]
              /\ UNCHANGED << b, c, k >>

Li3b(self) == /\ pc[self] = "Li3b"
              /\ IF b[temp[self]]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Li3c"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, k, temp >>

Li3c(self) == /\ pc[self] = "Li3c"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, temp >>

Li3d(self) == /\ pc[self] = "Li3d"
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                    THEN /\ \E j \in temp[self]:
                              /\ temp' = [temp EXCEPT 
                                            ![self] = temp[self] \ {j}]
                              /\ IF ~c[j]
                                    THEN /\ pc' = [pc EXCEPT 
                                                     ![self] = "Li1"]
                                    ELSE /\ pc' = [pc EXCEPT 
                                                     ![self] = "Li4b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ UNCHANGED temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Li5"]
            /\ UNCHANGED << b, c, k, temp >>

Li5(self) == /\ pc[self] = "Li5"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li6"]
             /\ UNCHANGED << b, k, temp >>

Li6(self) == /\ pc[self] = "Li6"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << c, k, temp >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

\*P(self) ==
Next ==
    \E self \in Proc :
        \/ Li0(self)
        \/ Li1(self)
        \/ Li2(self)
        \/ Li3a(self)
        \/ Li3b(self)
        \/ Li3c(self)
        \/ Li3d(self)
        \/ Li4a(self)
        \/ Li4b(self)
        \/ cs(self)
        \/ Li5(self)
        \/ Li6(self)
        \/ ncs(self)

(*
Next == (\E self \in Proc: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)
*)

Spec == Init /\ [][Next]_vars
\*/\ \A self \in Proc: WF_vars(P(self))

\*Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* The following formula asserts that no two processes are in their        *)
(* critcal sections at the same time.  It is the invariant that a mutual   *)
(* exclusion algorithm should satisfy.  You can have TLC check that the    *)
(* algorithm is a mutual exclusion algorithm by checking that this formula *)
(* is an invariant.                                                        *)
(***************************************************************************)
MutualExclusion == \A i, j \in Proc : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"
=============================================================================
\* Modification History
\* Last modified Sat Jan 01 12:14:14 PST 2011 by lamport
\* Created Fri Dec 31 14:14:14 PST 2010 by lamport
