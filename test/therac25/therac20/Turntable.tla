----------------------------- MODULE Turntable -----------------------------

VARIABLES tableState

vars == <<tableState>>

Init == tableState = "flattener"

TypeX ==
    \/ /\ tableState = "spreader"
       /\ tableState' = "rotateToFlattener"
    \/ /\ tableState = "flattener"
       /\ UNCHANGED <<tableState>>

TypeE ==
    \/ /\ tableState = "flattener"
       /\ tableState' = "rotateToSpreader"
    \/ /\ tableState = "spreader"
       /\ UNCHANGED <<tableState>>

Rotate ==
    \/ /\ tableState = "rotateToFlattener"
       /\ tableState' = "flattener"
    \/ /\ tableState = "rotateToSpreader"
       /\ tableState' = "spreader"

Next ==
    \/ TypeX
    \/ TypeE
    \/ Rotate

Spec == Init /\ [][Next]_vars

TypeOK == tableState \in {"flattener", "spreader", "rotateToFlattener", "rotateToSpreader"}

=============================================================================
