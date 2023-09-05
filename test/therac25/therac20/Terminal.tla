----------------------------- MODULE Terminal -----------------------------

VARIABLES termState

vars == <<termState>>

Init == termState = "blank"

TypeX ==
    /\ termState \in {"blank", "cursorAtTop"}
    /\ termState' = "cursorAtTop"

TypeE ==
    /\ termState \in {"blank", "cursorAtTop"}
    /\ termState' = "cursorAtTop"

TypeUp ==
    \/ /\ termState = "cursorAtBottom"
       /\ termState' = "cursorAtTop"
    \/ /\ termState \in {"blank", "cursorAtTop"}
       /\ UNCHANGED <<termState>>

TypeEnter ==
    \/ /\ termState = "cursorAtTop"
       /\ termState' = "cursorAtBottom"
    \/ /\ termState \in {"blank", "cursorAtBottom"}
       /\ UNCHANGED <<termState>>

BeamReady ==
    /\ termState = "cursorAtBottom"
    /\ termState' = "beamReady"

TypeB ==
    /\ termState = "beamReady"
    /\ termState' = "blank"

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeUp
    \/ TypeEnter
    \/ BeamReady
    \/ TypeB

Spec == Init /\ [][Next]_vars

TypeOK == termState \in {"blank", "cursorAtTop", "cursorAtBottom", "beamReady", "finished"}

=============================================================================
