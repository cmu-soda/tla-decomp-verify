----------------------------- MODULE Monolithic -----------------------------

VARIABLES termState, tableState, mode, readyToFire

vars == <<termState, tableState, mode, readyToFire>>

Init ==
    /\ termState = "blank"
    /\ tableState = "flattener"
    /\ mode = "xray"
    /\ readyToFire = FALSE

TypeX ==
    /\ termState \in {"blank", "cursorAtTop"}
    /\ termState' = "cursorAtTop"
    /\ \/ /\ tableState = "spreader"
          /\ tableState' = "rotateToFlattener"
       \/ /\ tableState = "flattener"
          /\ UNCHANGED <<tableState>>
    /\ \/ /\ mode = "electron"
          /\ readyToFire = FALSE
          /\ mode' = "switchToXray"
          /\ UNCHANGED readyToFire
       \/ /\ mode = "xray"
          /\ UNCHANGED <<mode, readyToFire>>

TypeE ==
    /\ termState \in {"blank", "cursorAtTop"}
    /\ termState' = "cursorAtTop"
    /\ \/ /\ tableState = "flattener"
          /\ tableState' = "rotateToSpreader"
       \/ /\ tableState = "spreader"
          /\ UNCHANGED <<tableState>>
    /\ \/ /\ mode = "xray"
          /\ readyToFire = FALSE
          /\ mode' = "electron"
          /\ UNCHANGED readyToFire
       \/ /\ mode = "electron"
          /\ UNCHANGED <<mode, readyToFire>>

TypeUp ==
    /\ \/ /\ termState = "cursorAtBottom"
          /\ termState' = "cursorAtTop"
       \/ /\ termState \in {"blank", "cursorAtTop"}
          /\ UNCHANGED <<termState>>
    /\ UNCHANGED <<tableState, mode, readyToFire>>

TypeEnter ==
    /\ \/ /\ termState = "cursorAtTop"
          /\ termState' = "cursorAtBottom"
       \/ /\ termState \in {"blank", "cursorAtBottom"}
          /\ UNCHANGED <<termState>>
    /\ UNCHANGED <<tableState, mode, readyToFire>>

BeamReady ==
    /\ termState = "cursorAtBottom"
    /\ termState' = "beamReady"
    /\ UNCHANGED <<tableState, mode, readyToFire>>

TypeB ==
    /\ termState = "beamReady"
    /\ termState' = "blank"
    /\ readyToFire = FALSE
    /\ readyToFire' = TRUE
    /\ UNCHANGED mode
    /\ UNCHANGED tableState

Rotate ==
    /\ \/ /\ tableState = "rotateToFlattener"
          /\ tableState' = "flattener"
       \/ /\ tableState = "rotateToSpreader"
          /\ tableState' = "spreader"
    /\ mode = "switchToXray"
    /\ mode' = "xray"
    /\ UNCHANGED readyToFire

fireXray ==
    /\ mode = "xray"
    /\ readyToFire = TRUE
    /\ readyToFire' = FALSE
    /\ UNCHANGED mode
    /\ UNCHANGED <<tableState, termState>>

fireElectron ==
    /\ mode = "electron"
    /\ readyToFire = TRUE
    /\ readyToFire' = FALSE
    /\ UNCHANGED mode
    /\ UNCHANGED <<tableState, termState>>

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeUp
    \/ TypeEnter
    \/ BeamReady
    \/ TypeB
    \/ Rotate
    \/ fireXray
    \/ fireElectron

Spec == Init /\ [][Next]_vars

XrayImpliesFlatMode ==
    (mode = "xray" /\ readyToFire = TRUE) => (tableState = "flattener")

=============================================================================
