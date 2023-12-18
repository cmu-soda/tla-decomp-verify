---------------------------- MODULE Monolithic ----------------------------
EXTENDS Naturals

Proc == {"p1","p2"}
Event == {"e1","e2"}

VARIABLES
    localClocks,   \* the logical clock for each process
    globalClock,   \* a ghost variable to keep track of global time
    processEvents, \* a ghost variable to keep track of all events per process
    events,        \* a ghost variable to keep track of all events that have occurred
    happensBefore  \* a ghost variable to keep track of the happensBefore relation (partial order)

vars == <<localClocks, globalClock, processEvents, events, happensBefore>>

FiniteNat == 0..100

HappensBeforePair == [before : Event, after : Event]

RECURSIVE TransitiveClosure(_)

TransitiveClosure(S) ==
    LET oneStepClosure ==
        {s \in HappensBeforePair :
            \E a,b \in S :
                /\ a.after = b.before
                /\ s.before = a.before
                /\ s.after = b.after
        } IN
    IF oneStepClosure \subseteq S
    THEN S
    ELSE TransitiveClosure(S \cup oneStepClosure)

Max(a,b) ==
    CHOOSE x \in FiniteNat :
        /\ x = a \/ x = b
        /\ x >= a
        /\ x >= b


Init ==
    /\ localClocks = [p \in Proc |-> 0]
    /\ globalClock = 0
    /\ processEvents = [p \in Proc |-> {}]
    /\ events = {}
    /\ happensBefore = {}

IndividualEvent(p,e) ==
    LET pNextTime == localClocks[p] + 1 IN
    /\ \A pastEvent \in events : pastEvent.event # e
    \* record that p engaged in event e
    /\ processEvents' = [processEvents EXCEPT![p] = processEvents[p] \cup {e}]
    \* add e to the set of all global events
    /\ events' = events \cup {[type |-> "ind", event |-> e, localTime |-> pNextTime, globalTime |-> globalClock]}
    \* increment p's local clock
    /\ localClocks' = [localClocks EXCEPT![p] = pNextTime]
    \* increment the global clock
    /\ globalClock' = globalClock + 1
    \* update the happensBefore relation
    /\ LET newHBs == {[before |-> a, after |-> e] : a \in processEvents[p]} IN
       happensBefore' = TransitiveClosure(happensBefore \cup newHBs)

MsgEvent(p,q,e1,e2) ==
    LET pNextTime == localClocks[p] + 1 IN
    LET qNextTime == Max(pNextTime,localClocks[q]) + 1 IN
    /\ \A pastEvent \in events : pastEvent.event \notin {e1,e2}
    /\ p # q
    /\ e1 # e2
    \* record that p and q engaged in event e1 and e2 respectively
    /\ processEvents' = [r \in Proc |-> IF      r = p THEN processEvents[p] \cup {e1}
                                        ELSE IF r = q THEN processEvents[q] \cup {e2}
                                        ELSE               processEvents[r]]
    \* add e1 and e2 to the set of all global events
    /\ events' = events
        \cup {[type |-> "snd", event |-> e1, localTime |-> pNextTime, globalTime |-> globalClock]}
        \cup {[type |-> "rec", event |-> e2, localTime |-> qNextTime, globalTime |-> globalClock+1]}
    \* increment p and q's local clocks
    /\ localClocks' = [r \in Proc |-> IF      r = p THEN pNextTime
                                      ELSE IF r = q THEN qNextTime
                                      ELSE               localClocks[r]]
    \* increment the global clock twice
    /\ globalClock' = globalClock + 2
    \* update the happensBefore relation
    /\ LET newHBs1 == {[before |-> a, after |-> e1] : a \in processEvents[p]} IN
       LET newHBs2 == {[before |-> a, after |-> e2] : a \in processEvents[q]} IN
       LET newHBs3 == {[before |-> e1, after |-> e2]} IN
       happensBefore' = TransitiveClosure(happensBefore \cup newHBs1 \cup newHBs2 \cup newHBs3)

Next ==
    \E p,q \in Proc :
    \E e1,e2 \in Event :
        \/ IndividualEvent(p,e1)
        \/ MsgEvent(p,q,e1,e2)

Spec == Init /\ [][Next]_vars


TypeOK ==
    /\ globalClock \in Nat
    /\ localClocks \in [Proc -> Nat]
    /\ processEvents \in [Proc -> SUBSET Event]
    /\ events \in SUBSET [type : {"ind","snd","rec"}, event : Event, localTime : Nat, globalTime : Nat]
    /\ happensBefore \in SUBSET HappensBeforePair

HappensBeforeIsTransitive ==
    \A a,b \in happensBefore :
        (a.after = b.before) => ([before |-> a.before, after |-> b.after] \in happensBefore)

HappensBeforeIsSound ==
    \A h \in happensBefore :
    \A e1,e2 \in events :
        (e1.event = h.before /\ e2.event = h.after) => (e1.globalTime < e2.globalTime)

HappensBeforeImpliesSmallerTimestamp ==
    \A h \in happensBefore :
    \A e1,e2 \in events :
        (e1.event = h.before /\ e2.event = h.after) => (e1.localTime < e2.localTime)

\* this protocol does NOT satisfy this property
SmallerTimestampImpliesHappensBefore ==
    \A e1,e2 \in events :
        (e1.localTime < e2.localTime) => [before |-> e1.event, after |-> e2.event] \in happensBefore

SmallerTimestampImpliesOppDoesntHappenBefore ==
    \A e1,e2 \in events :
        (e1.localTime < e2.localTime) => [before |-> e2.event, after |-> e1.event] \notin happensBefore

=============================================================================
\* Modification History
\* Last modified Wed Sep 13 10:01:27 EDT 2023 by idardik
\* Created Tue Sep 12 17:13:41 EDT 2023 by idardik
