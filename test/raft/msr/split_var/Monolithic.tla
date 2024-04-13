---- MODULE Monolithic ----
\*
\* Basic, static version of MongoDB Raft protocol. No reconfiguration is allowed.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

Server == {"n1", "n2"}
Secondary == "Secondary"
Primary == "Primary"
Nil == "Nil"
MaxLogLen == 10
MaxTerm == 5
NatLogLen == 0..MaxLogLen
NatTerm == 0..MaxTerm

VARIABLE currentTerm
VARIABLE state
VARIABLE log

VARIABLE committed

VARIABLE currentTermProxy, updateCurrentTermProxy
VARIABLE logLenProxy, updateLogLenProxy

vars == <<currentTerm, state, log, committed, currentTermProxy, updateCurrentTermProxy, logLenProxy, updateLogLenProxy>>

\*
\* Helper operators.
\*

Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

CanRollback(i, j) ==
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ ~IsPrefix(log[i],log[j])

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ updateLogLenProxy' = TRUE
    /\ UNCHANGED <<currentTerm, state, committed, currentTermProxy, updateCurrentTermProxy, logLenProxy>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ updateLogLenProxy' = TRUE
    /\ UNCHANGED <<committed, currentTerm, state, currentTermProxy, updateCurrentTermProxy, logLenProxy>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ updateLogLenProxy' = TRUE
    /\ UNCHANGED <<committed, currentTerm, state, currentTermProxy, updateCurrentTermProxy, logLenProxy>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ updateCurrentTermProxy' = TRUE
    /\ UNCHANGED <<log, committed, currentTermProxy, logLenProxy, updateLogLenProxy>>

UpdateCurrentTermProxy(v) ==
    /\ ~updateLogLenProxy
    /\ updateCurrentTermProxy
    /\ currentTerm = v
    /\ currentTermProxy' = v
    /\ updateCurrentTermProxy' = FALSE
    /\ UNCHANGED <<currentTerm, state, log, committed, logLenProxy, updateLogLenProxy>>

UpdateLogLenProxy(v) ==
    /\ ~updateCurrentTermProxy
    /\ updateLogLenProxy
    /\ \A i \in Server : Len(log[i]) = v[i]
    /\ logLenProxy' = v
    /\ updateLogLenProxy' = FALSE
    /\ UNCHANGED <<currentTerm, state, log, committed, currentTermProxy, updateCurrentTermProxy>>

\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c.entry = <<logLenProxy[i], currentTermProxy[i]>>
    /\ committed' = committed \cup
            {[ entry  |-> <<logLenProxy[i], currentTermProxy[i]>>,
               term  |-> currentTermProxy[i]]}
    /\ UNCHANGED <<currentTerm, state, log, currentTermProxy, updateCurrentTermProxy, logLenProxy, updateLogLenProxy>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ ~updateCurrentTermProxy
    /\ ~updateLogLenProxy
    /\ \A s \in Server : Len(log[s]) < MaxLogLen
    /\ \A s \in Server : currentTerm[s] < MaxTerm
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, committed, currentTermProxy, updateCurrentTermProxy, logLenProxy, updateLogLenProxy>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ committed = {}
    /\ currentTermProxy = [i \in Server |-> 0]
    /\ updateCurrentTermProxy = FALSE
    /\ logLenProxy = [i \in Server |-> 0]
    /\ updateLogLenProxy = FALSE

Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s,t \in Server : GetEntries(s, t)
    \/ \E s,t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums(Server) : BecomeLeader(s, Q)
    \/ \E s \in Server : \E Q \in Quorums(Server) : CommitEntry(s, Q)
    \/ \E s,t \in Server : UpdateTerms(s, t)
    \/ \E v \in [Server -> NatTerm] : UpdateCurrentTermProxy(v)
    \/ \E v \in [Server -> NatLogLen] : UpdateLogLenProxy(v)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*
StateMachineSafety == 
    \A c1, c2 \in committed :
        (c1.entry[1] = c2.entry[1]) => (c1 = c2)

OnePrimaryPerTerm ==
    \A s,t \in Server :
        (/\ state[s] = Primary
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

=============================================================================
