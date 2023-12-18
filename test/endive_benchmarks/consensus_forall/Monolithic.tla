---- MODULE Monolithic ----
\* benchmark: pyv-consensus-forall

EXTENDS TLC, Naturals, FiniteSets

\*Node == {"n1","n2"}
\*Node == {"n1","n2","n3"}
Node == {"n1","n2","n3","n4"}
Value == {"v1","v2","v3","v4"}
Quorum == { S \in SUBSET Node : Cardinality(S)*2 > Cardinality(Node) }

VARIABLE vote_request_msg
VARIABLE voted
VARIABLE vote_msg
VARIABLE votes
VARIABLE leader
VARIABLE voting_quorum
VARIABLE decided

vars == <<vote_request_msg,voted,vote_msg,votes,leader,voting_quorum,decided>>

SendRequestVote(i,j) ==
    /\ vote_request_msg' = vote_request_msg \cup {<<i,j>>}
    /\ UNCHANGED <<voted, vote_msg, votes, leader, voting_quorum,decided>>

SendVote(src,dst)==
    /\ ~voted[src]
    /\ <<dst,src>> \in vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ UNCHANGED <<vote_request_msg, votes, leader, voting_quorum,decided>>

RecvVote(i,sender)==
    /\ <<sender,i>> \in vote_msg
    /\ votes' = votes \cup {<<i,sender>>}
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, leader, voting_quorum,decided>>

ChooseVotingQuorum(i,Q) ==
    \*\E Q \in Quorum :
    /\ \A v \in Q : <<i,v>> \in votes
    /\ voting_quorum' = Q
    /\ UNCHANGED <<vote_request_msg, vote_msg, votes, voted, leader,decided>>

BecomeLeader(i) ==
    /\ voting_quorum # {}
    /\ \A v \in voting_quorum : <<i,v>> \in votes
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, voting_quorum,decided>>

Decide(i,v) ==
    /\ leader[i]
    /\ \A vx \in Value : <<i,vx>> \notin decided
    /\ decided' = decided \cup {<<i,v>>}
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, leader, voting_quorum>>

Init ==
    /\ vote_request_msg = {}
    /\ voted = [s \in Node |-> FALSE]
    /\ vote_msg = {}
    /\ votes = {}
    /\ leader = [s \in Node |-> FALSE]
    /\ voting_quorum \in Quorum
    /\ decided = {}

Next ==
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node : \E Q \in Quorum : ChooseVotingQuorum(i,Q)
    \/ \E i \in Node : BecomeLeader(i)
    \/ \E i \in Node, v \in Value : Decide(i, v)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ vote_request_msg \in SUBSET (Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET (Node \X Node)
    /\ votes \in SUBSET (Node \X Node)
    /\ leader \in [Node -> BOOLEAN]
    /\ voting_quorum \in Quorum
    /\ decided \in SUBSET (Node \X Value)

Safety ==
    \A n1,n2 \in Node : \A v1,v2 \in Value :
        (<<n1,v1>> \in decided /\ <<n2,v2>> \in decided) => (v1=v2)

NoLeader == ~\E i \in Node : leader[i]

====
