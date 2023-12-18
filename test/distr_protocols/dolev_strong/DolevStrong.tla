---------------------------- MODULE DolevStrong ----------------------------

EXTENDS Integers, FiniteSets

VARIABLES
    leader,
    round,
    pc,
    set,
    inbox,
    broadcast, \* messages to broadcast in the next round
    output

HonestNodes == {"h1","h2"}
ByzNodes == {"b1","b2"}
Values == {"v1","v2"}

vars == <<leader, round, pc, set, inbox, broadcast, output>>

AllNodes == HonestNodes \cup ByzNodes

States == {"broadcast", "receive"}

f == Cardinality(ByzNodes)
NumRounds == f + 1

Bottom == "Bottom"
None == "None"

NewMsg(v, n) == [val |-> v, sig |-> {n}]

AddSigToMsg(m, n) == [val |-> m.val, sig |-> m.sig \cup {n}]

MsgValues(messages) == {m.val : m \in messages}

MsgChainSize(m) == Cardinality(m.sig)


Init ==
    /\ leader = "b1" \* \in AllNodes
    /\ round = 1
    /\ pc = [n \in HonestNodes |-> IF n = leader THEN "broadcast" ELSE "receive"]
    /\ set = [n \in HonestNodes |-> {}]
    /\ inbox = [n \in HonestNodes |-> {}]
    /\ broadcast = [n \in HonestNodes |-> {}]
    /\ output = [n \in HonestNodes |-> None]

HonestLeaderBroadcast(n, v) ==
    /\ n = leader
    /\ round = 1
    /\ pc[n] = "broadcast"
    /\ pc' = [pc EXCEPT![n] = "receive"]
    /\ set' = [set EXCEPT![n] = @ \cup {v}]
    /\ inbox' = [h \in HonestNodes |-> inbox[h] \cup {NewMsg(v,n)}] \* the broadcast
    /\ UNCHANGED <<leader, round, broadcast, output>>

HonestBroadcast(n) ==
    /\ round > 1
    /\ round <= NumRounds
    /\ pc[n] = "broadcast"
    /\ inbox' = [h \in HonestNodes |-> inbox[h] \cup broadcast[n]] \* the broadcast
    /\ broadcast' = [broadcast EXCEPT![n] = {}]
    /\ pc' = [pc EXCEPT![n] = "receive"]
    /\ UNCHANGED <<leader, round, set, output>>

HonestNodeReceive(n, m) ==
    /\ pc[n] = "receive"
    /\ m.val \notin set[n]
    /\ m.val \notin MsgValues(broadcast[n])
    
    \* only accept the value if the number of signatures is equal to the round #
    /\ MsgChainSize(m) = round
    
    /\ set' = [set EXCEPT![n] = @ \cup {m.val}]
    
    \* add n's sig to the sig list
    /\ broadcast' = [broadcast EXCEPT![n] = @ \cup {AddSigToMsg(m,n)}]
    
    /\ UNCHANGED <<leader, round, pc, inbox, output>>

NextRound ==
    /\ \A n \in HonestNodes : 
        /\ pc[n] = "receive"
        /\ \A m \in inbox[n] :
            ~(/\ pc[n] = "receive"
              /\ m.val \notin set[n]
              /\ m.val \notin MsgValues(broadcast[n]))
            \*~ENABLED HonestNodeReceive(n,m)
    /\ round' = round + 1
    /\ pc' = [n \in HonestNodes |-> "broadcast"]
    /\ UNCHANGED <<leader, set, inbox, broadcast, output>>

Finish(n) ==
    /\ round > NumRounds
    /\ LET out == IF   Cardinality(set[n]) = 1
                  THEN CHOOSE v \in set[n] : TRUE
                  ELSE Bottom
       IN  output' = [output EXCEPT![n] = out]
    /\ UNCHANGED <<leader, round, pc, set, inbox, broadcast>>

ByzAttack1(v, bgroup, n) ==
    /\ Cardinality(bgroup) = round \* cuts down on the size of the state space we have to search
    /\ inbox' = [inbox EXCEPT![n] = @ \cup {[val |-> v, sig |-> bgroup]}]
    /\ UNCHANGED <<leader, round, pc, set, broadcast, output>>

ByzAttack2(m, bgroup, n) ==
    /\ Cardinality(bgroup) = round - 1 \* cuts down on the size of the state space we have to search
    /\ inbox' = [inbox EXCEPT![n] = @ \cup {[val |-> m.val, sig |-> bgroup \cup m.sig]}]
    /\ UNCHANGED <<leader, round, pc, set, broadcast, output>>

Next ==
    \/ \E n \in HonestNodes : \E v \in Values : HonestLeaderBroadcast(n, v)
    \/ \E n \in HonestNodes : HonestBroadcast(n)
    \/ \E n \in HonestNodes : \E m \in inbox[n] : HonestNodeReceive(n, m)
    \/ NextRound
    \/ \E n \in HonestNodes : Finish(n)
    \/ \E n \in HonestNodes : \E v \in Values : \E bgroup \in SUBSET ByzNodes : ByzAttack1(v, bgroup, n)

Spec == Init /\ [][Next]_vars


TypeOK ==
    /\ leader \in AllNodes
    /\ round \in Int
    /\ pc \in [HonestNodes -> States]
    /\ set \in [HonestNodes -> SUBSET Values]
    /\ inbox \in [HonestNodes -> SUBSET [val: Values, sig: SUBSET AllNodes]]
    /\ broadcast \in [HonestNodes -> SUBSET [val: Values, sig: SUBSET AllNodes]]

Consensus ==
    \A n1,n2 \in HonestNodes :
        output[n1] # output[n2] => (output[n1] = None \/ output[n2] = None)

=============================================================================
