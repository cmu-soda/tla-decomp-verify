-------------------------------- MODULE Bug -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in Voting.  *)
(***************************************************************************)
Value == {"v1","v2"}
Acceptor == {"n1","n2"}
Quorum == {{"n1","n2"}}

(*
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
                           *)
      
Ballot == 0..3 \* Nat

None == "None" \*CHOOSE v : v \notin Value
  (*************************************************************************)
  (* An unspecified value that is not a ballot number.                     *)
  (*************************************************************************)
  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]
-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs     \* The set of all messages that have been sent.

(***************************************************************************)
(* NOTE:                                                                   *)
(* The algorithm is easier to understand in terms of the set msgs of all   *)
(* messages that have ever been sent.  A more accurate model would use     *)
(* one or more variables to represent the messages actually in transit,    *)
(* and it would include actions representing message loss and duplication  *)
(* as well as message receipt.                                             *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss because we  *)
(* are mainly concerned with the algorithm's safety property.  The safety  *)
(* part of the spec says only what messages may be received and does not   *)
(* assert that any message actually is received.  Thus, there is no        *)
(* difference between a lost message and one that is never received.  The  *)
(* liveness property of the spec that we check makes it clear what         *)
(* messages must be received (and hence either not lost or successfully    *)
(* retransmitted if lost) to guarantee progress.                           *)
(***************************************************************************)

vars == <<maxBal, maxVBal, maxVal, msgs>>
  (*************************************************************************)
  (* It is convenient to define some identifier to be the tuple of all     *)
  (* variables.  I like to use the identifier `vars'.                      *)
  (*************************************************************************)
  
(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message


kNumSubsets == 18
nAvgSubsetSize == 4

Init == /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal = [a \in Acceptor |-> None]
        /\ msgs = {}

(***************************************************************************)
(* The actions.  We begin with the subaction (an action that will be used  *)
(* to define the actions that make up the next-state action.               *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup {m}

\* Helper predicates for checking presence of message types.
msg1a(a,b) == \E m \in msgs : m.type= "1b" /\ m.bal = a
msg1b(a,b,mb,v) == \E m \in msgs : m.type= "1b" /\ m.acc = a /\ m.bal = b /\ m.mbal = mb /\ m.mval = v
msg2a(b,v) == \E m \in msgs : m.type= "2a" /\ m.bal = b /\ m.val = v
msg2b(a,b,v) == \E m \in msgs : m.type= "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

(***************************************************************************)
(* In an implementation, there will be a leader process that orchestrates  *)
(* a ballot.  The ballot b leader performs actions Phase1a(b) and          *)
(* Phase2a(b).  The Phase1a(b) action sends a phase 1a message (a message  *)
(* m with m.type = "1a") that begins ballot b.                             *)
(***************************************************************************)
Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
                 
(***************************************************************************)
(* Upon receipt of a ballot b phase 1a message, acceptor a can perform a   *)
(* Phase1b(a) action only if b > maxBal[a].  The action sets maxBal[a] to  *)
(* b and sends a phase 1b message to the leader containing the values of   *)
(* maxVBal[a] and maxVal[a].                                               *)
(***************************************************************************)
Phase1b(a,m) == /\ m.type = "1a"
                /\ m.bal > maxBal[a]
                /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                          mbal |-> maxVBal[a], mval |-> maxVal[a]])
                /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* The Phase2a(b, v) action can be performed by the ballot b leader if two *)
(* conditions are satisfied: (i) it has not already performed a phase 2a   *)
(* action for ballot b and (ii) it has received ballot b phase 1b messages *)
(* from some quorum Q from which it can deduce that the value v is safe at *)
(* ballot b.  These enabling conditions are the first two conjuncts in the *)
(* definition of Phase2a(b, v).  This second conjunct, expressing          *)
(* condition (ii), is the heart of the algorithm.  To understand it,       *)
(* observe that the existence of a phase 1b message m in msgs implies that *)
(* m.mbal is the highest ballot number less than m.bal in which acceptor   *)
(* m.acc has or ever will cast a vote, and that m.mval is the value it     *)
(* voted for in that ballot if m.mbal # -1.  It is not hard to deduce from *)
(* this that the second conjunct implies that there exists a quorum Q such *)
(* that ShowsSafeAt(Q, b, v) (where ShowsSafeAt is defined in module       *)
(* Voting).                                                                *)
(*                                                                         *)
(* The action sends a phase 2a message that tells any acceptor a that it   *)
(* can vote for v in ballot b, unless it has already set maxBal[a]         *)
(* greater than b (thereby promising not to vote in ballot b).             *)
(***************************************************************************)
Q1b(Q, b) ==
    {m \in msgs : /\ m.type = "1b"
                  /\ m.acc \in Q
                  /\ m.bal = b}

Q1bv(Q, b) == {m \in Q1b(Q,b) : m.mbal \geq 0}
    
Phase2a(b, v, Q) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \A a \in Q : \E m \in Q1b(Q,b) : m.acc = a 
  /\ \/ Q1bv(Q, b) = {}
     \/ \E m \in Q1bv(Q, b) : 
          /\ m.mval = v
          /\ \A mm \in Q1bv(Q, b) : m.mbal \geq mm.mbal 
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
  
(***************************************************************************)
(* The Phase2b(a) action is performed by acceptor a upon receipt of a      *)
(* phase 2a message.  Acceptor a can perform this action only if the       *)
(* message is for a ballot number greater than or equal to maxBal[a].  In  *)
(* that case, the acceptor votes as directed by the phase 2a message,      *)
(* setting maxVBal[a] and maxVal[a] to record that vote and sending a      *)
(* phase 2b message announcing its vote.  It also sets maxBal[a] to the    *)
(* message's.  ballot number                                               *)
(***************************************************************************)
Phase2b(a,m) == /\ m.type = "2a"
                /\ m.bal \geq maxBal[a]
                /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
                /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
                /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                /\ Send([type |-> "2b", acc |-> a,
                         bal |-> m.bal, val |-> m.val]) 

(***************************************************************************)
(* In an implementation, there will be learner processes that learn from   *)
(* the phase 2b messages if a value has been chosen.  The learners are     *)
(* omitted from this abstract specification of the algorithm.              *)
(***************************************************************************)

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E b \in Ballot : \E v \in Value : \E Q \in Quorum : Phase2a(b, v, Q)
    \/ \E a \in Acceptor : \E m \in msgs : Phase1b(a,m)
    \/ \E a \in Acceptor : \E m \in msgs : Phase2b(a,m)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping under which this algorithm         *)
(* implements the specification in module Voting.                          *)
(***************************************************************************)

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
votes == [a \in Acceptor |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum : 
      \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
   
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) : 
      /\ (c /= -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

Inv == 
    /\ Cardinality(chosen) <= 0

============================================================================
