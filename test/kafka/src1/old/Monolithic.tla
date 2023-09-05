------------------------------ MODULE Monolithic ------------------------------
EXTENDS Naturals, Sequences, Functions

Event == {"e1", "e2", "e3"}
Consumer == {"c1", "c2"}
Partition == {"p1", "p2"}
MaxPartitionLen == 5

ProduceAction == [
    produce_event: Event,
    produce_partition: Partition,
    produce_time: Nat
]

ConsumeAction == [
    consume_consumer: Consumer,
    consume_partition: Partition,
    consume_event: Event,
    consume_time: Nat
]

\** Sequences are 1 indexed, 0 implies the partition has not been read
\*AllowedOffsets == 0..MaxPartitionLen
AllowedOffsets == {0,1,2,3,4,5}

VARIABLES partition_contents, offsets, time, produce_actions, consume_actions
vars == <<partition_contents, offsets, time, produce_actions, consume_actions>>

TypeInv ==
    /\ partition_contents \in [Partition -> Seq(Event)]
    /\ offsets \in [Consumer -> [Partition -> AllowedOffsets]]
    /\ time \in Nat
    /\ produce_actions \in SUBSET ProduceAction
    /\ consume_actions \in SUBSET ConsumeAction

Produce(event, partition) ==
    LET curr_action == [produce_event |-> event, produce_partition |-> partition, produce_time |-> time] IN
    /\ Len(partition_contents[partition]) < MaxPartitionLen
    /\ \A p \in Partition: event \notin Range(partition_contents[p])
    /\ partition_contents' = [partition_contents EXCEPT ![partition] = Append(partition_contents[partition], event)]
    /\ produce_actions' = produce_actions \cup {curr_action}
    /\ time' = time + 1
    /\ UNCHANGED <<offsets, consume_actions>>
    
Consume(consumer, partition, event) ==
    LET curr_action == [consume_consumer |-> consumer, 
        consume_partition |-> partition, 
        consume_event |-> event, 
        consume_time |-> time] IN
    LET last_read_idx == offsets[consumer][partition] IN
    LET offset_func == offsets[consumer] IN
    /\ Len(partition_contents[partition]) > 0
    /\ Len(partition_contents[partition]) > last_read_idx
    /\ event = partition_contents[partition][last_read_idx + 1]
    /\ offsets' = [offsets EXCEPT ![consumer] = [offset_func EXCEPT ![partition] = last_read_idx + 1]]
    /\ consume_actions' = consume_actions \cup {curr_action}
    /\ time' = time + 1
    /\ UNCHANGED <<partition_contents, produce_actions>>
    
Init ==
    /\ partition_contents = [partition \in Partition |-> <<>>]
    /\ offsets = [consumer \in Consumer |-> [partition \in Partition |-> 0]]
    /\ time = 0
    /\ produce_actions = {}
    /\ consume_actions = {}
  
Next == 
    \*\/ \E consumer \in Consumer, partition \in Partition, event \in Event : Consume(consumer, partition, event)
    \*\/ \E partition \in Partition, event \in Event : Produce(event, partition)
    \E consumer \in Consumer :
    \E partition \in Partition :
    \E event \in Event :
        \/ Consume(consumer, partition, event)
        \/ Produce(event, partition)
        
Spec == Init /\ [][Next]_vars

ConsumeOnlyAfterProduce ==
    \A ca \in consume_actions :
    \A pa \in produce_actions : 
        ca.consume_event = pa.produce_event => pa.produce_time < ca.consume_time
=============================================================================
