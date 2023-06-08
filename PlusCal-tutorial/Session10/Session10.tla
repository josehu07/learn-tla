----------------------------- MODULE Session10 -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

HasTwoElts(S) == \E a,b \in S : (a # b) /\ (S = {a,b})

ASSUME /\ \A e \in Edges : (e \subseteq Nodes) /\ HasTwoElts(e)
       /\ root \in Nodes
       /\ MaxNodes >= Cardinality(Nodes)

Nbrs(n) == {m \in Nodes : {m,n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) == LET R == SetNbrs(S)
                    IN  IF R \subseteq S THEN S
                                         ELSE ReachableFrom(R \cup S)

ASSUME ReachableFrom({root}) = Nodes
                         
----------------------------------------------------------------------------

(***************************************************************************)
(* A more efficiently executable definition of ReachableFrom(S) is         *)
(* RF(S, {}), where RF is defined as follows.                              *)
(***************************************************************************)
RECURSIVE RF(_, _)
RF(B, T)  ==  IF B = {} THEN T ELSE RF(SetNbrs(B) \ T, B \cup T)

(***************************************************************************)
(* The following theorem asserts the correctness of the definition of      *)
(* ReachableFrom in terms of RF.                                           *)
(***************************************************************************)
THEOREM RFCorrect == \A S \in SUBSET Nodes : RF(S, {}) = ReachableFrom(S)

-----------------------------------------------------------------------------

RemoveElt(sq, i) == [j \in 1..(Len(sq)-1) |-> IF j < i THEN sq[j] ELSE sq[j+1]]

\* NumNodes == Len(Nodes)
\*
\* QueueOfSet(S) == LET InSet(e) == e \in S
\*                  IN SelectSeq([i \in 1..NumNodes |-> NumNodes-i], InSet)
\*
\* PossibleQueues == {QueueOfSet(S): S \in SUBSET (0..(NumNodes-1))}
\*
\* THEOREM RemoveEltCorrect == \A q \in PossibleQueues: \A i \in 1..Len(q):
\*                                 RemoveElt(q, i) = SubSeq(q, 1, i-1) \o SubSeq(q, i+1, Len(q))

-----------------------------------------------------------------------------

QueuesFrom(n) == {<<n, m>> : m \in Nbrs(n)}
QueuesTo(n)  == {<<m, n>> : m \in Nbrs(n)}
Queues == UNION {QueuesFrom(n) : n \in Nodes}

(*--algorithm PathsToRoot
variable msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>];

fair process node \in Nodes
variables depth = IF self = root THEN 0 ELSE MaxNodes, parent = self;
begin
    a: while TRUE do
        with q \in {r \in QueuesTo(self): msgs[r] /= << >>} do
            with i \in 1..Len(msgs[q]) do
                if msgs[q][i] < depth - 1 then
                    depth := msgs[q][i] + 1;
                    parent := q[1];
                    msgs := [r \in Queues |->
                                IF r = q
                                    THEN RemoveElt(msgs[q], i)
                                    ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                        THEN Append(msgs[r], depth)
                                        ELSE msgs[r]
                            ];
                else
                    msgs[q] := RemoveElt(msgs[q], i);
                end if;
            end with;
        end with;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "87b524e3" /\ chksum(tla) = "3adbea13")
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>]
        (* Process node *)
        /\ depth = [self \in Nodes |-> IF self = root THEN 0 ELSE MaxNodes]
        /\ parent = [self \in Nodes |-> self]

node(self) == \E q \in {r \in QueuesTo(self): msgs[r] /= << >>}:
                \E i \in 1..Len(msgs[q]):
                  IF msgs[q][i] < depth[self] - 1
                     THEN /\ depth' = [depth EXCEPT ![self] = msgs[q][i] + 1]
                          /\ parent' = [parent EXCEPT ![self] = q[1]]
                          /\ msgs' = [r \in Queues |->
                                         IF r = q
                                             THEN RemoveElt(msgs[q], i)
                                             ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                                 THEN Append(msgs[r], depth'[self])
                                                 ELSE msgs[r]
                                     ]
                     ELSE /\ msgs' = [msgs EXCEPT ![q] = RemoveElt(msgs[q], i)]
                          /\ UNCHANGED << depth, parent >>

Next == (\E self \in Nodes: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 05 17:35:59 PDT 2021 by lamport
\* Created Thu Jun 24 13:50:11 PDT 2021 by lamport   
