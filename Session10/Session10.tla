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
QueuesFrom(n) == {<<n, m>> : m \in Nbrs(n)}
QueuesTo(n)  == {<<m, n>> : m \in Nbrs(n)}
Queues == UNION {QueuesFrom(n) : n \in Nodes}

(***************************************************************************
--algorithm PathsToRoot {
    variable msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>] ;

    fair process (node \in Nodes) 
      variables depth = IF self = root THEN 0 ELSE MaxNodes,
                parent = self ;              
      { a: while (TRUE) { 
             with (q \in {r \in QueuesTo(self) : msgs[r] /= << >>}) {
               if (Head(msgs[q]) < depth - 1) {
                  depth := Head(msgs[q]) + 1 ;
                  parent := q[1] ;
                  msgs := [r \in Queues |->
                            IF r = q 
                              THEN Tail(msgs[q])
                              ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                     THEN Append(msgs[r], depth)
                                     ELSE msgs[r] ]
                                     
               } else { msgs[q] := Tail(msgs[q]) }
             }
           }
      } 
}


 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "fcd1f17a" /\ chksum(tla) = "8e5e4284")
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>]
        (* Process node *)
        /\ depth = [self \in Nodes |-> IF self = root THEN 0 ELSE MaxNodes]
        /\ parent = [self \in Nodes |-> self]

node(self) == \E q \in {r \in QueuesTo(self) : msgs[r] /= << >>}:
                IF Head(msgs[q]) < depth[self] - 1
                   THEN /\ depth' = [depth EXCEPT ![self] = Head(msgs[q]) + 1]
                        /\ parent' = [parent EXCEPT ![self] = q[1]]
                        /\ msgs' = [r \in Queues |->
                                     IF r = q
                                       THEN Tail(msgs[q])
                                       ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                              THEN Append(msgs[r], depth'[self])
                                              ELSE msgs[r] ]
                   ELSE /\ msgs' = [msgs EXCEPT ![q] = Tail(msgs[q])]
                        /\ UNCHANGED << depth, parent >>

Next == (\E self \in Nodes: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

\* END TRANSLATION 
-----------------------------------------------------------------------------
Terminated  ==  \A q \in Queues : msgs[q] = << >>


TypeOK  ==  /\ depth  \in [Nodes -> 0..MaxNodes]
            /\ parent \in [Nodes -> Nodes]
            /\ msgs \in [Queues -> Seq(0..(Cardinality(Nodes)-1))]
            

                    
RECURSIVE PPath(_)
PPath(n) == IF n = root THEN <<n>> ELSE <<n>> \o PPath(parent[n]) 

RECURSIVE DistanceFrom(_, _)
DistanceFrom(n, S) == IF n \in S THEN 0 
                                 ELSE 1 + DistanceFrom(n, S \cup SetNbrs(S))

Dist(n, m) == DistanceFrom(n, {m})

Postcondition == \A n \in Nodes : Len(PPath(n)) - 1 = Dist(n, root)
=============================================================================
\* Modification History
\* Last modified Thu Aug 05 17:35:59 PDT 2021 by lamport
\* Created Thu Jun 24 13:50:11 PDT 2021 by lamport
   
