----------------------------- MODULE Session10set -----------------------------
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

(*--algorithm PathsToRoot
variable msgs = [q \in Queues |-> IF q[1] = root THEN {0} ELSE { }];

fair process node \in Nodes
variables depth = IF self = root THEN 0 ELSE MaxNodes, parent = self;
begin
    a: while TRUE do
        with q \in {r \in QueuesTo(self): msgs[r] /= { }} do
            with d \in msgs[q] do
                if d < depth - 1 then
                    depth := d + 1;
                    parent := q[1];
                    msgs := [r \in Queues |->
                                IF r = q
                                    THEN msgs[r] \ {d}
                                    ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                        THEN msgs[r] \cup {depth}
                                        ELSE msgs[r]
                            ];
                else
                    msgs[q] := msgs[q] \ {d};
                end if;
            end with;
        end with;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "370fe203" /\ chksum(tla) = "665e3feb")
VARIABLES msgs, depth, parent

vars == << msgs, depth, parent >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ msgs = [q \in Queues |-> IF q[1] = root THEN {0} ELSE { }]
        (* Process node *)
        /\ depth = [self \in Nodes |-> IF self = root THEN 0 ELSE MaxNodes]
        /\ parent = [self \in Nodes |-> self]

node(self) == \E q \in {r \in QueuesTo(self): msgs[r] /= { }}:
                \E d \in msgs[q]:
                  IF d < depth[self] - 1
                     THEN /\ depth' = [depth EXCEPT ![self] = d + 1]
                          /\ parent' = [parent EXCEPT ![self] = q[1]]
                          /\ msgs' = [r \in Queues |->
                                         IF r = q
                                             THEN msgs[r] \ {d}
                                             ELSE IF r \in QueuesFrom(self) \ {<<self, q[1]>>}
                                                 THEN msgs[r] \cup {depth'[self]}
                                                 ELSE msgs[r]
                                     ]
                     ELSE /\ msgs' = [msgs EXCEPT ![q] = msgs[q] \ {d}]
                          /\ UNCHANGED << depth, parent >>

Next == (\E self \in Nodes: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 05 17:35:59 PDT 2021 by lamport
\* Created Thu Jun 24 13:50:11 PDT 2021 by lamport   
