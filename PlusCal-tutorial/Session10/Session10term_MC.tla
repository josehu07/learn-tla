---- MODULE Session10term_MC ----
EXTENDS Session10term

Terminated  ==  \A q \in Queues : msgs[q] = { }
Termination == <>Terminated

TypeOK  ==  /\ depth  \in [Nodes -> 0..MaxNodes]
            /\ parent \in [Nodes -> Nodes]
            /\ msgs \in [Queues -> SUBSET (0..(Cardinality(Nodes)-1))]
            /\ \A q \in Queues: \A d \in msgs[q]: d >= depth[q[1]]

RECURSIVE PPath(_)
PPath(n) == IF n = root THEN <<n>> ELSE <<n>> \o PPath(parent[n]) 

RECURSIVE DistanceFrom(_, _)
DistanceFrom(n, S) == IF n \in S THEN 0 
                                 ELSE 1 + DistanceFrom(n, S \cup SetNbrs(S))

Dist(n, m) == DistanceFrom(n, {m})

Postcondition == \A n \in Nodes : Len(PPath(n)) - 1 = Dist(n, root)
DepthCorrect == Terminated => Postcondition

====
