---- MODULE Session9sem_MC ----
EXTENDS Session9sem

ConstN == 3
ConstProcs == 0..(ConstN-1)

MutualExclusion == \A p, q \in Procs:
                    (p /= q) => ~((pc[p] = "cs") /\ (pc[q] = "cs"))

DeadAndLivelockFree == (\E i \in Procs: pc[i] = "enter") ~> (\E i \in Procs: pc[i] = "cs")

StarvationFree == \A i \in Procs: (pc[i] = "enter") ~> (pc[i] = "cs")

====