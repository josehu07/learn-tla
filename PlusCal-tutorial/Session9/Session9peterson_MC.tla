---- MODULE Session9peterson_MC ----
EXTENDS Session9peterson

ConstN == 3
ConstProcs == 0..(ConstN-1)

MutualExclusion == \A p, q \in Procs:
                    (p /= q) => ~((pc[p] = "cs") /\ (pc[q] = "cs"))

StarvationFree == \A i \in Procs: (pc[i] = "enter") ~> (pc[i] = "cs")

====