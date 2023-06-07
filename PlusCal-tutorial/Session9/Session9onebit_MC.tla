---- MODULE Session9onebit_MC ----
EXTENDS Session9onebit

ConstN == 3
ConstProcs == 0..(ConstN-1)

MutualExclusion == \A p, q \in Procs:
                    (p /= q) => ~((pc[p] = "cs") /\ (pc[q] = "cs"))

LivenessNaive == \A i \in Procs: []<>(pc[i] = "cs")

====
