---- MODULE TCommit_MC ----
EXTENDS TCommit

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent == \A r1, r2 \in RM: ~(rmState[r1] = "aborted" /\ rmState[r2] = "committed")

====
