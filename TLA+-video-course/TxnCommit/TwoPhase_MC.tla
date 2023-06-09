---- MODULE TwoPhase_MC ----
EXTENDS TwoPhase

TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages

TCommitSpec == INSTANCE TCommit
TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM TPSpec => TCommitSpecProperty

====
