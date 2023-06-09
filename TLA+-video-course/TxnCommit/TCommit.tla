---- MODULE TCommit ----
EXTENDS TLC, Integers

CONSTANT RM

VARIABLE rmState

vars == <<rmState>>

TCInit == rmState = [r \in RM |-> "working"]

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

CanCommit == \A r \in RM: rmState[r] \in {"prepared", "committed"}

DecideCommit(r) == /\ rmState[r] = "prepared"
                   /\ CanCommit
                   /\ rmState' = [rmState EXCEPT ![r] = "committed"]

NotCommitted == \A r \in RM: rmState[r] /= "committed"

DecideAbort(r) == /\ rmState[r] \in {"working", "prepared"}
                  /\ NotCommitted
                  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM: Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r)

TCSpec == TCInit /\ [][TCNext]_vars

====