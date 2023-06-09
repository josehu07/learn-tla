---- MODULE TwoPhase ----
EXTENDS TLC, Integers

CONSTANT RM

VARIABLES rmState, tmState, tmPrepared,
          msgs  \* All messages that have ever been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages == [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]

TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ tmPrepared = { }
          /\ msgs = { }

TMRcvPrepared(r) == /\ tmState = "init"
                    /\ [type |-> "Prepared", rm |-> r] \in msgs
                    /\ tmPrepared' = tmPrepared \cup {r}
                    /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit == /\ tmState = "init"
            /\ tmPrepared = RM
            /\ msgs' = msgs \cup {[type |-> "Commit"]}
            /\ tmState' = "done"
            /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort == /\ tmState = "init"
           /\ msgs' = msgs \cup {[type |-> "Abort"]}
           /\ tmState' = "done"
           /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) == /\ rmState[r] = "working"
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommit(r) == /\ [type |-> "Commit"] \in msgs
                  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbort(r) == /\ [type |-> "Abort"] \in msgs
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                 /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext == \/ TMCommit
          \/ TMAbort
          \/ \E r \in RM:
                \/ TMRcvPrepared(r)
                \/ RMPrepare(r)
                \/ RMChooseToAbort(r)
                \/ RMRcvCommit(r)
                \/ RMRcvAbort(r)

TPSpec == TPInit /\ [][TPNext]_vars

====
