---- MODULE PaxosCommit_MC ----
EXTENDS PaxosCommit

(***************************************************************************)
(* We now assert that the Paxos Commit protocol implements the transaction *)
(* commit protocol of module TCommit.  The following statement imports     *)
(* into the current module the definitions from module TCommit, including  *)
(* the definition of TCSpec.                                               *)
(***************************************************************************)

TCommitSpec == INSTANCE TCommit
TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM PCSpec => TCommitSpecProperty

====
