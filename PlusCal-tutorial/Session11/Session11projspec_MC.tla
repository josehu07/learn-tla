---- MODULE Session11projspec_MC ----
EXTENDS Session11projspec

ConstData == {"Fred", "Mary", "Ted"}

StateConstraint == Len(NewValQueue) =< 3

ABESpec_TypeOK == /\ AVar \in Msgs
                  /\ BVar \in Msgs
                  /\ NewValQueue \in Seq(Data)

(*
 * The following invariant may no longer be satisfied, because the environment
 * E may be proposing new values too quickly and the process A be accepting new
 * proposals too quickly, such that two new proposals are accepted before B
 * receives any message from A.
 * That is, the alternating bit may be 1 -> 0 -> 1 on A while B still holds the
 * old value for the old 1 bit.
 *)
ABESpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

InfinitelyAlternating == []<>(AVar = BVar) /\ []<>(AVar /= BVar)

Liveness == (AVar /= BVar) ~> (AVar = BVar)

====
