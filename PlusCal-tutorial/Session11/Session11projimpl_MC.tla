---- MODULE Session11projimpl_MC ----
EXTENDS Session11projimpl

ConstData == {"Fred", "Mary", "Ted"}

StateConstraint == /\ Len(AtoB) =< 3
                   /\ Len(BtoA) =< 3
                   /\ Len(NewValQueue) =< 3

ABE_TypeOK == /\ AVar \in Msgs
              /\ BVar \in Msgs
              /\ NewValQueue \in Seq(Data)
              /\ AtoB \in Seq(Msgs)
              /\ BtoA \in Seq({0,1})

(*
 * The following invariant may no longer be satisfied, because the environment
 * E may be proposing new values too quickly and the process A be accepting new
 * proposals too quickly, such that two new proposals are accepted before B
 * receives any message from A.
 * That is, the alternating bit may be 1 -> 0 -> 1 on A while B still holds the
 * old value for the old 1 bit.
 *)
ABE_Inv == (BtoA # << >>) /\ (Head(BtoA) = AVar.bit) => (AVar = BVar)

TwoValsSeq(seq) == \E i \in 0..Len(seq): \A j \in 1..Len(seq):
                        IF j =< i
                            THEN IF j = 1 THEN TRUE ELSE seq[j] = seq[j-1]
                            ELSE IF j = Len(seq) THEN TRUE ELSE seq[j] = seq[j+1]
ABE_TwoValsSeq == TwoValsSeq(AtoB) /\ TwoValsSeq(BtoA)

ABESpec == INSTANCE Session11projspec
ABESpecProperty == ABESpec!Spec

====
