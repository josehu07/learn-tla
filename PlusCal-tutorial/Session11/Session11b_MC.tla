---- MODULE Session11b_MC ----
EXTENDS Session11b

ConstData == {"Fred", "Mary", "Ted"}

StateConstraint == (Len(AtoB) =< 3) /\ (Len(BtoA) =< 3)

AB_TypeOK ==  /\ AVar \in Msgs
              /\ BVar \in Msgs
              /\ AtoB \in Seq(Msgs)
              /\ BtoA \in Seq({0,1})

AB_Inv == (BtoA # << >>) /\ (Head(BtoA) = AVar.bit) => (AVar = BVar)

TwoValsSeq(seq) == \E i \in 0..Len(seq): \A j \in 1..Len(seq):
                        IF j =< i
                            THEN IF j = 1 THEN TRUE ELSE seq[j] = seq[j-1]
                            ELSE IF j = Len(seq) THEN TRUE ELSE seq[j] = seq[j+1]
AB_TwoValsSeq == TwoValsSeq(AtoB) /\ TwoValsSeq(BtoA)

ABSpec == INSTANCE Session11a
ABSpecProperty == ABSpec!Spec

====