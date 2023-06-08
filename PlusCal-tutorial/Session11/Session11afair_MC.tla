---- MODULE Session11afair_MC ----
EXTENDS Session11afair

ConstData == {"Fred", "Mary", "Ted"}

ABSpec_TypeOK == (AVar \in Msgs) /\ (BVar \in Msgs)

ABSpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

InfinitelyAlternating == []<>(AVar = BVar) /\ []<>(AVar /= BVar)

Liveness == (AVar /= BVar) ~> (AVar = BVar)

====