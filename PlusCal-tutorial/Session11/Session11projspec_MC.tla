---- MODULE Session11projspec_MC ----
EXTENDS Session11projspec

ConstData == {"Fred", "Mary", "Ted"}

ABESpec_TypeOK == (AVar \in Msgs) /\ (BVar \in Msgs)

ABESpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

InfinitelyAlternating == []<>(AVar = BVar) /\ []<>(AVar /= BVar)

Liveness == (AVar /= BVar) ~> (AVar = BVar)

====