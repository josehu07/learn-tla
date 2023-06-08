---- MODULE Session11a_MC ----
EXTENDS Session11a

ConstData == {"Fred", "Mary", "Ted"}

ABSpec_TypeOK == (AVar \in Msgs) /\ (BVar \in Msgs)

ABSpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

====