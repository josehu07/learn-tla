---- MODULE Session11c_MC ----
EXTENDS Session11c

ConstData == {"Fred", "Mary", "Ted"}

StateConstraint == (Len(AtoB) =< 3) /\ (Len(BtoA) =< 3)

AB2_TypeOK ==  /\ AVar2 \in Msgs
               /\ BVar2 \in Msgs
               /\ AtoB \in Seq(Msgs)
               /\ BtoA \in Seq({0,1})
           
AVar_Impl == [data |-> AVar2[1], bit |-> AVar2[2]]

BVar_Impl == [data |-> BVar2[1], bit |-> BVar2[2]]

\* Implementation with Data Refinement:
ABSpec == INSTANCE Session11a WITH AVar <- AVar_Impl, BVar <- BVar_Impl
   (************************************************************************)
   (* We could replace this statement by                                   *)
   (*                                                                      *)
   (*   ABSpec == INSTANCE Session11a                                      *)
   (*                 WITH AVar <- [data |-> AVar2[1], bit |-> AVar2[2]],  *)
   (*                      BVar <- [data |-> BVar2[1], bit |-> BVar2[2]]   *)
   (************************************************************************)
ABSpecProperty == ABSpec!Spec

====