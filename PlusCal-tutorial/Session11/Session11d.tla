----------------------------- MODULE Session11d ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == [data: Data, bit : {0,1}]

(***************************************************************************
--algorithm AABB  {
   variables AVar \in Msgs,  BVar = AVar,
             AtoB = <<  >>,  BtoA = <<  >> ;

   fair process (ASend = "AS") {
     as: while (TRUE) { AtoB := Append(AtoB, AVar) } 
   }

   fair+ process (ARcv = "AR") {
     ar: while (TRUE) {
           await BtoA /= << >> ;
           if (Head(BtoA) = AVar.bit) 
             { with (d \in Data) 
                { AVar := [data |-> d, bit |-> 1 - AVar.bit] } 
             };
           BtoA := Tail(BtoA)                              
         }  
   }

   fair process (BSend = "BS") {
     bs: while (TRUE) { BtoA := Append(BtoA, BVar.bit) }
   }

   fair+ process (BRcv = "BR") {
     br: while (TRUE) { 
           await AtoB /= << >> ;
           if (Head(AtoB).bit # BVar.bit) { BVar := Head(AtoB) };
           AtoB := Tail(AtoB)  
         }     
   }

   process (LoseMsgs = "C") {
     c: while (TRUE) {
          either with (i \in 1..Len(AtoB)) AtoB := Remove(i, AtoB) 
          or     with (i \in 1..Len(BtoA)) BtoA := Remove(i, BtoA) 
        }
   }   
 }
 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "812d51c0" /\ chksum(tla) = "a180c44")
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"AS"} \cup {"AR"} \cup {"BS"} \cup {"BR"} \cup {"C"}

Init == (* Global variables *)
        /\ AVar \in Msgs
        /\ BVar = AVar
        /\ AtoB = <<  >>
        /\ BtoA = <<  >>

ASend == /\ AtoB' = Append(AtoB, AVar)
         /\ UNCHANGED << AVar, BVar, BtoA >>

ARcv == /\ BtoA /= << >>
        /\ IF Head(BtoA) = AVar.bit
              THEN /\ \E d \in Data:
                        AVar' = [data |-> d, bit |-> 1 - AVar.bit]
              ELSE /\ TRUE
                   /\ AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

BSend == /\ BtoA' = Append(BtoA, BVar.bit)
         /\ UNCHANGED << AVar, BVar, AtoB >>

BRcv == /\ AtoB /= << >>
        /\ IF Head(AtoB).bit # BVar.bit
              THEN /\ BVar' = Head(AtoB)
              ELSE /\ TRUE
                   /\ BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = Remove(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = Remove(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar >>

Next == ASend \/ ARcv \/ BSend \/ BRcv \/ LoseMsgs

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASend)
        /\ SF_vars(ARcv)
        /\ WF_vars(BSend)
        /\ SF_vars(BRcv)

\* END TRANSLATION

Foo == INSTANCE Session11a
=============================================================================
\* Modification History
\* Last modified Wed Nov 24 06:41:06 PST 2021 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
