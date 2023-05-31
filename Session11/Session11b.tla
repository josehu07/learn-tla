----------------------------- MODULE Session11b ----------------------------
(***************************************************************************)
(* This module describes the Alternating Bit protocol, omitting liveness   *)
(* requirements.                                                           *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> 
                       IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == [data: Data, bit : {0,1}]

(***************************************************************************
--algorithm AB {
    variables AVar \in Msgs,  BVar = AVar,
              AtoB = <<  >>,  BtoA = <<  >> ;
              
    process (A = "A") {
      a: while (TRUE) { 
            either { AtoB := Append(AtoB, AVar) }
            or     { await BtoA /= << >> ;
                     if (Head(BtoA) = AVar.bit) 
                       { with (d \in Data) 
                          { AVar := [data |-> d, bit |-> 1 - AVar.bit] } 
                       };
                     BtoA := Tail(BtoA)                                
                   } 
          } 
    }
                      
    process (B = "B") {
      b: while (TRUE) {
           either { BtoA := Append(BtoA, BVar.bit) }
           or     { await AtoB /= << >> ;
                    if (Head(AtoB).bit /= BVar.bit) { BVar := Head(AtoB) };
                    AtoB := Tail(AtoB)   
                  }  
         } 
    }
                            
    process (LoseMsgs = "L") {
      c: while (TRUE) {
           either with (i \in 1..Len(AtoB)) { AtoB := RemoveElt(i, AtoB) }
           or     with (i \in 1..Len(BtoA)) { BtoA := RemoveElt(i, BtoA) } 
         } 
    } 
 }
 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "b444f4b2" /\ chksum(tla) = "5c071f24")
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar \in Msgs
        /\ BVar = AVar
        /\ AtoB = <<  >>
        /\ BtoA = <<  >>

A == /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED <<AVar, BtoA>>
        \/ /\ BtoA /= << >>
           /\ IF Head(BtoA) = AVar.bit
                 THEN /\ \E d \in Data:
                           AVar' = [data |-> d, bit |-> 1 - AVar.bit]
                 ELSE /\ TRUE
                      /\ AVar' = AVar
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ BVar' = BVar

B == /\ \/ /\ BtoA' = Append(BtoA, BVar.bit)
           /\ UNCHANGED <<BVar, AtoB>>
        \/ /\ AtoB /= << >>
           /\ IF Head(AtoB).bit /= BVar.bit
                 THEN /\ BVar' = Head(AtoB)
                 ELSE /\ TRUE
                      /\ BVar' = BVar
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ AVar' = AVar

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
AB_TypeOK ==  /\ AVar \in Msgs
              /\ BVar \in Msgs
              /\ AtoB \in Seq(Msgs)
              /\ BtoA \in Seq({0,1})

Inv == (BtoA # << >>) /\ (Head(BtoA) = AVar.bit) => (AVar = BVar)
           
Foo == INSTANCE Session11a
=============================================================================
\* Modification History
\* Last modified Wed Nov 24 07:22:31 PST 2021 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
