---------------------------- MODULE Session11c  ----------------------------
(***************************************************************************)
(* Specifies algorithm AB2, which is algorithm AB of module Session11c     *)
(* except with a message of the form [data |-> d, bit |-> b] replaced by   *)
(* the ordered pair <<d, b>>.                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences\* , TLAPS

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == Data \X {0,1}
   (************************************************************************)
   (* Msgs could also be defined by                                        *)
   (*                                                                      *)
   (*     Msgs == {<<d, b>> : d \in Data, b \in {0,1}}                     *)
   (************************************************************************)

(***************************************************************************
--algorithm AB2 {
    variables AVar2 \in Msgs,  BVar2 = AVar2,
              AtoB = <<  >>,  BtoA = <<  >> ;
              
    process (A = "A") {
      a: while (TRUE) { 
            either { AtoB := Append(AtoB, AVar2) }
            or     { await BtoA /= << >> ;
                     if (Head(BtoA) = AVar2[2]) 
                       { with (d \in Data) 
                          { AVar2 := <<d, 1 - AVar2[2]>> } 
                       };
                     BtoA := Tail(BtoA)                                
                   } 
          } 
    }
                      
    process (B = "B") {
      b: while (TRUE) {
           either { BtoA := Append(BtoA, BVar2[2]) }
           or     { await AtoB /= << >> ;
                    if (Head(AtoB)[2] # BVar2[2]) { BVar2 := Head(AtoB) };
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
\* BEGIN TRANSLATION (chksum(pcal) = "ee938e83" /\ chksum(tla) = "37d308eb")
VARIABLES AVar2, BVar2, AtoB, BtoA

vars == << AVar2, BVar2, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar2 \in Msgs
        /\ BVar2 = AVar2
        /\ AtoB = <<  >>
        /\ BtoA = <<  >>

A == /\ \/ /\ AtoB' = Append(AtoB, AVar2)
           /\ UNCHANGED <<AVar2, BtoA>>
        \/ /\ BtoA /= << >>
           /\ IF Head(BtoA) = AVar2[2]
                 THEN /\ \E d \in Data:
                           AVar2' = <<d, 1 - AVar2[2]>>
                 ELSE /\ TRUE
                      /\ AVar2' = AVar2
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ BVar2' = BVar2

B == /\ \/ /\ BtoA' = Append(BtoA, BVar2[2])
           /\ UNCHANGED <<BVar2, AtoB>>
        \/ /\ AtoB /= << >>
           /\ IF Head(AtoB)[2] # BVar2[2]
                 THEN /\ BVar2' = Head(AtoB)
                 ELSE /\ TRUE
                      /\ BVar2' = BVar2
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ AVar2' = AVar2

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar2, BVar2 >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Here is the type-correctness invariant.                                 *)
(***************************************************************************)
AB2_TypeOK ==  /\ AVar2 \in Msgs
               /\ BVar2 \in Msgs
               /\ AtoB \in Seq(Msgs)
               /\ BtoA \in Seq({0,1})
           
AVar_Impl == [data |-> AVar2[1], bit |-> AVar2[2]]

BVar_Impl == [data |-> BVar2[1], bit |-> BVar2[2]]

Foo == INSTANCE Session11a WITH AVar <- AVar_Impl, BVar <- BVar_Impl
   (************************************************************************)
   (* We could replace this statement by                                   *)
   (*                                                                      *)
   (*   Foo == INSTANCE Session11a                                         *)
   (*              WITH AVar <- [data |-> AVar2[1], bit |-> AVar2[2]],     *)
   (*                   BVar <- [data |-> BVar2[1], bit |-> BVar2[2]]      *)
   (************************************************************************)
=============================================================================
\* Modification History
\* Last modified Fri Nov 26 13:37:42 PST 2021 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
