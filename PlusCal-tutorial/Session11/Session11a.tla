---------------------------- MODULE Session11a ------------------------------
(***************************************************************************)
(* This module contains an algorithm ABSpec that describes what the        *)
(* Alternating Bit protocol is supposed to accomplish.  For a video        *)
(* explaining this algorithm, go to                                        *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/video/video9a.html                  *)
(*                                                                         *)
(* click on "What the Protocol Should Accomplish" and watch that section,  *)
(* which begins 5 min 39 sec into the video and runs for 2 min 13 seconds. *)
(*                                                                         *)
(* Instead of sending strings, this spec sends elements in some constant   *)
(* set Data.  Moreover, instead of sending pairs of values like            *)
(* <<"Mary", 0>>, we send a record [data |-> "Mary", bit |-> 0] for no     *)
(* reason except to give you a little practice using records.  We call the *)
(* set of all such records Msgs, because, in the Alternating Bit protocol, *)
(* those values will be sent as messages.                                  *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data

Msgs == [data: Data, bit : {0,1}]

(****************************************************************************
--algorithm ABSpec {
    variables AVar \in Msgs,  BVar = AVar ;

    process (A = "A") {
      a: while (TRUE) {
           await AVar.bit = BVar.bit ;
           with (d \in Data) { AVar := [data |-> d, bit |-> 1 - AVar.bit] }
         } 
    }

    process (B = "B"){
      b: while (TRUE) { 
           await AVar.bit /= BVar.bit;
           BVar := AVar                             
         } 
    }
  }
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "4827fe5c" /\ chksum(tla) = "d668c466")
VARIABLES AVar, BVar

vars == << AVar, BVar >>

ProcSet == {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ AVar \in Msgs
        /\ BVar = AVar

A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data:
          AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

B == /\ AVar.bit /= BVar.bit
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

ABSpec_TypeOK == (AVar \in Msgs) /\ (BVar \in Msgs)

ABSpec_Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

Liveness == (AVar /= BVar) ~> (AVar = BVar)
=============================================================================
\* Modification History
\* Last modified Wed Nov 24 07:23:30 PST 2021 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport
