---------------------------- MODULE Session11projspec ------------------------------
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
EXTENDS Integers, Sequences

CONSTANT Data

Msgs == [data: Data, bit : {0,1}]

(*--algorithm ABESpec
variables AVar \in Msgs, BVar = AVar,
          NewValQueue = << >>;

fair process A = "A"
begin
    a: while TRUE do
        await Len(NewValQueue) > 0;
        AVar := [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit];
        NewValQueue := Tail(NewValQueue);
    end while;
end process;

fair process B = "B"
begin
    b: while TRUE do
        await AVar.bit /= BVar.bit;
        BVar := AVar;
    end while;
end process;

process E = "E"
begin
    e: while TRUE do
        await AVar.bit = BVar.bit;
        with d \in Data do
            NewValQueue := Append(NewValQueue, d);
        end with;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "23583917" /\ chksum(tla) = "333c5d95")
VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

ProcSet == {"A"} \cup {"B"} \cup {"E"}

Init == (* Global variables *)
        /\ AVar \in Msgs
        /\ BVar = AVar
        /\ NewValQueue = << >>

A == /\ Len(NewValQueue) > 0
     /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
     /\ NewValQueue' = Tail(NewValQueue)
     /\ BVar' = BVar

B == /\ AVar.bit /= BVar.bit
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

E == /\ AVar.bit = BVar.bit
     /\ \E d \in Data:
          NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Nov 24 07:23:30 PST 2021 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport
