------------------------------ MODULE Session6 ------------------------------
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat

(*********

--algorithm Square {
  variable x = 0, i = 0 ;
  { a: while (i < N) {
           i := i + 1  ;
        b: x := x + (2*i - 1) ;
       } ;
  }
}

*********)
\* BEGIN TRANSLATION (chksum(pcal) = "1721f49f" /\ chksum(tla) = "f182e238")
VARIABLES x, i, pc

vars == << x, i, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < N
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ i' = i
     /\ x' = x

b == /\ pc = "b"
     /\ x' = x + (2*i - 1)
     /\ pc' = "a"
     /\ i' = i

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jan 17 16:54:37 PST 2021 by lamport
\* Created Sun Jan 17 14:43:02 PST 2021 by claus
