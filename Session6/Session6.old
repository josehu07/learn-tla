------------------------------ MODULE Session6 ------------------------------
EXTENDS Integers, TLC

CONSTANT NSet
ASSUME \A n \in NSet: n \in Nat

(*--algorithm Square
variable n \in NSet, x = 0, i = 0;

begin
    a: while i < n do
        i := i + 1;
        b: x := x + (2*i - 1);
    end while;

    \* assert FALSE
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "1f3e42de" /\ chksum(tla) = "a083c2a")
VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == (* Global variables *)
        /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << n, x >>

b == /\ pc = "b"
     /\ x' = x + (2*i - 1)
     /\ pc' = "a"
     /\ UNCHANGED << n, i >>

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
