------------------------------ MODULE Session6func ------------------------------
EXTENDS Integers, TLC

CONSTANT NSet
ASSUME \A n \in NSet: n \in Nat

(*--algorithm Square
variable n \in NSet, x = [j \in 0..n |-> 0], i = 0;

begin
    a: while i < n do
        i := i + 1;
        x[i] := x[i-1] + (2*i - 1);
    end while;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "ca19c291" /\ chksum(tla) = "496323bb")
VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == (* Global variables *)
        /\ n \in NSet
        /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ x' = [x EXCEPT ![i'] = x[i'-1] + (2*i' - 1)]
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << x, i >>
     /\ n' = n

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Jan 17 16:54:37 PST 2021 by lamport
\* Created Sun Jan 17 14:43:02 PST 2021 by claus
