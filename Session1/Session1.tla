------------------------------ MODULE Session1 ------------------------------
EXTENDS TLC, Integers

(*--algorithm Session1
variables x \in 1..10;

begin
    assert x ^ 2 <= 100;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "dd41ef93" /\ chksum(tla) = "b20ba679")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x ^ 2 <= 100, "Failure of assertion at line 8, column 5.")
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Dec 17 15:34:55 PST 2020 by lamport
\* Created Sat Dec 05 17:41:14 PST 2020 by lamport
