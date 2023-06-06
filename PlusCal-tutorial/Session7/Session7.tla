------------------------------ MODULE Session7 ------------------------------
EXTENDS Integers

(*--algorithm Add2
variable x = 0;

process A = "ProcA"
begin
    a: x := x + 1
end process;

process B = "ProcB"
begin
    b: x := x + 1
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "95e0a33" /\ chksum(tla) = "fe9d3937")
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"ProcA"} \cup {"ProcB"}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "ProcA" -> "a"
                                        [] self = "ProcB" -> "b"]

a == /\ pc["ProcA"] = "a"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

A == a

b == /\ pc["ProcB"] = "b"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

B == b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == A \/ B
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
