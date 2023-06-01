------------------------------ MODULE Session7fg ------------------------------
EXTENDS Integers

CONSTANT N
ASSUME (N \in Nat) /\ (N > 0)

(*--algorithm Add2FGSem
variable x = 0, sem = 1;

process Procs \in 1..N
variable t = -1;
begin
    lock: await sem = 1;
          sem := 0;
    p1: t := x;
    p2: x := t + 1;
    unlock: sem := 1;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "20bbc7b2" /\ chksum(tla) = "f5955bc4")
VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ sem = 1
        (* Process Procs *)
        /\ t = [self \in 1..N |-> -1]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ sem = 1
              /\ sem' = 0
              /\ pc' = [pc EXCEPT ![self] = "p1"]
              /\ UNCHANGED << x, t >>

p1(self) == /\ pc[self] = "p1"
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << x, sem >>

p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << sem, t >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << x, t >>

Procs(self) == lock(self) \/ p1(self) \/ p2(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: Procs(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Feb 12 09:46:15 PST 2021 by lamport
\* Created Fri Feb 12 09:44:05 PST 2021 by lamport
