---- MODULE Session9sem ----
EXTENDS TLC, Integers

CONSTANT N, Procs
ASSUME /\ N \in Nat
       /\ N > 0
       /\ Procs = 0..(N-1)

(*--algorithm SemMutex
variable sem = 1;

fair process procs \in Procs
begin
    ncs:- while TRUE do
            skip;
    enter:+ await sem = 1;
            sem := 0;
    cs:     skip;
    exit:   sem := 1;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "855ad01c" /\ chksum(tla) = "db0decc1")
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ sem = 1
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ sem' = sem

enter(self) == /\ pc[self] = "enter"
               /\ sem = 1
               /\ sem' = 0
               /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ sem' = sem

exit(self) == /\ pc[self] = "exit"
              /\ sem' = 1
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

procs(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: procs(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ procs(self)) /\ SF_vars(enter(self))

\* END TRANSLATION 

====
