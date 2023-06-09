---- MODULE Session9alt ----
EXTENDS TLC, Integers

CONSTANT N, Procs
ASSUME /\ N \in Nat
       /\ N > 0
       /\ Procs = 0..(N-1)

(*--algorithm Alternate
variable turn \in Procs;

fair process procs \in Procs
begin
    ncs: while TRUE do
            skip;
    enter:  await turn = self;
    cs:     skip;
    exit:   turn := (turn + 1) % N;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "22b4e645" /\ chksum(tla) = "f601b133")
VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ turn \in Procs
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ turn' = turn

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ turn' = turn

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (turn + 1) % N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

procs(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: procs(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(procs(self))

\* END TRANSLATION 
====
