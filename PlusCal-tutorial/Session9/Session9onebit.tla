---- MODULE Session9onebit ----
EXTENDS TLC, Integers, FiniteSets

CONSTANT N, Procs
ASSUME /\ N \in Nat
       /\ N > 0
       /\ Procs = 0..(N-1)

(*--algorithm 1BitProtocol
variable flag = [i \in Procs |-> FALSE];

fair process procs \in Procs
variable j = 0;
begin
    ncs:- while TRUE do
            skip;
    enter:  flag[self] := TRUE;
    enter2: while j /= self do
                if flag[j] then
    enter3:         flag[self] := FALSE;
    enter4:         await ~flag[j];
                    j := 0;
                    goto enter;
                else
                    j := j + 1;
                end if;
            end while;
            j := self + 1;
    enter5: while j < N do
                await ~flag[j];
                j := j + 1;
            end while;
    cs:     skip;
    exit:   flag[self] := FALSE;
            j := 0;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "d5952dd1" /\ chksum(tla) = "b87ca15c")
VARIABLES flag, pc, j

vars == << flag, pc, j >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ flag = [i \in Procs |-> FALSE]
        (* Process procs *)
        /\ j = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << flag, j >>

enter(self) == /\ pc[self] = "enter"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "enter2"]
               /\ j' = j

enter2(self) == /\ pc[self] = "enter2"
                /\ IF j[self] /= self
                      THEN /\ IF flag[j[self]]
                                 THEN /\ pc' = [pc EXCEPT ![self] = "enter3"]
                                      /\ j' = j
                                 ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                      /\ pc' = [pc EXCEPT ![self] = "enter2"]
                      ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                           /\ pc' = [pc EXCEPT ![self] = "enter5"]
                /\ flag' = flag

enter3(self) == /\ pc[self] = "enter3"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "enter4"]
                /\ j' = j

enter4(self) == /\ pc[self] = "enter4"
                /\ ~flag[j[self]]
                /\ j' = [j EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "enter"]
                /\ flag' = flag

enter5(self) == /\ pc[self] = "enter5"
                /\ IF j[self] < N
                      THEN /\ ~flag[j[self]]
                           /\ j' = [j EXCEPT ![self] = j[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "enter5"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                           /\ j' = j
                /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << flag, j >>

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ j' = [j EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

procs(self) == ncs(self) \/ enter(self) \/ enter2(self) \/ enter3(self)
                  \/ enter4(self) \/ enter5(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: procs(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ procs(self))

\* END TRANSLATION 

====
