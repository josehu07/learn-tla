---- MODULE Session8 ----
EXTENDS TLC, Integers, FiniteSets

CONSTANT N, Procs
ASSUME /\ N \in Nat
       /\ N > 0
       /\ Procs = 0..(N-1)

(*-- OFF algorithm Alternate
variable turn \in Procs;

process procs \in Procs
begin
    ncs: while TRUE do
            skip;
    enter:  await turn = self;
    cs:     skip;
    exit:   turn := (turn + 1) % N;
    end while;
end process;

end algorithm; *)

(*-- OFF algorithm 1BitProtocol
variable flag = [i \in Procs |-> FALSE];

process procs \in Procs
variable j = 0;
begin
    ncs: while TRUE do
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

(*--algorithm Peterson
variable level = [i \in Procs |-> -1], last_to_enter = [i \in 0..N-2 |-> -1];

process procs \in Procs
variable l = 0, k = 0;
begin
    ncs: while TRUE do
            skip;
    enter:  while l < (N-1) do
                level[self] := l;
    enter2:     last_to_enter[l] := self;
    enter3:     while k < N do
                    if (k /= self) /\ (level[k] >= l) then
    enter4:             if last_to_enter[l] = self then
    enter5:                 await (level[k] < 0) \/ (last_to_enter[l] /= self);
                        end if;
                    end if;
    enter6:         k := k + 1;
                end while;
                l := l + 1;
                k := 0;
            end while;
            l := 0;
    cs:     skip;
    exit:   level[self] := -1;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "a88d1e14" /\ chksum(tla) = "d2e0d6db")
VARIABLES level, last_to_enter, pc, l, k

vars == << level, last_to_enter, pc, l, k >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ level = [i \in Procs |-> -1]
        /\ last_to_enter = [i \in 0..N-2 |-> -1]
        (* Process procs *)
        /\ l = [self \in Procs |-> 0]
        /\ k = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << level, last_to_enter, l, k >>

enter(self) == /\ pc[self] = "enter"
               /\ IF l[self] < (N-1)
                     THEN /\ level' = [level EXCEPT ![self] = l[self]]
                          /\ pc' = [pc EXCEPT ![self] = "enter2"]
                          /\ l' = l
                     ELSE /\ l' = [l EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "cs"]
                          /\ level' = level
               /\ UNCHANGED << last_to_enter, k >>

enter2(self) == /\ pc[self] = "enter2"
                /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
                /\ pc' = [pc EXCEPT ![self] = "enter3"]
                /\ UNCHANGED << level, l, k >>

enter3(self) == /\ pc[self] = "enter3"
                /\ IF k[self] < N
                      THEN /\ IF (k[self] /= self) /\ (level[k[self]] >= l[self])
                                 THEN /\ pc' = [pc EXCEPT ![self] = "enter4"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "enter6"]
                           /\ UNCHANGED << l, k >>
                      ELSE /\ l' = [l EXCEPT ![self] = l[self] + 1]
                           /\ k' = [k EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "enter"]
                /\ UNCHANGED << level, last_to_enter >>

enter6(self) == /\ pc[self] = "enter6"
                /\ k' = [k EXCEPT ![self] = k[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "enter3"]
                /\ UNCHANGED << level, last_to_enter, l >>

enter4(self) == /\ pc[self] = "enter4"
                /\ IF last_to_enter[l[self]] = self
                      THEN /\ pc' = [pc EXCEPT ![self] = "enter5"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "enter6"]
                /\ UNCHANGED << level, last_to_enter, l, k >>

enter5(self) == /\ pc[self] = "enter5"
                /\ (level[k[self]] < 0) \/ (last_to_enter[l[self]] /= self)
                /\ pc' = [pc EXCEPT ![self] = "enter6"]
                /\ UNCHANGED << level, last_to_enter, l, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, l, k >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << last_to_enter, l, k >>

procs(self) == ncs(self) \/ enter(self) \/ enter2(self) \/ enter3(self)
                  \/ enter6(self) \/ enter4(self) \/ enter5(self)
                  \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: procs(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
