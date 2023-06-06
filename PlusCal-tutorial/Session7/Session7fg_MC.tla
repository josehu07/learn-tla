---- MODULE Session7fg_MC ----
EXTENDS Session7fg

ConstN == 5

AddCorrect == (\A proc \in ProcSet: pc[proc] = "Done") => (x = N)

TypeOK == /\ x \in 0..N
          /\ \A proc \in ProcSet: t[proc] \in {-1} \cup 0..(N-1)

ProcPairs == {pair \in {<<p, q>>: p, q \in ProcSet}: pair[1] /= pair[2]}
CriticalSecInv == \A pair \in ProcPairs:
                    (pc[pair[1]] \in {"p1", "p2"}) => ~(pc[pair[2]] \in {"p1", "p2"})

====