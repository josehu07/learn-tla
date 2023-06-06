---- MODULE Session6func_MC ----
EXTENDS Session6func

ConstNSet == {2, 7, 0}

SquareCorrect == (pc = "Done") => (\A j \in 0..n: x[j] = j^2)

TypeOK == /\ n \in Nat
          /\ x \in [0..n -> 0..n^2]
          /\ i \in 0..n
          /\ pc \in {"a", "b", "Done"}

ReachableStateInv == /\ TypeOK
                     /\ (pc = "a") => (x[i] = i^2)
                     /\ (pc = "b") => (x[i-1] = (i-1)^2) /\ (i > 0)
                     /\ (pc = "Done") => (\A j \in 0..n: x[j] = j^2) /\ (i = n)

====