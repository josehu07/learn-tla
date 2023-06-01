---- MODULE Session6_MC ----
EXTENDS Session6

ConstNSet == {2, 7, 0}

SquareCorrect == (pc = "Done") => (x = n^2)

TypeOK == /\ n \in Nat
          /\ x \in 0..n^2
          /\ i \in 0..n
          /\ pc \in {"a", "b", "Done"}

ReachableStateInv == /\ TypeOK
                     /\ (pc = "a") => (x = i^2)
                     /\ (pc = "b") => (x = (i-1)^2) /\ (i > 0)
                     /\ (pc = "Done") => (x = n^2) /\ (i = n)

====