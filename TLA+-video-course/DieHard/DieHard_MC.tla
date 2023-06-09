---- MODULE DieHard_MC ----
EXTENDS DieHard

ConstSmallCap == 3
ConstBigCap == 5

TypeOK == /\ small \in 0..SmallCap
          /\ big \in 0..BigCap

BigJarNot4 == big /= 4

====
