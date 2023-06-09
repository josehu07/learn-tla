---- MODULE DieHard ----
EXTENDS TLC, Integers

CONSTANT SmallCap, BigCap

VARIABLES small, big

vars == << small, big >>

Init == /\ small = 0
        /\ big = 0

FillSmall == small' = SmallCap /\ big' = big

FillBig == big' = BigCap /\ small' = small

EmptySmall == small' = 0 /\ big' = big

EmptyBig == big' = 0 /\ small' = small

SmallToBig == IF big + small =< BigCap
                THEN /\ big' = big + small
                     /\ small' = 0
                ELSE /\ big' = BigCap
                     /\ small' = small - (BigCap - big)

BigToSmall == IF big + small =< SmallCap
                THEN /\ small' = big + small
                     /\ big' = 0
                ELSE /\ small' = SmallCap
                     /\ big' = big - (SmallCap - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

====
