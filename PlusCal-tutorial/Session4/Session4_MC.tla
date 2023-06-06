---- MODULE Session4_MC ----
EXTENDS Session4

ConstMinValue == -99999
ConstTuples == UNION { [1..l -> (l+1)..(2*l)]: l \in 0..5 }

====