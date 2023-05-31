---- MODULE Session3proj ----
EXTENDS TLC, Integers, Sequences

CONSTANT MSet, NSet
ASSUME /\ MSet \subseteq Int
       /\ NSet \subseteq Nat

(*--algorithm ComputePower
variables m \in MSet, n \in NSet, res = 1, i = 1;

begin
    assert /\ m \in Int
           /\ n \in Nat;
    
    while i =< n do
        res := res * m;
        i := i + 1;
    end while;
        
    assert res = m ^ n;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "837e543b" /\ chksum(tla) = "8a8883fb")
VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

Init == (* Global variables *)
        /\ m \in MSet
        /\ n \in NSet
        /\ res = 1
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(/\ m \in Int
                   /\ n \in Nat, 
                   "Failure of assertion at line 12, column 5.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << m, n, res, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i =< n
               THEN /\ res' = res * m
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(res = m ^ n, 
                              "Failure of assertion at line 20, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << res, i >>
         /\ UNCHANGED << m, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
