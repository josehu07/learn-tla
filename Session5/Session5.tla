------------------------------ MODULE Session5 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Tuples, minValue
ASSUME /\ Tuples \subseteq Seq(Int)
       /\ minValue \in Int
       /\ \A t \in Tuples : \A i \in 1..Len(t) : t[i] > minValue 

(*--algorithm TupleMaxND {
   variables inp \in Tuples, max = minValue, I = 1..Len(inp) ;    
   { while (I /= {}) {
       with (i \in I) {
         if (inp[i] > max) { max := inp[i] } ;
         I := I \ {i}
       }
     } ;
     assert IF inp = << >> THEN max = minValue
                           ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                /\ \A n \in 1..Len(inp) : max >= inp[n]
   }
} *)

\* BEGIN TRANSLATION (chksum(pcal) = "53b5c462" /\ chksum(tla) = "fb4ac102")
VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init == (* Global variables *)
        /\ inp \in Tuples
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF I /= {}
               THEN /\ \E i \in I:
                         /\ IF inp[i] > max
                               THEN /\ max' = inp[i]
                               ELSE /\ TRUE
                                    /\ max' = max
                         /\ I' = I \ {i}
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(IF inp = << >> THEN max = minValue
                                             ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                                  /\ \A n \in 1..Len(inp) : max >= inp[n], 
                              "Failure of assertion at line 17, column 6.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << max, I >>
         /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Wed Jan 13 18:38:54 PST 2021 by lamport
\* Created Fri Dec 25 16:30:13 PST 2020 by claus
