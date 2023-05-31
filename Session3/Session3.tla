------------------------------- MODULE Session3 -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT minValue, Tuples
ASSUME /\ minValue \in Int
       /\ Tuples \subseteq Seq(Int)
       /\ \A t \in Tuples: \A i \in 1..Len(t) : t[i] >= minValue

(*--algorithm TupleMax
variables inp \in Tuples,  max = minValue, i = 1 ;  

begin
    assert  \A n \in 1..Len(inp) : inp[n] > minValue ;

    while i =< Len(inp) do
        if inp[i] > max then
            max := inp[i];
        end if;
        i := i + 1
    end while;
    
    assert IF inp = << >>
            THEN max = minValue
            ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                 /\ \A n \in 1..Len(inp) : max >= inp[n]
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "ec40375c" /\ chksum(tla) = "57ee1e17")
VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == (* Global variables *)
        /\ inp \in Tuples
        /\ max = minValue
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue, 
                   "Failure of assertion at line 13, column 5.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << inp, max, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i =< Len(inp)
               THEN /\ IF inp[i] > max
                          THEN /\ max' = inp[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(IF inp = << >>
                               THEN max = minValue
                               ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                    /\ \A n \in 1..Len(inp) : max >= inp[n], 
                              "Failure of assertion at line 22, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << max, i >>
         /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

===========================================
\* Modification History
\* Last modified Sat Dec 26 11:48:57 PST 2020 by claus
\* Created Fri Dec 25 00:00:00 PST 2020 by claus

