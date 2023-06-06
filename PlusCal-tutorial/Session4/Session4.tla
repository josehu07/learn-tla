------------------------------ MODULE Session4 ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Tuples, minValue
ASSUME /\ Tuples \subseteq Seq(Int)
       /\ minValue \in Int
       /\ \A t \in Tuples : \A i \in 1..Len(t) : t[i] > minValue

(*--algorithm TupleMaxND
variables inp \in Tuples, max = minValue, I = 1..Len(inp) ; 

begin
    while I /= {} do
        with i \in I do
            if inp[i] > max then
                max := inp[i];
            end if;
            I := I \ {i};
        end with;
    end while;

    assert IF inp = << >>
            THEN max = minValue
            ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                 /\ \A n \in 1..Len(inp) : max >= inp[n]
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "48cc0d40" /\ chksum(tla) = "50ed721e")
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
               ELSE /\ Assert(IF inp = << >>
                               THEN max = minValue
                               ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                    /\ \A n \in 1..Len(inp) : max >= inp[n], 
                              "Failure of assertion at line 22, column 5.")
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
\* Last modified Sun Jan 10 12:01:14 PST 2021 by lamport
\* Created Fri Jan 08 16:30:13 PST 2021 by lamport
