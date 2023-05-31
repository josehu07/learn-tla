The module begins with a string of four or more - characters. Text that
precedes the module is ignored.

------------------------------- MODULE Session2 -------------------------------
EXTENDS Integers, TLC
 
(*--algorithm AnyName {
   variable x = {"a", "b"}, y = <<1, 2, 3>> ;
   {  
     x := x \cup {"c"} ;
     print x ;
     y[2] := 4 ;
     print y ;
   }
} *)

\* BEGIN TRANSLATION (chksum(pcal) = "4e2a2588" /\ chksum(tla) = "1d904e56")
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = (x \cup {"c"})
         /\ PrintT(x')
         /\ y' = [y EXCEPT ![2] = 4]
         /\ PrintT(y')
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* This is a single-line comment.  
\* The module is ended by a string of four or more = characters.  
===============================================================================
Text that follows the module is ignored.  The Toolbox maintains the following 
information.

\* Modification History
\* Last modified Tue Dec 22 16:15:06 PST 2020 by lamport
\* Created Sat Dec 05 17:41:14 PST 2020 by lamport
