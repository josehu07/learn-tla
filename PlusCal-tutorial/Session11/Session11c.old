---------------------------- MODULE Session11c  ----------------------------
(***************************************************************************)
(* Specifies algorithm AB2, which is algorithm AB of module Session11c     *)
(* except with a message of the form [data |-> d, bit |-> b] replaced by   *)
(* the ordered pair <<d, b>>.                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences\* , TLAPS

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == Data \X {0,1}
   (************************************************************************)
   (* Msgs could also be defined by                                        *)
   (*                                                                      *)
   (*     Msgs == {<<d, b>> : d \in Data, b \in {0,1}}                     *)
   (************************************************************************)

(*--algorithm AB2
variable AVar2 \in {msg \in Msgs: msg[2] = 1}, BVar2 = AVar2,
         AtoB = << >>, BtoA = << >>;

process A = "A"
begin
    a: while TRUE do
        either
            AtoB := Append(AtoB, AVar2);
        or
            await BtoA /= << >>;
            if Head(BtoA) = AVar2[2] then
                with d \in Data do
                    AVar2 := <<d, 1 - AVar2[2]>>;
                end with;
            end if;
            BtoA := Tail(BtoA);
        end either;
    end while;
end process;

process B = "B"
begin
    b: while TRUE do
        either
            BtoA := Append(BtoA, BVar2[2]);
        or
            await AtoB /= << >>;
            if Head(AtoB)[2] /= BVar2[2] then
                BVar2 := Head(AtoB);
            end if;
            AtoB := Tail(AtoB);
        end either;
    end while;
end process;

process LoseMsgs = "L"
begin
    c: while TRUE do
        either
            with i \in 1..Len(AtoB) do
                AtoB := RemoveElt(i, AtoB);
            end with;
        or
            with i \in 1..Len(BtoA) do 
                BtoA := RemoveElt(i, BtoA);
            end with;
        end either;
    end while;
end process;
end algorithm; *)

(*--algorithm AB2 {
    variables AVar2 \in Msgs,  BVar2 = AVar2,
              AtoB = <<  >>,  BtoA = <<  >> ;
              
    process (A = "A") {
      a: while (TRUE) { 
            either { AtoB := Append(AtoB, AVar2) }
            or     { await BtoA /= << >> ;
                     if (Head(BtoA) = AVar2[2]) 
                       { with (d \in Data) 
                          { AVar2 := <<d, 1 - AVar2[2]>> } 
                       };
                     BtoA := Tail(BtoA)                                
                   } 
          } 
    }
                      
    process (B = "B") {
      b: while (TRUE) {
           either { BtoA := Append(BtoA, BVar2[2]) }
           or     { await AtoB /= << >> ;
                    if (Head(AtoB)[2] # BVar2[2]) { BVar2 := Head(AtoB) };
                    AtoB := Tail(AtoB)   
                  }  
         } 
    }
                           
    process (LoseMsgs = "L") {
      c: while (TRUE) {
           either with (i \in 1..Len(AtoB)) { AtoB := RemoveElt(i, AtoB) }
           or     with (i \in 1..Len(BtoA)) { BtoA := RemoveElt(i, BtoA) } 
         } 
    } 
 } *)

\* BEGIN TRANSLATION (chksum(pcal) = "24db5976" /\ chksum(tla) = "4d90b6fc")
VARIABLES AVar2, BVar2, AtoB, BtoA

vars == << AVar2, BVar2, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar2 \in {msg \in Msgs: msg[2] = 1}
        /\ BVar2 = AVar2
        /\ AtoB = << >>
        /\ BtoA = << >>

A == /\ \/ /\ AtoB' = Append(AtoB, AVar2)
           /\ UNCHANGED <<AVar2, BtoA>>
        \/ /\ BtoA /= << >>
           /\ IF Head(BtoA) = AVar2[2]
                 THEN /\ \E d \in Data:
                           AVar2' = <<d, 1 - AVar2[2]>>
                 ELSE /\ TRUE
                      /\ AVar2' = AVar2
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ BVar2' = BVar2

B == /\ \/ /\ BtoA' = Append(BtoA, BVar2[2])
           /\ UNCHANGED <<BVar2, AtoB>>
        \/ /\ AtoB /= << >>
           /\ IF Head(AtoB)[2] /= BVar2[2]
                 THEN /\ BVar2' = Head(AtoB)
                 ELSE /\ TRUE
                      /\ BVar2' = BVar2
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ AVar2' = AVar2

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar2, BVar2 >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Nov 26 13:37:42 PST 2021 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
