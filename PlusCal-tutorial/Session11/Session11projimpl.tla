----------------------------- MODULE Session11projimpl ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == [data: Data, bit : {0,1}]

(*--algorithm AABBE
variables AVar \in {msg \in Msgs: msg.bit = 1}, BVar = AVar,
          AtoB = << >>, BtoA = << >>;

fair process ASend = "AS"
begin
    as: while TRUE do
        AtoB := Append(AtoB, AVar);
    end while;
end process;

fair+ process ARecv = "AR"
begin
    ar: while TRUE do
        await BtoA /= << >>;
        if Head(BtoA) = AVar.bit then
            with d \in Data do
                AVar := [data |-> d, bit |-> 1 - AVar.bit];
            end with;
        end if;
        BtoA := Tail(BtoA);
    end while;
end process;

fair process BSend = "BS"
begin
    bs: while TRUE do
        BtoA := Append(BtoA, BVar.bit);
    end while;
end process;

fair+ process BRecv = "BR"
begin
    br: while TRUE do
        await AtoB /= << >>;
        if Head(AtoB).bit /= BVar.bit then
            BVar := Head(AtoB);
        end if;
        AtoB := Tail(AtoB);
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

\* BEGIN TRANSLATION (chksum(pcal) = "df6d355d" /\ chksum(tla) = "72d9443f")
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"AS"} \cup {"AR"} \cup {"BS"} \cup {"BR"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar \in {msg \in Msgs: msg.bit = 1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASend == /\ AtoB' = Append(AtoB, AVar)
         /\ UNCHANGED << AVar, BVar, BtoA >>

ARecv == /\ BtoA /= << >>
         /\ IF Head(BtoA) = AVar.bit
               THEN /\ \E d \in Data:
                         AVar' = [data |-> d, bit |-> 1 - AVar.bit]
               ELSE /\ TRUE
                    /\ AVar' = AVar
         /\ BtoA' = Tail(BtoA)
         /\ UNCHANGED << BVar, AtoB >>

BSend == /\ BtoA' = Append(BtoA, BVar.bit)
         /\ UNCHANGED << AVar, BVar, AtoB >>

BRecv == /\ AtoB /= << >>
         /\ IF Head(AtoB).bit /= BVar.bit
               THEN /\ BVar' = Head(AtoB)
               ELSE /\ TRUE
                    /\ BVar' = BVar
         /\ AtoB' = Tail(AtoB)
         /\ UNCHANGED << AVar, BtoA >>

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar >>

Next == ASend \/ ARecv \/ BSend \/ BRecv \/ LoseMsgs

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASend)
        /\ SF_vars(ARecv)
        /\ WF_vars(BSend)
        /\ SF_vars(BRecv)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Nov 24 06:41:06 PST 2021 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
