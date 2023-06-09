----------------------------- MODULE Session11projimpl ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Msgs == [data: Data, bit : {0,1}]

(*--algorithm AABBE
variables AVar \in Msgs, BVar = AVar,
          NewValQueue = << >>,
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
            await Len(NewValQueue) > 0;
            AVar := [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit];
            NewValQueue := Tail(NewValQueue);
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

process E = "E"
begin
    e: while TRUE do
        await AVar = BVar;
        with d \in Data do
            NewValQueue := Append(NewValQueue, d);
        end with;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "5345c49e" /\ chksum(tla) = "b0e7f8eb")
VARIABLES AVar, BVar, NewValQueue, AtoB, BtoA

vars == << AVar, BVar, NewValQueue, AtoB, BtoA >>

ProcSet == {"AS"} \cup {"AR"} \cup {"BS"} \cup {"BR"} \cup {"L"} \cup {"E"}

Init == (* Global variables *)
        /\ AVar \in Msgs
        /\ BVar = AVar
        /\ NewValQueue = << >>
        /\ AtoB = << >>
        /\ BtoA = << >>

ASend == /\ AtoB' = Append(AtoB, AVar)
         /\ UNCHANGED << AVar, BVar, NewValQueue, BtoA >>

ARecv == /\ BtoA /= << >>
         /\ IF Head(BtoA) = AVar.bit
               THEN /\ Len(NewValQueue) > 0
                    /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
                    /\ NewValQueue' = Tail(NewValQueue)
               ELSE /\ TRUE
                    /\ UNCHANGED << AVar, NewValQueue >>
         /\ BtoA' = Tail(BtoA)
         /\ UNCHANGED << BVar, AtoB >>

BSend == /\ BtoA' = Append(BtoA, BVar.bit)
         /\ UNCHANGED << AVar, BVar, NewValQueue, AtoB >>

BRecv == /\ AtoB /= << >>
         /\ IF Head(AtoB).bit /= BVar.bit
               THEN /\ BVar' = Head(AtoB)
               ELSE /\ TRUE
                    /\ BVar' = BVar
         /\ AtoB' = Tail(AtoB)
         /\ UNCHANGED << AVar, NewValQueue, BtoA >>

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB):
                       AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA):
                       BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar, NewValQueue >>

E == /\ AVar = BVar
     /\ \E d \in Data:
          NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == ASend \/ ARecv \/ BSend \/ BRecv \/ LoseMsgs \/ E

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
