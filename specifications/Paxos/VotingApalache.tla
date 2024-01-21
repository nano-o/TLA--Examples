------------------------------- MODULE VotingApalache -------------------------------

\* Version of Voting.tla that works with Apalache

EXTENDS Integers, FiniteSets

Value == {"V1_OF_VALUEORNONE","V2_OF_VALUEORNONE","V3_OF_VALUEORNONE"}
Acceptor == {"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}
\* The quorums are the sets of 2 acceptors:
Quorum == {{"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR"},{"A1_OF_ACCEPTOR","A3_OF_ACCEPTOR"},{"A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}}
\* The quorums are the sets consisting of a strict majority of the acceptors:
(* Quorum == {Q \in SUBSET Acceptor : 2*Cardinality(Q)>Cardinality(Acceptor)} *)

MaxBal == 3 \* 1m45s with MaxBal=3
Ballot == 0..MaxBal \* NOTE: has to be finite for Apalache because it is used as the domain of a function

VARIABLES
    \* @type: ACCEPTOR -> Set(<<Int,VALUEORNONE>>);
    votes,
    \* @type: ACCEPTOR -> Int;
    maxBal

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ maxBal \in [Acceptor -> Ballot\cup {-1}]
TypeOK_ == TypeOK

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) ==
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: Apalache does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)

VoteFor(a, b, v) ==
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next  ==  \E a \in Acceptor, b \in Ballot :
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)

ChosenAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

Safety == \A v,w \in chosen : v = w

Canary1 == \neg (
    \E a \in Acceptor : votes[a] # {}
)

Canary2 == \neg (
    /\  chosen # {}
    /\  \A a \in Acceptor : \A vt \in votes[a] : vt[2] \in chosen => vt[1] > 1
    /\  \E a \in Acceptor : \E vt \in votes[a] : vt[2] \notin chosen /\ vt[1] = 0
)

SafeAt(b, v) == \A c \in Ballot : c < b => NoneOtherChoosableAt(c, v)

Inv0 == \A a \in Acceptor, b \in Ballot, v \in Value :
  <<b,v>> \in votes[a] => b <= maxBal[a]
Inv0_ == TypeOK /\ Inv0

Inv1 == \A a1,a2 \in Acceptor, b \in Ballot, v1,v2 \in Value :
  <<b,v1>> \in votes[a1] /\ <<b,v2>> \in votes[a2] => v1 = v2
Inv1_ == TypeOK /\ Inv1

Inv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
  <<b,v>> \in votes[a] => SafeAt(b,v)
Inv2_ == TypeOK /\ Inv0 /\ Inv1 /\ Inv2

Safety_ante == TypeOK /\ Inv1 /\ Inv2 \* We need the fact that a node does not vote for two different values in the same ballot

\* This invariant is inductive and establishes the safety property:
Invariant ==
  /\ TypeOK
  /\ \A a \in Acceptor, b \in Ballot, v \in Value  :
    <<b,v>> \in votes[a] => \* If acceptor a votes for v in ballot b, then:
      /\ b <= maxBal[a] \* b is smaller than or equal to maxBal[a]
      \* No other acceptor votes for different values in the same round:
      /\ \A a2 \in Acceptor, v2 \in Value : <<b,v2>> \in votes[a2] => v = v2
      /\ SafeAt(b,v) \* v is safe at b
  /\ Safety
Invariant_ == Invariant

\* To check that the invariant holds initially, run:
\* ${APALACHE_HOME}/script/run-docker.sh check --init=Init --inv=Invariant --length=0 VotingApalache.tla
\* To check that the invariant is preserved, run:
\* ${APALACHE_HOME}/script/run-docker.sh check search.invariantFilter=1->.*' --init=Invariant --inv=Invariant --length=1 VotingApalache.tla

=====================================================================================
