------------------------------- MODULE VotingApalache -------------------------------

EXTENDS Integers

ValueOrNone == {"V1_OF_VALUEORNONE","NONE_OF_VALUEORNONE"}
Value == {"V1_OF_VALUEORNONE"}
Acceptor == {"A1_OF_ACCEPTOR"}
Quorum == {{"A1_OF_ACCEPTOR"}}

Ballot == 0..3 \* NOTE: has to be finite for Apalache because it is used a the domain of a function

None == "NONE_OF_VALUEORNONE"

VARIABLES
    \* @type: ACCEPTOR -> Set(<<Int,VALUEORNONE>>);
    votes,
    \* @type: ACCEPTOR -> Int;
    maxBal

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times ValueOrNone)]
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

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: Apalache does not support non-constant integer ranges
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b /\ \A a \in Q : DidNotVoteAt(a, d)

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

=====================================================================================
