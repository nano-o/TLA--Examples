--------------------------- MODULE ApaVoting -------------------------------

EXTENDS Integers

CONSTANT
    \* @type: Set(VALUE);
    Value,
    \* @type: Set(ACCEPTOR);
    Acceptor,
    \* @type: Set(Set(ACCEPTOR));
    Quorum

MaxBal == 2
ApaBallot == 0..MaxBal

VARIABLES
    \* @type: ACCEPTOR -> Set(<<Int,VALUE>>);
    votes,
    \* @type: ACCEPTOR -> Int;
    maxBal

INSTANCE Voting

\* SafeAt and ShowsSafeAt, as defined in Voting.tla, using non-constant integer ranges that are not supported by Apalache. We therefore rewrite them without using ranges:

ApaSafeAt(b, v) == \A c \in Ballot : c < b => NoneOtherChoosableAt(c, v)

ApaShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: `^Apalache^' does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)


\* The indutive invariant:

NoVoteAfterMaxBal == \A a \in Acceptor, b \in Ballot, v \in Value :
    <<b,v>> \in votes[a] => /\ b <= maxBal[a]

Consistency == \A v,w \in chosen : v = w

\* This invariant is inductive and establishes consistency:
Invariant ==
  /\ TypeOK
  /\ VotesSafe
  /\ OneValuePerBallot
  /\ NoVoteAfterMaxBal
  /\ Consistency

===================================================================================
