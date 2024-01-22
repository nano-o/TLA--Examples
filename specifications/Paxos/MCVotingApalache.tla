--------------------------- MODULE MCVotingApalache -------------------------------

EXTENDS Integers

Value == {"V1_OF_VALUE","V2_OF_VALUE"}
Acceptor == {"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}
\* The quorums are the sets of 2 acceptors:
Quorum == {
    {"A1_OF_ACCEPTOR","A2_OF_ACCEPTOR"},
    {"A1_OF_ACCEPTOR","A3_OF_ACCEPTOR"},
    {"A2_OF_ACCEPTOR","A3_OF_ACCEPTOR"}}

MaxBal == 2
Ballot == 0..MaxBal \* NOTE: has to be finite for `^Apalache^' because it is used as the domain of a function

VARIABLES
    \* @type: ACCEPTOR -> Set(<<Int,VALUE>>);
    votes,
    \* @type: ACCEPTOR -> Int;
    maxBal

INSTANCE VotingApalache

\* To install `^Apalache,^' see the `^Apalache^' website at `^https://apalache.informal.systems/^'.
\* Note that this is not necessary if you are using the devcontainer, as `^Apalache,^' is already installed.
\* To check that the invariant holds initially, run:
\* apalache-mc check --init=Init --inv=Invariant --length=0 MCVotingApalache.tla
\* To check that the invariant is preserved, run:
\* apalache-mc check '--tuning-options=search.invariantFilter=1->.*' --init=Invariant --inv=Invariant --length=1 MCVotingApalache.tla

===================================================================================

