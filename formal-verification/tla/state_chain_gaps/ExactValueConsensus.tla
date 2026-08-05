----------------------- MODULE ExactValueConsensus -----------------------
(***************************************************************************)
(* Model of cf-elections ExactValue::check_consensus.                      *)
(*                                                                         *)
(* Source: electoral_systems/exact_value.rs ~215-239                       *)
(* utilities/src/lib.rs:                                                   *)
(*   threshold_from_share_count(n) = (2n-1)/3                              *)
(*   success_threshold_from_share_count(n) = threshold + 1                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Authorities,
    VoteValues

VARIABLES
    votes,      \* [Authorities -> VoteValues \union {"Abstain"}]
    consensus   \* VoteValues \union {"None"}

vars == <<votes, consensus>>

n == Cardinality(Authorities)
Threshold == IF n = 0 THEN 0 ELSE (2 * n - 1) \div 3
SuccessThreshold == Threshold + 1

Count(v) == Cardinality({a \in Authorities : votes[a] = v})
ActiveCount == Cardinality({a \in Authorities : votes[a] # "Abstain"})

Init ==
    /\ votes \in [Authorities -> (VoteValues \union {"Abstain"})]
    /\ consensus = "None"

Evaluate ==
    /\ consensus = "None"
    /\ IF ActiveCount >= SuccessThreshold /\
          \E v \in VoteValues : Count(v) >= SuccessThreshold
       THEN consensus' = CHOOSE v \in VoteValues : Count(v) >= SuccessThreshold
       ELSE UNCHANGED consensus
    /\ UNCHANGED votes

Next == Evaluate \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ votes \in [Authorities -> (VoteValues \union {"Abstain"})]
    /\ consensus \in (VoteValues \union {"None"})

AtMostOneConsensusValue ==
    Cardinality({v \in VoteValues : Count(v) >= SuccessThreshold}) <= 1

ConsensusSound ==
    consensus \in VoteValues => Count(consensus) >= SuccessThreshold

UniqueConsensus ==
    \A v1, v2 \in VoteValues :
        (Count(v1) >= SuccessThreshold /\ Count(v2) >= SuccessThreshold) => v1 = v2

AbstentionSafety ==
    ActiveCount < SuccessThreshold => consensus = "None"

\* FINDING probe candidate: BTreeMap::find_map returns the *smallest key*
\* among threshold-meeting votes. With a properly set threshold at most one
\* value can meet it, so order is irrelevant — UniqueConsensus proves that.

=============================================================================
