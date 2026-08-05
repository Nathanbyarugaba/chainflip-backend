--------------------------- MODULE BrokerFeeSplit ---------------------------
(***************************************************************************)
(* Fund-safety model of take_broker_fees rounding.                         *)
(*                                                                         *)
(* Source: state-chain/pallets/cf-swapping/src/lib.rs ~1947-1981           *)
(*         validate_broker_fees                  ~3604                     *)
(*                                                                         *)
(* fee(amount, bps) = floor( (amount * bps * 100 + 499999) / 1000000 )     *)
(*                                                                         *)
(* Mainline config (AllowUnvalidated = FALSE): exhaustively checks every   *)
(* amount ∈ 0..MaxAmount and every bps-list of length ≤ MaxBeneficiaries   *)
(* with Σ bps ≤ MaxBps (= 1000).                                           *)
(*                                                                         *)
(* Finding config (AllowUnvalidated = TRUE): additionally includes the     *)
(* equal-split 100%-fee families that take_broker_fees's own gate allows;  *)
(* NoOverchargeValidated is then expected to fail.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxAmount,
    MaxBeneficiaries,
    MaxBps,
    AllowUnvalidated

BPM == 100
MILLION == 1000000
HALF_ADJ == 499999
ONE_AS_BPS == 10000

Fee(amount, bps) ==
    IF amount = 0 \/ bps = 0 THEN 0
    ELSE (amount * bps * BPM + HALF_ADJ) \div MILLION

RECURSIVE SumSeq(_)
SumSeq(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE SumFees(_, _)
SumFees(amount, s) ==
    IF Len(s) = 0 THEN 0 ELSE Fee(amount, Head(s)) + SumFees(amount, Tail(s))

\* Equal-split lists: n copies of (total \div n), only when total is divisible.
EqualSplit(total, n) ==
    IF n = 0 THEN <<>>
    ELSE [i \in 1..n |-> total \div n]

\* Validated universe: equal splits of every total ≤ MaxBps into n parts
\* (covers the worst-case rounding alignment; uneven splits are covered by
\* the conformance proptest which samples freely).
ValidatedLists ==
    UNION {
        { EqualSplit(total, n) :
            total \in { t \in 0..MaxBps : n = 0 \/ t % n = 0 } }
        : n \in 0..MaxBeneficiaries
    }

\* Unvalidated 100%-class equal splits (the known overcharge family).
UnvalidatedLists ==
    { EqualSplit(ONE_AS_BPS, n) :
        n \in { k \in 1..MaxBeneficiaries : ONE_AS_BPS % k = 0 } }

VARIABLES amount, bps, totalFee, validated

Init ==
    /\ amount \in 0..MaxAmount
    /\ \/ /\ validated = TRUE
          /\ bps \in ValidatedLists
       \/ /\ AllowUnvalidated
          /\ validated = FALSE
          /\ bps \in UnvalidatedLists
    /\ totalFee = SumFees(amount, bps)

Next == UNCHANGED <<amount, bps, totalFee, validated>>

Spec == Init /\ [][Next]_<<amount, bps, totalFee, validated>>

NoOverchargeValidated ==
    validated => totalFee <= amount

\* Stronger (intentionally false under AllowUnvalidated): no overcharge in
\* any mode. Used by the finding config to obtain a counterexample.
NoOverchargeOnAllModes ==
    totalFee <= amount

\* When unvalidated equal 100% splits are included, overcharge must be
\* reachable (anti-vacuity of the finding).
UnvalidatedOverchargeExists ==
    \/ ~AllowUnvalidated
    \/ \E a \in 0..MaxAmount, n \in { k \in 1..MaxBeneficiaries : ONE_AS_BPS % k = 0 } :
          SumFees(a, EqualSplit(ONE_AS_BPS, n)) > a

\* Upper bound vs the truncating linear share of the total: each of the n
\* nearest-rounds can overshoot its own linear share by < 1, so the sum
\* overshoots the combined truncating share by < n. (The sum can also
\* *undershoot* — e.g. amount=10, two×500 bps → fees 0+0 < 1 — so there is
\* no matching lower bound; see REPORT.md §6.3.)
RoundingInflationBound ==
    totalFee <= (amount * SumSeq(bps)) \div ONE_AS_BPS + Len(bps)

=============================================================================
