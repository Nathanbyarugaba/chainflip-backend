--------------------------- MODULE BoostLifecycle ---------------------------
(***************************************************************************)
(* Fund-safety model of deposit boosting (prewitness → boost → finalise /  *)
(* loss / amount-mismatch).                                                *)
(*                                                                         *)
(* Sources:                                                                *)
(*   state-chain/pallets/cf-ingress-egress/src/lib.rs                      *)
(*     process_channel_deposit_prewitness / vault prewitness → try_boosting*)
(*     process_full_witness_deposit_inner (~3001 / match ~3159)            *)
(*       Boosted + amount match  → FinaliseBoost (no second user credit)   *)
(*       Boosted + amount mismatch → PerformChannelAction / BoostNotConsumed*)
(*         WITHOUT clearing boost_status                                   *)
(*     recycle_channel / process_timed_out_boosted_vault_transactions      *)
(*       → process_deposit_as_lost (boosters absorb loss)                  *)
(*   state-chain/pallets/cf-lending-pools/src/boost.rs                     *)
(*     try_boosting / finalise_boost / process_deposit_as_lost             *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - One deposit identity at a time (DepositIds = 1..MaxDeposits).       *)
(*   - Boost fee abstracted away (conservation tracked on principal).      *)
(*   - Booster pool is a single aggregate balance.                         *)
(*   - "UserCredit" counts every PerformChannelAction / boost-time action  *)
(*     credited to the user for that deposit identity.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    MaxDeposits,          \* e.g. 2
    MaxAmount,            \* e.g. 5
    AllowAmountMismatch   \* TRUE enables the finding path

DepositIds == 1..MaxDeposits
Amounts == 1..MaxAmount

\* Per-deposit lifecycle status from the protocol's point of view.
Statuses == {
    "None",          \* not yet seen
    "Boosted",       \* prewitnessed + try_boosting succeeded; user already credited
    "Finalised",     \* full witness matched amount; boosters repaid; no second user credit
    "Lost",          \* recycled / timed out; boosters absorbed loss; user keeps boost credit
    "NonBoosted",    \* full witness processed as a fresh non-boosted deposit
    "DoubleCredited" \* FINDING: was Boosted, then mismatched full witness credited again
}

VARIABLES
    status,         \* [DepositIds -> Statuses]
    boostAmt,       \* [DepositIds -> Nat] amount recorded at boost time
    userCredit,     \* [DepositIds -> Nat] total credited to the user for this id
    boosterPool,    \* aggregate available booster liquidity
    boosterLocked,  \* funds locked in open boosts
    boosterLosses,  \* cumulative losses absorbed by boosters
    boosterRepaid   \* cumulative repaid to boosters on finalisation

vars == <<status, boostAmt, userCredit, boosterPool, boosterLocked,
          boosterLosses, boosterRepaid>>

TypeOK ==
    /\ status \in [DepositIds -> Statuses]
    /\ boostAmt \in [DepositIds -> 0..MaxAmount]
    /\ userCredit \in [DepositIds -> 0..(2 * MaxAmount)]
    /\ boosterPool \in Nat
    /\ boosterLocked \in Nat
    /\ boosterLosses \in Nat
    /\ boosterRepaid \in Nat

\* Global fund conservation for the booster side:
\* initial pool = available + locked + losses + repaid_out - (repaid returns to pool)
\* We track: InitPool = boosterPool + boosterLocked + boosterLosses
\* (repayments return locked funds to boosterPool, so repaid is not additive).
InitPool == MaxDeposits * MaxAmount   \* generous initial liquidity

BoosterConservation ==
    boosterPool + boosterLocked + boosterLosses = InitPool

\* A deposit identity is never both Finalised and DoubleCredited, etc.
StatusExclusive ==
    \A id \in DepositIds :
        status[id] \in Statuses

RECURSIVE SumBoost(_)
SumBoost(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN boostAmt[x] + SumBoost(S \ {x})

\* No open boost without locked funds covering it.
LockedCoversOpenBoosts ==
    LET open == { id \in DepositIds : status[id] \in {"Boosted", "DoubleCredited"} }
    IN boosterLocked = SumBoost(open)

\* ---- Actions --------------------------------------------------------------

Init ==
    /\ status = [id \in DepositIds |-> "None"]
    /\ boostAmt = [id \in DepositIds |-> 0]
    /\ userCredit = [id \in DepositIds |-> 0]
    /\ boosterPool = InitPool
    /\ boosterLocked = 0
    /\ boosterLosses = 0
    /\ boosterRepaid = 0

\* Prewitness + successful try_boosting: lock booster funds, credit user.
Boost(id, amt) ==
    /\ status[id] = "None"
    /\ amt \in Amounts
    /\ boosterPool >= amt
    /\ status' = [status EXCEPT ![id] = "Boosted"]
    /\ boostAmt' = [boostAmt EXCEPT ![id] = amt]
    /\ userCredit' = [userCredit EXCEPT ![id] = amt]
    /\ boosterPool' = boosterPool - amt
    /\ boosterLocked' = boosterLocked + amt
    /\ UNCHANGED <<boosterLosses, boosterRepaid>>

\* Full witness with matching amount → FinaliseBoost: repay boosters, no
\* second user credit (DepositAction::BoostersCredited).
Finalise(id) ==
    /\ status[id] = "Boosted"
    /\ status' = [status EXCEPT ![id] = "Finalised"]
    /\ boosterLocked' = boosterLocked - boostAmt[id]
    /\ boosterPool' = boosterPool + boostAmt[id]
    /\ boosterRepaid' = boosterRepaid + boostAmt[id]
    /\ UNCHANGED <<boostAmt, userCredit, boosterLosses>>

\* Recycle / vault timeout → process_deposit_as_lost.
Lose(id) ==
    /\ status[id] = "Boosted"
    /\ status' = [status EXCEPT ![id] = "Lost"]
    /\ boosterLocked' = boosterLocked - boostAmt[id]
    /\ boosterLosses' = boosterLosses + boostAmt[id]
    /\ UNCHANGED <<boostAmt, userCredit, boosterPool, boosterRepaid>>

\* Full witness with NO prior boost → normal non-boosted credit.
NonBoostedDeposit(id, amt) ==
    /\ status[id] = "None"
    /\ amt \in Amounts
    /\ status' = [status EXCEPT ![id] = "NonBoosted"]
    /\ userCredit' = [userCredit EXCEPT ![id] = amt]
    /\ UNCHANGED <<boostAmt, boosterPool, boosterLocked, boosterLosses, boosterRepaid>>

\* FINDING PATH: Boosted, then full witness with a *different* amount.
\* Code takes PerformChannelAction / BoostNotConsumed and does NOT clear
\* boost_status (only BoostConsumed clears it). User is credited again;
\* boost remains open (can later Finalise if a matching amount arrives, or
\* Lose). Modelled here as transitioning to DoubleCredited while keeping
\* the boost locked.
MismatchCredit(id, amt) ==
    /\ AllowAmountMismatch
    /\ status[id] = "Boosted"
    /\ amt \in Amounts
    /\ amt /= boostAmt[id]
    /\ status' = [status EXCEPT ![id] = "DoubleCredited"]
    /\ userCredit' = [userCredit EXCEPT ![id] = userCredit[id] + amt]
    /\ UNCHANGED <<boostAmt, boosterPool, boosterLocked, boosterLosses, boosterRepaid>>

\* After a mismatch credit, the original boost can still be lost (recycle /
\* timeout) — boosters pay while the user keeps both credits.
LoseAfterMismatch(id) ==
    /\ status[id] = "DoubleCredited"
    /\ status' = [status EXCEPT ![id] = "Lost"]
    /\ boosterLocked' = boosterLocked - boostAmt[id]
    /\ boosterLosses' = boosterLosses + boostAmt[id]
    /\ UNCHANGED <<boostAmt, userCredit, boosterPool, boosterRepaid>>

\* After a mismatch credit, a later matching full witness of the *original*
\* boosted amount finalises the boost (boosters repaid). User still has the
\* extra mismatched credit.
FinaliseAfterMismatch(id) ==
    /\ status[id] = "DoubleCredited"
    /\ status' = [status EXCEPT ![id] = "Finalised"]
    /\ boosterLocked' = boosterLocked - boostAmt[id]
    /\ boosterPool' = boosterPool + boostAmt[id]
    /\ boosterRepaid' = boosterRepaid + boostAmt[id]
    /\ UNCHANGED <<boostAmt, userCredit, boosterLosses>>

Next ==
    \E id \in DepositIds :
        \/ \E amt \in Amounts : Boost(id, amt) \/ NonBoostedDeposit(id, amt) \/ MismatchCredit(id, amt)
        \/ Finalise(id) \/ Lose(id)
        \/ LoseAfterMismatch(id) \/ FinaliseAfterMismatch(id)

Spec == Init /\ [][Next]_vars

\* ---- Safety invariants ----------------------------------------------------

\* Under the production assumption that full-witness amount always equals the
\* boosted amount for the same deposit (AllowAmountMismatch = FALSE), the user
\* is never credited twice for one deposit identity. Equivalently: once a
\* boost has been opened, userCredit equals boostAmt until/unless a mismatch
\* path (DoubleCredited) is taken.
NoDoubleCredit ==
    \A id \in DepositIds :
        status[id] \in {"Boosted", "Finalised", "Lost"} =>
            userCredit[id] = boostAmt[id]

\* Stronger: user credit never exceeds what was deposited for that id, when
\* mismatch is disabled. (With mismatch enabled this fails — the finding.)
UserCreditBoundedByDeposit ==
    \A id \in DepositIds :
        \/ status[id] = "None"
        \/ status[id] = "NonBoosted" /\ userCredit[id] \in Amounts
        \/ status[id] \in {"Boosted", "Finalised", "Lost"} /\ userCredit[id] = boostAmt[id]
        \/ status[id] = "DoubleCredited"  \* only reachable if AllowAmountMismatch

\* When mismatch is disabled, DoubleCredited is unreachable.
NoMismatchPath ==
    ~AllowAmountMismatch => \A id \in DepositIds : status[id] /= "DoubleCredited"

=============================================================================
