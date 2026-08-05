-------------------------- MODULE LendingRepay --------------------------
(***************************************************************************)
(* Model of lending repay_principal / repay_via_liquidation conservation.  *)
(*                                                                         *)
(* Sources: general_lending.rs                                             *)
(*   repay_principal (~1121):                                              *)
(*     repayment = min(provided, owed); owed -= repayment;                 *)
(*     returns excess = provided - repayment                               *)
(*   repay_via_liquidation (~1077):                                        *)
(*     collect interest; take liquidation fee from min(provided, owed);    *)
(*     fee split network/pool; then repay_principal on remainder           *)
(*                                                                         *)
(* Invariants: provided = repaid_to_pool + fees + excess;                  *)
(*             owed never increases on repay; excess <= provided.          *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    MaxAmount,
    MaxFeeBps,          \* liquidation fee in bps (0..10000)
    NetworkFeePercent   \* 0..100 share of liquidation fee to network

VARIABLES
    owed,
    provided,           \* last repayment attempt size (ghost of call arg)
    repaid,
    feeNetwork,
    feePool,
    excess,
    phase               \* Idle | AfterRepay

vars == <<owed, provided, repaid, feeNetwork, feePool, excess, phase>>

Init ==
    /\ owed \in 1..MaxAmount
    /\ provided = 0
    /\ repaid = 0
    /\ feeNetwork = 0
    /\ feePool = 0
    /\ excess = 0
    /\ phase = "Idle"

\* Plain repay_principal(provided_amount).
RepayPrincipal(amt) ==
    /\ phase = "Idle"
    /\ amt \in 1..MaxAmount
    /\ LET r == IF amt <= owed THEN amt ELSE owed IN
       /\ provided' = amt
       /\ repaid' = r
       /\ owed' = owed - r
       /\ excess' = amt - r
       /\ feeNetwork' = 0
       /\ feePool' = 0
       /\ phase' = "AfterRepay"

\* Liquidation repay with fee.
RepayViaLiquidation(amt, feeBps, voluntary) ==
    /\ phase = "Idle"
    /\ amt \in 1..MaxAmount
    /\ feeBps \in 0..MaxFeeBps
    /\ LET base == IF amt <= owed THEN amt ELSE owed
           fee == IF voluntary THEN 0 ELSE (base * feeBps) \div 10000
           feeNet == (fee * NetworkFeePercent) \div 100
           feeP == fee - feeNet
           afterFee == amt - fee
           r == IF afterFee <= owed THEN afterFee ELSE owed
       IN
       /\ provided' = amt
       /\ feeNetwork' = feeNet
       /\ feePool' = feeP
       /\ repaid' = r
       /\ owed' = owed - r
       /\ excess' = afterFee - r
       /\ phase' = "AfterRepay"

Reset ==
    /\ phase = "AfterRepay"
    /\ owed' \in 1..MaxAmount
    /\ provided' = 0
    /\ repaid' = 0
    /\ feeNetwork' = 0
    /\ feePool' = 0
    /\ excess' = 0
    /\ phase' = "Idle"

Next ==
    \/ \E amt \in 1..MaxAmount : RepayPrincipal(amt)
    \/ \E amt \in 1..MaxAmount, bps \in 0..MaxFeeBps, vol \in BOOLEAN :
          RepayViaLiquidation(amt, bps, vol)
    \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ owed \in 0..MaxAmount
    /\ provided \in 0..MaxAmount
    /\ repaid \in 0..MaxAmount
    /\ excess \in 0..MaxAmount
    /\ feeNetwork + feePool <= provided

\* Core conservation after a repay action.
Conservation ==
    phase = "AfterRepay" =>
        provided = repaid + feeNetwork + feePool + excess

\* Owed never increases on repay (Reset can set a new loan).
OwedNonIncreaseOnRepay == [][
    phase = "Idle" /\ phase' = "AfterRepay" => owed' <= owed
]_vars

ExcessBounded ==
    phase = "AfterRepay" => excess <= provided

RepaidBoundedByOwed ==
    phase = "AfterRepay" => repaid <= provided

=============================================================================
