---------------------- MODULE LendingInterestRepay ----------------------
(***************************************************************************)
(* Refined lending: charge interest → collect into owed → repay/liquidate. *)
(*                                                                         *)
(* Sources: general_lending.rs                                             *)
(*   charge_interest / collect_pending_interest / repay_via_liquidation    *)
(*                                                                         *)
(* FINDING (fee-base coupling): liquidation fee is computed on owed after  *)
(* interest capitalisation, so pending interest increases the fee base.    *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    MaxPrincipal,
    MaxPending,
    MaxProvided,
    InterestRateBps,
    LiqFeeBps,
    NetworkFeePercent

VARIABLES
    owed,
    pending,
    poolAvailable,
    owedBeforeCollect,   \* ghost: owed snapshot at CollectInterest
    provided,
    repaid,
    feeNetwork,
    feePool,
    excess,
    phase

vars == <<owed, pending, poolAvailable, owedBeforeCollect, provided, repaid,
          feeNetwork, feePool, excess, phase>>

MaxOwed == MaxPrincipal + MaxPending

FeeOn(base) == (base * LiqFeeBps) \div 10000

Init ==
    /\ owed \in 1..MaxPrincipal
    /\ pending = 0
    /\ poolAvailable \in 0..MaxPrincipal
    /\ owedBeforeCollect = owed
    /\ provided = 0
    /\ repaid = 0
    /\ feeNetwork = 0
    /\ feePool = 0
    /\ excess = 0
    /\ phase = "Idle"

ChargeInterest ==
    /\ phase = "Idle"
    /\ LET add == (owed * InterestRateBps) \div 10000 IN
       /\ add > 0
       /\ pending + add <= MaxPending
       /\ pending' = pending + add
       /\ phase' = "Charged"
       /\ UNCHANGED <<owed, poolAvailable, owedBeforeCollect, provided, repaid,
                      feeNetwork, feePool, excess>>

SkipCharge ==
    /\ phase = "Idle"
    /\ phase' = "Charged"
    /\ UNCHANGED <<owed, pending, poolAvailable, owedBeforeCollect, provided,
                   repaid, feeNetwork, feePool, excess>>

CollectInterest ==
    /\ phase = "Charged"
    /\ owed + pending <= MaxOwed
    /\ LET realised == IF pending <= poolAvailable THEN pending ELSE poolAvailable IN
       /\ owedBeforeCollect' = owed
       /\ owed' = owed + pending
       /\ pending' = 0
       /\ poolAvailable' = poolAvailable - realised
       /\ phase' = "AfterCollect"
       /\ UNCHANGED <<provided, repaid, feeNetwork, feePool, excess>>

RepayPrincipal(amt) ==
    /\ phase = "AfterCollect"
    /\ amt \in 1..MaxProvided
    /\ LET r == IF amt <= owed THEN amt ELSE owed IN
       /\ provided' = amt
       /\ repaid' = r
       /\ owed' = owed - r
       /\ excess' = amt - r
       /\ feeNetwork' = 0
       /\ feePool' = 0
       /\ phase' = "AfterRepay"
       /\ UNCHANGED <<pending, poolAvailable, owedBeforeCollect>>

RepayViaLiquidation(amt, voluntary) ==
    /\ phase = "AfterCollect"
    /\ amt \in 1..MaxProvided
    /\ LET base == IF amt <= owed THEN amt ELSE owed
           fee == IF voluntary THEN 0 ELSE FeeOn(base)
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
       /\ UNCHANGED <<pending, poolAvailable, owedBeforeCollect>>

Reset ==
    /\ phase = "AfterRepay"
    /\ owed' \in 1..MaxPrincipal
    /\ pending' = 0
    /\ poolAvailable' \in 0..MaxPrincipal
    /\ owedBeforeCollect' = owed'
    /\ provided' = 0
    /\ repaid' = 0
    /\ feeNetwork' = 0
    /\ feePool' = 0
    /\ excess' = 0
    /\ phase' = "Idle"

Next ==
    \/ ChargeInterest \/ SkipCharge \/ CollectInterest
    \/ \E amt \in 1..MaxProvided : RepayPrincipal(amt)
    \/ \E amt \in 1..MaxProvided, vol \in BOOLEAN : RepayViaLiquidation(amt, vol)
    \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ owed \in 0..MaxOwed
    /\ pending \in 0..MaxPending
    /\ phase \in {"Idle","Charged","AfterCollect","AfterRepay"}

Conservation ==
    phase = "AfterRepay" =>
        provided = repaid + feeNetwork + feePool + excess

CollectIncreasesOwedByPending == [][
    (phase = "Charged" /\ phase' = "AfterCollect") =>
        owed' = owed + pending
]_vars

ExcessBounded ==
    phase = "AfterRepay" => excess <= provided

\* Probe (EXPECTED TO FAIL as a global invariant): liquidation fee never
\* exceeds the fee computed on pre-collect owed. When pending > 0 was
\* capitalised, post-collect owed is larger ⇒ fee can grow.
FeeNeverGrowsVsPreCollect ==
    ~(phase = "AfterRepay" /\ feeNetwork + feePool >
        FeeOn(IF provided <= owedBeforeCollect THEN provided ELSE owedBeforeCollect))

=============================================================================
