---------------------- MODULE AmmSwapConservation ----------------------
(***************************************************************************)
(* Abstract model of cf-amm PoolState::inner_swap fund conservation.       *)
(*                                                                         *)
(* Sources: state-chain/amm/src/lib.rs (inner_swap)                        *)
(*          range_orders.rs / limit_orders.rs swap loops                   *)
(*          reduce_by_pool_fee (lib.rs ~545)                               *)
(*                                                                         *)
(* Fee: fee = floor(input * FeeHundredthPips / 1_000_000)                  *)
(* After-fee input is sold into pool liquidity for output.                 *)
(*                                                                         *)
(* Invariants checked exhaustively on small constants.                     *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    MaxInput,
    MaxDepth,
    MaxLots,
    FeeHundredthPips,
    ONE

ASSUME FeeHundredthPips \in 0..(ONE \div 2)
ASSUME ONE = 1000000

VARIABLES
    inputRemaining,
    inputOriginal,
    outputAccrued,
    poolBase,       \* receives sold asset (input + fees)
    poolQuote,      \* pays bought asset
    feesAccrued,
    lotsLeft,
    steps

vars == <<inputRemaining, inputOriginal, outputAccrued, poolBase, poolQuote,
          feesAccrued, lotsLeft, steps>>

FeeOf(amount) == (amount * FeeHundredthPips) \div ONE

Init ==
    /\ inputOriginal \in 1..MaxInput
    /\ inputRemaining = inputOriginal
    /\ outputAccrued = 0
    /\ poolBase = 0
    /\ poolQuote \in 1..(MaxDepth * MaxLots)
    /\ feesAccrued = 0
    /\ lotsLeft \in 1..MaxLots
    /\ steps = 0

\* One liquidity lot of depth d absorbs all remaining after-fee input.
SwapStep(d) ==
    /\ inputRemaining > 0
    /\ lotsLeft > 0
    /\ d \in 1..MaxDepth
    /\ d <= poolQuote
    /\ LET fee == FeeOf(inputRemaining)
           afterFee == inputRemaining - fee
           out == IF afterFee + d = 0 THEN 0 ELSE (afterFee * d) \div (afterFee + d)
           outCapped == IF out > d THEN d ELSE out
       IN
       /\ outputAccrued' = outputAccrued + outCapped
       /\ poolQuote' = poolQuote - outCapped
       /\ poolBase' = poolBase + inputRemaining   \* fee + afterFee
       /\ feesAccrued' = feesAccrued + fee
       /\ inputRemaining' = 0
       /\ lotsLeft' = lotsLeft - 1
       /\ steps' = steps + 1
       /\ UNCHANGED inputOriginal

NoLiquidity ==
    /\ inputRemaining > 0
    /\ lotsLeft = 0
    /\ UNCHANGED vars

Finished ==
    /\ inputRemaining = 0
    /\ UNCHANGED vars

Next == (\E d \in 1..MaxDepth : SwapStep(d)) \/ NoLiquidity \/ Finished
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ inputRemaining \in 0..MaxInput
    /\ inputOriginal \in 1..MaxInput
    /\ feesAccrued <= inputOriginal
    /\ steps <= MaxLots

\* All consumed input sits in poolBase.
PoolReceivedEqualsConsumed ==
    poolBase = (inputOriginal - inputRemaining)

\* Fees are a portion of consumed input.
FeesBounded ==
    feesAccrued <= (inputOriginal - inputRemaining)

\* Output never exceeds what left the quote side.
OutputMatchesQuoteDrain ==
    outputAccrued + poolQuote <= MaxDepth * MaxLots

StepsBounded == steps <= MaxLots

=============================================================================
