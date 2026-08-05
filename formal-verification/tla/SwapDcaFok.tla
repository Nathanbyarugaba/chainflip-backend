------------------------------ MODULE SwapDcaFok ------------------------------
(***************************************************************************)
(* Model of one Chainflip swap request executing with DCA (chunked)        *)
(* execution and fill-or-kill (refund-on-expiry) semantics.                *)
(*                                                                         *)
(* Source modelled: state-chain/pallets/cf-swapping/src/lib.rs            *)
(*   DcaState + calculate_next_chunk/record_* (~lines 419-480)            *)
(*   init_swap_request, UserSwap arm         (~lines 3288-3360)           *)
(*   on_finalize batch execution + refund-or-reschedule (~lines 1144-1190)*)
(*   process_swap_outcome, UserSwap arm      (~lines 2505-2620)           *)
(*   refund_failed_swap                      (~lines 2346-2460)           *)
(*   reschedule_swap                         (~line 2860)                 *)
(*   cancel_swap                             (~line 2492)                 *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - Exchange rate is 1:1 and fee-free: each executed chunk of input     *)
(*     produces an equal amount of output. This makes value conservation   *)
(*     directly checkable on integers. (Fee arithmetic is verified         *)
(*     separately, at code level, in ../verus/.)                           *)
(*   - Block timing is abstracted: any scheduled chunk may execute,        *)
(*     fail-and-reschedule, or fail-and-refund (reaching refund_block) at  *)
(*     any moment. Reschedules are bounded by MaxReschedules to keep the   *)
(*     state space finite.                                                 *)
(*   - AllowSameBlockFailures enables the (reachable, see REPORT.md        *)
(*     "Findings") scenario of two chunks of the same request failing in   *)
(*     the same on_finalize batch and both taking the refund path.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    TotalInput,             \* deposited input amount, e.g. 5
    NumChunks,              \* DcaParameters::number_of_chunks, e.g. 3
    TwoInFlight,            \* chunk_interval == 1: two chunks kept in flight
    MaxReschedules,         \* bound on fail-and-reschedule events
    AllowSameBlockFailures  \* enable the same-block double-failure scenario

ASSUME TotalInput \in Nat /\ TotalInput >= 1
ASSUME NumChunks \in Nat /\ NumChunks >= 1

\* Chunk/swap ids; exactly NumChunks chunks are ever scheduled, because every
\* record_scheduled_chunk decrements remaining_chunks.
Ids == 1..NumChunks

VARIABLES
    state,       \* "Init" | "Active" | "Completed" | "Refunded"
    chunkAmt,    \* [Ids -> Nat]: input amount of each allocated chunk swap
    scheduled,   \* SUBSET Ids: chunks currently in ScheduledSwaps
                 \* (= DcaState.scheduled_chunks)
    nextId,      \* SwapIdCounter
    remInput,    \* DcaState.remaining_input_amount
    remChunks,   \* DcaState.remaining_chunks
    accOut,      \* DcaState.accumulated_output_amount
    executedIn,  \* ghost: total input consumed by successful chunks
    refunded,    \* input refunded to the user (refund egress amount)
    egressedOut, \* output egressed / credited to the user
    budget,      \* remaining fail-and-reschedule events
    panicked     \* ghost: TRUE if a log_or_panic! path was taken

vars == <<state, chunkAmt, scheduled, nextId, remInput, remChunks, accOut,
          executedIn, refunded, egressedOut, budget, panicked>>

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN chunkAmt[x] + SumOver(S \ {x})

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init ==
    /\ state = "Init"
    /\ chunkAmt = [id \in Ids |-> 0]
    /\ scheduled = {}
    /\ nextId = 1
    /\ remInput = TotalInput
    /\ remChunks = NumChunks
    /\ accOut = 0
    /\ executedIn = 0
    /\ refunded = 0
    /\ egressedOut = 0
    /\ budget = MaxReschedules
    /\ panicked = FALSE

\* init_swap_request, UserSwap arm: schedule the first chunk
\* (calculate_next_chunk = remaining / remaining_chunks, floor division -
\* note this schedules a zero-amount chunk when TotalInput < NumChunks),
\* and, when chunk_interval == 1, a second chunk if its amount is nonzero.
InitRequest ==
    /\ state = "Init"
    /\ state' = "Active"
    /\ LET c1 == remInput \div remChunks
           rem1 == remInput - c1
           chunks1 == remChunks - 1
       IN
       IF TwoInFlight /\ chunks1 > 0 /\ (rem1 \div chunks1) > 0
       THEN LET c2 == rem1 \div chunks1 IN
            /\ chunkAmt' = [chunkAmt EXCEPT ![1] = c1, ![2] = c2]
            /\ scheduled' = {1, 2}
            /\ nextId' = 3
            /\ remInput' = rem1 - c2
            /\ remChunks' = chunks1 - 1
       ELSE /\ chunkAmt' = [chunkAmt EXCEPT ![1] = c1]
            /\ scheduled' = {1}
            /\ nextId' = 2
            /\ remInput' = rem1
            /\ remChunks' = chunks1
    /\ UNCHANGED <<accOut, executedIn, refunded, egressedOut, budget, panicked>>

\* on_finalize success path -> process_swap_outcome, UserSwap arm:
\* if chunks remain, schedule the next one (record_scheduled_chunk), then
\* record_chunk_completion; when no chunks remain and nothing is scheduled,
\* egress the accumulated output and complete the request.
ExecuteSuccess(id) ==
    /\ state = "Active"
    /\ id \in scheduled
    /\ LET out == chunkAmt[id]                    \* 1:1 rate abstraction
           afterTake == scheduled \ {id}
       IN
       IF remChunks > 0
       THEN \* calculate_next_chunk = Some(_) - may be zero, still scheduled
            LET next == remInput \div remChunks IN
            /\ chunkAmt' = [chunkAmt EXCEPT ![nextId] = next]
            /\ scheduled' = afterTake \union {nextId}
            /\ nextId' = nextId + 1
            /\ remInput' = remInput - next
            /\ remChunks' = remChunks - 1
            /\ accOut' = accOut + out
            /\ executedIn' = executedIn + chunkAmt[id]
            /\ UNCHANGED <<state, refunded, egressedOut>>
       ELSE \* debug_assert!(remaining_input_amount == 0) here - checked by
            \* the DebugAssertHolds invariant below.
            /\ accOut' = IF afterTake = {} THEN 0 ELSE accOut + out
            /\ executedIn' = executedIn + chunkAmt[id]
            /\ scheduled' = afterTake
            /\ IF afterTake = {}
               THEN /\ egressedOut' = egressedOut + accOut + out
                    /\ state' = "Completed"
               ELSE /\ UNCHANGED <<egressedOut, state>>
            /\ UNCHANGED <<chunkAmt, nextId, remInput, remChunks, refunded>>
    /\ UNCHANGED <<budget, panicked>>

\* on_finalize failure path, refund_block not yet reached: reschedule_swap
\* re-inserts the chunk (and delays sibling chunks); accounting is unchanged.
ExecuteFailReschedule(id) ==
    /\ state = "Active"
    /\ id \in scheduled
    /\ budget > 0
    /\ budget' = budget - 1
    /\ UNCHANGED <<state, chunkAmt, scheduled, nextId, remInput, remChunks,
                   accOut, executedIn, refunded, egressedOut, panicked>>

\* on_finalize failure path at/after refund_block: refund_failed_swap.
\* Sibling scheduled chunks are cancelled (their amounts recovered), the
\* failed chunk's amount plus remaining input is refunded, and any partial
\* DCA output is egressed to the user.
ExecuteFailRefund(id) ==
    /\ state = "Active"
    /\ id \in scheduled
    /\ LET cancelled == SumOver(scheduled \ {id}) IN
       refunded' = refunded + chunkAmt[id] + remInput + cancelled
    /\ egressedOut' = egressedOut + accOut
    /\ accOut' = 0
    /\ remInput' = 0
    /\ scheduled' = {}
    /\ state' = "Refunded"
    /\ UNCHANGED <<chunkAmt, nextId, remChunks, executedIn, budget, panicked>>

\* FINDING (see REPORT.md): two chunks of the same request fail in the same
\* on_finalize batch, both past their refund_block (their refund_blocks are
\* equal by construction when chunk_interval == 1). Both were already taken
\* out of ScheduledSwaps for the batch, so:
\*   1. the first refund_failed_swap cancels "other scheduled chunks", but
\*      the sibling is not in ScheduledSwaps -> cancel_swap returns 0 and
\*      log_or_panic!s (~2499); its amount is NOT added to the refund;
\*   2. the second refund_failed_swap finds the SwapRequest already removed
\*      -> log_or_panic! and early return (~2352); the second chunk's input
\*      amount is dropped entirely.
DoubleFailureRefund(id1, id2) ==
    /\ AllowSameBlockFailures
    /\ state = "Active"
    /\ id1 \in scheduled /\ id2 \in scheduled /\ id1 /= id2
    /\ refunded' = refunded + chunkAmt[id1] + remInput   \* id2's amount lost
    /\ egressedOut' = egressedOut + accOut
    /\ accOut' = 0
    /\ remInput' = 0
    /\ scheduled' = {}
    /\ state' = "Refunded"
    /\ panicked' = TRUE
    /\ UNCHANGED <<chunkAmt, nextId, remChunks, executedIn, budget>>

Next ==
    \/ InitRequest
    \/ \E id \in Ids :
        \/ ExecuteSuccess(id)
        \/ ExecuteFailReschedule(id)
        \/ ExecuteFailRefund(id)
    \/ \E id1, id2 \in Ids : DoubleFailureRefund(id1, id2)

\* Fairness: scheduled swaps are executed every block; a chunk cannot sit in
\* ScheduledSwaps forever. Refund/success choice is nondeterministic but some
\* outcome always eventually happens (reschedules are budget-bounded).
Progress ==
    /\ WF_vars(InitRequest)
    /\ \A id \in Ids :
        WF_vars(ExecuteSuccess(id) \/ ExecuteFailReschedule(id) \/ ExecuteFailRefund(id))

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ Progress

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
    /\ state \in {"Init", "Active", "Completed", "Refunded"}
    /\ chunkAmt \in [Ids -> 0..TotalInput]
    /\ scheduled \subseteq Ids
    /\ nextId \in 1..(NumChunks + 1)
    /\ remInput \in 0..TotalInput
    /\ remChunks \in 0..NumChunks
    /\ accOut \in 0..TotalInput
    /\ executedIn \in 0..TotalInput
    /\ refunded \in 0..TotalInput
    /\ egressedOut \in 0..TotalInput
    /\ budget \in 0..MaxReschedules
    /\ panicked \in BOOLEAN

\* No log_or_panic! code path is ever taken.
NoPanic == ~panicked

\* Every unit of input is, at all times, in exactly one place: not yet
\* chunked, scheduled in a chunk, already swapped, or refunded.
InputConservation ==
    remInput + SumOver(scheduled) + executedIn + refunded = TotalInput

\* Every unit of output (1:1 with executed input) is either accumulated in
\* the DCA state or already egressed/credited to the user.
OutputConservation ==
    state \in {"Active", "Completed", "Refunded"} =>
        accOut + egressedOut = executedIn

\* Terminal accounting: nothing is lost. A completed request egressed the
\* full output; a refunded request returned refund + partial output, which
\* together account for the full input.
TerminalConservation ==
    /\ state = "Completed" => egressedOut = TotalInput /\ refunded = 0
    /\ state = "Refunded" => refunded + egressedOut = TotalInput

\* Mirrors the debug_assert! in process_swap_outcome (~2568): when
\* calculate_next_chunk returns None, all input has been allocated to chunks.
DebugAssertHolds ==
    remChunks = 0 => remInput = 0

\* An active request always has at least one scheduled chunk: a swap request
\* can never be stranded with funds but no scheduled swap.
ActiveHasScheduled ==
    state = "Active" => scheduled /= {}

\* At most two chunks are ever in flight (exactly the init_swap_request
\* chunk_interval == 1 special case), otherwise one.
InFlightBound ==
    Cardinality(scheduled) <= IF TwoInFlight THEN 2 ELSE 1

\* Terminal states hold no residual scheduled chunks or unallocated input.
TerminalClean ==
    state \in {"Completed", "Refunded"} =>
        scheduled = {} /\ remInput = 0 /\ accOut = 0

(***************************************************************************)
(* Liveness: every swap request eventually completes or refunds.           *)
(***************************************************************************)
RequestResolves == (state = "Active") ~> (state \in {"Completed", "Refunded"})

=============================================================================
