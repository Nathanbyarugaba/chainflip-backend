-------------------------- MODULE BroadcastLifecycle --------------------------
(***************************************************************************)
(* Model of the Chainflip broadcast pallet lifecycle.                      *)
(*                                                                         *)
(* Source modelled: state-chain/pallets/cf-broadcast/src/lib.rs           *)
(*   threshold_sign_and_broadcast        (~line 921)                      *)
(*   on_signature_ready                  (~line 546, incl. barrier check   *)
(*                                        and the Err(_offenders) arm)     *)
(*   start_broadcast_attempt             (~line 1003, nomination+timeout)  *)
(*   transaction_failed                  (~line 681)                       *)
(*   on_initialize                       (~line 465, timeout + retry queue)*)
(*   handle_broadcast_failure            (~line 1076, retry-or-abort)      *)
(*   abort_broadcast                     (~line 1113)                      *)
(*   egress_success                      (~line 804)                       *)
(*   remove_pending_broadcast            (~line 903, barrier popping)      *)
(*   start_next_broadcast_attempt        (~line 961, resign-or-retry)      *)
(*   threshold_sign_and_broadcast_rotation_tx (~line 1194, barriers)       *)
(*                                                                         *)
(* Broadcast state encoding (derived from the pallet's storage items):     *)
(*   "Unrequested"  broadcast id not yet allocated                         *)
(*   "Signing"      in PendingBroadcasts, awaiting threshold signature     *)
(*   "Attempting"   in PendingBroadcasts + AwaitingBroadcast with nominee, *)
(*                  timeout entry registered                               *)
(*   "RetryQueued"  in PendingBroadcasts + DelayedBroadcastRetryQueue      *)
(*   "Succeeded"    resolved via egress_success                            *)
(*   "Aborted"      resolved via abort_broadcast (all authorities failed)  *)
(*   "Dropped"      removed from PendingBroadcasts by the                  *)
(*                  on_signature_ready Err(_offenders) arm. Only reachable *)
(*                  for historical-key signing requests: Standard signing  *)
(*                  ceremonies retry forever (cf-threshold-signature       *)
(*                  ~line 956) and never resolve to Err.                   *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*   - Chain-block/state-chain-block timing is abstracted: timeouts and    *)
(*     queued retries fire nondeterministically.                           *)
(*   - Safe mode `retry_enabled = false` merely defers timeout and retry   *)
(*     processing to a later block, so it is modelled as those actions     *)
(*     not firing (stuttering), which TLC explores anyway.                 *)
(*   - transaction_failed reports are modelled only for broadcasts that    *)
(*     have completed signing. (The code also accepts reports during the   *)
(*     Signing stage; see REPORT.md "Observations".)                       *)
(*   - A witnessed success is possible from any state with a registered    *)
(*     transaction_out_id - including RetryQueued (a signed tx submitted   *)
(*     outside the nomination path) and Aborted (late inclusion), since    *)
(*     abort_broadcast does not remove TransactionOutIdToBroadcastId.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Validators,           \* current authorities, e.g. {v1, v2, v3}
    MaxBroadcasts,        \* number of broadcast ids explored, e.g. 3
    RotationIds,          \* ids that are rotation txs installing barriers
    AllowSigningFailure   \* enable the historical-key terminal signing
                          \* failure path (on_signature_ready Err arm)

Ids == 1..MaxBroadcasts

ASSUME RotationIds \subseteq Ids

NoNominee == "NoNominee"

States == {"Unrequested", "Signing", "Attempting", "RetryQueued",
           "Succeeded", "Aborted", "Dropped"}

\* States in which the id is a member of the PendingBroadcasts storage set.
PendingStates == {"Signing", "Attempting", "RetryQueued"}

\* States in which a transaction_out_id has been registered
\* (TransactionOutIdToBroadcastId), i.e. a witnessed success is possible.
WitnessableStates == {"Attempting", "RetryQueued", "Aborted"}

VARIABLES
    bstate,   \* [Ids -> States]
    nominee,  \* [Ids -> Validators \cup {NoNominee}]  (AwaitingBroadcast.nominee)
    failed,   \* [Ids -> SUBSET Validators]            (FailedBroadcasters)
    timeouts, \* SUBSET (Ids \X Validators)            (Timeouts entries)
    barriers  \* SUBSET Ids                            (BroadcastBarriers)

vars == <<bstate, nominee, failed, timeouts, barriers>>

PendingSet == {id \in Ids : bstate[id] \in PendingStates}

\* remove_pending_broadcast (~903): barriers are popped while the smallest
\* remaining pending id is beyond them. Equivalently: a barrier survives iff
\* some pending id at-or-before it remains.
PopBarriers(pendingAfter) == {b \in barriers : \E id \in pendingAfter : id <= b}

\* On-initialize retry gate (~529): retries only run for ids at or below the
\* first (smallest) barrier.
RetryAllowed(id) == \A b \in barriers : id <= b

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init ==
    /\ bstate = [id \in Ids |-> "Unrequested"]
    /\ nominee = [id \in Ids |-> NoNominee]
    /\ failed = [id \in Ids |-> {}]
    /\ timeouts = {}
    /\ barriers = {}

\* threshold_sign_and_broadcast (+ rotation-tx barrier installation).
\* Broadcast ids are allocated in increasing order by BroadcastIdCounter.
RequestBroadcast(id) ==
    /\ bstate[id] = "Unrequested"
    /\ \A j \in Ids : j < id => bstate[j] /= "Unrequested"
    /\ bstate' = [bstate EXCEPT ![id] = "Signing"]
    /\ barriers' = IF id \in RotationIds THEN barriers \union {id} ELSE barriers
    /\ UNCHANGED <<nominee, failed, timeouts>>

\* start_broadcast_attempt (~1003): nominate a broadcaster excluding
\* FailedBroadcasters and register a timeout for (id, nominee). Nomination
\* failure (no eligible/online broadcaster) => schedule_for_retry; that case
\* is covered by the caller's RetryQueued alternative.
StartAttempt(id, v) ==
    /\ bstate' = [bstate EXCEPT ![id] = "Attempting"]
    /\ nominee' = [nominee EXCEPT ![id] = v]
    /\ timeouts' = timeouts \union {<<id, v>>}
    /\ UNCHANGED failed

\* on_signature_ready, Ok(signature) arm with should_broadcast = true (~546):
\* registers the transaction_out_id, then either starts an attempt or, if a
\* barrier is in front of this id, queues it for retry.
SignatureReady(id) ==
    /\ bstate[id] = "Signing"
    /\ IF ~RetryAllowed(id)
       THEN /\ bstate' = [bstate EXCEPT ![id] = "RetryQueued"]
            /\ UNCHANGED <<nominee, failed, timeouts>>
       ELSE \/ \E v \in Validators \ failed[id] : StartAttempt(id, v)
            \/ \* nominate_broadcaster returned None => schedule_for_retry
               /\ bstate' = [bstate EXCEPT ![id] = "RetryQueued"]
               /\ UNCHANGED <<nominee, failed, timeouts>>
    /\ UNCHANGED barriers

\* on_signature_ready, Err(_offenders) arm (~630): the broadcast is removed
\* from PendingBroadcasts with a *plain* remove - crucially NOT via
\* remove_pending_broadcast, so barriers are not re-evaluated. Terminal
\* signature failure only occurs for historical-key requests.
SigningFailed(id) ==
    /\ AllowSigningFailure
    /\ bstate[id] = "Signing"
    /\ bstate' = [bstate EXCEPT ![id] = "Dropped"]
    /\ UNCHANGED <<nominee, failed, timeouts, barriers>>

\* handle_broadcast_failure (~1076): record the reporter; abort when every
\* authority has failed, otherwise schedule a retry.
HandleFailure(id, v) ==
    IF failed[id] \union {v} = Validators
    THEN \* abort_broadcast (~1113): clear FailedBroadcasters, dispatch the
         \* aborted callback, remove from pending (popping barriers).
         /\ bstate' = [bstate EXCEPT ![id] = "Aborted"]
         /\ failed' = [failed EXCEPT ![id] = {}]
         /\ barriers' = PopBarriers(PendingSet \ {id})
    ELSE /\ bstate' = [bstate EXCEPT ![id] = "RetryQueued"]
         /\ failed' = [failed EXCEPT ![id] = failed[id] \union {v}]
         /\ UNCHANGED barriers

\* transaction_failed extrinsic (~681): any current authority may report any
\* pending broadcast as failed. Duplicate reports are no-ops (modelled by the
\* v \notin failed[id] guard).
ReportFailure(id, v) ==
    /\ bstate[id] \in {"Attempting", "RetryQueued"}
    /\ v \notin failed[id]
    /\ HandleFailure(id, v)
    /\ UNCHANGED <<nominee, timeouts>>

\* on_initialize timeout processing (~478): an expired timeout entry is
\* removed; if the broadcast is still pending, the nominee of that (possibly
\* stale) attempt is treated as failed. Duplicate reports are no-ops but the
\* entry is still consumed.
TimeoutFires(id, v) ==
    /\ <<id, v>> \in timeouts
    /\ timeouts' = timeouts \ {<<id, v>>}
    /\ IF bstate[id] \in PendingStates /\ v \notin failed[id]
       THEN HandleFailure(id, v)
       ELSE UNCHANGED <<bstate, failed, barriers>>
    /\ UNCHANGED nominee

\* on_initialize retry processing (~529) -> start_next_broadcast_attempt
\* (~961): a queued retry behind the first barrier stays queued; otherwise
\* either the signature is refreshed (requires_signature_refresh, e.g. after
\* a key rotation) sending the broadcast back to Signing, or a new attempt
\* is started (or re-queued if nomination fails - a stutter step).
ProcessRetryAttempt(id) ==
    /\ bstate[id] = "RetryQueued"
    /\ RetryAllowed(id)
    /\ \E v \in Validators \ failed[id] : StartAttempt(id, v)
    /\ UNCHANGED barriers

ProcessRetryResign(id) ==
    /\ bstate[id] = "RetryQueued"
    /\ RetryAllowed(id)
    /\ bstate' = [bstate EXCEPT ![id] = "Signing"]
    /\ UNCHANGED <<nominee, failed, timeouts, barriers>>

\* transaction_succeeded -> egress_success (~804): witnessed on the external
\* chain. Possible for any broadcast with a registered transaction_out_id,
\* including previously aborted ones (late inclusion). Clears
\* FailedBroadcasters (after reporting them) and pops barriers.
TransactionSucceeded(id) ==
    /\ bstate[id] \in WitnessableStates
    /\ bstate' = [bstate EXCEPT ![id] = "Succeeded"]
    /\ failed' = [failed EXCEPT ![id] = {}]
    /\ barriers' = PopBarriers(PendingSet \ {id})
    /\ UNCHANGED <<nominee, timeouts>>

Next ==
    \E id \in Ids :
        \/ RequestBroadcast(id)
        \/ SignatureReady(id)
        \/ SigningFailed(id)
        \/ \E v \in Validators : ReportFailure(id, v) \/ TimeoutFires(id, v)
        \/ ProcessRetryAttempt(id)
        \/ ProcessRetryResign(id)
        \/ TransactionSucceeded(id)

\* Fairness for liveness checking: block production keeps processing
\* signatures, timeouts and retry queues (weak fairness), and the retry
\* processor cannot choose the resign path forever (strong fairness on
\* direct attempts - in the code, requires_signature_refresh only holds
\* while the signing key is outdated, which cannot recur indefinitely).
Progress ==
    /\ \A id \in Ids :
        /\ WF_vars(SignatureReady(id))
        /\ SF_vars(ProcessRetryAttempt(id))
    /\ \A id \in Ids : \A v \in Validators : WF_vars(TimeoutFires(id, v))

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ Progress

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
    /\ bstate \in [Ids -> States]
    /\ nominee \in [Ids -> Validators \union {NoNominee}]
    /\ failed \in [Ids -> SUBSET Validators]
    /\ timeouts \subseteq Ids \X Validators
    /\ barriers \subseteq RotationIds

\* An in-flight attempt always has a registered timeout for its current
\* nominee: the chain can never silently forget an in-flight broadcast.
AttemptHasTimeout ==
    \A id \in Ids :
        bstate[id] = "Attempting" =>
            /\ nominee[id] /= NoNominee
            /\ <<id, nominee[id]>> \in timeouts

\* FailedBroadcasters is cleared when a broadcast resolves
\* (egress_success reports-and-takes it; abort_broadcast removes it).
FailedClearedOnResolution ==
    \A id \in Ids :
        bstate[id] \in {"Succeeded", "Aborted", "Unrequested"} => failed[id] = {}

\* A broadcast can never abort while an authority remains that has not
\* failed it: abort requires reports from ALL current authorities.
AbortOnlyWhenAllFailed == [][
    \A id \in Ids :
        (bstate[id] /= "Aborted" /\ bstate'[id] = "Aborted") =>
            Cardinality(failed[id]) = Cardinality(Validators) - 1
]_vars

\* Terminal states are stable, except that an aborted broadcast may still be
\* witnessed as succeeded (late chain inclusion).
TerminalStability == [][
    \A id \in Ids :
        /\ bstate[id] = "Succeeded" => bstate'[id] = "Succeeded"
        /\ bstate[id] = "Dropped"   => bstate'[id] = "Dropped"
        /\ bstate[id] = "Aborted"   => bstate'[id] \in {"Aborted", "Succeeded"}
]_vars

\* Every barrier is backed by a pending broadcast at-or-before it. If this
\* is violated, all later broadcasts are blocked forever (the barrier can
\* only be popped by remove_pending_broadcast, which requires one of the
\* backing broadcasts to resolve). Holds when AllowSigningFailure = FALSE;
\* violated otherwise - see REPORT.md "Findings".
BarrierBacked ==
    \A b \in barriers : \E id \in PendingSet : id <= b

(***************************************************************************)
(* Liveness: every requested broadcast eventually resolves.                *)
(***************************************************************************)
AllBroadcastsResolve ==
    \A id \in Ids :
        (bstate[id] \in PendingStates) ~>
            (bstate[id] \in {"Succeeded", "Aborted"})

=============================================================================
