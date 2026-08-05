-------------------------- MODULE AuthorityRotation --------------------------
(***************************************************************************)
(* Model of the Chainflip authority / key rotation state machine.         *)
(*                                                                         *)
(* Sources modelled (file:line references are to the commit this spec was *)
(* written against):                                                       *)
(*   - state-chain/pallets/cf-validator/src/lib.rs                        *)
(*       RotationPhase                    (~line 134)                     *)
(*       on_initialize rotation driver    (~lines 583-706)                *)
(*       start_authority_rotation         (~line 1933)                    *)
(*       try_restart_keygen               (~line 2003)                    *)
(*       start_keygen_attempt             (~line 2041)                    *)
(*       try_start_key_handover           (~line 2088)                    *)
(*       abort_rotation                   (~line 1841)                    *)
(*       SessionManager::new_session / start_session (~lines 2336-2390)   *)
(*   - state-chain/pallets/cf-threshold-signature/src/lib.rs              *)
(*       KeyRotationStatus                (~line 181)                     *)
(*   - state-chain/pallets/cf-threshold-signature/src/key_rotator.rs      *)
(*       KeyRotator impl (keygen, key_handover, status, activate_keys,    *)
(*       reset_key_rotation)                                              *)
(*   - state-chain/runtime/src/chainflip/cons_key_rotator.rs              *)
(*       ConsKeyRotator::status (combination of per-chain statuses)       *)
(*                                                                         *)
(* Abstractions (documented in ../REPORT.md):                              *)
(*   - The auction is abstracted: winners are always `Validators \ banned` *)
(*     and the auction can nondeterministically fail (AuctionError).       *)
(*   - Keygen/handover *verification* signing ceremonies are kept as       *)
(*     distinct pending states, but their internals are not modelled.      *)
(*   - Offender sets are chosen nondeterministically, bounded only by the  *)
(*     participant sets, and may be empty (mirroring an inconclusive       *)
(*     ceremony resolution).                                               *)
(*   - `FailureBudget` bounds the number of ceremony failures so that the  *)
(*     state space is finite; liveness results are therefore relative to   *)
(*     the assumption that ceremonies do not fail forever.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Validators,      \* e.g. {v1, v2, v3}
    Chains,          \* e.g. {c1, c2}; one per ChainCrypto instance
    HandoverChains,  \* subset of Chains whose crypto requires key handover (e.g. Bitcoin)
    MinSize,         \* minimum authority-set size (SetSizeParameters::min_size)
    MaxEpochs,       \* bound on the number of epoch transitions explored
    MaxFailures      \* bound on the number of ceremony failures explored

ASSUME HandoverChains \subseteq Chains
ASSUME MinSize \in Nat /\ MinSize >= 1 /\ Cardinality(Validators) >= MinSize

(***************************************************************************)
(* Per-chain key rotation states: cf-threshold-signature                  *)
(* KeyRotationStatus, with `PendingKeyRotation = None` modelled as "Void". *)
(* AwaitingActivationSignatures->Complete collapse: a chain's activation   *)
(* signatures completing and VaultActivator reporting readiness are        *)
(* modelled as a single per-chain step.                                    *)
(***************************************************************************)
ChainStates == {
    "Void",                          \* PendingKeyRotation empty
    "AwaitingKeygen",
    "AwaitingKeygenVerification",
    "KeygenVerificationComplete",
    "AwaitingKeyHandover",
    "AwaitingKeyHandoverVerification",
    "KeyHandoverComplete",
    "KeyHandoverFailed",
    "AwaitingActivationSignatures",
    "Complete",
    "Failed"
}

Phases == {
    "Idle", "KeygensInProgress", "KeyHandoversInProgress",
    "ActivatingKeys", "NewKeysActivated", "SessionRotating"
}

VARIABLES
    phase,        \* cf-validator CurrentRotationPhase
    chainState,   \* [Chains -> ChainStates]         (PendingKeyRotation per instance)
    chainOffenders, \* [Chains -> SUBSET Validators] (offenders recorded in Failed states)
    banned,       \* RotationState::banned
    candidates,   \* RotationState::primary_candidates
    authorities,  \* CurrentAuthorities
    epoch,        \* CurrentEpoch
    safeMode,     \* SafeMode::authority_rotation_enabled
    broadcastsPending, \* RotationBroadcastsPending::rotation_broadcasts_pending()
    failureBudget,
    violation     \* TRUE if a code assert!/log_or_panic!/debug_assert! would have fired

vars == <<phase, chainState, chainOffenders, banned, candidates, authorities,
          epoch, safeMode, broadcastsPending, failureBudget, violation>>

(***************************************************************************)
(* Status combination: key_rotator.rs `status()` per chain, then           *)
(* cons_key_rotator.rs across chains.                                      *)
(***************************************************************************)
PendingStates == {
    "AwaitingKeygen", "AwaitingKeygenVerification",
    "AwaitingKeyHandover", "AwaitingKeyHandoverVerification",
    "AwaitingActivationSignatures"
}

\* Per-chain AsyncResult<KeyRotationStatusOuter>, encoded as a string.
ChainStatus(c) ==
    CASE chainState[c] = "Void"                        -> "Void"
      [] chainState[c] \in PendingStates               -> "Pending"
      [] chainState[c] = "KeygenVerificationComplete"  -> "KeygenComplete"
      [] chainState[c] = "KeyHandoverComplete"         -> "KeyHandoverComplete"
      [] chainState[c] = "KeyHandoverFailed"           -> "Failed"
      [] chainState[c] = "Failed"                      -> "Failed"
      [] chainState[c] = "Complete"                    -> "RotationComplete"

\* ConsKeyRotator::status(): Void dominates, then Pending; homogeneous Ready
\* statuses pass through; any other mix (incl. any failure) is Failed.
CombinedStatus ==
    IF \E c \in Chains : ChainStatus(c) = "Void" THEN "Void"
    ELSE IF \E c \in Chains : ChainStatus(c) = "Pending" THEN "Pending"
    ELSE IF \A c \in Chains : ChainStatus(c) = "KeygenComplete" THEN "KeygenComplete"
    ELSE IF \A c \in Chains : ChainStatus(c) = "KeyHandoverComplete" THEN "KeyHandoverComplete"
    ELSE IF \A c \in Chains : ChainStatus(c) = "RotationComplete" THEN "RotationComplete"
    ELSE "Failed"

\* Failed(offenders): union of offenders over failed chains.
CombinedOffenders ==
    UNION { chainOffenders[c] : c \in { cc \in Chains :
                ChainStatus(cc) = "Failed" } }

\* cf-validator current_consensus_success_threshold():
\* success_threshold_from_share_count = ceil(2/3 * n) rounded up to strict
\* two-thirds majority; we use floor(2n/3) + 1.
Threshold(n) == ((2 * n) \div 3) + 1

(***************************************************************************)
(* Helpers mirroring pallet functions.                                     *)
(***************************************************************************)

\* abort_rotation() (~1841): reset_key_rotation() on every chain + phase Idle.
\* `banned` and `candidates` are rotation-scoped state whose handling differs
\* per call site, so they are constrained by the caller.
Abort ==
    /\ phase' = "Idle"
    /\ chainState' = [c \in Chains |-> "Void"]
    /\ chainOffenders' = [c \in Chains |-> {}]
    /\ UNCHANGED <<authorities, epoch>>

\* key_rotator.rs `keygen`: PendingKeyRotation := AwaitingKeygen on all chains.
\* start_keygen_attempt (~2041) calls reset_key_rotation() first, then checks
\* the min-size condition before invoking keygen.
StartKeygen(cands) ==
    /\ chainState' = [c \in Chains |-> "AwaitingKeygen"]
    /\ chainOffenders' = [c \in Chains |-> {}]
    /\ candidates' = cands
    /\ phase' = "KeygensInProgress"

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init ==
    /\ phase = "Idle"
    /\ chainState = [c \in Chains |-> "Void"]
    /\ chainOffenders = [c \in Chains |-> {}]
    /\ banned = {}
    /\ candidates = {}
    /\ authorities = Validators
    /\ epoch = 0
    /\ safeMode \in BOOLEAN
    /\ broadcastsPending \in BOOLEAN
    /\ failureBudget = MaxFailures
    /\ violation = FALSE

\* --- Environment -----------------------------------------------------------

\* Governance can toggle the AUTHORITY_ROTATION safe-mode flag at any time.
ToggleSafeMode ==
    /\ safeMode' = ~safeMode
    /\ UNCHANGED <<phase, chainState, chainOffenders, banned, candidates,
                   authorities, epoch, broadcastsPending, failureBudget, violation>>

\* Rotation broadcasts (from the previous rotation) completing or appearing.
ToggleBroadcastsPending ==
    /\ broadcastsPending' = ~broadcastsPending
    /\ UNCHANGED <<phase, chainState, chainOffenders, banned, candidates,
                   authorities, epoch, safeMode, failureBudget, violation>>

\* --- Rotation start: on_initialize Idle arm (~591) + start_authority_rotation

\* Auction winners are abstracted as "all non-banned validators". At initial
\* rotation start nobody is banned/excluded (start_authority_rotation passes
\* an empty exclusion set and a fresh RotationState is created).
StartRotation ==
    /\ phase = "Idle"
    /\ epoch < MaxEpochs                     \* state-space bound
    /\ ~broadcastsPending                    \* RotationBroadcastsPending gate (~593)
    /\ safeMode                              \* safe-mode gate in start_authority_rotation
    /\ \/ \* Auction failure (AuctionError) => abort_rotation() (~2030)
          /\ Abort
          /\ UNCHANGED <<banned, candidates>>
       \/ \* Auction success. NotEnoughCandidates cannot fire here since
          \* winners = Validators and |Validators| >= MinSize (ASSUME).
          /\ banned' = {}
          /\ StartKeygen(Validators)
          /\ UNCHANGED <<authorities, epoch>>
    /\ UNCHANGED <<safeMode, broadcastsPending, failureBudget, violation>>

\* --- Per-chain ceremony progress (extrinsics / hooks on the ts pallet) ------

\* Keygen ceremony resolves: success -> verification signing starts
\* (trigger_keygen_verification), failure -> Failed{offenders} where
\* offenders are a subset of the keygen participants (= candidates).
ChainKeygenSuccess(c) ==
    /\ chainState[c] = "AwaitingKeygen"
    /\ chainState' = [chainState EXCEPT ![c] = "AwaitingKeygenVerification"]
    /\ UNCHANGED <<phase, chainOffenders, banned, candidates, authorities, epoch,
                   safeMode, broadcastsPending, failureBudget, violation>>

ChainKeygenFailure(c) ==
    /\ chainState[c] = "AwaitingKeygen"
    /\ failureBudget > 0
    /\ \E offs \in SUBSET candidates :
        /\ chainState' = [chainState EXCEPT ![c] = "Failed"]
        /\ chainOffenders' = [chainOffenders EXCEPT ![c] = offs]
    /\ failureBudget' = failureBudget - 1
    /\ UNCHANGED <<phase, banned, candidates, authorities, epoch, safeMode,
                   broadcastsPending, violation>>

\* Keygen verification signing ceremony resolves
\* (on_keygen_verification_result, ~1242 / keygen_failure ~1559).
ChainKeygenVerificationSuccess(c) ==
    /\ chainState[c] = "AwaitingKeygenVerification"
    /\ chainState' = [chainState EXCEPT ![c] = "KeygenVerificationComplete"]
    /\ UNCHANGED <<phase, chainOffenders, banned, candidates, authorities, epoch,
                   safeMode, broadcastsPending, failureBudget, violation>>

ChainKeygenVerificationFailure(c) ==
    /\ chainState[c] = "AwaitingKeygenVerification"
    /\ failureBudget > 0
    /\ \E offs \in SUBSET candidates :
        /\ chainState' = [chainState EXCEPT ![c] = "Failed"]
        /\ chainOffenders' = [chainOffenders EXCEPT ![c] = offs]
    /\ failureBudget' = failureBudget - 1
    /\ UNCHANGED <<phase, banned, candidates, authorities, epoch, safeMode,
                   broadcastsPending, violation>>

\* Key handover ceremony participants are sharing (old authorities) union
\* receiving (candidates); offenders may come from either set.
ChainHandoverSuccess(c) ==
    /\ chainState[c] = "AwaitingKeyHandover"
    /\ chainState' = [chainState EXCEPT ![c] = "AwaitingKeyHandoverVerification"]
    /\ UNCHANGED <<phase, chainOffenders, banned, candidates, authorities, epoch,
                   safeMode, broadcastsPending, failureBudget, violation>>

ChainHandoverFailure(c) ==
    /\ chainState[c] = "AwaitingKeyHandover"
    /\ failureBudget > 0
    /\ \E offs \in SUBSET (authorities \union candidates) :
        /\ chainState' = [chainState EXCEPT ![c] = "KeyHandoverFailed"]
        /\ chainOffenders' = [chainOffenders EXCEPT ![c] = offs]
    /\ failureBudget' = failureBudget - 1
    /\ UNCHANGED <<phase, banned, candidates, authorities, epoch, safeMode,
                   broadcastsPending, violation>>

ChainHandoverVerificationSuccess(c) ==
    /\ chainState[c] = "AwaitingKeyHandoverVerification"
    /\ chainState' = [chainState EXCEPT ![c] = "KeyHandoverComplete"]
    /\ UNCHANGED <<phase, chainOffenders, banned, candidates, authorities, epoch,
                   safeMode, broadcastsPending, failureBudget, violation>>

ChainHandoverVerificationFailure(c) ==
    /\ chainState[c] = "AwaitingKeyHandoverVerification"
    /\ failureBudget > 0
    /\ \E offs \in SUBSET (authorities \union candidates) :
        /\ chainState' = [chainState EXCEPT ![c] = "KeyHandoverFailed"]
        /\ chainOffenders' = [chainOffenders EXCEPT ![c] = offs]
    /\ failureBudget' = failureBudget - 1
    /\ UNCHANGED <<phase, banned, candidates, authorities, epoch, safeMode,
                   broadcastsPending, violation>>

\* A chain's activation signatures complete and the vault activates
\* (AwaitingActivationSignatures arm of status() + mark_key_rotation_complete).
ChainActivationDone(c) ==
    /\ chainState[c] = "AwaitingActivationSignatures"
    /\ chainState' = [chainState EXCEPT ![c] = "Complete"]
    /\ UNCHANGED <<phase, chainOffenders, banned, candidates, authorities, epoch,
                   safeMode, broadcastsPending, failureBudget, violation>>

\* --- Validator pallet on_initialize polling --------------------------------

\* try_restart_keygen (~2003): ban offenders, re-run auction excluding banned,
\* restart keygen or abort. The auction itself may also fail nondeterministically.
RestartKeygen(offs) ==
    LET newBanned == banned \union offs
        winners   == Validators \ newBanned
    IN
    /\ banned' = newBanned
    /\ IF Cardinality(winners) >= MinSize
       THEN \/ /\ StartKeygen(winners)   \* auction succeeded
               /\ UNCHANGED <<authorities, epoch>>
            \/ /\ Abort                  \* AuctionFailed { .. } => abort
               /\ UNCHANGED candidates
       ELSE \* NotEnoughCandidates => handle_rotation_error + abort
            /\ Abort
            /\ UNCHANGED candidates

\* try_start_key_handover (~2088). Sharing participants are selected from
\* unbanned current authorities; selection fails when too many are banned.
\* Chains not requiring handover jump straight to KeyHandoverComplete
\* (NoKeyHandover branch in key_rotator.rs). Chains already KeyHandoverComplete
\* are left untouched ("Key handover already complete").
TryStartKeyHandover(newBanned) ==
    IF ~safeMode
    THEN /\ Abort
         /\ UNCHANGED candidates
    ELSE IF Cardinality(authorities \ newBanned) >= Threshold(Cardinality(authorities))
    THEN /\ phase' = "KeyHandoversInProgress"
         /\ chainState' = [c \in Chains |->
                IF chainState[c] = "KeyHandoverComplete"
                THEN "KeyHandoverComplete"
                ELSE IF c \in HandoverChains
                     THEN "AwaitingKeyHandover"
                     ELSE "KeyHandoverComplete"]
         /\ chainOffenders' = [c \in Chains |-> {}]
         /\ UNCHANGED <<candidates, authorities, epoch>>
    ELSE \* select_sharing_participants returned None => abort (~2113)
         /\ Abort
         /\ UNCHANGED candidates

\* on_initialize, KeygensInProgress arm (~605).
PollKeygen ==
    /\ phase = "KeygensInProgress"
    /\ CombinedStatus \in {"KeygenComplete", "Failed"}
    /\ IF CombinedStatus = "KeygenComplete"
       THEN /\ TryStartKeyHandover(banned)
            /\ UNCHANGED banned
            /\ violation' = violation \/
                 \* key_handover() log_or_panic!s unless every chain is in
                 \* KeygenVerificationComplete / KeyHandoverFailed /
                 \* KeyHandoverComplete.
                 (safeMode /\ Cardinality(authorities \ banned) >= Threshold(Cardinality(authorities))
                  /\ \E c \in Chains : chainState[c] \notin
                        {"KeygenVerificationComplete", "KeyHandoverFailed", "KeyHandoverComplete"})
       ELSE \* Failed(offenders) => try_restart_keygen or abort (~611)
            /\ RestartKeygen(CombinedOffenders)
            /\ UNCHANGED violation
    /\ UNCHANGED <<safeMode, broadcastsPending, failureBudget>>

\* on_initialize, KeyHandoversInProgress arm (~634).
PollHandover ==
    /\ phase = "KeyHandoversInProgress"
    /\ CombinedStatus \in {"KeyHandoverComplete", "Failed"}
    /\ IF CombinedStatus = "KeyHandoverComplete"
       THEN \* KeyRotator::activate_keys(): each chain either needs activation
            \* signatures or completes immediately (no activation tx / chain
            \* not initialised / first vault handled by governance are all
            \* collapsed into the nondeterministic immediate-Complete branch).
            /\ phase' = "ActivatingKeys"
            /\ \E immediate \in SUBSET Chains :
                   chainState' = [c \in Chains |->
                       IF c \in immediate THEN "Complete"
                       ELSE "AwaitingActivationSignatures"]
            /\ chainOffenders' = [c \in Chains |-> {}]
            /\ UNCHANGED <<banned, candidates, authorities, epoch, violation>>
       ELSE \* Failed(offenders) (~641)
            LET offs == CombinedOffenders IN
            IF offs \intersect candidates /= {}
            THEN \* candidate offenders: retry from keygen (~652)
                 /\ RestartKeygen(offs)
                 /\ UNCHANGED violation
            ELSE \* only non-candidate (sharing) offenders: ban them and retry
                 \* the handover with a new participant set (~663)
                 /\ TryStartKeyHandover(banned \union offs)
                 /\ banned' = banned \union offs
                 /\ UNCHANGED violation
    /\ UNCHANGED <<safeMode, broadcastsPending, failureBudget>>

\* on_initialize, ActivatingKeys arm (~682). Only Pending / RotationComplete
\* are expected here; anything else is a debug_assert + abort in the code and
\* is proven unreachable by the ActivatingStatusSane invariant below.
PollActivating ==
    /\ phase = "ActivatingKeys"
    /\ CombinedStatus = "RotationComplete"
    /\ phase' = "NewKeysActivated"
    /\ UNCHANGED <<chainState, chainOffenders, banned, candidates, authorities,
                   epoch, safeMode, broadcastsPending, failureBudget, violation>>

\* --- Session pallet handoff -------------------------------------------------

\* SessionManager::new_session with NewKeysActivated (~2343): queue the new
\* authorities and move to SessionRotating.
SessionRotateFirst ==
    /\ phase = "NewKeysActivated"
    /\ phase' = "SessionRotating"
    /\ UNCHANGED <<chainState, chainOffenders, banned, candidates, authorities,
                   epoch, safeMode, broadcastsPending, failureBudget, violation>>

\* start_session with SessionRotating => transition_to_next_epoch (authorities
\* and epoch update), and new_session with SessionRotating => back to Idle.
\* Both occur during the same session rotation; modelled as one atomic step.
SessionRotateSecond ==
    /\ phase = "SessionRotating"
    /\ phase' = "Idle"
    /\ authorities' = candidates
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<chainState, chainOffenders, banned, candidates, safeMode,
                   broadcastsPending, failureBudget, violation>>

Next ==
    \/ StartRotation
    \/ PollKeygen \/ PollHandover \/ PollActivating
    \/ SessionRotateFirst \/ SessionRotateSecond
    \/ ToggleSafeMode \/ ToggleBroadcastsPending
    \/ \E c \in Chains :
        \/ ChainKeygenSuccess(c) \/ ChainKeygenFailure(c)
        \/ ChainKeygenVerificationSuccess(c) \/ ChainKeygenVerificationFailure(c)
        \/ ChainHandoverSuccess(c) \/ ChainHandoverFailure(c)
        \/ ChainHandoverVerificationSuccess(c) \/ ChainHandoverVerificationFailure(c)
        \/ ChainActivationDone(c)

\* Fairness: block production keeps polling hooks and session rotation running,
\* and ceremonies eventually resolve (success is always possible; failure is
\* bounded by failureBudget).
Progress ==
    /\ WF_vars(PollKeygen) /\ WF_vars(PollHandover) /\ WF_vars(PollActivating)
    /\ WF_vars(SessionRotateFirst) /\ WF_vars(SessionRotateSecond)
    /\ \A c \in Chains :
        /\ WF_vars(ChainKeygenSuccess(c) \/ ChainKeygenFailure(c))
        /\ WF_vars(ChainKeygenVerificationSuccess(c) \/ ChainKeygenVerificationFailure(c))
        /\ WF_vars(ChainHandoverSuccess(c) \/ ChainHandoverFailure(c))
        /\ WF_vars(ChainHandoverVerificationSuccess(c) \/ ChainHandoverVerificationFailure(c))
        /\ WF_vars(ChainActivationDone(c))

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ Progress

(***************************************************************************)
(* Invariants (safety)                                                     *)
(***************************************************************************)

TypeOK ==
    /\ phase \in Phases
    /\ chainState \in [Chains -> ChainStates]
    /\ chainOffenders \in [Chains -> SUBSET Validators]
    /\ banned \subseteq Validators
    /\ candidates \subseteq Validators
    /\ authorities \subseteq Validators
    /\ epoch \in 0..MaxEpochs
    /\ safeMode \in BOOLEAN
    /\ broadcastsPending \in BOOLEAN
    /\ failureBudget \in 0..MaxFailures
    /\ violation \in BOOLEAN

\* No assert!/log_or_panic! guard inside KeyRotator can fire.
NoViolation == ~violation

\* Validator-pallet phase and per-chain key rotation statuses always agree.
PhaseCoherence ==
    /\ phase = "Idle" =>
        \A c \in Chains : chainState[c] \in {"Void", "Complete"}
    /\ phase = "KeygensInProgress" =>
        \A c \in Chains : chainState[c] \in
            {"AwaitingKeygen", "AwaitingKeygenVerification",
             "KeygenVerificationComplete", "Failed"}
    /\ phase = "KeyHandoversInProgress" =>
        \A c \in Chains : chainState[c] \in
            {"AwaitingKeyHandover", "AwaitingKeyHandoverVerification",
             "KeyHandoverComplete", "KeyHandoverFailed"}
    /\ phase = "ActivatingKeys" =>
        \A c \in Chains : chainState[c] \in
            {"AwaitingActivationSignatures", "Complete"}
    /\ phase \in {"NewKeysActivated", "SessionRotating"} =>
        \A c \in Chains : chainState[c] = "Complete"

\* The debug_assert!s on unexpected statuses in the on_initialize arms
\* (~lines 622, 674, 690) can never fire.
StatusSanity ==
    /\ phase = "KeygensInProgress" =>
        CombinedStatus \in {"Pending", "KeygenComplete", "Failed"}
    /\ phase = "KeyHandoversInProgress" =>
        CombinedStatus \in {"Pending", "KeyHandoverComplete", "Failed"}
    /\ phase = "ActivatingKeys" =>
        CombinedStatus \in {"Pending", "RotationComplete"}

\* Mirrors the debug_assert in try_restart_keygen (~2037): banned validators
\* are never primary candidates while a rotation is in progress.
BannedNotCandidates ==
    phase \in {"KeygensInProgress", "KeyHandoversInProgress"} =>
        banned \intersect candidates = {}

\* New keys are only ever activated for a full candidate set of at least
\* MinSize (the chain never rotates to a degenerate authority set).
AuthoritySetNeverTooSmall ==
    /\ Cardinality(authorities) >= MinSize
    /\ phase \in {"ActivatingKeys", "NewKeysActivated", "SessionRotating"} =>
          Cardinality(candidates) >= MinSize

(***************************************************************************)
(* Action properties (safety over transitions)                             *)
(***************************************************************************)

\* Once keys are activated the rotation cannot abort: it must run forward to
\* epoch transition. Funds are already controlled by the new keys.
NoAbortAfterActivation == [][
    /\ phase = "NewKeysActivated" =>
          phase' \in {"NewKeysActivated", "SessionRotating"}
    /\ phase = "SessionRotating" =>
          \/ phase' = "SessionRotating"
          \/ (phase' = "Idle" /\ epoch' = epoch + 1 /\ authorities' = candidates)
]_vars

\* The authority set only changes at the SessionRotating -> Idle epoch
\* transition, and the epoch only advances there.
AuthoritiesOnlyChangeAtEpochBoundary == [][
    authorities' /= authorities =>
        /\ phase = "SessionRotating" /\ phase' = "Idle"
        /\ epoch' = epoch + 1
        /\ authorities' = candidates
]_vars

EpochOnlyAdvancesFromSessionRotating == [][
    epoch' /= epoch =>
        /\ epoch' = epoch + 1
        /\ phase = "SessionRotating"
        /\ \A c \in Chains : chainState[c] = "Complete"
]_vars

(***************************************************************************)
(* Liveness: every started rotation terminates (completes or aborts),      *)
(* under fairness and bounded ceremony failures.                           *)
(***************************************************************************)
RotationTerminates == (phase /= "Idle") ~> (phase = "Idle")

\* All validators are interchangeable in this model (used for TLC symmetry
\* reduction in safety-only configurations).
ValidatorPerms == Permutations(Validators)

=============================================================================
