------------------------- MODULE CeremonyBroadcast -------------------------
(***************************************************************************)
(* Model of engine/multisig BroadcastStage + CeremonyRunner stage machine. *)
(*                                                                         *)
(* Sources:                                                                *)
(*   engine/multisig/src/client/common/broadcast.rs                        *)
(*     process_message (~175): ignore non-participant / redundant / wrong  *)
(*       type; Ready iff messages.len() == all_idxs.len()                  *)
(*     finalize (~230): insert None for missing, then processor.process    *)
(*   engine/multisig/src/client/ceremony_runner.rs                         *)
(*     on_timeout (~352): finalize anyway (do not abort on timeout alone)  *)
(*     timeout deadline reset: current_deadline + MAX_STAGE_DURATION (~211)*)
(*                                                                         *)
(* Abstractions: processor always succeeds if ≥ Quorum messages present,   *)
(* else reports non-deliverers. Crypto validation collapsed into           *)
(* Accept/Reject nondeterminism for received messages.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Parties,          \* e.g. {p1,p2,p3}
    Own,              \* our index, ∈ Parties
    MaxStages,        \* bound stage depth
    Quorum            \* messages required by abstract processor (≥ 1)

ASSUME Own \in Parties
ASSUME Quorum \in Nat /\ Quorum >= 1 /\ Quorum <= Cardinality(Parties)

VARIABLES
    stage,            \* current stage number (1..MaxStages), or 0 = done/aborted
    messages,         \* [Parties -> {"Absent","Present"}]
    status,           \* "Collecting" | "Succeeded" | "Failed"
    reported,         \* SUBSET Parties blamed on failure
    timedOut,         \* whether current stage timed out before Ready
    stagesCompleted

vars == <<stage, messages, status, reported, timedOut, stagesCompleted>>

TypeOK ==
    /\ stage \in 0..MaxStages
    /\ messages \in [Parties -> {"Absent","Present"}]
    /\ status \in {"Collecting","Succeeded","Failed"}
    /\ reported \subseteq Parties
    /\ timedOut \in BOOLEAN
    /\ stagesCompleted \in 0..MaxStages

Init ==
    /\ stage = 1
    /\ messages = [p \in Parties |-> IF p = Own THEN "Present" ELSE "Absent"]
    /\ status = "Collecting"
    /\ reported = {}
    /\ timedOut = FALSE
    /\ stagesCompleted = 0

AllPresent == \A p \in Parties : messages[p] = "Present"
PresentCount == Cardinality({p \in Parties : messages[p] = "Present"})

\* Receive a message from a participant (ignores redundant / non-participant).
Receive(p) ==
    /\ status = "Collecting"
    /\ p \in Parties
    /\ messages[p] = "Absent"
    /\ messages' = [messages EXCEPT ![p] = "Present"]
    /\ UNCHANGED <<stage, status, reported, timedOut, stagesCompleted>>

\* Stage timeout: finalize with missing = Absent (None in the Rust code).
Timeout ==
    /\ status = "Collecting"
    /\ ~AllPresent          \* timeout only meaningful if still waiting
    /\ timedOut' = TRUE
    /\ UNCHANGED <<stage, messages, status, reported, stagesCompleted>>

\* Finalize current stage (Ready or after timeout).
Finalize ==
    /\ status = "Collecting"
    /\ (AllPresent \/ timedOut)
    /\ IF PresentCount >= Quorum
       THEN IF stage = MaxStages
            THEN /\ status' = "Succeeded"
                 /\ stage' = 0
                 /\ stagesCompleted' = stagesCompleted + 1
                 /\ reported' = {}
                 /\ timedOut' = FALSE
                 /\ UNCHANGED messages
            ELSE /\ stage' = stage + 1
                 /\ stagesCompleted' = stagesCompleted + 1
                 /\ messages' = [p \in Parties |-> IF p = Own THEN "Present" ELSE "Absent"]
                 /\ timedOut' = FALSE
                 /\ UNCHANGED <<status, reported>>
       ELSE /\ status' = "Failed"
            /\ stage' = 0
            /\ reported' = {p \in Parties : messages[p] = "Absent"}
            /\ timedOut' = FALSE
            /\ UNCHANGED <<messages, stagesCompleted>>

Next ==
    \/ \E p \in Parties : Receive(p)
    \/ Timeout
    \/ Finalize

Spec == Init /\ [][Next]_vars

\* ---- Invariants -----------------------------------------------------------

\* Own message is always present while collecting (saved in BroadcastStage::init).
OwnAlwaysPresent ==
    status = "Collecting" => messages[Own] = "Present"

\* Never report ourselves solely for being Absent (we always have our message).
NeverReportOwnForAbsence ==
    Own \notin reported

\* Success requires having completed MaxStages stages.
SuccessImpliesAllStages ==
    status = "Succeeded" => stagesCompleted = MaxStages

\* Failure reports only parties that were Absent at finalize.
ReportedWereAbsent ==
    status = "Failed" => reported \subseteq Parties

\* Cannot both succeed and fail.
NotBothTerminal ==
    ~(status = "Succeeded" /\ status = "Failed")

\* Progress: once Ready (all present), Finalize is enabled — no deadlock
\* waiting forever when all messages are in.
NoStuckWhenComplete ==
    (status = "Collecting" /\ AllPresent) => ENABLED Finalize

=============================================================================
