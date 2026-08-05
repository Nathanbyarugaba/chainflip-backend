------------------------------ MODULE Retrier ------------------------------
(***************************************************************************)
(* Model of engine/src/retrier.rs attempt counting with RetryLimit::Limit. *)
(*                                                                         *)
(* FINDING: Limit(0) still runs attempt 0 (the Limit check is only on the  *)
(* retry path). A caller passing 0 does not get zero attempts.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Limit,
    FailForever

VARIABLES
    attempt,        \* last started attempt index (meaningful when started)
    started,        \* has attempt 0 been started?
    phase,          \* Idle | InFlight | Delay | DoneOk | DoneErr
    deliveries

vars == <<attempt, started, phase, deliveries>>

Init ==
    /\ attempt = 0
    /\ started = FALSE
    /\ phase = "Idle"
    /\ deliveries = 0

StartFirst ==
    /\ phase = "Idle"
    /\ ~started
    /\ started' = TRUE
    /\ attempt' = 0
    /\ phase' = "InFlight"
    /\ UNCHANGED deliveries

Succeed ==
    /\ phase = "InFlight"
    /\ ~FailForever
    /\ phase' = "DoneOk"
    /\ deliveries' = deliveries + 1
    /\ UNCHANGED <<attempt, started>>

Fail ==
    /\ phase = "InFlight"
    /\ phase' = "Delay"
    /\ UNCHANGED <<attempt, started, deliveries>>

RetryOrExhaust ==
    /\ phase = "Delay"
    /\ LET next == attempt + 1 IN
       IF next >= Limit
       THEN /\ phase' = "DoneErr"
            /\ UNCHANGED <<attempt, started, deliveries>>
       ELSE /\ attempt' = next
            /\ phase' = "InFlight"
            /\ UNCHANGED <<started, deliveries>>

Next == StartFirst \/ Succeed \/ Fail \/ RetryOrExhaust
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ attempt \in Nat
    /\ started \in BOOLEAN
    /\ phase \in {"Idle","InFlight","Delay","DoneOk","DoneErr"}
    /\ deliveries \in 0..1

AtMostOneDelivery == deliveries <= 1

AttemptIndexValid ==
    \/ ~started
    \/ /\ Limit = 0 /\ attempt = 0
    \/ /\ Limit > 0 /\ attempt < Limit

\* Probe (expected FALSE under Limit=0): "Limit(0) means no attempts start".
AttemptNeverStarts == ~started

=============================================================================
