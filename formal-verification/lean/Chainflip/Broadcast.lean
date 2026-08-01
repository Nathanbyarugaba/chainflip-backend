/-
  Model of egress / broadcast authorization and abort/retry safety.

  Correspondence: `state-chain/pallets/cf-broadcast/src/lib.rs`
    - `threshold_sign_and_broadcast`, `on_signature_ready`
    - `transaction_succeeded` / `egress_success` / `clean_up_broadcast_storage`
    - `transaction_failed` / `handle_broadcast_failure`
    - `re_sign_aborted_broadcasts` / `refresh_replay_protection`
  Audits: CF-SEC-006, CF-SEC-007, CF-SEC-023.

  Properties:
    F1. Payload (destination + amount) is immutable after authorization.
    F2. Success callback fires at most once per broadcast id.
    F3. Resign without replay refresh admits double outflow; with refresh, at most one.
    F4. Nonces are unique / monotone under the refresh discipline.
    F5. (negative) Unbound failure reporters can abort; nominee-bound cannot via strangers.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Chainflip.Broadcast

/-- Outflow payload fixed at authorization time. -/
structure Payload where
  dest : ℕ
  amount : ℕ
  deriving DecidableEq

structure Attempt where
  payload : Payload
  nonce : ℕ
  replay : ℕ
  deriving DecidableEq

inductive Status where
  | pending (attempt : Attempt)
  | succeeded (attempt : Attempt)
  | aborted (attempt : Attempt)
  deriving DecidableEq

structure St where
  status : Status
  /-- Number of times the on-chain success / vault-debit effect has fired. -/
  successEffects : ℕ
  /-- Distinct validators who self-reported failure. -/
  failedReporters : Finset ℕ
  /-- Nominated broadcaster for the current attempt (CF-SEC-006). -/
  nominee : ℕ

namespace St

def authorize (payload : Payload) (nonce replay nominee : ℕ) : St where
  status := .pending ⟨payload, nonce, replay⟩
  successEffects := 0
  failedReporters := ∅
  nominee := nominee

/-- Extract the authorized payload (unchanged across status). -/
def payloadOf : Status → Payload
  | .pending a | .succeeded a | .aborted a => a.payload

def attemptOf : Status → Attempt
  | .pending a | .succeeded a | .aborted a => a

/-- Success path: consume the pending broadcast. -/
def succeed (s : St) : St :=
  match s.status with
  | .pending a =>
      { status := .succeeded a
        successEffects := s.successEffects + 1
        failedReporters := s.failedReporters
        nominee := s.nominee }
  | _ => s

/-- Abort path. -/
def abort (s : St) : St :=
  match s.status with
  | .pending a =>
      { status := .aborted a
        successEffects := s.successEffects
        failedReporters := s.failedReporters
        nominee := s.nominee }
  | _ => s

/-- Re-sign an aborted broadcast. -/
def resign (s : St) (refresh : Bool) : St :=
  match s.status with
  | .aborted a =>
      let a' : Attempt :=
        if refresh then { a with nonce := a.nonce + 1, replay := a.replay + 1 }
        else a
      { status := .pending a'
        successEffects := s.successEffects
        failedReporters := ∅
        nominee := s.nominee }
  | _ => s

/-- Failure report. `requireNominee` models the CF-SEC-006 fix. -/
def reportFailure (s : St) (reporter : ℕ) (requireNominee : Bool) : St :=
  match s.status with
  | .pending _ =>
      if requireNominee && reporter ≠ s.nominee then s
      else
        { status := s.status
          successEffects := s.successEffects
          failedReporters := insert reporter s.failedReporters
          nominee := s.nominee }
  | _ => s

/-- Abort once enough distinct failure reporters accumulate. -/
def maybeAbort (s : St) (failureThreshold : ℕ) : St :=
  match s.status with
  | .pending _ =>
      if failureThreshold ≤ s.failedReporters.card then s.abort else s
  | _ => s

end St

/-! ### F1. Payload immutability -/

theorem payload_immutable_succeed (s : St) :
    St.payloadOf s.succeed.status = St.payloadOf s.status := by
  rcases s with ⟨status, se, fr, nom⟩
  cases status <;> simp [St.succeed, St.payloadOf]

theorem payload_immutable_abort (s : St) :
    St.payloadOf s.abort.status = St.payloadOf s.status := by
  rcases s with ⟨status, se, fr, nom⟩
  cases status <;> simp [St.abort, St.payloadOf]

theorem payload_immutable_resign (s : St) (refresh : Bool) :
    St.payloadOf (s.resign refresh).status = St.payloadOf s.status := by
  rcases s with ⟨status, se, fr, nom⟩
  cases status <;> cases refresh <;> simp [St.resign, St.payloadOf]

/-! ### F2. Success callback at most once -/

theorem succeed_idempotent_effect (s : St) :
    s.succeed.succeed.successEffects = s.succeed.successEffects := by
  rcases s with ⟨status, se, fr, nom⟩
  cases status <;> simp [St.succeed]

theorem succeed_effect_le_one_from_fresh (payload : Payload) (n r nom : ℕ) :
    (St.authorize payload n r nom).succeed.successEffects ≤ 1 := by
  simp [St.authorize, St.succeed]

theorem succeed_effect_le_one_after_retry (payload : Payload) (n r nom : ℕ) :
    (((St.authorize payload n r nom).abort.resign true).succeed).successEffects ≤ 1 := by
  simp [St.authorize, St.abort, St.resign, St.succeed]

/-! ### F3. Resign replay safety -/

def sameReplay (a b : Attempt) : Prop :=
  a.nonce = b.nonce ∧ a.replay = b.replay

theorem resign_without_refresh_reuses_replay (a : Attempt)
    (s : St) (h : s.status = .aborted a) :
    sameReplay a (St.attemptOf (s.resign false).status) := by
  simp [St.resign, St.attemptOf, sameReplay, h]

theorem resign_with_refresh_advances (a : Attempt)
    (s : St) (h : s.status = .aborted a) :
    a.nonce < (St.attemptOf (s.resign true).status).nonce ∧
      a.replay < (St.attemptOf (s.resign true).status).replay := by
  simp [St.resign, St.attemptOf, h]

theorem resign_with_refresh_no_collision (a : Attempt)
    (s : St) (h : s.status = .aborted a) :
    ¬ sameReplay a (St.attemptOf (s.resign true).status) := by
  intro ⟨hne, _⟩
  have ⟨hn, _⟩ := resign_with_refresh_advances a s h
  exact absurd hne (Nat.ne_of_lt hn)

/-! ### F4. Nonce uniqueness under refresh discipline -/

theorem authorize_nonce (payload : Payload) (n r nom : ℕ) :
    (St.attemptOf (St.authorize payload n r nom).status).nonce = n := by
  rfl

theorem refreshed_nonce_ne_original (a : Attempt)
    (s : St) (h : s.status = .aborted a) :
    (St.attemptOf (s.resign true).status).nonce ≠ a.nonce := by
  have ⟨hn, _⟩ := resign_with_refresh_advances a s h
  exact (Nat.ne_of_lt hn).symm

/-! ### F5. Failure reporter binding (CF-SEC-006) -/

theorem unbound_failure_accepts_stranger (payload : Payload) (n r nom stranger : ℕ)
    (_hne : stranger ≠ nom) :
    stranger ∈
      ((St.authorize payload n r nom).reportFailure stranger false).failedReporters := by
  simp [St.authorize, St.reportFailure]

theorem nominee_bound_rejects_stranger (payload : Payload) (n r nom stranger : ℕ)
    (hne : stranger ≠ nom) :
    ((St.authorize payload n r nom).reportFailure stranger true).failedReporters = ∅ := by
  simp [St.authorize, St.reportFailure, hne]

theorem single_stranger_cannot_abort (payload : Payload) (n r nom stranger : ℕ)
    (hne : stranger ≠ nom) :
    (((St.authorize payload n r nom).reportFailure stranger true).maybeAbort 1).status =
      .pending ⟨payload, n, r⟩ := by
  simp [St.authorize, St.reportFailure, St.maybeAbort, hne]

theorem nominee_failure_is_recorded (payload : Payload) (n r nom : ℕ) :
    nom ∈ ((St.authorize payload n r nom).reportFailure nom true).failedReporters := by
  simp [St.authorize, St.reportFailure]

end Chainflip.Broadcast
