/-
  Model of the Chainflip witnesser: threshold voting + at-most-once dispatch.

  Correspondence: `state-chain/pallets/cf-witnesser/src/lib.rs`
    - `witness_at_epoch` (vote bitmask, DuplicateWitness, success-threshold dispatch)
    - `CallHashExecuted` (epoch-windowed idempotence)
    - `dispatch_call` / `force_witness`

  Security properties:
    B1. No double-vote by the same authority.
    B2. Once dispatched, further votes never re-dispatch (idempotence).
    B3. Dispatch implies a success-sized quorum of distinct authorities.
    B4. (negative) `force_witness` can re-dispatch (documented governance hole).
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Chainflip.Threshold

namespace Chainflip.Witnesser

open Chainflip.Threshold

abbrev AuthIdx := ℕ

/-- Witnesser state for a single call-hash under a fixed authority set of size `n`. -/
structure St (n : ℕ) where
  votes : Finset AuthIdx
  executed : Bool
  votes_subset : ∀ a ∈ votes, a < n

namespace St

def empty (n : ℕ) : St n where
  votes := ∅
  executed := false
  votes_subset := by intro _ ha; cases ha

/-- Vote step mirroring `witness_at_epoch`. Returns `(newState, dispatchedThisStep)`. -/
def step (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n) : St n × Bool :=
  if a ∈ s.votes then
    (s, false)
  else
    let votes' := insert a s.votes
    let dispatch : Bool := decide (s.executed = false ∧ votes'.card = success n)
    let s' : St n := {
      votes := votes'
      executed := s.executed || dispatch
      votes_subset := by
        intro b hb
        have hb' : b = a ∨ b ∈ s.votes := by simpa [votes'] using hb
        rcases hb' with rfl | hb
        · exact ha
        · exact s.votes_subset b hb
    }
    (s', dispatch)

end St

/-! ### B1. No double-vote inflation -/

theorem step_duplicate_noop (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (hin : a ∈ s.votes) :
    St.step n s a ha = (s, false) := by
  simp [St.step, hin]

theorem votes_card_le (n : ℕ) (s : St n) : s.votes.card ≤ n := by
  have hsub : s.votes ⊆ Finset.range n := by
    intro a ha
    exact Finset.mem_range.mpr (s.votes_subset a ha)
  exact (Finset.card_le_card hsub).trans_eq (by simp)

theorem step_preserves_votes_subset (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n) :
    ∀ b ∈ (St.step n s a ha).1.votes, b < n :=
  (St.step n s a ha).1.votes_subset

/-! ### B2. At-most-once dispatch (idempotence) -/

/-- Once executed, further votes never re-dispatch.
    This is the core CallHashExecuted guard. -/
theorem no_redispatch_after_executed (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (hex : s.executed = true) :
    (St.step n s a ha).2 = false := by
  unfold St.step
  by_cases hdup : a ∈ s.votes
  · simp [hdup]
  · simp [hdup, hex]

/-- Dispatch sets the executed flag, so a subsequent step cannot dispatch again. -/
theorem dispatch_sets_executed (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (hdisp : (St.step n s a ha).2 = true) :
    (St.step n s a ha).1.executed = true := by
  unfold St.step at hdisp ⊢
  by_cases hdup : a ∈ s.votes
  · simp [hdup] at hdisp
  · have h : s.executed = false ∧ (insert a s.votes).card = success n := by
      simpa [hdup, decide_eq_true_eq] using hdisp
    have hcard : s.votes.card + 1 = success n := by
      have := Finset.card_insert_of_notMem hdup
      omega
    simp [hdup, h.1, hcard]

/-- Two consecutive steps cannot both dispatch. -/
theorem no_double_dispatch_consecutive (n : ℕ) (s : St n)
    (a₁ a₂ : AuthIdx) (ha₁ : a₁ < n) (ha₂ : a₂ < n)
    (h1 : (St.step n s a₁ ha₁).2 = true) :
    (St.step n (St.step n s a₁ ha₁).1 a₂ ha₂).2 = false := by
  have hex := dispatch_sets_executed n s a₁ ha₁ h1
  exact no_redispatch_after_executed n _ a₂ ha₂ hex

/-! ### B3. Dispatch implies quorum -/

theorem dispatch_implies_quorum (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (hdisp : (St.step n s a ha).2 = true) :
    (St.step n s a ha).1.votes.card = success n := by
  unfold St.step at hdisp ⊢
  by_cases hdup : a ∈ s.votes
  · simp [hdup] at hdisp
  · simp only [hdup, ↓reduceIte] at hdisp ⊢
    have h : s.executed = false ∧ (insert a s.votes).card = success n := by
      simpa [decide_eq_true_eq] using hdisp
    simp [h.2]

/-- Under `b ≤ threshold n` byzantine authorities, a dispatched call has
    at least one honest voter (importing Surface A forge-resistance). -/
theorem dispatch_has_honest (n b : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (hdisp : (St.step n s a ha).2 = true)
    (hb : b ≤ threshold n) :
    b < (St.step n s a ha).1.votes.card := by
  have hq := dispatch_implies_quorum n s a ha hdisp
  have hf := forge_resistance n b hb
  omega

/-! ### B4. Negative: force_witness is replayable -/

/-- Governance force-dispatch ignores the executed flag (mirrors documented
    "does not protect against replays"). -/
def forceWitness (n : ℕ) (s : St n) : St n × Bool :=
  ({ s with executed := true }, true)

theorem force_witness_replayable (n : ℕ) (s : St n) :
    (forceWitness n s).2 = true ∧ (forceWitness n s).1.executed = true := by
  simp [forceWitness]

/-- Even after a normal dispatch, force_witness still reports a (second) dispatch. -/
theorem force_witness_after_dispatch (n : ℕ) (s : St n) (a : AuthIdx) (ha : a < n)
    (_hdisp : (St.step n s a ha).2 = true) :
    (forceWitness n (St.step n s a ha).1).2 = true := by
  simp [forceWitness]

end Chainflip.Witnesser
