/-
  Lean cross-check of Chainflip Byzantine threshold arithmetic.

  Correspondence: `utilities/src/lib.rs`
  Mirror of `formal-verification/fstar/Chainflip.Threshold.fst`.

  The F* development discharges the full arithmetic suite via SMT. This Lean
  module re-states the security-critical facts with Mathlib and proves them
  by a mix of computation (test vectors) and elementary Nat reasoning.
-/
import Mathlib.Tactic

namespace Chainflip.Threshold

/-- Maximum number of parties *not* enough to succeed. -/
def threshold (n : ℕ) : ℕ :=
  if n = 0 then 0 else (2 * n - 1) / 3

/-- Parties required for a witness / threshold-sig ceremony to succeed. -/
def success (n : ℕ) : ℕ := threshold n + 1

/-- Bad parties required to force a ceremony to fail. -/
def failure (n : ℕ) : ℕ := n - threshold n

/-! ### A1. Test vectors (Rust `check_threshold_calculation`) -/

theorem test_vectors :
    threshold 150 = 99 ∧ threshold 100 = 66 ∧ threshold 90 = 59 ∧
    threshold 3 = 1 ∧ threshold 4 = 2 ∧
    success 150 = 100 ∧ success 100 = 67 ∧ success 90 = 60 ∧
    success 3 = 2 ∧ success 4 = 3 ∧
    failure 150 = 51 ∧ failure 100 = 34 ∧ failure 90 = 31 ∧
    failure 3 = 2 ∧ failure 4 = 2 := by
  native_decide

/-! ### A2. Definitional equalities -/

theorem succ_eq (n : ℕ) : success n = threshold n + 1 := rfl

theorem fail_eq (n : ℕ) : failure n = n - threshold n := rfl

/-! ### A4. Forge resistance (sub-threshold coalition cannot reach success) -/

theorem threshold_lt_success (n : ℕ) : threshold n < success n := by
  simp [success]

theorem forge_resistance (n b : ℕ) (hb : b ≤ threshold n) : b < success n := by
  have := threshold_lt_success n
  omega

/-! ### A3. Success bounds for n ≥ 1 -/

private lemma threshold_eq_of_pos (n : ℕ) (hn : 0 < n) :
    threshold n = (2 * n - 1) / 3 := by
  simp [threshold, Nat.ne_of_gt hn]

theorem succ_le (n : ℕ) (hn : 0 < n) : success n ≤ n := by
  have hthr := threshold_eq_of_pos n hn
  simp only [success, hthr]
  -- (2n-1)/3 + 1 ≤ n  ⇔  (2n-1)/3 ≤ n-1
  have hmul : 3 * ((2 * n - 1) / 3) ≤ 2 * n - 1 := Nat.mul_div_le (2 * n - 1) 3
  have hlt : 2 * n - 1 < 3 * ((2 * n - 1) / 3 + 1) :=
    Nat.lt_mul_div_succ (2 * n - 1) (by decide : 0 < (3 : ℕ))
  omega

theorem succ_strict_majority (n : ℕ) (hn : 0 < n) : n / 2 < success n := by
  have hthr := threshold_eq_of_pos n hn
  simp only [success, hthr]
  -- Goal: n/2 < (2n-1)/3 + 1
  have hmul : 3 * ((2 * n - 1) / 3) ≤ 2 * n - 1 := Nat.mul_div_le (2 * n - 1) 3
  have hlt : 2 * n - 1 < 3 * ((2 * n - 1) / 3 + 1) :=
    Nat.lt_mul_div_succ (2 * n - 1) (by decide : 0 < (3 : ℕ))
  have hhalf : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  omega

theorem succ_bounds (n : ℕ) (hn : 0 < n) :
    n / 2 < success n ∧ success n ≤ n :=
  ⟨succ_strict_majority n hn, succ_le n hn⟩

/-! ### A5. No-stall liveness -/

theorem fail_minus_one_eq (n : ℕ) (hn : 0 < n) :
    n - success n = failure n - 1 := by
  have hs := succ_le n hn
  simp [success, failure] at hs ⊢
  omega

theorem no_stall (n b : ℕ) (hn : 0 < n) (_hb : b ≤ n) :
    (n - b ≥ success n) ↔ (b ≤ n - success n) := by
  have hs := succ_le n hn
  constructor <;> intro <;> omega

/-! ### A6. Quorum intersection -/

theorem quorum_overlap_positive (n : ℕ) (hn : 0 < n) :
    1 ≤ 2 * success n - n := by
  have hmaj := succ_strict_majority n hn
  have hle := succ_le n hn
  omega

theorem honest_overlap_positive (n b : ℕ) (hn : 0 < n)
    (hb : b < 2 * success n - n) :
    1 ≤ 2 * success n - n - b := by
  have := quorum_overlap_positive n hn
  omega

/-! ### A7. Off-by-one guard for equality dispatch -/

theorem first_crossing (n k : ℕ) (_hn : 0 < n) (_hk : 0 < k)
    (hprev : k - 1 < success n) (hnow : success n ≤ k) :
    k = success n := by
  omega

end Chainflip.Threshold
