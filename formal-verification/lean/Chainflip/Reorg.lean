/-
  Model of reorg safety and hash-binding for deposit witnessing.

  Correspondence:
    - engine block witnesser / elections (`EngineElectionType::BlockHeight`)
    - audits CF-SEC-017 (height-only votes), CF-SEC-018 (ByHash without hash check)
    - confirmation depth / safe-height tracking

  Properties:
    D1. Credits at `height ≤ tip - confirmationDepth` lie strictly below any
        reorg of depth `d < confirmationDepth` (preserved-prefix bound).
    D2. (negative) Height-only votes admit two distinct blocks at the same height.
        Hash-bound votes do not.
-/
import Mathlib.Tactic

namespace Chainflip.Reorg

/-- An external-chain block, identified by height and hash. -/
structure Block where
  height : ℕ
  hash : ℕ
  deriving DecidableEq

/-- Safe height under confirmation depth. -/
def safeHeight (tip confirmationDepth : ℕ) : ℕ :=
  tip - confirmationDepth

/-- A deposit is credit-safe when its height is at most the safe height. -/
def isCreditSafe (tip confirmationDepth depositHeight : ℕ) : Prop :=
  depositHeight ≤ safeHeight tip confirmationDepth

/-! ### D1. Safe credits sit in the preserved prefix of shallow reorgs -/

/-- Equal-length reorg of depth `d` leaves the tip height unchanged (when `d ≤ tip`). -/
theorem tip_unchanged_by_equal_length_reorg (tip d : ℕ) (hd : d ≤ tip) :
    tip - d + d = tip := by
  omega

/-- Heights at or below `tip - confirmationDepth` are strictly below `tip - d`
    whenever `d < confirmationDepth` (and `confirmationDepth ≤ tip`).
    Therefore a depth-`d` reorg cannot replace a credit-safe block. -/
theorem preserved_prefix_bound
    (tip confirmationDepth depositHeight d : ℕ)
    (hconf : confirmationDepth ≤ tip)
    (hdepth : d < confirmationDepth)
    (hsafe : isCreditSafe tip confirmationDepth depositHeight) :
    depositHeight < tip - d := by
  simp only [isCreditSafe, safeHeight] at hsafe
  omega

/-- Credit-safety itself is preserved when tip height is unchanged. -/
theorem credit_safe_preserved
    (tip tip' confirmationDepth depositHeight : ℕ)
    (htip : tip' = tip)
    (hsafe : isCreditSafe tip confirmationDepth depositHeight) :
    isCreditSafe tip' confirmationDepth depositHeight := by
  simpa [isCreditSafe, safeHeight, htip] using hsafe

/-- Combined D1: after an equal-length reorg of depth `d < confirmationDepth`,
    a previously credit-safe deposit height remains credit-safe and lies in the
    preserved prefix. -/
theorem safe_credit_survives_reorg
    (tip confirmationDepth depositHeight d : ℕ)
    (hconf : confirmationDepth ≤ tip)
    (_hd : d ≤ tip)
    (hdepth : d < confirmationDepth)
    (hsafe : isCreditSafe tip confirmationDepth depositHeight) :
    isCreditSafe tip confirmationDepth depositHeight ∧
      depositHeight < tip - d := by
  exact ⟨hsafe, preserved_prefix_bound tip confirmationDepth depositHeight d hconf hdepth hsafe⟩

/-! ### D2. Hash binding necessity (negative for height-only) -/

/-- Height-only admissibility: any block at the elected height is accepted. -/
def heightOnlyAdmissible (electedHeight : ℕ) (b : Block) : Prop :=
  b.height = electedHeight

/-- Hash-bound admissibility: block must match the elected (height, hash). -/
def hashBoundAdmissible (elected : Block) (b : Block) : Prop :=
  b = elected

theorem height_only_ambiguous (h : ℕ) :
    ∃ b₁ b₂ : Block, b₁ ≠ b₂ ∧
      heightOnlyAdmissible h b₁ ∧ heightOnlyAdmissible h b₂ := by
  refine ⟨⟨h, 0⟩, ⟨h, 1⟩, ?_, rfl, rfl⟩
  intro heq
  have : (0 : ℕ) = 1 := congrArg Block.hash heq
  exact absurd this (by decide)

theorem hash_bound_unique (elected b₁ b₂ : Block)
    (h1 : hashBoundAdmissible elected b₁)
    (h2 : hashBoundAdmissible elected b₂) :
    b₁ = b₂ := by
  simp only [hashBoundAdmissible] at h1 h2
  exact h1.trans h2.symm

end Chainflip.Reorg
