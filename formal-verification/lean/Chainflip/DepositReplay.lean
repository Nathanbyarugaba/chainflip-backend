/-
  Model of per-chain deposit identity and credit idempotence.

  Correspondence:
    - `state-chain/chains/src/btc.rs` — `Utxo` DepositDetails
    - `state-chain/pallets/cf-ingress-egress/src/lib.rs`
        `BoostedVaultTransactions`, deposit processing

  A deposit identity is credited at most once. Distinct identities credit
  independently. Boosted and normal paths share the same dedup key.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Chainflip.DepositReplay

/-- Abstract deposit identity. For Bitcoin this is `(tx_id, vout)` at the UTXO
    layer; the witnessed call (and therefore the witnesser call-hash) binds the
    full deposit details. -/
structure DepositId where
  txId : ℕ
  vout : ℕ
  deriving DecidableEq

/-- Credit ledger: set of credited deposit ids + total credited units. -/
structure Ledger where
  credited : Finset DepositId
  balance : ℕ

namespace Ledger

def empty : Ledger := ⟨∅, 0⟩

/-- Credit `amount` against `id`. No-op if already credited (idempotent). -/
def credit (L : Ledger) (id : DepositId) (amount : ℕ) : Ledger :=
  if id ∈ L.credited then L
  else { credited := insert id L.credited, balance := L.balance + amount }

end Ledger

/-! ### C1. Credit is idempotent -/

theorem credit_idempotent (L : Ledger) (id : DepositId) (amount : ℕ) :
    (L.credit id amount).credit id amount = L.credit id amount := by
  unfold Ledger.credit
  by_cases h : id ∈ L.credited
  · simp [h]
  · simp [h]

theorem credit_idempotent_balance (L : Ledger) (id : DepositId) (amount : ℕ) :
    ((L.credit id amount).credit id amount).balance = (L.credit id amount).balance := by
  rw [credit_idempotent]

/-! ### C2. Distinct ids are independent -/

theorem distinct_ids_balance (L : Ledger) (id₁ id₂ : DepositId)
    (hne : id₁ ≠ id₂) (a₁ a₂ : ℕ)
    (h1 : id₁ ∉ L.credited) (h2 : id₂ ∉ L.credited) :
    ((L.credit id₁ a₁).credit id₂ a₂).balance = L.balance + a₁ + a₂ := by
  have h1' : id₁ ∉ L.credited := h1
  have h2' : id₂ ∉ insert id₁ L.credited := by
    intro hin
    simp [Finset.mem_insert] at hin
    rcases hin with rfl | hin
    · exact hne rfl
    · exact h2 hin
  simp only [Ledger.credit, h1', ↓reduceIte, h2']

/-! ### C3. Boost vs normal path share the dedup key -/

inductive Path | boost | normal
  deriving DecidableEq

/-- Combined ledger: both paths share the same dedup set. -/
def creditPath (L : Ledger) (_p : Path) (id : DepositId) (amount : ℕ) : Ledger :=
  L.credit id amount

theorem boost_vs_normal_exclusive (L : Ledger) (id : DepositId) (a b : ℕ)
    (hfresh : id ∉ L.credited) :
    (creditPath (creditPath L .boost id a) .normal id b).balance =
      L.balance + a := by
  simp [creditPath, Ledger.credit, hfresh]

end Chainflip.DepositReplay
