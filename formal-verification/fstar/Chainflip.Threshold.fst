(*
  Model of Chainflip Byzantine threshold arithmetic.

  Correspondence: utilities/src/lib.rs
    - threshold_from_share_count
    - success_threshold_from_share_count
    - failure_threshold_from_share_count

  Notation (matches the Rust comments and the multisig literature):
    threshold(n)  = max parties *not* enough to succeed  (= floor((2n-1)/3))
    success(n)    = threshold(n) + 1                     (= ceil(2n/3))
    failure(n)    = n - threshold(n)                     (= parties needed to force fail)
*)
module Chainflip.Threshold

/// Maximum number of parties *not* enough to generate a signature / witness.
/// Matches `cf_utilities::threshold_from_share_count`.
let threshold (n:nat) : Tot nat =
  if n = 0 then 0 else (2 * n - 1) / 3

/// Number of parties required for a threshold ceremony / witness vote to *succeed*.
/// Matches `cf_utilities::success_threshold_from_share_count`.
let success (n:nat) : Tot nat = threshold n + 1

/// Number of bad parties required for a ceremony to *fail*.
/// Matches `cf_utilities::failure_threshold_from_share_count`.
let failure (n:nat) : Tot nat = n - threshold n

(* -------------------------------------------------------------------- *)
(* A1. Test vectors — pin the model to the Rust unit test               *)
(*     `check_threshold_calculation` in utilities/src/lib.rs.           *)
(* -------------------------------------------------------------------- *)
let test_vectors (_:unit)
  : Lemma
    (ensures
      threshold 150 = 99 /\
      threshold 100 = 66 /\
      threshold 90  = 59 /\
      threshold 3   = 1  /\
      threshold 4   = 2  /\
      success 150   = 100 /\
      success 100   = 67  /\
      success 90    = 60  /\
      success 3     = 2   /\
      success 4     = 3   /\
      failure 150   = 51  /\
      failure 100   = 34  /\
      failure 90    = 31  /\
      failure 3     = 2   /\
      failure 4     = 2)
  = ()

(* -------------------------------------------------------------------- *)
(* A2. Definitional equalities                                          *)
(* -------------------------------------------------------------------- *)
let succ_eq (n:nat) : Lemma (success n = threshold n + 1) = ()
let fail_eq (n:nat) : Lemma (failure n = n - threshold n) = ()

(* -------------------------------------------------------------------- *)
(* A3. Success is a strict majority; never exceeds n                    *)
(* -------------------------------------------------------------------- *)
let succ_bounds (n:nat{n >= 1})
  : Lemma (ensures success n > n / 2 /\ success n <= n)
  = ()

(* -------------------------------------------------------------------- *)
(* A4. Forge resistance                                                 *)
(*     A coalition of size <= threshold(n) is strictly below success(n) *)
(*     and therefore cannot produce a valid witness / threshold sig.    *)
(* -------------------------------------------------------------------- *)
let forge_resistance (n:nat) (b:nat{b <= threshold n})
  : Lemma (ensures b < success n)
  = ()

let threshold_lt_success (n:nat)
  : Lemma (ensures threshold n < success n)
  = ()

(* -------------------------------------------------------------------- *)
(* A5. No-stall liveness                                                *)
(*     With h = n - b honest parties:                                   *)
(*       h >= success(n)  <=>  b <= failure(n) - 1                      *)
(*     So any adversary of size <= floor((n-1)/3) cannot stall.         *)
(* -------------------------------------------------------------------- *)
let fail_minus_one_eq (n:nat{n >= 1})
  : Lemma (ensures n - success n = failure n - 1)
  = ()

let no_stall (n:nat{n >= 1}) (b:nat{b <= n})
  : Lemma (ensures ((n - b >= success n) <==> (b <= n - success n)))
  = ()

(* -------------------------------------------------------------------- *)
(* A6. Quorum intersection                                              *)
(*     Two success-sized subsets of an n-set intersect in                *)
(*     >= 2*success(n) - n members, and that quantity is >= 1.          *)
(*     Under b < 2*success(n)-n byzantine, the honest overlap is        *)
(*     nonempty — so two successful witnesses on conflicting values     *)
(*     are impossible below the safety bound.                           *)
(* -------------------------------------------------------------------- *)
let quorum_overlap_positive (n:nat{n >= 1})
  : Lemma (ensures 2 * success n - n >= 1)
  = ()

let honest_overlap_positive (n:nat{n >= 1}) (b:nat{b < 2 * success n - n})
  : Lemma (ensures 2 * success n - n - b >= 1)
  = ()

(* -------------------------------------------------------------------- *)
(* A7. Off-by-one guard for the witnesser dispatch condition            *)
(*     witness_at_epoch dispatches when num_votes == success(n).         *)
(*     For a monotone vote count that increments by 1, the first time   *)
(*     the count reaches success(n) is exactly when it equals it — so   *)
(*     the equality check is not an off-by-one relative to >=.          *)
(* -------------------------------------------------------------------- *)
let first_crossing (n:nat{n >= 1}) (k:nat{k > 0})
  : Lemma
    (requires k - 1 < success n /\ k >= success n)
    (ensures k = success n)
  = ()
