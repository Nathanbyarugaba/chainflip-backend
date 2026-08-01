(*
  Model of Chainflip amount casting and Bitcoin output summation.

  Correspondence:
    - state-chain/chains/src/lib.rs
        Chain::ChainAmount : Into<AssetAmount> + TryFrom<AssetAmount>
        AssetAmount = u128
    - state-chain/chains/src/btc/api.rs
        total_output_amount: u64  with  += transfer_param.amount   (CF-SEC-013)
    - state-chain/primitives/src/chains/assets.rs
        Asset::decimals() per asset

  Properties:
    - Widening to a larger bound is lossless and round-trips through narrowing.
    - Narrowing fails closed (never truncates).
    - Same-decimal rescale is identity; scale-up is injective.
    - Checked BTC output sum never wraps; naive += can wrap (counterexample).
*)
module Chainflip.Amounts

/// Bound of a w-bit unsigned integer, given as 2^w.
/// We keep the exponent explicit so SMT does not need pow2-monotonicity lemmas.
let bound_bits (w:nat) : Tot pos = pow2 w

let max_u128 : nat = pow2 128 - 1
let max_u64  : nat = pow2 64  - 1

/// Widening cast: identity on naturals. Models `Into<AssetAmount>`.
let widen (x:nat) : Tot nat = x

/// Narrowing cast into values strictly below `hi` (e.g. hi = 2^w).
/// Fails closed when the value does not fit — never truncates.
let narrow (hi:pos) (a:nat) : Tot (option (x:nat{x < hi})) =
  if a < hi then Some a else None

(* -------------------------------------------------------------------- *)
(* E1. Widen / narrow round-trip (lossless up-cast)                     *)
(* -------------------------------------------------------------------- *)
let widen_narrow_roundtrip (hi:pos) (x:nat{x < hi})
  : Lemma (ensures narrow hi (widen x) == Some x)
  = ()

(* -------------------------------------------------------------------- *)
(* E2. Narrow never truncates                                           *)
(* -------------------------------------------------------------------- *)
let narrow_no_truncation (hi:pos) (a:nat)
  : Lemma
    (ensures
      (match narrow hi a with
       | Some y -> y = a
       | None   -> a >= hi))
  = ()

let narrow_fails_closed (hi:pos) (a:nat{a >= hi})
  : Lemma (ensures narrow hi a == None)
  = ()

(* -------------------------------------------------------------------- *)
(* E3. Decimal rescale                                                  *)
(*     Amounts on the state chain are already in AssetAmount (u128)     *)
(*     units; per-asset decimals annotate scale for pricing, not for a  *)
(*     silent cast between vault-credit units. Same-decimal rescale is  *)
(*     the identity. Scale-up is injective.                             *)
(* -------------------------------------------------------------------- *)
let rec pow10 (k:nat) : Tot pos =
  if k = 0 then 1 else 10 * pow10 (k - 1)

let rescale (a:nat) (d_src d_dst:nat) : Tot nat =
  if d_src = d_dst then a
  else if d_dst > d_src then a * pow10 (d_dst - d_src)
  else a / pow10 (d_src - d_dst)

let rescale_same_decimals (a:nat) (d:nat)
  : Lemma (ensures rescale a d d = a)
  = ()

let rescale_scale_up_injective (a b:nat) (d_src:nat) (delta:pos)
  : Lemma
    (requires rescale a d_src (d_src + delta) = rescale b d_src (d_src + delta))
    (ensures a = b)
  = ()

(* -------------------------------------------------------------------- *)
(* E4. Bitcoin output summation (CF-SEC-013)                            *)
(* -------------------------------------------------------------------- *)

/// Checked addition on the u64 domain. Models the recommended fix.
let checked_add_u64 (x:nat{x <= max_u64}) (y:nat{y <= max_u64})
  : Tot (option (z:nat{z <= max_u64}))
  = if x + y <= max_u64 then Some (x + y) else None

/// Naive wrapping addition (current buggy pattern: `total += amount` on u64).
let wrapping_add_u64 (x:nat{x <= max_u64}) (y:nat{y <= max_u64})
  : Tot (z:nat{z <= max_u64})
  = (x + y) % (pow2 64)

let checked_add_sound (x:nat{x <= max_u64}) (y:nat{y <= max_u64})
  : Lemma
    (ensures
      (match checked_add_u64 x y with
       | Some z -> z = x + y /\ z <= max_u64
       | None   -> x + y > max_u64))
  = ()

/// Checked fold: None on any overflow; Some total = exact integer sum otherwise.
let rec checked_sum (xs:list (x:nat{x <= max_u64}))
  : Tot (option (z:nat{z <= max_u64}))
    (decreases xs)
  = match xs with
    | [] -> Some 0
    | h :: t ->
      (match checked_sum t with
       | None -> None
       | Some s -> checked_add_u64 h s)

let rec list_sum (xs:list (x:nat{x <= max_u64})) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | h :: t -> h + list_sum t

let rec checked_sum_correct (xs:list (x:nat{x <= max_u64}))
  : Lemma
    (ensures
      (match checked_sum xs with
       | Some z -> z = list_sum xs
       | None   -> list_sum xs > max_u64))
    (decreases xs)
  = match xs with
    | [] -> ()
    | h :: t ->
      checked_sum_correct t;
      ()

/// Counterexample for CF-SEC-013: wrapping addition disagrees with the
/// integer sum, while checked addition fails closed.
let wrapping_can_disagree (_:unit)
  : Lemma
    (ensures
      wrapping_add_u64 max_u64 1 = 0 /\
      max_u64 + 1 = pow2 64 /\
      checked_add_u64 max_u64 1 == None)
  = ()
