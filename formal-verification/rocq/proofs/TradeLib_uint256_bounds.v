(** TradeLib uint256 upper-bound derivation.

    Mirrors [proofs/IssuancePremium_uint256_bounds.v]. The
    [TradeLib] simulation in [simulations/TradeLib.v] is purely
    functional: the user-facing kernels [buyAmount], [buyAmountPre],
    and [coverDeficitSellAmount] take Z scalars and return Z. The
    natural "uint256 bounds" claim is therefore on the *output* of
    those pure functions.

    Production has uint256 ceilings on every storage word and
    arithmetic by EVM semantics. Here we lift the existing FIX_MAX
    output bounds on [buyAmount] / [buyAmountPre] (already proved in
    [TradeLib.v] via [safeMulDiv_le_fix_max]) to [<= UINT256_MAX].

    [coverDeficitSellAmount] does *not* saturate at FIX_MAX in
    general — its outer [div] kernel does not clamp — so we expose
    only the non-negativity bound for it (already proved in
    [TradeLib_validity.v]) and a joint bound covering the two
    saturating outputs together with the two FIX_MAX-bounded inputs.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.proofs.TradeLib.
Require Import Reserve.proofs.TradeLib_validity.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module TradeLibUint256Bounds.

Import FixLib.
Import Reserve.simulations.TradeLib.TradeLib.
Import Reserve.proofs.TradeLib.TradeLibProofs.
Import TradeLibValidityProofs.

(** ---------- FIX_MAX < UINT256_MAX ---------- *)
Lemma FIX_MAX_le_UINT256_MAX :
  FIX_MAX <= UINT256_MAX.
Proof.
  unfold FIX_MAX, UINT256_MAX.
  vm_compute. discriminate.
Qed.

(** ---------- output bounds: buyAmount ----------

    [buyAmount_le_fix_max] (already proved upstream) gives
    [<= FIX_MAX]. Lifted here to [<= UINT256_MAX]. *)
Lemma buyAmount_le_FIX_MAX (s slippage sellLow buyHigh : Z) :
  buyAmount s slippage sellLow buyHigh <= FIX_MAX.
Proof.
  apply buyAmount_le_fix_max.
Qed.

Lemma buyAmount_le_UINT256_MAX (s slippage sellLow buyHigh : Z) :
  buyAmount s slippage sellLow buyHigh <= UINT256_MAX.
Proof.
  pose proof (buyAmount_le_FIX_MAX s slippage sellLow buyHigh) as Hfm.
  pose proof FIX_MAX_le_UINT256_MAX as Hcap.
  lia.
Qed.

(** ---------- output bounds: buyAmountPre ---------- *)
Lemma buyAmountPre_le_FIX_MAX (s slippage sellLow buyHigh : Z) :
  buyAmountPre s slippage sellLow buyHigh <= FIX_MAX.
Proof.
  apply buyAmountPre_le_fix_max.
Qed.

Lemma buyAmountPre_le_UINT256_MAX (s slippage sellLow buyHigh : Z) :
  buyAmountPre s slippage sellLow buyHigh <= UINT256_MAX.
Proof.
  pose proof (buyAmountPre_le_FIX_MAX s slippage sellLow buyHigh) as Hfm.
  pose proof FIX_MAX_le_UINT256_MAX as Hcap.
  lia.
Qed.

(** ---------- output bounds: coverDeficitSellAmount ----------

    Unlike [buyAmount] / [buyAmountPre], the
    [coverDeficitSellAmount] kernel composes [div ... CEIL] without
    a saturating outer [safeMulDiv], so it does not admit a
    universal [<= FIX_MAX] bound. We expose only the non-negativity
    fact (lifted from [TradeLib_validity]) here, leaving any
    upper-bound work to call-site analyses that have concrete input
    envelopes. *)
Lemma coverDeficitSellAmount_nonneg_lifted
    (b slippage sellLow buyHigh : Z) :
  0 <= b ->
  0 <= slippage < FIX_ONE ->
  0 < sellLow ->
  0 <= buyHigh ->
  0 <= coverDeficitSellAmount b slippage sellLow buyHigh.
Proof.
  apply coverDeficitSellAmount_nonneg.
Qed.

(** ---------- joint bound: buyAmount + buyAmountPre outputs ----------

    Sums the two saturating output kernels. Each is bounded by
    [FIX_MAX < UINT256_MAX], so the sum is at most
    [2 * UINT256_MAX]. *)
Lemma buyAmount_outputs_jointly_bounded
    (s slippage sellLow buyHigh : Z) :
  buyAmount s slippage sellLow buyHigh
  + buyAmountPre s slippage sellLow buyHigh
    <= 2 * UINT256_MAX.
Proof.
  pose proof (buyAmount_le_UINT256_MAX s slippage sellLow buyHigh) as Hba.
  pose proof (buyAmountPre_le_UINT256_MAX s slippage sellLow buyHigh) as Hbp.
  lia.
Qed.

End TradeLibUint256Bounds.
