(** IssuancePremium uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and
    [proofs/Throttle_uint256_bounds.v]. Unlike StRSR/Throttle, the
    [IssuancePremium] simulation in [simulations/IssuancePremium.v] is
    purely functional: there is no storage record, just the kernel
    [safeDiv_ceil] and the user-facing [issuancePremium]. The natural
    "uint256 bounds" claim is therefore on the *output* of those
    pure functions.

    Production has uint256 ceilings on every storage word and
    arithmetic by EVM semantics. Here we show the stronger fact that
    [issuancePremium] is bounded by [FIX_MAX] (a uint192 saturation
    ceiling) — and therefore strictly below [UINT256_MAX]. The
    [safeDiv_ceil] kernel inherits the same envelope.

    [premium_bounded] in [proofs/IssuancePremium.v] already gives the
    [<= FIX_MAX] bound on [issuancePremium]. This file lifts it to
    [<= UINT256_MAX], adds the analogous bound on [safeDiv_ceil], and
    states a joint envelope, in the same shape as the StRSR/Throttle
    bounds files for callers that want a uniform interface.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.
Require Import Reserve.proofs.IssuancePremium.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module IssuancePremiumUint256Bounds.

Import FixLib.
Import Reserve.simulations.IssuancePremium.IssuancePremium.
Import IssuancePremiumProofs.

(** ---------- FIX_MAX < UINT256_MAX ---------- *)
Lemma FIX_MAX_le_UINT256_MAX :
  FIX_MAX <= UINT256_MAX.
Proof.
  unfold FIX_MAX, UINT256_MAX.
  vm_compute. discriminate.
Qed.

(** ---------- output bounds: issuancePremium ----------

    [premium_bounded] (already proved upstream) gives [<= FIX_MAX].
    Lifted here to [<= UINT256_MAX] via [FIX_MAX_le_UINT256_MAX]. *)
Lemma issuancePremium_le_FIX_MAX
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 <= targetPerRef <= FIX_MAX ->
  0 <= pegPrice <= FIX_MAX ->
  issuancePremium enable lastSaveIsNow pegPrice targetPerRef <= FIX_MAX.
Proof.
  intros Ht Hp.
  apply premium_bounded; assumption.
Qed.

Lemma issuancePremium_le_UINT256_MAX
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 <= targetPerRef <= FIX_MAX ->
  0 <= pegPrice <= FIX_MAX ->
  issuancePremium enable lastSaveIsNow pegPrice targetPerRef <= UINT256_MAX.
Proof.
  intros Ht Hp.
  pose proof (issuancePremium_le_FIX_MAX enable lastSaveIsNow
                pegPrice targetPerRef Ht Hp) as Hfm.
  pose proof FIX_MAX_le_UINT256_MAX as Hcap.
  lia.
Qed.

(** ---------- output bounds: safeDiv_ceil ----------

    The CEIL [safeDiv] kernel saturates at [FIX_MAX] in every branch
    that would otherwise exceed it. So under the natural input
    envelope (both arguments in [0, FIX_MAX]) the output is bounded
    by [FIX_MAX], hence by [UINT256_MAX]. *)
Lemma safeDiv_ceil_le_FIX_MAX
    (a b : Z) :
  0 <= a <= FIX_MAX ->
  0 <= b ->
  safeDiv_ceil a b <= FIX_MAX.
Proof.
  intros [Ha_nn Ha_hi] Hb_nn.
  assert (Hzero_le_max : 0 <= FIX_MAX) by (vm_compute; discriminate).
  unfold safeDiv_ceil.
  destruct (a =? 0).
  - exact Hzero_le_max.
  - destruct (a =? FIX_MAX).
    + apply Z.le_refl.
    + destruct (b =? 0).
      * apply Z.le_refl.
      * destruct (FIX_MAX <=? FixLib.div a b RoundingMode.CEIL) eqn:Hsat.
        -- apply Z.le_refl.
        -- apply Z.leb_gt in Hsat. lia.
Qed.

Lemma safeDiv_ceil_le_UINT256_MAX
    (a b : Z) :
  0 <= a <= FIX_MAX ->
  0 <= b ->
  safeDiv_ceil a b <= UINT256_MAX.
Proof.
  intros Ha Hb.
  pose proof (safeDiv_ceil_le_FIX_MAX a b Ha Hb) as Hfm.
  pose proof FIX_MAX_le_UINT256_MAX as Hcap.
  lia.
Qed.

(** ---------- joint bound: input + output envelope ----------

    Sums the two uint192 inputs and the premium output. Each is
    bounded by [FIX_MAX = 2^192 - 1 < UINT256_MAX], so the sum is at
    most [3 * UINT256_MAX]. *)
Lemma issuancePremium_inputs_outputs_jointly_bounded
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 <= targetPerRef <= FIX_MAX ->
  0 <= pegPrice <= FIX_MAX ->
  pegPrice
  + targetPerRef
  + issuancePremium enable lastSaveIsNow pegPrice targetPerRef
    <= 3 * UINT256_MAX.
Proof.
  intros Ht Hp.
  pose proof (issuancePremium_le_UINT256_MAX
                enable lastSaveIsNow pegPrice targetPerRef Ht Hp) as Hout.
  pose proof FIX_MAX_le_UINT256_MAX as Hcap.
  destruct Ht as [_ Ht_hi]. destruct Hp as [_ Hp_hi].
  lia.
Qed.

End IssuancePremiumUint256Bounds.
