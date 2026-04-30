(** IssuancePremium validity preservation.

    Small validity-preservation lemmas for [IssuancePremium]:

      safeDiv_ceil_nonneg:
        The CEIL [safeDiv] kernel returns a non-negative integer
        whenever both inputs are non-negative.

      issuancePremium_nonneg:
        The premium output is always non-negative — combines the
        FIX_ONE fall-back arms with [safeDiv_ceil_nonneg].

      issuancePremium_ge_FIX_ONE_when_below_peg:
        On the active branch (pegPrice < targetPerRef, both non-zero
        and feature flags on), the premium is at least [FIX_ONE].
        Direct corollary of [premium_at_least_one].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.
Require Import Reserve.proofs.IssuancePremium.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module IssuancePremiumValidity.

Import FixLib.
Import Reserve.simulations.IssuancePremium.IssuancePremium.
Import IssuancePremiumProofs.

(** ===== safeDiv_ceil is non-negative under non-negative inputs. =====
    Each branch lands on either 0, FIX_MAX, or a CEIL-divide of two
    non-negative values, all of which are >= 0. *)
Lemma safeDiv_ceil_nonneg
    (a b : Z) :
  0 <= a ->
  0 <= b ->
  0 <= safeDiv_ceil a b.
Proof.
  intros Ha Hb.
  assert (Hmax_nn : 0 <= FIX_MAX) by (vm_compute; discriminate).
  unfold safeDiv_ceil.
  destruct (a =? 0).
  - apply Z.le_refl.
  - destruct (a =? FIX_MAX).
    + exact Hmax_nn.
    + destruct (b =? 0) eqn:Hb0.
      * exact Hmax_nn.
      * apply Z.eqb_neq in Hb0.
        destruct (FIX_MAX <=?
                    FixLib.div a b RoundingMode.CEIL) eqn:Hsat.
        -- exact Hmax_nn.
        -- (* div a b CEIL = divrnd (a*FIX_SCALE) b CEIL *)
           unfold FixLib.div, divrnd.
           assert (Hb_pos : 0 < b) by lia.
           assert (Hnum_nn : 0 <= a * FIX_SCALE)
             by (apply Z.mul_nonneg_nonneg; [lia | unfold FIX_SCALE; lia]).
           destruct (a * FIX_SCALE mod b =? 0).
           ++ apply Z.div_pos; lia.
           ++ assert (0 <= a * FIX_SCALE / b)
                by (apply Z.div_pos; lia).
              lia.
Qed.

(** ===== issuancePremium is always non-negative. =====
    Combines the FIX_ONE fall-back arms (FIX_ONE > 0) with
    [safeDiv_ceil_nonneg] on the active branch. *)
Lemma issuancePremium_nonneg
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 <= pegPrice ->
  0 <= targetPerRef ->
  0 <= issuancePremium enable lastSaveIsNow pegPrice targetPerRef.
Proof.
  intros Hp Ht.
  assert (Hone_nn : 0 <= FIX_ONE) by (vm_compute; discriminate).
  unfold issuancePremium.
  destruct enable; cbn [negb].
  2: { exact Hone_nn. }
  destruct lastSaveIsNow; cbn [negb].
  2: { exact Hone_nn. }
  destruct (pegPrice =? 0).
  - exact Hone_nn.
  - destruct (targetPerRef <=? pegPrice).
    + exact Hone_nn.
    + apply safeDiv_ceil_nonneg; assumption.
Qed.

(** ===== On the active branch, premium >= FIX_ONE. =====
    Direct corollary of [premium_at_least_one]; specialised to the
    "below-peg" case where pegPrice < targetPerRef. *)
Lemma issuancePremium_ge_FIX_ONE_when_below_peg
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 < targetPerRef ->
  0 <= pegPrice ->
  FIX_ONE <= issuancePremium enable lastSaveIsNow pegPrice targetPerRef.
Proof.
  intros HtPos HpNN.
  apply premium_at_least_one; assumption.
Qed.

End IssuancePremiumValidity.
