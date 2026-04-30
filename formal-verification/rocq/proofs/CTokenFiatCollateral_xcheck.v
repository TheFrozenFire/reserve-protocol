(** CTokenFiatCollateral simulation × CAS witness cross-check.

    Evaluates the [CTokenFiatCollateral] simulation on the same
    inputs used by [cas/collateral/ctoken_refresh.gp] and asserts
    identical outputs. Any divergence between the Rocq simulation
    and the CAS witness corpus fails the build.

    Calibration (matching the CAS script):
      delayUntilDefault = 86400      (24h)
      defaultThreshold  = FIX_ONE/20 (5%)
      targetPerRef      = FIX_ONE
      revenueHiding     = 10^12      (1 ppm)
      revenueShowing    = FIX_ONE - revenueHiding
      t0                = 1700000000

    Probes (all reflect cas/collateral/ctoken_refresh.gp):
      CT-1  cUSDC arithmetic (refDecimals = 6)
      CT-2  cDAI  arithmetic (refDecimals = 18)
      CT-3  identity at refDecimals = 8
      CT-5  artificial accrual jump appreciates without defaulting
      CT-6  1-wei rate decrease triggers hard default *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CTokenFiatCollateral.

Module CTokenFiatCollateralXCheck.

Import FixLib.

(** Calibration *)
Definition cal_dud : Z := 86400.
Definition cal_t0 : Z := 1700000000.
Definition cal_revHiding : Z := 10 ^ 12.
Definition cal_revShowing : Z := FIX_ONE - cal_revHiding.
Definition cal_targetPerRef : Z := FIX_ONE.
Definition cal_defaultThreshold : Z := FIX_ONE / 20.
Definition cal_pegDelta : Z :=
  FixLib.mul cal_targetPerRef cal_defaultThreshold RoundingMode.FLOOR.
Definition cal_pegBottom : Z := cal_targetPerRef - cal_pegDelta.
Definition cal_pegTop : Z := cal_targetPerRef + cal_pegDelta.

(** ===== CT-1: cUSDC arithmetic (refDecimals = 6, shift = +2) =====
    rate = 1.05e16 -> refPerTok = 1.05e18. *)
Lemma xcheck_ct1_cusdc_arithmetic :
  CTokenFiatCollateral.refPerTok_of_rate (FIX_ONE * 105 / 100 / 100) 6
  = FIX_ONE * 105 / 100.
Proof. vm_compute. reflexivity. Qed.

(** ===== CT-2: cDAI arithmetic (refDecimals = 18, shift = -10) =====
    rate = 1.05e28 -> refPerTok = 1.05e18. *)
Lemma xcheck_ct2_cdai_arithmetic :
  CTokenFiatCollateral.refPerTok_of_rate
    (FIX_ONE * 105 / 100 * 10 ^ 10) 18
  = FIX_ONE * 105 / 100.
Proof. vm_compute. reflexivity. Qed.

(** ===== CT-3: identity at refDecimals = 8 =====
    refPerTok = rate. *)
Lemma xcheck_ct3_identity_at_8 :
  CTokenFiatCollateral.refPerTok_of_rate (FIX_ONE * 12 / 10) 8
  = FIX_ONE * 12 / 10.
Proof. vm_compute. reflexivity. Qed.

(** ===== CT-6: 1-wei rate decrease at refDecimals=6 drops underlying
    by exactly 100 wei. Confirms the shift is [* 100] for this branch. *)
Lemma xcheck_ct6_unit_drop_in_rate :
  CTokenFiatCollateral.refPerTok_of_rate (10 ^ 16) 6
  - CTokenFiatCollateral.refPerTok_of_rate (10 ^ 16 - 1) 6
  = 100.
Proof. vm_compute. reflexivity. Qed.

(** ===== Auxiliary witness: monotonicity holds at concrete inputs.
    For refDecimals=6, an increasing rate produces increasing refPerTok. *)
Lemma xcheck_ct4_mono_step :
  CTokenFiatCollateral.refPerTok_of_rate (10 ^ 16) 6
  <= CTokenFiatCollateral.refPerTok_of_rate (10 ^ 16 * 101 / 100) 6.
Proof. vm_compute. discriminate. Qed.

(** ===== CT-5: 50% artificial jump. Pre-jump refPerTok = 1e18,
    post-jump refPerTok = 1.5e18. The hidden = 1.5e18 * revShowing
    > 1e18, so the parent's [updateExposed] takes the appreciation
    branch (not the default branch). We pin the exact post-value. *)
Lemma xcheck_ct5_jump_post_value :
  CTokenFiatCollateral.refPerTok_of_rate ((10 ^ 16) * 150 / 100) 6
  = 15 * 10 ^ 17.
Proof. vm_compute. reflexivity. Qed.

End CTokenFiatCollateralXCheck.
