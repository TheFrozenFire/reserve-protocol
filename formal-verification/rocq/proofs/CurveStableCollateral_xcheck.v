(** CurveStableCollateral simulation × CAS witness cross-check.

    Evaluates the [CurveStableCollateral] simulation on the same
    inputs used by [cas/collateral/curve_virtual_price_drop.gp] and
    asserts identical outputs. Any divergence between the Rocq
    simulation and the CAS witness corpus fails the build.

    Calibration (matching the CAS script):
      delayUntilDefault = 86400      (24h)
      defaultThreshold  = FIX_ONE/20 (5%)
      targetPerRef      = FIX_ONE
      revenueHiding     = 10^12      (1 ppm)
      revenueShowing    = FIX_ONE - revenueHiding
      t0                = 1700000000

    Probes (all reflect cas/collateral/curve_virtual_price_drop.gp):
      CV-1  identity refPerTok (underlyingRefPerTok = vp)
      CV-2  small drop within revenue-hiding band: no default
      CV-3  vp < exposed: hard default with exposed = vp
      CV-7  revenue-hiding band IS the hard-default threshold *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CurveStableCollateral.

Module CurveStableCollateralXCheck.

Import FixLib.

(** Calibration *)
Definition cal_dud : Z := 86400.
Definition cal_t0 : Z := 1700000000.
Definition cal_revHiding : Z := 10 ^ 12.
Definition cal_revShowing : Z := FIX_ONE - cal_revHiding.

(** ===== CV-1: refPerTok = vp identity ===== *)
Lemma xcheck_cv1_identity :
  CurveStableCollateral.underlyingRefPerTok (FIX_ONE * 102 / 100)
  = FIX_ONE * 102 / 100.
Proof. vm_compute. reflexivity. Qed.

(** ===== CV-2: small drop within revenue-hiding band -> no default =====
    Establish exposed = 2*FIX_ONE * revShowing first. Then a 1-wei drop
    in vp_high keeps vp >= exposed -> updateExposed flag is false. *)
Definition cv2_exposed : Z :=
  fst (Collateral.updateExposed 0 (2 * FIX_ONE) cal_revShowing).

Lemma xcheck_cv2_first_climb :
  cv2_exposed = (2 * FIX_ONE * cal_revShowing) / FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_cv2_within_band_no_default :
  snd (Collateral.updateExposed cv2_exposed (2 * FIX_ONE - 1)
         cal_revShowing) = false.
Proof. vm_compute. reflexivity. Qed.

(** ===== CV-3: vp < exposed -> hard default, exposed = vp ===== *)
Lemma xcheck_cv3_hard_default :
  Collateral.updateExposed FIX_ONE (FIX_ONE - 1) cal_revShowing
  = (FIX_ONE - 1, true).
Proof. vm_compute. reflexivity. Qed.

(** ===== CV-7: revenue-hiding band = hard-default threshold =====
    boundary_drop = vp_high * revHiding / FIX_ONE
    vp at boundary = vp_high - boundary_drop = exposed.
    A 1-wei extra drop crosses to vp < exposed. *)
Definition cv7_vp_high : Z := 2 * FIX_ONE.
Definition cv7_exposed : Z := (cv7_vp_high * cal_revShowing) / FIX_ONE.
Definition cv7_boundary_drop : Z := (cv7_vp_high * cal_revHiding) / FIX_ONE.
Definition cv7_vp_at : Z := cv7_vp_high - cv7_boundary_drop.

Lemma xcheck_cv7_vp_at_boundary_equals_exposed :
  cv7_vp_at = cv7_exposed.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_cv7_at_boundary_no_default :
  snd (Collateral.updateExposed cv7_exposed cv7_vp_at cal_revShowing)
  = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_cv7_below_boundary_default :
  snd (Collateral.updateExposed cv7_exposed (cv7_vp_at - 1) cal_revShowing)
  = true.
Proof. vm_compute. reflexivity. Qed.

End CurveStableCollateralXCheck.
