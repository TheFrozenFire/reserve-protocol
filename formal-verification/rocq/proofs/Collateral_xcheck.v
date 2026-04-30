(** Collateral simulation × CAS witness cross-check.

    Evaluates the [Collateral] simulation on the same calibration inputs
    used by [cas/collateral/status_state_machine.gp] and
    [cas/collateral/ref_per_tok_monotonicity.gp] and asserts identical
    outputs. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build.

    Calibration (matching the CAS scripts):
      delayUntilDefault = 86400      (24h)
      defaultThreshold  = FIX_ONE/20 (5%)
      targetPerRef      = FIX_ONE
      revenueHiding     = 10^12      (1 ppm)
      revenueShowing    = FIX_ONE - revenueHiding
      t0                = 1700000000
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.

Module CollateralXCheck.

Import FixLib.
Import Collateral.

Definition cal_dud         : Z := 86400.
Definition cal_t0          : Z := 1700000000.
Definition cal_revHiding   : Z := 10 ^ 12.
Definition cal_revShowing  : Z := FIX_ONE - cal_revHiding.

(** ===== SM-1 boundary: now == _whenDefault flips to DISABLED. ===== *)
Definition sm1_wd : Z := cal_t0 + cal_dud.

Lemma xcheck_sm1_before :
  Status.to_Z (statusOf sm1_wd (sm1_wd - 1)) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm1_at :
  Status.to_Z (statusOf sm1_wd sm1_wd) = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm1_after :
  Status.to_Z (statusOf sm1_wd (sm1_wd + 1)) = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== SM-2 terminal: markStatus(SOUND/IFFY) after DISABLED is no-op. ===== *)
Definition sm2_wd_disabled : Z :=
  markStatus NEVER Status.DISABLED cal_t0 cal_dud.

Lemma xcheck_sm2_disabled :
  sm2_wd_disabled = cal_t0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm2_try_sound :
  markStatus sm2_wd_disabled Status.SOUND (cal_t0 + 1) cal_dud
  = sm2_wd_disabled.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm2_try_iffy :
  markStatus sm2_wd_disabled Status.IFFY (cal_t0 + 1) cal_dud
  = sm2_wd_disabled.
Proof. vm_compute. reflexivity. Qed.

(** ===== SM-3: markStatus(IFFY) deadline cannot be extended. ===== *)
Definition sm3_wd_a : Z :=
  markStatus NEVER Status.IFFY cal_t0 cal_dud.

Lemma xcheck_sm3_iffy_a :
  sm3_wd_a = cal_t0 + cal_dud.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm3_iffy_b_unchanged :
  markStatus sm3_wd_a Status.IFFY (cal_t0 + 100) cal_dud = sm3_wd_a.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm3_iffy_c_earlier :
  markStatus sm3_wd_a Status.IFFY (cal_t0 - 100) cal_dud
  = (cal_t0 - 100) + cal_dud.
Proof. vm_compute. reflexivity. Qed.

(** ===== SM-9: soft default elapses at t0 + dud. ===== *)
Lemma xcheck_sm9_just_before :
  Status.to_Z (statusOf sm3_wd_a (cal_t0 + cal_dud - 1)) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm9_at_deadline :
  Status.to_Z (statusOf sm3_wd_a (cal_t0 + cal_dud)) = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_sm9_after :
  Status.to_Z (statusOf sm3_wd_a (cal_t0 + cal_dud + 1)) = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== M-2: hard default lowers exposed and flags DISABLED. =====
    exposed_pre = FIX_ONE = 10^18; underlying = FIX_ONE - 10^15.
    Expected: (underlying, true). *)
Lemma xcheck_m2_hard_default :
  updateExposed FIX_ONE (FIX_ONE - 10^15) cal_revShowing
  = (FIX_ONE - 10^15, true).
Proof. vm_compute. reflexivity. Qed.

(** ===== M-4: first refresh from exposed = 0 always appreciates. =====
    exposed = 0, underlying = FIX_ONE.
    hidden = (FIX_ONE * revShowing) / FIX_ONE = revShowing = FIX_ONE - 10^12.
    Expected: (revShowing, false). *)
Lemma xcheck_m4_first_refresh :
  updateExposed 0 FIX_ONE cal_revShowing = (cal_revShowing, false).
Proof. vm_compute. reflexivity. Qed.

(** ===== M-6: 1-wei drop below exposed triggers hard default. =====
    exposed = FIX_ONE; underlying = FIX_ONE - 1.
    Expected: (FIX_ONE - 1, true). *)
Lemma xcheck_m6_minimal_default :
  updateExposed FIX_ONE (FIX_ONE - 1) cal_revShowing
  = (FIX_ONE - 1, true).
Proof. vm_compute. reflexivity. Qed.

(** ===== M-3: drawdown within revenue-hiding band: no default,
    no exposed change. =====
    Climb to u_high = 2 * FIX_ONE first; that sets exposed to
    (u_high * revShowing) / FIX_ONE = 2*revShowing.
    Then a 0.5 ppm dip stays above exposed -> no default. *)
Definition m3_exposed_after_climb : Z :=
  fst (updateExposed 0 (2 * FIX_ONE) cal_revShowing).

Lemma xcheck_m3_climb :
  m3_exposed_after_climb = 2 * cal_revShowing.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_m3_dip_no_default :
  let u_high := 2 * FIX_ONE in
  let u_dip := u_high - (u_high / 2000000) in
  snd (updateExposed m3_exposed_after_climb u_dip cal_revShowing) = false.
Proof. vm_compute. reflexivity. Qed.

(** ===== Sanity: NEVER + MAX_DUD overflow guard pins to NEVER. =====
    From SM-9 sanity: mark(NEVER, IFFY, NEVER-1, MAX_DUD) = NEVER. *)
Lemma xcheck_overflow_pins_to_never :
  markStatus NEVER Status.IFFY (NEVER - 1) 1209600 = NEVER.
Proof. vm_compute. reflexivity. Qed.

End CollateralXCheck.
