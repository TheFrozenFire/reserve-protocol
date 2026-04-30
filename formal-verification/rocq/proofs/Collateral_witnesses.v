(** Collateral additional pinned witnesses.

    The CAS scripts
      cas/collateral/status_state_machine.gp
      cas/collateral/ref_per_tok_monotonicity.gp
    probe the FiatCollateral / AppreciatingFiatCollateral state machine
    and the [refPerTok] monotonicity envelope. This file pins concrete
    numerical witnesses as Rocq theorems, closed by [vm_compute].

    [proofs/Collateral_xcheck.v] already pins witnesses for SM-1..SM-3,
    SM-9, M-2..M-4, M-6, and the NEVER overflow guard. This file adds
    NEW witnesses not covered there:

      W1  SM-4: IFFY -> SOUND clears the deadline (recovery path).
      W2  SM-4: post-recovery [statusOf] reads SOUND.
      W3  SM-5: markStatus(DISABLED) flips status this block.
      W4  SM-6: pegPrice exactly at pegBottom -> SOUND (boundary inclusive).
      W5  SM-6: pegPrice exactly at pegTop -> SOUND (boundary inclusive).
      W6  SM-6: pegPrice = pegBottom - 1 -> IFFY (strict comparison).
      W7  SM-6: low = 0 inside band -> IFFY (unpriced low).
      W8  SM-7: soft default produces IFFY this block, never DISABLED.
      W9  SM-8: soft-default cure cycle restores SOUND before deadline.
      W10 M-1: refPerTok non-decreasing across two consecutive sound updates.
      W11 M-5: hidden == exposed boundary does not appreciate (strict >).
      W12 Refresh at exactly t0 + delayUntilDefault on a soft-default'd
          state: status flips to DISABLED.
      W13 Hard default via [refresh] sets exposed to underlying and
          DISABLES whenDefault on the same step.
      W14 Soft default via [refresh] (peg out of band) leaves exposed
          unchanged but moves whenDefault forward.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.

Module CollateralWitnesses.

Import FixLib.
Import Collateral.

(** Calibration matching the CAS scripts. *)
Definition cal_dud         : Z := 86400.
Definition cal_t0          : Z := 1700000000.
Definition cal_revHiding   : Z := 10 ^ 12.
Definition cal_revShowing  : Z := FIX_ONE - cal_revHiding.
Definition cal_targetPerRef : Z := FIX_ONE.
Definition cal_defaultThreshold : Z := FIX_ONE / 20.    (* 5% *)
Definition cal_pegDelta : Z :=
  FixLib.mul cal_targetPerRef cal_defaultThreshold RoundingMode.FLOOR.
Definition cal_pegBottom : Z := cal_targetPerRef - cal_pegDelta.
Definition cal_pegTop    : Z := cal_targetPerRef + cal_pegDelta.

(** ===== W1: SM-4 — IFFY -> SOUND clears deadline. =====
    First mark IFFY at t0 (sets _whenDefault = t0 + dud). Then mark SOUND
    at t0 + 1. The recovery path resets _whenDefault to NEVER. *)
Definition w1_wd_iffy : Z :=
  markStatus NEVER Status.IFFY cal_t0 cal_dud.

Lemma w1_recovery_clears_deadline :
  markStatus w1_wd_iffy Status.SOUND (cal_t0 + 1) cal_dud = NEVER.
Proof. vm_compute. reflexivity. Qed.

(** ===== W2: SM-4 — post-recovery [statusOf] reads SOUND. ===== *)
Lemma w2_recovery_status_is_sound :
  Status.to_Z
    (statusOf
       (markStatus w1_wd_iffy Status.SOUND (cal_t0 + 1) cal_dud)
       (cal_t0 + 2)) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== W3: SM-5 — markStatus(DISABLED) flips status this block. ===== *)
Definition w3_wd_hard : Z :=
  markStatus NEVER Status.DISABLED cal_t0 cal_dud.

Lemma w3_hard_default_status_now :
  Status.to_Z (statusOf w3_wd_hard cal_t0) = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== W4: SM-6 — pegPrice == pegBottom yields SOUND (inclusive). ===== *)
Lemma w4_peg_at_bottom_is_sound :
  Status.to_Z
    (softDefaultStatus cal_pegBottom (FIX_ONE / 2)
       cal_pegBottom cal_pegTop) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== W5: SM-6 — pegPrice == pegTop yields SOUND (inclusive). ===== *)
Lemma w5_peg_at_top_is_sound :
  Status.to_Z
    (softDefaultStatus cal_pegTop (FIX_ONE / 2)
       cal_pegBottom cal_pegTop) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== W6: SM-6 — pegBottom - 1 yields IFFY (strict comparison). ===== *)
Lemma w6_peg_below_strict_is_iffy :
  Status.to_Z
    (softDefaultStatus (cal_pegBottom - 1) (FIX_ONE / 2)
       cal_pegBottom cal_pegTop) = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== W7: SM-6 — low = 0 within band still yields IFFY. ===== *)
Lemma w7_low_zero_in_band_is_iffy :
  Status.to_Z
    (softDefaultStatus cal_targetPerRef 0
       cal_pegBottom cal_pegTop) = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== W8: SM-7 — soft default never skips IFFY.
    Starting from SOUND (whenDefault = NEVER), a soft-default decision
    produces _whenDefault = t0 + dud > t0, i.e. status() at t0 = IFFY,
    never DISABLED. *)
Lemma w8_soft_default_yields_iffy_not_disabled :
  Status.to_Z
    (statusOf
       (markStatus NEVER Status.IFFY cal_t0 cal_dud)
       cal_t0) = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== W9: SM-8 — soft-default cure cycle restores SOUND before
    deadline. Step 1: IFFY at t0. Step 2: at t0 + dud - 1, the peg is
    back in band -> SOUND. The decoder reports SOUND afterwards. *)
Definition w9_wd_step1 : Z :=
  markStatus NEVER Status.IFFY cal_t0 cal_dud.
Definition w9_wd_step2 : Z :=
  markStatus w9_wd_step1 Status.SOUND (cal_t0 + cal_dud - 1) cal_dud.

Lemma w9_cure_cycle_restores_sound :
  Status.to_Z (statusOf w9_wd_step2 (cal_t0 + cal_dud - 1)) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== W10: M-1 — refPerTok non-decreasing across two sound updates.
    Climb from exposed=0 with u1=FIX_ONE then u2=2*FIX_ONE. Exposed
    after step 1 = revShowing; after step 2 = 2*revShowing. Strict
    increase, no default flag. *)
Definition w10_step1 : Z * bool :=
  updateExposed 0 FIX_ONE cal_revShowing.
Definition w10_step2 : Z * bool :=
  updateExposed (fst w10_step1) (2 * FIX_ONE) cal_revShowing.

Lemma w10_two_step_climb_no_default :
  snd w10_step1 = false /\ snd w10_step2 = false.
Proof. vm_compute. split; reflexivity. Qed.

Lemma w10_two_step_climb_monotone :
  fst w10_step1 = cal_revShowing /\ fst w10_step2 = 2 * cal_revShowing.
Proof. vm_compute. split; reflexivity. Qed.

(** ===== W11: M-5 — hidden == exposed boundary, no appreciation
    (strict > comparison). After climb to u=2*FIX_ONE, exposed equals
    2*revShowing = hidden(2*FIX_ONE). Re-applying the same u must not
    change exposed and must not default. *)
Definition w11_exposed_calib : Z :=
  FixLib.mul (2 * FIX_ONE) cal_revShowing RoundingMode.FLOOR.

Lemma w11_eq_boundary_no_change :
  updateExposed w11_exposed_calib (2 * FIX_ONE) cal_revShowing
  = (w11_exposed_calib, false).
Proof. vm_compute. reflexivity. Qed.

(** ===== W12: refresh at exactly t0 + dud after a soft default
    transitions to DISABLED. *)
Lemma w12_soft_default_elapses_at_deadline :
  Status.to_Z
    (statusOf
       (markStatus NEVER Status.IFFY cal_t0 cal_dud)
       (cal_t0 + cal_dud)) = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== W13: hard default via the full [refresh] step.
    Build a SOUND state with exposed = FIX_ONE; underlying drops by 1 wei;
    refresh sets exposed = underlying and DISABLES whenDefault now. *)
Definition w13_state_sound : State.t :=
  {| State.whenDefault           := NEVER;
     State.exposedReferencePrice := FIX_ONE;
     State.delayUntilDefault     := cal_dud;
     State.revenueShowing        := cal_revShowing;
     State.pegBottom             := cal_pegBottom;
     State.pegTop                := cal_pegTop; |}.

Definition w13_refreshed : State.t :=
  refresh w13_state_sound (FIX_ONE - 1) cal_targetPerRef (FIX_ONE / 2)
          cal_t0.

Lemma w13_hard_default_drops_exposed :
  w13_refreshed.(State.exposedReferencePrice) = FIX_ONE - 1.
Proof. vm_compute. reflexivity. Qed.

Lemma w13_hard_default_disables_now :
  Status.to_Z (statusOf w13_refreshed.(State.whenDefault) cal_t0) = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== W14: soft default via the full [refresh] step (peg out of
    band). Exposed stays put; whenDefault advances to t0 + dud, so the
    decoded status is IFFY this block but DISABLED at the deadline. *)
Definition w14_state_sound : State.t :=
  {| State.whenDefault           := NEVER;
     State.exposedReferencePrice := cal_revShowing;
     State.delayUntilDefault     := cal_dud;
     State.revenueShowing        := cal_revShowing;
     State.pegBottom             := cal_pegBottom;
     State.pegTop                := cal_pegTop; |}.

(** Use a peg below pegBottom (soft default) and underlying = FIX_ONE
    (no hard default since exposed = revShowing < FIX_ONE). *)
Definition w14_refreshed : State.t :=
  refresh w14_state_sound FIX_ONE (cal_pegBottom - 1) (FIX_ONE / 2)
          cal_t0.

Lemma w14_soft_default_status_iffy_now :
  Status.to_Z (statusOf w14_refreshed.(State.whenDefault) cal_t0) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma w14_soft_default_status_disabled_at_deadline :
  Status.to_Z
    (statusOf w14_refreshed.(State.whenDefault) (cal_t0 + cal_dud)) = 2.
Proof. vm_compute. reflexivity. Qed.

End CollateralWitnesses.
