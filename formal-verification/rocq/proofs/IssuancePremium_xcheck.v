(** IssuancePremium simulation × CAS witness cross-check.

    Evaluates the [IssuancePremium] simulation on the same calibration
    inputs used by [cas/issuance_premium/premium_curve.gp] and asserts
    identical outputs. Any divergence between the Rocq simulation and
    the CAS witness corpus fails the build.

    Calibration mirrors the CAS 5-token stablecoin basket:
      target_per_ref = FIX_ONE
      peg_prices     = [1.00, 1.00, 1.00, 0.998, 0.995] * FIX_ONE
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.

Module IssuancePremiumXCheck.

Import FixLib.
Import IssuancePremium.

(** ===== INV-P1: premium >= FIX_ONE for all calibration peg prices. ===== *)

(** USDC/USDT/DAI on peg -> premium = FIX_ONE. *)
Lemma xcheck_p1_on_peg :
  issuancePremium true true FIX_ONE FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** FRAX (0.998 = FIX_ONE * 998/1000) under peg -> premium > FIX_ONE.
    safeDiv(FIX_ONE, 998 * 10^15, CEIL)
      = ceil(10^36 / (998 * 10^15))
      = ceil(10^36 / 998000000000000000) *)
Definition cal_pegFRAX : Z := FIX_ONE - FIX_ONE * 2 / 1000.

Lemma xcheck_p1_FRAX_value :
  cal_pegFRAX = 998000000000000000.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_p1_FRAX_premium :
  issuancePremium true true cal_pegFRAX FIX_ONE = 1002004008016032065.
Proof. vm_compute. reflexivity. Qed.

(** LUSD (0.995) under peg. *)
Definition cal_pegLUSD : Z := FIX_ONE - FIX_ONE * 5 / 1000.

Lemma xcheck_p1_LUSD_value :
  cal_pegLUSD = 995000000000000000.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_p1_LUSD_premium :
  issuancePremium true true cal_pegLUSD FIX_ONE = 1005025125628140704.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-P2: premium == FIX_ONE when pegPrice == targetPerRef. ===== *)
Lemma xcheck_p2_at_peg :
  issuancePremium true true FIX_ONE FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** Slightly above peg (1.001 * FIX_ONE) also returns FIX_ONE. *)
Lemma xcheck_p2_above_peg :
  issuancePremium true true (FIX_ONE + 10^15) FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-P3: monotone non-increasing in pegPrice across the curve. =====
    CAS prints concrete witnesses at 0.99, 0.98, 0.95, 0.90. *)
Lemma xcheck_p3_99 :
  issuancePremium true true (FIX_ONE * 99 / 100) FIX_ONE
  = 1010101010101010102.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_p3_98 :
  issuancePremium true true (FIX_ONE * 98 / 100) FIX_ONE
  = 1020408163265306123.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_p3_95 :
  issuancePremium true true (FIX_ONE * 95 / 100) FIX_ONE
  = 1052631578947368422.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_p3_90 :
  issuancePremium true true (FIX_ONE * 90 / 100) FIX_ONE
  = 1111111111111111112.
Proof. vm_compute. reflexivity. Qed.

(** Concrete monotonicity witness: pegPrice 0.99 < 0.98 (strictly higher
    premium for lower peg). *)
Lemma xcheck_p3_strict :
  issuancePremium true true (FIX_ONE * 99 / 100) FIX_ONE
  < issuancePremium true true (FIX_ONE * 98 / 100) FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-P4: safeDiv saturation at FIX_MAX boundary. ===== *)

(** safeDiv(FIX_MAX, FIX_ONE, CEIL) = FIX_MAX. *)
Lemma xcheck_p4_saturated :
  safeDiv_ceil FIX_MAX FIX_ONE = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** safeDiv(FIX_MAX, FIX_ONE/2, CEIL) = FIX_MAX. *)
Lemma xcheck_p4_saturated_halfdiv :
  safeDiv_ceil FIX_MAX (FIX_ONE / 2) = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** safeDiv(FIX_ONE, 0, CEIL) = FIX_MAX (sentinel). *)
Lemma xcheck_p4_div_zero :
  safeDiv_ceil FIX_ONE 0 = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** safeDiv(0, FIX_ONE, CEIL) = 0. *)
Lemma xcheck_p4_zero_num :
  safeDiv_ceil 0 FIX_ONE = 0.
Proof. vm_compute. reflexivity. Qed.

(** Through issuancePremium: targetPerRef = FIX_MAX, pegPrice = FIX_ONE/2.
    Goes through the full saturation path. *)
Lemma xcheck_p4_full_saturated :
  issuancePremium true true (FIX_ONE / 2) FIX_MAX = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-P4b: pegPrice = 0 falls back to FIX_ONE (no premium). ===== *)
Lemma xcheck_p4b_zero_peg :
  issuancePremium true true 0 FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** lastSave != now disables the premium. *)
Lemma xcheck_p4b_stale :
  issuancePremium true false (FIX_ONE / 2) FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** enableIssuancePremium = false: always FIX_ONE. *)
Lemma xcheck_p4b_disabled :
  issuancePremium false true (FIX_ONE / 2) FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

End IssuancePremiumXCheck.
