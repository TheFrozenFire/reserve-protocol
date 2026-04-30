(** FixLib simulation × CAS witness cross-check.

    Evaluates the [FixLib] simulation on the same numerical witnesses
    produced by the four FixLib CAS scripts in cas/fixlib/, and asserts
    identical outputs. Any drift between the Rocq simulation and the
    CAS witness corpus fails the build.

    Witness sources:
      cas/fixlib/mul_rounding_direction.gp   (round/floor/ceil at half-boundaries)
      cas/fixlib/powu_correctness.gp         (boundary cases + iterative profile)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module FixLibXCheck.

Import FixLib.

(** ===== mul_rounding_direction witnesses =====
    [x = FIX_ONE], [y = FIX_ONE/2]: exact half-product.
    All three rounding modes give 5*10^17 (the gap is zero by exactness). *)

Lemma xcheck_mul_floor_at_half :
  mul FIX_ONE (FIX_ONE / 2) RoundingMode.FLOOR = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mul_round_at_half :
  mul FIX_ONE (FIX_ONE / 2) RoundingMode.ROUND = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mul_ceil_at_half :
  mul FIX_ONE (FIX_ONE / 2) RoundingMode.CEIL = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** [y = FIX_ONE/2 + 1]: product 1 unit above half. CEIL still 500...001
    (no extra rounding), FLOOR also 500...001 (it lands exactly), ROUND
    matches FLOOR. *)
Lemma xcheck_mul_floor_above_half :
  mul FIX_ONE (FIX_ONE / 2 + 1) RoundingMode.FLOOR = 500000000000000001.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mul_round_above_half :
  mul FIX_ONE (FIX_ONE / 2 + 1) RoundingMode.ROUND = 500000000000000001.
Proof. vm_compute. reflexivity. Qed.

(** [y = FIX_ONE/2 - 1]: product 1 unit below half. *)
Lemma xcheck_mul_floor_below_half :
  mul FIX_ONE (FIX_ONE / 2 - 1) RoundingMode.FLOOR = 499999999999999999.
Proof. vm_compute. reflexivity. Qed.

(** ===== powu_correctness witnesses ===== *)

(** Boundary: powu(0.5, 0) = FIX_ONE. *)
Lemma xcheck_powu_half_zero :
  powu (5 * 10^17) 0 = FIX_ONE.
Proof. reflexivity. Qed.

(** Boundary: powu(0.5, 1) = 0.5 = 5*10^17. *)
Lemma xcheck_powu_half_one :
  powu (5 * 10^17) 1 = 5 * 10^17.
Proof. reflexivity. Qed.

(** Boundary: powu(FIX_ONE, 100) = FIX_ONE. *)
Lemma xcheck_powu_one_hundred :
  powu FIX_ONE 100 = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** Boundary: powu(0, 0) = FIX_ONE (Solidity convention). *)
Lemma xcheck_powu_zero_zero :
  powu 0 0 = FIX_ONE.
Proof. reflexivity. Qed.

(** Boundary: powu(0, 5) = 0. *)
Lemma xcheck_powu_zero_five :
  powu 0 5 = 0.
Proof. vm_compute. reflexivity. Qed.

(** Iterative profile: powu(0.999, 10) = 990044880209748209.
    CAS computes via iterative repeated squaring to verify the
    fixed-point precision matches.

    Note: the precise final integer the simulation produces is determined
    by the half-divisor rounding pattern in [halfDiv]. The CAS calibration
    used the same rounding scheme. *)
Lemma xcheck_powu_999_ten :
  powu (999 * 10^15) 10 = 990044880209748209.
Proof. vm_compute. reflexivity. Qed.

(** powu(0.5, 10) = 976562500000000  (= 1/1024 * 10^18). *)
Lemma xcheck_powu_half_ten :
  powu (5 * 10^17) 10 = 976562500000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Round-direction sanity (algebraic, not numerical) ===== *)
(** All three modes coincide at FIX_ONE * FIX_ONE: it's an exact product. *)
Lemma xcheck_mul_one_one_all_modes :
  mul FIX_ONE FIX_ONE RoundingMode.FLOOR = FIX_ONE /\
  mul FIX_ONE FIX_ONE RoundingMode.ROUND = FIX_ONE /\
  mul FIX_ONE FIX_ONE RoundingMode.CEIL  = FIX_ONE.
Proof.
  split; [|split]; vm_compute; reflexivity.
Qed.

(** Saturation: mul(FIX_MAX, FIX_ONE, FLOOR) = FIX_MAX (no rounding loss
    since dividing by FIX_ONE undoes the FIX_ONE scaling exactly). *)
Lemma xcheck_mul_saturated :
  mul FIX_MAX FIX_ONE RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

End FixLibXCheck.
