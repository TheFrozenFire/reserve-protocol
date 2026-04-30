(** FixLib.mul rounding-mode disagreement witnesses.

    The CAS script [cas/fixlib/mul_rounding_direction.gp] reports a 49.3%
    disagreement density between FLOOR / ROUND / CEIL outputs of [FixLib.mul]
    over random uint192 pairs. The disagreement is fundamental: choice of
    rounding mode is load-bearing in nearly half of inputs, not a corner case.

    This file pins concrete Rocq witnesses for that disagreement so the
    lemma graph documents *that mode choice matters* with closed numerals.
    Each witness is a closed evaluation of [mul x y mode] discharged by
    [vm_compute] + [reflexivity] / [discriminate].

    Companion to:
      - [proofs/Fixed.v]: round-direction inequalities (FLOOR <= ROUND <= CEIL).
      - [proofs/Fixed_xcheck.v]: equality witnesses against CAS oracle outputs.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module FixLibMulModeWitnesses.

Import FixLib.

(** ===== Witness 1: (1, 1) — minimal disagreement point =====

    [1 * 1 = 1]; dividing by [FIX_SCALE = 10^18] gives quotient 0 and
    remainder 1. FLOOR truncates to 0; ROUND keeps 0 (remainder is far
    below the half-mark [(FIX_SCALE - 1) / 2]); CEIL rounds up to 1.
    FLOOR/ROUND therefore disagree with CEIL by exactly 1 fp wei. *)

Lemma mul_one_one_FLOOR : mul 1 1 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_one_one_ROUND : mul 1 1 RoundingMode.ROUND = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_one_one_CEIL : mul 1 1 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_mode_disagrees_at_one_one :
  mul 1 1 RoundingMode.FLOOR <> mul 1 1 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 2: (FIX_ONE / 2, 1) — half-boundary disagreement =====

    Product is [FIX_ONE / 2 = 5 * 10^17]. The remainder modulo [FIX_SCALE]
    is exactly the half-mark, which lies strictly above [(FIX_SCALE - 1) / 2]
    (since [FIX_SCALE] is even). FLOOR returns 0; ROUND rounds up to 1;
    CEIL also returns 1. FLOOR therefore disagrees with both ROUND and CEIL. *)

Lemma mul_half_one_FLOOR : mul (FIX_ONE / 2) 1 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_half_one_ROUND : mul (FIX_ONE / 2) 1 RoundingMode.ROUND = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_half_one_CEIL : mul (FIX_ONE / 2) 1 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_mode_disagrees_at_half_one_floor_round :
  mul (FIX_ONE / 2) 1 RoundingMode.FLOOR <> mul (FIX_ONE / 2) 1 RoundingMode.ROUND.
Proof. vm_compute. discriminate. Qed.

Theorem mul_mode_disagrees_at_half_one_floor_ceil :
  mul (FIX_ONE / 2) 1 RoundingMode.FLOOR <> mul (FIX_ONE / 2) 1 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 3: (FIX_ONE - 1, 2) — large-remainder disagreement =====

    Product is [2 * FIX_ONE - 2]. Quotient is 1, remainder is [FIX_ONE - 2],
    which sits above the half-mark. FLOOR = 1, ROUND = 2, CEIL = 2.
    Round mode shifts the answer by an entire fp wei. *)

Lemma mul_minus_one_two_FLOOR :
  mul (FIX_ONE - 1) 2 RoundingMode.FLOOR = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_minus_one_two_ROUND :
  mul (FIX_ONE - 1) 2 RoundingMode.ROUND = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_minus_one_two_CEIL :
  mul (FIX_ONE - 1) 2 RoundingMode.CEIL = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_mode_disagrees_at_minus_one_two :
  mul (FIX_ONE - 1) 2 RoundingMode.FLOOR
    <> mul (FIX_ONE - 1) 2 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 4: (2, 3) — small-remainder ROUND/CEIL split =====

    Product is 6. Quotient is 0, remainder is 6 — far below the half-mark.
    FLOOR = ROUND = 0 (the remainder is too small to push the half-up rule),
    while CEIL = 1 (any non-zero remainder forces the round-up). This is the
    flavour of disagreement Reserve's mid-2023 [mul] default-mode flip
    targeted at fee-accrual call sites: switching default from ROUND to FLOOR
    changes nothing here, but switching to CEIL shifts the answer up by a wei. *)

Lemma mul_two_three_FLOOR : mul 2 3 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_two_three_ROUND : mul 2 3 RoundingMode.ROUND = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_two_three_CEIL : mul 2 3 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_mode_disagrees_at_two_three_round_ceil :
  mul 2 3 RoundingMode.ROUND <> mul 2 3 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 5: (FIX_ONE / 2 + 1, FIX_ONE) — at-and-above-half =====

    Mirrors [xcheck_mul_floor_above_half] in [Fixed_xcheck.v] but framed
    as a disagreement witness. Product is [FIX_ONE * FIX_ONE / 2 + FIX_ONE],
    so [(x*y) mod FIX_SCALE = 0] — the division is exact and *all three modes
    agree*. This is the negative witness: it pins the fact that disagreement
    is not universal, only present when [(x*y) mod FIX_SCALE != 0]. The 49.3%
    density measured by the CAS script is consistent with disagreement
    happening exactly when the remainder is non-zero, which under uniform
    sampling is overwhelmingly the case. *)

Lemma mul_half_plus_one_one_FLOOR :
  mul (FIX_ONE / 2 + 1) FIX_ONE RoundingMode.FLOOR = 500000000000000001.
Proof. vm_compute. reflexivity. Qed.

Lemma mul_half_plus_one_one_CEIL :
  mul (FIX_ONE / 2 + 1) FIX_ONE RoundingMode.CEIL = 500000000000000001.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_mode_agrees_when_remainder_zero :
  mul (FIX_ONE / 2 + 1) FIX_ONE RoundingMode.FLOOR
    = mul (FIX_ONE / 2 + 1) FIX_ONE RoundingMode.CEIL.
Proof. vm_compute. reflexivity. Qed.

End FixLibMulModeWitnesses.
