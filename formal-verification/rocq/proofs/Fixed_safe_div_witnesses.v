(** FixLib.div / safeDiv witnesses pinning the Certora-FixLib finding.

    The CAS script [cas/fixlib/safe_div_propagation.gp] characterizes the
    pre-mitigation behaviour of [safeDiv(FIX_MAX, b)] for b > 0. Pre-
    mitigation, [safeDiv] fell through to
        raw = floor(FIX_ONE * FIX_MAX / b)
    which silently scaled the saturated value by 1/b instead of preserving
    it. The mitigation (PR #1283) added an early [if (a == FIX_MAX) return
    FIX_MAX] above the [b == 0] guard.

    The simulation in [simulations/Fixed.v] models the *arithmetic* kernel
    [div(x, y, mode) = divrnd(x * FIX_SCALE, y, mode)], which is exactly
    the [raw] expression the pre-mitigation [safeDiv] returned in the
    bug-affected region [b >= FIX_ONE]. Each lemma below pins a closed
    evaluation of [div] discharged by [vm_compute] + [reflexivity] /
    [discriminate], anchoring the CAS findings as Rocq theorems.

    Companions:
      - [proofs/Fixed_certora_mitigation.v]  : pre/post lifting at the
        TradeLib boundary.
      - [proofs/Fixed_mul_mode_witnesses.v]  : same witness style for the
        rounding-mode disagreement on [mul]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module FixLibSafeDivWitnesses.

Import FixLib.

(** ===== Witness 1: div FIX_ONE FIX_ONE FLOOR = FIX_ONE — identity =====

    The fixed-point identity element for division. [(FIX_ONE * FIX_SCALE)
    / FIX_ONE = FIX_SCALE = FIX_ONE], remainder zero, all modes agree. *)

Lemma div_FIX_ONE_FIX_ONE_FLOOR :
  div FIX_ONE FIX_ONE RoundingMode.FLOOR = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

Lemma div_FIX_ONE_FIX_ONE_CEIL :
  div FIX_ONE FIX_ONE RoundingMode.CEIL = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 2: div 1 FIX_ONE — minimal numerator =====

    [div 1 FIX_ONE _ = (1 * FIX_SCALE) / FIX_ONE = 1]. The pre-scaling
    by FIX_SCALE is exactly what saves precision here: an unscaled
    [1 / FIX_ONE] would have been zero. All modes agree (remainder zero). *)

Lemma div_one_FIX_ONE_FLOOR :
  div 1 FIX_ONE RoundingMode.FLOOR = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma div_one_FIX_ONE_CEIL :
  div 1 FIX_ONE RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 3: div FIX_ONE 1 FLOOR — small-divisor blowup =====

    [div FIX_ONE 1 FLOOR = (FIX_ONE * FIX_SCALE) / 1 = 10^36]. The result
    fits in Z (and in fact in uint192, since [10^36 < 2^192 - 1]), so the
    pure [div] returns it. The point of this witness is to pin the
    *unsaturated* magnitude — at b = 1, division acts as a pure scale-up,
    contrasting with the FIX_MAX-propagation witnesses below. *)

Lemma div_FIX_ONE_one_FLOOR :
  div FIX_ONE 1 RoundingMode.FLOOR = 1000000000000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 4: div FIX_MAX FIX_ONE FLOOR = FIX_MAX =====

    The post-mitigation invariant at the boundary [b = FIX_ONE]: dividing
    FIX_MAX by FIX_ONE preserves FIX_MAX. The arithmetic kernel naturally
    yields FIX_MAX here because [(FIX_MAX * FIX_SCALE) / FIX_ONE = FIX_MAX]
    with zero remainder — no rounding hazard, no saturation guard needed.
    This is the b = FIX_ONE row of the CAS sweep. *)

Lemma div_FIX_MAX_FIX_ONE_FLOOR :
  div FIX_MAX FIX_ONE RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

Lemma div_FIX_MAX_FIX_ONE_CEIL :
  div FIX_MAX FIX_ONE RoundingMode.CEIL = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 5: div FIX_MAX (2 * FIX_ONE) FLOOR — Certora regression =====

    The exact regression input from Fixed.test.ts:
      "safeDiv() does not correctly propagate the FIX_MAX value".
    Pre-mitigation, [safeDiv FIX_MAX (2 * FIX_ONE) ROUND] returned
    approximately FIX_MAX/2 instead of FIX_MAX. The arithmetic kernel
    here returns the bug magnitude:
      [(FIX_MAX * FIX_SCALE) / (2 * FIX_ONE) = FIX_MAX / 2 (FLOOR)],
    pinning the silent scale-by-1/b that the mitigation closed off. *)

Lemma div_FIX_MAX_2_FIX_ONE_FLOOR :
  div FIX_MAX (2 * FIX_ONE) RoundingMode.FLOOR
    = 3138550867693340381917894711603833208051177722232017256447.
Proof. vm_compute. reflexivity. Qed.

(** The strict inequality is the key Certora finding: the arithmetic
    [div FIX_MAX (2 * FIX_ONE) FLOOR] is NOT [FIX_MAX]. Post-mitigation
    [safeDiv] short-circuits to FIX_MAX *despite* the kernel disagreeing. *)
Theorem pre_mitigation_safeDiv_FIX_MAX_diverges :
  div FIX_MAX (2 * FIX_ONE) RoundingMode.FLOOR <> FIX_MAX.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 6: div FIX_MAX (10 * FIX_ONE) FLOOR — sweep row =====

    A second row of the CAS sweep: the bug magnitude at b = 10 * FIX_ONE
    is approximately FIX_MAX / 10. Together with witness 5 this anchors
    the "for b >= FIX_ONE the bug is everywhere" claim from the script. *)

Lemma div_FIX_MAX_10_FIX_ONE_FLOOR :
  div FIX_MAX (10 * FIX_ONE) RoundingMode.FLOOR
    = 627710173538668076383578942320766641610235544446403451289.
Proof. vm_compute. reflexivity. Qed.

Theorem pre_mitigation_diverges_at_b_10_FIX_ONE :
  div FIX_MAX (10 * FIX_ONE) RoundingMode.FLOOR <> FIX_MAX.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 7: div_opt FIX_MAX 1 = None — saturation overflow =====

    The opposite extreme of the saturation analysis: dividing FIX_MAX by
    a divisor smaller than FIX_ONE (here, 1) produces a raw result far
    above FIX_MAX, and [div_opt] (which composes [safeWrap]) refuses it.
    This is the [raw > FIX_MAX] branch of the existing [safeDiv]
    saturation guard from the script's commentary. *)

Lemma div_opt_FIX_MAX_one_overflows :
  div_opt FIX_MAX 1 RoundingMode.FLOOR = None.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 8: FLOOR vs CEIL divergence on remainders =====

    A non-zero remainder makes FLOOR and CEIL differ by exactly 1.
    [(1 * FIX_SCALE) / 3 = 333...333] with remainder 1; CEIL bumps it. *)

Lemma div_one_three_FLOOR :
  div 1 3 RoundingMode.FLOOR = 333333333333333333.
Proof. vm_compute. reflexivity. Qed.

Lemma div_one_three_CEIL :
  div 1 3 RoundingMode.CEIL = 333333333333333334.
Proof. vm_compute. reflexivity. Qed.

Theorem div_FLOOR_CEIL_disagree_on_thirds :
  div 1 3 RoundingMode.FLOOR <> div 1 3 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 9: div 2 3 — ROUND/CEIL agree, FLOOR differs =====

    [(2 * FIX_SCALE) / 3 = 666...666] with remainder 2 * 10^18 / 3 mod 1
    sitting above the half-mark, so ROUND rounds up alongside CEIL. *)

Lemma div_two_three_FLOOR :
  div 2 3 RoundingMode.FLOOR = 666666666666666666.
Proof. vm_compute. reflexivity. Qed.

Lemma div_two_three_ROUND :
  div 2 3 RoundingMode.ROUND = 666666666666666667.
Proof. vm_compute. reflexivity. Qed.

Lemma div_two_three_CEIL :
  div 2 3 RoundingMode.CEIL = 666666666666666667.
Proof. vm_compute. reflexivity. Qed.

Theorem div_FLOOR_ROUND_disagree_at_two_thirds :
  div 2 3 RoundingMode.FLOOR <> div 2 3 RoundingMode.ROUND.
Proof. vm_compute. discriminate. Qed.

(** ===== Witness 10: precision-loss boundary =====

    When the divisor exceeds [FIX_ONE * FIX_MAX], even the pre-scaling by
    FIX_SCALE cannot save precision: FLOOR collapses the result to 0.
    CEIL then differs from FLOOR by an entire fp wei. This is the
    counterpart to witness 2 (where pre-scaling rescues precision):
    pre-scaling has its limits, and at very large divisors the operation
    becomes either zero (FLOOR) or one (CEIL). *)

Lemma div_one_huge_b_FLOOR :
  div 1 (FIX_ONE * FIX_MAX + 1) RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma div_one_huge_b_CEIL :
  div 1 (FIX_ONE * FIX_MAX + 1) RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem div_precision_loss_at_huge_b :
  div 1 (FIX_ONE * FIX_MAX + 1) RoundingMode.FLOOR
    <> div 1 (FIX_ONE * FIX_MAX + 1) RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

End FixLibSafeDivWitnesses.
