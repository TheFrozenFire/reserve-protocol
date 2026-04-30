(** FixLib.safeMulDiv — Certora witness corpus, pinned as Rocq theorems.

    Companion to:
      cas/fixlib/safe_muldiv_certora_witness.gp

    The CAS script enumerates 4753 (a, b, c) triples on the FIX_MAX
    overflow boundary and confirms that the post-mitigation
    [safeMulDiv] saturates to FIX_MAX on each. This file pins a
    representative slice (~10 witnesses) as closed Rocq evaluations,
    so the lemma graph documents the saturation behaviour, the
    edge-case short-circuits, and a few non-saturating points
    against which the saturating path can be distinguished.

    The simulation under test is [TradeLib.safeMulDiv] (from
    [simulations/TradeLib.v]) — the same name and shape as the
    production [Fixed.sol] function, modeled in pure Z. Its
    branching structure is:

        if a = 0 \/ b = 0 then 0
        else if a = FIX_MAX \/ b = FIX_MAX \/ c = 0 then FIX_MAX
        else let raw := divrnd (a*b) c mode in
             if FIX_MAX <= raw then FIX_MAX else raw.

    Witness selection criteria:
      - The Certora regression-test inputs (a = 2^191 + 1,
        b = 2^192 - 2, c = 2^127) — the canonical pre-mitigation
        bug witness.
      - Smallest-overflow boundary points from the CAS corpus
        (overflow = +1 wei past FIX_MAX).
      - Edge-case short-circuits (a = 0, b = 0, c = 0).
      - FIX_MAX-driven saturation (a = FIX_MAX, b = FIX_MAX).
      - Non-saturating points to fix the comparison (a*b/c < FIX_MAX).
      - FLOOR vs CEIL rounding split at a non-saturating point —
        confirms the rounding mode is honoured below the saturation
        threshold.
    All proofs are [vm_compute. reflexivity.] (or [discriminate.]
    for inequalities). *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.

Module FixLibSafeMulDivWitnesses.

Import FixLib.
Import Reserve.simulations.TradeLib.TradeLib.

(** ============================================================ *)
(** ===== Witness 1: Certora regression-test inputs ============= *)
(** ============================================================ *)

(** The exact triple from [protocol/test/libraries/Fixed.test.ts]
    "safeMulDiv() may return 0 instead of FIX_MAX". The exact
    product [a*b/c] is approximately [2^64 * FIX_MAX], so the
    intended (post-mitigation) saturated answer is FIX_MAX
    independent of rounding mode. *)

Lemma muldiv_certora_regression_FLOOR :
  safeMulDiv (2^191 + 1) (2^192 - 2) (2^127) RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

Lemma muldiv_certora_regression_CEIL :
  safeMulDiv (2^191 + 1) (2^192 - 2) (2^127) RoundingMode.CEIL = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 2: smallest-overflow boundary (a=2^96 b=2^96 c=1)  *)
(** ============================================================ *)

(** First entry in the CAS-sorted boundary corpus: [2^96 * 2^96 / 1
    = 2^192 = FIX_MAX + 1]. Overflow by exactly 1 wei past FIX_MAX,
    so saturation triggers via the [FIX_MAX <=? raw] clamp (not via
    the FIX_MAX-input short-circuit). *)

Lemma muldiv_boundary_pow96_pow96_1_FLOOR :
  safeMulDiv (2^96) (2^96) 1 RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

Lemma muldiv_boundary_pow96_pow96_1_CEIL :
  safeMulDiv (2^96) (2^96) 1 RoundingMode.CEIL = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 3: equivalent-overflow shape (a=2^96 b=2^97 c=2)  *)
(** ============================================================ *)

(** Second entry in the boundary corpus: [2^96 * 2^97 / 2 = 2^192].
    Same exact value as Witness 2 but a different (a, b, c) shape,
    pinning that the saturation behaviour is shape-invariant. *)

Lemma muldiv_boundary_pow96_pow97_2 :
  safeMulDiv (2^96) (2^97) 2 RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 4: FIX_MAX short-circuit ====================== *)
(** ============================================================ *)

(** When [a = FIX_MAX], the function short-circuits to FIX_MAX
    before computing the inner product. This guards against the
    256-bit intermediate overflow path the production code uses. *)

Lemma muldiv_a_fix_max_short_circuit :
  safeMulDiv FIX_MAX FIX_ONE FIX_ONE RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** Symmetric short-circuit on b = FIX_MAX. *)
Lemma muldiv_b_fix_max_short_circuit :
  safeMulDiv FIX_ONE FIX_MAX FIX_ONE RoundingMode.CEIL = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 5: c = 0 saturation =========================== *)
(** ============================================================ *)

(** Division-by-zero saturates to FIX_MAX (rather than reverting,
    which would block higher-level callers). This matches
    [Fixed.sol#L583] in the post-mitigation code. *)

Lemma muldiv_c_zero_saturates :
  safeMulDiv FIX_ONE FIX_ONE 0 RoundingMode.FLOOR = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 6: a = 0 / b = 0 short-circuit ================ *)
(** ============================================================ *)

(** Zero-input short-circuits to 0, which takes precedence over
    even the c = 0 saturation branch. *)

Lemma muldiv_a_zero_returns_zero :
  safeMulDiv 0 FIX_MAX 0 RoundingMode.CEIL = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma muldiv_b_zero_returns_zero :
  safeMulDiv FIX_MAX 0 0 RoundingMode.CEIL = 0.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 7: non-saturating exact value ================= *)
(** ============================================================ *)

(** [FIX_ONE * FIX_ONE / FIX_ONE = FIX_ONE], well below FIX_MAX.
    The clamp does not fire and the returned value is the exact
    fixed-point arithmetic result. *)

Lemma muldiv_non_saturating_fix_one :
  safeMulDiv FIX_ONE FIX_ONE FIX_ONE RoundingMode.FLOOR = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** [(2 * FIX_ONE) * FIX_ONE / FIX_ONE = 2 * FIX_ONE]: a typical
    non-saturating, exact-divisible point. *)
Lemma muldiv_non_saturating_two_fix_one :
  safeMulDiv (2 * FIX_ONE) FIX_ONE FIX_ONE RoundingMode.CEIL = 2 * FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 8: just-below-FIX_MAX, no clamp =============== *)
(** ============================================================ *)

(** [(FIX_MAX - 1) * 1 / 1 = FIX_MAX - 1]: raw is one wei below
    the saturation threshold, so the clamp does *not* fire. This
    pins the strict inequality in [if FIX_MAX <=? raw then FIX_MAX
    else raw]: the clamp is non-inclusive of FIX_MAX-1. *)

Lemma muldiv_just_below_fix_max :
  safeMulDiv (FIX_MAX - 1) 1 1 RoundingMode.FLOOR = FIX_MAX - 1.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================ *)
(** ===== Witness 9: rounding split below saturation ============ *)
(** ============================================================ *)

(** [1 * 1 / 2]: FLOOR = 0, CEIL = 1. A non-saturating point that
    distinguishes the rounding modes — confirms the [mode] argument
    is honoured below the saturation threshold (the saturating path
    is mode-agnostic, but the non-saturating path is not). *)

Lemma muldiv_rounding_split_FLOOR :
  safeMulDiv 1 1 2 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma muldiv_rounding_split_CEIL :
  safeMulDiv 1 1 2 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem muldiv_rounding_modes_disagree_below_saturation :
  safeMulDiv 1 1 2 RoundingMode.FLOOR
    <> safeMulDiv 1 1 2 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

(** ============================================================ *)
(** ===== Witness 10: pre-mitigation bug class — saturated ====== *)
(** ============================================================ *)

(** The Certora finding was that pre-mitigation [_safeMulDiv]
    could return 0 (instead of FIX_MAX) on the regression input.
    The post-mitigation Rocq model returns FIX_MAX, and FIX_MAX
    is distinguishable from 0 — closing the bug at the type level. *)

Theorem muldiv_post_mitigation_distinguishes_zero :
  safeMulDiv (2^191 + 1) (2^192 - 2) (2^127) RoundingMode.FLOOR <> 0.
Proof. vm_compute. discriminate. Qed.

End FixLibSafeMulDivWitnesses.
