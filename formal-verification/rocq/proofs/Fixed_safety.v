(** FixLib bound-preservation safety lemmas.

    States precise conditions under which the optional FixLib operations
    ([plus_opt], [minus_opt], [mul_opt], [mulu_opt]) return [Some] given
    uint192-valid inputs. These lemmas plug directly into downstream
    obligations that need to discharge "operation succeeded" hypotheses.

    Builds on [safeWrap_some_iff] and the [divrnd] identities from
    [proofs/Fixed.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.

Module FixLibSafety.

Import FixLib.
Import FixLibProofs.

(** ===== plus_opt: if x + y fits, plus_opt returns Some. =====

    The uint192 hypotheses on x and y aren't strictly required (only
    [x + y <= FIX_MAX] and non-negativity matter), but the canonical
    callsite ships them. *)
Lemma plus_opt_uint192_safe (x y : Z) :
  uint192_valid x ->
  uint192_valid y ->
  x + y <= FIX_MAX ->
  plus_opt x y = Some (x + y).
Proof.
  intros _ _ Hbound.
  unfold plus_opt, safeWrap.
  destruct (x + y <=? FIX_MAX) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

(** ===== minus_opt: if y <= x, minus_opt returns Some (x - y). =====

    No overflow side: [x - y <= x <= FIX_MAX] is automatic when x is valid. *)
Lemma minus_opt_uint192_safe (x y : Z) :
  uint192_valid x ->
  uint192_valid y ->
  y <= x ->
  minus_opt x y = Some (x - y).
Proof.
  intros _ _ Hyx.
  unfold minus_opt.
  destruct (y <=? x) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

(** ===== mul_opt: if the rounded product fits, mul_opt returns Some. =====

    This is the [mul_safe] lemma from proofs/Fixed.v restated with the
    canonical [uint192_valid] precondition shape. *)
Lemma mul_opt_safe (x y : Z) (mode : RoundingMode.t) :
  uint192_valid x ->
  uint192_valid y ->
  divrnd (x * y) FIX_SCALE mode <= FIX_MAX ->
  mul_opt x y mode = Some (mul x y mode).
Proof.
  intros [Hx _] [Hy _] Hbound.
  apply mul_safe; assumption.
Qed.

(** ===== mulu_opt: if x * y fits, mulu_opt returns Some. ===== *)
Lemma mulu_opt_safe (x y : Z) :
  uint192_valid x ->
  uint192_valid y ->
  x * y <= FIX_MAX ->
  mulu_opt x y = Some (x * y).
Proof.
  intros _ _ Hbound.
  unfold mulu_opt, safeWrap.
  destruct (x * y <=? FIX_MAX) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

(** ===== Auxiliary: divrnd of a scale multiple equals the cofactor. =====

    For all rounding modes, [divrnd (x * d) d mode = x] when [d > 0].
    The remainder [(x * d) mod d = 0] kills every mode's correction term. *)
Lemma divrnd_mul_cancel (x d : Z) (mode : RoundingMode.t) :
  0 < d ->
  divrnd (x * d) d mode = x.
Proof.
  intros Hd.
  unfold divrnd.
  assert (Hdiv : (x * d) / d = x) by (apply Z.div_mul; lia).
  assert (Hmod : (x * d) mod d = 0) by (apply Z.mod_mul; lia).
  rewrite Hdiv, Hmod.
  destruct mode.
  - reflexivity.
  - destruct (0 >? (d - 1) / 2) eqn:H.
    + apply Z.gtb_lt in H.
      assert (0 <= (d - 1) / 2) by (apply Z.div_pos; lia).
      lia.
    + reflexivity.
  - reflexivity.
Qed.

(** ===== mul_opt with FIX_ONE: x * FIX_ONE rounded by FIX_SCALE = x exactly. =====

    Since FIX_ONE = FIX_SCALE, the product [x * FIX_ONE] divides FIX_SCALE
    exactly — no rounding kicks in. *)
Lemma mul_opt_when_at_least_one_is_FIX_ONE (x : Z) (mode : RoundingMode.t) :
  uint192_valid x ->
  mul_opt x FIX_ONE mode = Some x.
Proof.
  intros [Hx_lo Hx_hi].
  unfold mul_opt.
  unfold FIX_ONE.
  rewrite divrnd_mul_cancel by (unfold FIX_SCALE; lia).
  unfold safeWrap.
  destruct (x <=? FIX_MAX) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

End FixLibSafety.
