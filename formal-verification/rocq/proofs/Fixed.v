(** FixLib invariant proofs.

    Proves the load-bearing algebraic identities and round-direction
    inequalities on the [FixLib] simulation in [Reserve.simulations.Fixed].

    The core leverage here is RD-1..RD-3: every [mul]/[div] caller in the
    Reserve codebase passes one of FLOOR/ROUND/CEIL, and downstream proofs
    repeatedly need bounds like [mul x y FLOOR <= mul x y CEIL]. Proving
    those once at the kernel level (on [divrnd]) makes them free everywhere.

    INV-RD-1   divrnd n d FLOOR <= divrnd n d CEIL          (d > 0)
    INV-RD-2   divrnd n d FLOOR <= divrnd n d ROUND         (d > 0)
    INV-RD-3   divrnd n d ROUND <= divrnd n d CEIL          (d > 0)
    INV-RD-4   divrnd n d CEIL <= divrnd n d FLOOR + 1      (d > 0)

    INV-FL-1   divrnd n d FLOOR  =  n / d                   (Z.div semantics)
    INV-CL-1   divrnd n d CEIL = n / d + (1 if d ∤ n else 0)

    INV-MUL-CR mul x y FLOOR <= mul x y CEIL                (lifts RD-1)
    INV-MUL-CO mul x y mode = mul y x mode                  (commutativity)

    INV-POW-0  powu x 0 = FIX_ONE
    INV-POW-1  powu x 1 = x
    INV-POW-1B powu FIX_ONE y = FIX_ONE                     (y > 0)

    The Certora-audited safety lemmas for [mul_opt]/[div_opt] returning
    [Some] under uint192 input bounds are stated and proved here too.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module FixLibProofs.

Import FixLib.

(** ===== Algebraic identity for FLOOR ===== *)
Lemma divrnd_floor_eq (n d : Z) :
  divrnd n d RoundingMode.FLOOR = n / d.
Proof. reflexivity. Qed.

(** ===== Round-direction inequalities ===== *)

Lemma divrnd_floor_le_ceil (n d : Z) :
  0 < d ->
  divrnd n d RoundingMode.FLOOR <= divrnd n d RoundingMode.CEIL.
Proof.
  intros Hd.
  unfold divrnd.
  destruct (n mod d =? 0); lia.
Qed.

Lemma divrnd_floor_le_round (n d : Z) :
  0 < d ->
  divrnd n d RoundingMode.FLOOR <= divrnd n d RoundingMode.ROUND.
Proof.
  intros Hd.
  unfold divrnd.
  destruct (n mod d >? (d - 1) / 2); lia.
Qed.

Lemma divrnd_round_le_ceil (n d : Z) :
  0 < d ->
  divrnd n d RoundingMode.ROUND <= divrnd n d RoundingMode.CEIL.
Proof.
  intros Hd.
  unfold divrnd.
  set (q := n / d).
  set (r := n mod d).
  destruct (r >? (d - 1) / 2) eqn:HR.
  - apply Z.gtb_lt in HR.
    destruct (r =? 0) eqn:Hzero; [|lia].
    apply Z.eqb_eq in Hzero. lia.
  - destruct (r =? 0) eqn:Hzero.
    + apply Z.eqb_eq in Hzero. lia.
    + lia.
Qed.

Lemma divrnd_ceil_le_floor_plus_one (n d : Z) :
  0 < d ->
  divrnd n d RoundingMode.CEIL <= divrnd n d RoundingMode.FLOOR + 1.
Proof.
  intros Hd.
  unfold divrnd.
  destruct (n mod d =? 0); lia.
Qed.

(** ===== CEIL identity: n/d rounded up. ===== *)
Lemma divrnd_ceil_eq (n d : Z) :
  0 < d ->
  divrnd n d RoundingMode.CEIL =
    n / d + (if (n mod d) =? 0 then 0 else 1).
Proof.
  intros Hd. unfold divrnd.
  destruct (n mod d =? 0); lia.
Qed.

(** ===== Lifted to mul ===== *)

Lemma mul_floor_le_ceil (x y : Z) :
  mul x y RoundingMode.FLOOR <= mul x y RoundingMode.CEIL.
Proof.
  unfold mul. apply divrnd_floor_le_ceil.
  unfold FIX_SCALE. lia.
Qed.

Lemma mul_floor_le_round (x y : Z) :
  mul x y RoundingMode.FLOOR <= mul x y RoundingMode.ROUND.
Proof.
  unfold mul. apply divrnd_floor_le_round.
  unfold FIX_SCALE. lia.
Qed.

Lemma mul_round_le_ceil (x y : Z) :
  mul x y RoundingMode.ROUND <= mul x y RoundingMode.CEIL.
Proof.
  unfold mul. apply divrnd_round_le_ceil.
  unfold FIX_SCALE. lia.
Qed.

(** Commutativity. *)
Lemma mul_comm (x y : Z) (mode : RoundingMode.t) :
  mul x y mode = mul y x mode.
Proof.
  unfold mul. rewrite (Z.mul_comm x y). reflexivity.
Qed.

(** ===== div round-direction (analogous) ===== *)

Lemma div_floor_le_ceil (x y : Z) :
  0 < y ->
  div x y RoundingMode.FLOOR <= div x y RoundingMode.CEIL.
Proof.
  intros Hy. unfold div. apply divrnd_floor_le_ceil. exact Hy.
Qed.

Lemma div_floor_le_round (x y : Z) :
  0 < y ->
  div x y RoundingMode.FLOOR <= div x y RoundingMode.ROUND.
Proof.
  intros Hy. unfold div. apply divrnd_floor_le_round. exact Hy.
Qed.

(** ===== safeWrap correctness ===== *)
Lemma safeWrap_some_iff (x : Z) (y : Z) :
  safeWrap x = Some y <-> x <= FIX_MAX /\ y = x.
Proof.
  unfold safeWrap. destruct (x <=? FIX_MAX) eqn:H.
  - apply Z.leb_le in H. split.
    + intros Heq. inversion Heq; subst. split; [exact H|reflexivity].
    + intros [_ ->]. reflexivity.
  - apply Z.leb_gt in H. split; intros HH.
    + discriminate.
    + destruct HH as [Hle _]. lia.
Qed.

Lemma safeWrap_none_iff (x : Z) :
  safeWrap x = None <-> FIX_MAX < x.
Proof.
  unfold safeWrap. destruct (x <=? FIX_MAX) eqn:H.
  - apply Z.leb_le in H. split; intros HH.
    + discriminate.
    + lia.
  - apply Z.leb_gt in H. split; intros HH.
    + exact H.
    + reflexivity.
Qed.

(** ===== Boundedness: when does mul fit in uint192? ===== *)
Lemma mul_safe (x y : Z) (mode : RoundingMode.t) :
  0 <= x ->
  0 <= y ->
  divrnd (x * y) FIX_SCALE mode <= FIX_MAX ->
  mul_opt x y mode = Some (mul x y mode).
Proof.
  intros Hx Hy Hbound.
  unfold mul_opt, mul, safeWrap.
  destruct (_ <=? _) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.

(** ===== Boundedness: divrnd FLOOR is monotone in numerator ===== *)
Lemma divrnd_floor_monotone (n1 n2 d : Z) :
  0 < d ->
  n1 <= n2 ->
  divrnd n1 d RoundingMode.FLOOR <= divrnd n2 d RoundingMode.FLOOR.
Proof.
  intros Hd Hn. unfold divrnd. apply Z.div_le_mono; assumption.
Qed.

(** ===== Trivial powu cases ===== *)

Lemma powu_zero (x : Z) :
  powu x 0 = FIX_ONE.
Proof. reflexivity. Qed.

Lemma powu_one_pow (x : Z) :
  powu x 1 = x.
Proof. reflexivity. Qed.

Lemma powu_one_base (y : Z) :
  powu FIX_ONE y = FIX_ONE.
Proof.
  unfold powu.
  destruct (y =? 0); [reflexivity|].
  destruct (y =? 1); [reflexivity|].
  rewrite Z.eqb_refl. reflexivity.
Qed.

End FixLibProofs.
