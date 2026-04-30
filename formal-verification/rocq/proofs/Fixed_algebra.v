(** FixLib algebraic identities — second layer.

    Builds on proofs/Fixed.v (round-direction inequalities) with
    commutativity, distributivity, and saturation behavior on the
    [FixLib] simulation.

    Coverage:
      - mul saturation at 0 (mul_zero_left/right)
      - div_one identity for FLOOR
      - divrnd_self for n > 0
      - mulu_zero/mulu_one trivial saturation
      - plus identity laws (plus_zero, minus_zero), commutativity, associativity
      - mulu_toUint_floor unfolding lemma
      - safeWrap idempotence
      - mul_opt boundedness lift
      - comparison reflexivity / antisymmetry / lt -> lte
      - powu_two: powu FIX_ONE 2 = FIX_ONE
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.

Module FixLibAlgebra.

Import FixLib.
Import FixLibProofs.

(** ===== mul saturation at 0 ===== *)

Lemma mul_zero_left (y : Z) (mode : RoundingMode.t) :
  mul 0 y mode = 0.
Proof.
  unfold mul, divrnd. rewrite Z.mul_0_l.
  rewrite Zdiv_0_l, Zmod_0_l.
  destruct mode; reflexivity.
Qed.

Lemma mul_zero_right (x : Z) (mode : RoundingMode.t) :
  mul x 0 mode = 0.
Proof.
  unfold mul, divrnd. rewrite Z.mul_0_r.
  rewrite Zdiv_0_l, Zmod_0_l.
  destruct mode; reflexivity.
Qed.

(** ===== div by FIX_ONE for FLOOR is identity for non-negative x ===== *)

Lemma div_one_floor (x : Z) :
  0 <= x ->
  div x FIX_ONE RoundingMode.FLOOR = x.
Proof.
  intros Hx. unfold div, divrnd, FIX_ONE, FIX_SCALE.
  rewrite Z.div_mul by (vm_compute; discriminate).
  reflexivity.
Qed.

(** ROUND/CEIL on div x FIX_ONE coincide with FLOOR because x*FIX_SCALE is
    exactly divisible by FIX_SCALE — remainder is zero. *)
Lemma div_one_ceil (x : Z) :
  0 <= x ->
  div x FIX_ONE RoundingMode.CEIL = x.
Proof.
  intros Hx. unfold div, divrnd, FIX_ONE, FIX_SCALE.
  rewrite Z.mod_mul by (vm_compute; discriminate).
  rewrite Z.div_mul by (vm_compute; discriminate).
  reflexivity.
Qed.

Lemma div_one_round (x : Z) :
  0 <= x ->
  div x FIX_ONE RoundingMode.ROUND = x.
Proof.
  intros Hx. unfold div, divrnd, FIX_ONE, FIX_SCALE.
  rewrite Z.mod_mul by (vm_compute; discriminate).
  rewrite Z.div_mul by (vm_compute; discriminate).
  destruct (0 >? (10 ^ 18 - 1) / 2) eqn:HC.
  - apply Z.gtb_lt in HC.
    assert ((10 ^ 18 - 1) / 2 >= 0).
    { apply Z.le_ge. apply Z.div_pos; [vm_compute; discriminate|lia]. }
    lia.
  - reflexivity.
Qed.

(** ===== divrnd n n = 1 for n > 0 (all modes) ===== *)
Lemma divrnd_self (n : Z) (mode : RoundingMode.t) :
  0 < n ->
  divrnd n n mode = 1.
Proof.
  intros Hn. unfold divrnd.
  rewrite Z_div_same by lia.
  rewrite Z_mod_same_full.
  destruct mode.
  - reflexivity.
  - destruct (0 >? (n - 1) / 2) eqn:HC; [|reflexivity].
    apply Z.gtb_lt in HC.
    assert ((n - 1) / 2 >= 0).
    { apply Z.le_ge. apply Z.div_pos; lia. }
    lia.
  - reflexivity.
Qed.

(** ===== mulu trivial saturation ===== *)

Lemma mulu_zero_left (y : Z) :
  mulu 0 y = 0.
Proof. unfold mulu. lia. Qed.

Lemma mulu_zero_right (x : Z) :
  mulu x 0 = 0.
Proof. unfold mulu. lia. Qed.

Lemma mulu_one_left (y : Z) :
  mulu 1 y = y.
Proof. unfold mulu. lia. Qed.

Lemma mulu_one_right (x : Z) :
  mulu x 1 = x.
Proof. unfold mulu. lia. Qed.

(** ===== plus / minus identity laws ===== *)

Lemma plus_zero_left (x : Z) :
  plus 0 x = x.
Proof. unfold plus. lia. Qed.

Lemma plus_zero_right (x : Z) :
  plus x 0 = x.
Proof. unfold plus. lia. Qed.

Lemma minus_zero_right (x : Z) :
  minus x 0 = x.
Proof. unfold minus. lia. Qed.

Lemma minus_self (x : Z) :
  minus x x = 0.
Proof. unfold minus. lia. Qed.

(** ===== plus commutativity / associativity ===== *)

Lemma plus_comm (x y : Z) :
  plus x y = plus y x.
Proof. unfold plus. lia. Qed.

Lemma plus_assoc (x y z : Z) :
  plus (plus x y) z = plus x (plus y z).
Proof. unfold plus. lia. Qed.

(** ===== divrnd_div_double for FLOOR/CEIL ===== *)

Lemma divrnd_div_double_floor (n d : Z) :
  0 < d ->
  divrnd (2 * n) (2 * d) RoundingMode.FLOOR = divrnd n d RoundingMode.FLOOR.
Proof.
  intros Hd. unfold divrnd.
  rewrite Z.mul_comm with (n := 2) (m := n).
  rewrite Z.mul_comm with (n := 2) (m := d).
  rewrite Z.div_mul_cancel_r by lia.
  reflexivity.
Qed.

Lemma divrnd_div_double_ceil (n d : Z) :
  0 < d ->
  divrnd (2 * n) (2 * d) RoundingMode.CEIL = divrnd n d RoundingMode.CEIL.
Proof.
  intros Hd. unfold divrnd.
  rewrite Z.mul_comm with (n := 2) (m := n).
  rewrite Z.mul_comm with (n := 2) (m := d).
  rewrite Z.div_mul_cancel_r by lia.
  (* Need: (n*2) mod (d*2) =? 0 has same boolean value as n mod d =? 0 *)
  assert (Hmod : (n * 2) mod (d * 2) = (n mod d) * 2).
  { rewrite Z.mul_mod_distr_r by lia. reflexivity. }
  rewrite Hmod.
  destruct (n mod d =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. simpl. reflexivity.
  - apply Z.eqb_neq in E.
    destruct (n mod d * 2 =? 0) eqn:E2.
    + apply Z.eqb_eq in E2. lia.
    + reflexivity.
Qed.

(** ===== mulu_toUint FLOOR unfolding ===== *)

Lemma mulu_toUint_floor_eq (x y : Z) :
  mulu_toUint x y RoundingMode.FLOOR = x * y / FIX_SCALE.
Proof. reflexivity. Qed.

(** ===== safeWrap idempotence ===== *)

Lemma safeWrap_idempotent (x y : Z) :
  safeWrap x = Some y ->
  safeWrap y = Some y.
Proof.
  intros H. apply safeWrap_some_iff in H.
  destruct H as [Hle Heq]. subst y.
  apply safeWrap_some_iff. split; [exact Hle | reflexivity].
Qed.

(** ===== mul_opt boundedness ===== *)

Lemma mul_opt_le_FIX_MAX (x y : Z) (mode : RoundingMode.t) (r : Z) :
  mul_opt x y mode = Some r ->
  r <= FIX_MAX.
Proof.
  intros H. unfold mul_opt in H.
  apply safeWrap_some_iff in H. destruct H as [Hle Heq]. subst r. exact Hle.
Qed.

Lemma mul_opt_nonneg (x y : Z) (mode : RoundingMode.t) (r : Z) :
  0 <= x ->
  0 <= y ->
  mul_opt x y mode = Some r ->
  0 <= r.
Proof.
  intros Hx Hy H. unfold mul_opt in H.
  apply safeWrap_some_iff in H. destruct H as [_ Heq]. subst r.
  unfold mul, divrnd.
  assert (Hxy : 0 <= x * y) by (apply Z.mul_nonneg_nonneg; assumption).
  assert (HS : 0 < FIX_SCALE) by (vm_compute; reflexivity).
  assert (Hq : 0 <= x * y / FIX_SCALE) by (apply Z.div_pos; lia).
  destruct mode.
  - exact Hq.
  - destruct (x * y mod FIX_SCALE >? (FIX_SCALE - 1) / 2); lia.
  - destruct (x * y mod FIX_SCALE =? 0); lia.
Qed.

(** ===== Comparisons ===== *)

Lemma lt_irrefl (x : Z) :
  lt x x = false.
Proof. unfold lt. apply Z.ltb_irrefl. Qed.

Lemma lte_refl (x : Z) :
  lte x x = true.
Proof. unfold lte. apply Z.leb_refl. Qed.

Lemma eq_refl (x : Z) :
  eq x x = true.
Proof. unfold eq. apply Z.eqb_refl. Qed.

Lemma lt_lte (x y : Z) :
  lt x y = true -> lte x y = true.
Proof.
  unfold lt, lte. intros H.
  apply Z.ltb_lt in H. apply Z.leb_le. lia.
Qed.

Lemma lte_antisym (x y : Z) :
  lte x y = true -> lte y x = true -> x = y.
Proof.
  unfold lte. intros H1 H2.
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma neq_iff (x y : Z) :
  neq x y = true <-> x <> y.
Proof.
  unfold neq. split; intros H.
  - apply Bool.negb_true_iff in H. apply Z.eqb_neq in H. exact H.
  - apply Bool.negb_true_iff. apply Z.eqb_neq. exact H.
Qed.

Lemma gt_iff (x y : Z) :
  gt x y = true <-> y < x.
Proof.
  unfold gt. split; intros H.
  - apply Z.ltb_lt in H. exact H.
  - apply Z.ltb_lt. exact H.
Qed.

Lemma gte_iff (x y : Z) :
  gte x y = true <-> y <= x.
Proof.
  unfold gte. split; intros H.
  - apply Z.leb_le in H. exact H.
  - apply Z.leb_le. exact H.
Qed.

(** ===== powu_two: square of one is one ===== *)

Lemma powu_two :
  powu FIX_ONE 2 = FIX_ONE.
Proof.
  apply powu_one_base.
Qed.

End FixLibAlgebra.
