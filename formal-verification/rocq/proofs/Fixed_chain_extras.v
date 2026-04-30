(** FixLib chain — additional composition lemmas.

    Small follow-ups to proofs/Fixed_chain.v: tight inequalities and
    idempotence facts that didn't fit the original chain file but are
    useful as chain-level identities (relate one operation expressed in
    one rounding mode to the same operation in another, or simplify a
    rounding-mode-aware divrnd to plain Z division when the remainder
    is zero).

    Coverage:
      - mul_ROUND_le_FLOOR_plus_one: [mul x y ROUND <= mul x y FLOOR + 1].
        ROUND never exceeds FLOOR by more than one ULP — composes RD-2
        (FLOOR <= ROUND <= CEIL) with RD-4 (CEIL <= FLOOR + 1).
      - divrnd_idempotent_when_zero_remainder: when [d > 0] and [d ∣ n],
        every rounding mode collapses to plain [Z] division. The rounding
        mode is irrelevant when there's nothing to round.
      - mul_ROUND_eq_FLOOR_when_exact: corollary — when [FIX_SCALE ∣ x*y],
        [mul x y ROUND = mul x y FLOOR]. Lifts the divrnd identity to mul.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.

Module FixLibChainExtras.

Import FixLib.
Import FixLibProofs.

(** ===== ROUND is at most FLOOR + 1 =====

    Compose [divrnd_round_le_ceil] (RD-3) with [divrnd_ceil_le_floor_plus_one]
    (RD-4). Used when bounding the gap between rounding modes on a [mul]. *)
Lemma mul_ROUND_le_FLOOR_plus_one (x y : Z) :
  mul x y RoundingMode.ROUND <= mul x y RoundingMode.FLOOR + 1.
Proof.
  unfold mul.
  assert (HS : 0 < FIX_SCALE) by (vm_compute; reflexivity).
  pose proof (divrnd_round_le_ceil (x * y) FIX_SCALE HS) as H1.
  pose proof (divrnd_ceil_le_floor_plus_one (x * y) FIX_SCALE HS) as H2.
  lia.
Qed.

(** ===== Rounding is irrelevant when the divisor divides exactly =====

    If [d > 0] and [n mod d = 0], then [divrnd n d mode = n / d] for every
    rounding mode. Simplifies chains like [div (mul x FIX_ONE _) FIX_ONE _]
    where intermediate exact divisions appear. *)
Lemma divrnd_idempotent_when_zero_remainder (n d : Z) (mode : RoundingMode.t) :
  0 < d ->
  n mod d = 0 ->
  divrnd n d mode = n / d.
Proof.
  intros Hd Hmod.
  unfold divrnd.
  destruct mode.
  - reflexivity.
  - rewrite Hmod.
    destruct (0 >? (d - 1) / 2) eqn:HC; [|reflexivity].
    apply Z.gtb_lt in HC.
    assert ((d - 1) / 2 >= 0).
    { apply Z.le_ge. apply Z.div_pos; lia. }
    lia.
  - rewrite Hmod. simpl. reflexivity.
Qed.

(** ===== ROUND collapses to FLOOR when [FIX_SCALE | x*y] =====

    Corollary lifting [divrnd_idempotent_when_zero_remainder] to [mul]:
    when the inner product is exactly divisible by FIX_SCALE, the rounding
    mode chosen for [mul] doesn't matter. *)
Lemma mul_ROUND_eq_FLOOR_when_exact (x y : Z) :
  (x * y) mod FIX_SCALE = 0 ->
  mul x y RoundingMode.ROUND = mul x y RoundingMode.FLOOR.
Proof.
  intros Hmod. unfold mul.
  rewrite (divrnd_idempotent_when_zero_remainder _ _ RoundingMode.ROUND).
  - rewrite (divrnd_idempotent_when_zero_remainder _ _ RoundingMode.FLOOR);
      [reflexivity | unfold FIX_SCALE; lia | exact Hmod].
  - unfold FIX_SCALE; lia.
  - exact Hmod.
Qed.

End FixLibChainExtras.
