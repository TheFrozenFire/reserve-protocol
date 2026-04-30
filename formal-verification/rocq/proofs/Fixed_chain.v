(** FixLib composition / chaining lemmas.

    Small algebraic identities about composing FixLib operations.
    Builds on proofs/Fixed.v and proofs/Fixed_algebra.v.

    Coverage:
      - mul_then_div_inverse_at_FIX_ONE: [div (mul x FIX_ONE FLOOR) FIX_ONE FLOOR = x]
        for non-negative [x]. Multiplying by [FIX_ONE] and then dividing by
        [FIX_ONE] is the identity at FLOOR — both directions cancel exactly.
      - divrnd_floor_chain: chained FLOOR divisions equal a single division
        by the product, [divrnd (divrnd a b FLOOR) c FLOOR = a / (b * c)],
        when both divisors are positive and the dividend is non-negative.
        This is exactly the [Z.div_div] identity, lifted into FixLib's
        [divrnd] surface.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.

Module FixLibChain.

Import FixLib.
Import FixLibProofs.

(** ===== mul then div by FIX_ONE round-trips at FLOOR =====

    For non-negative x, [mul x FIX_ONE FLOOR] equals [x] (no rounding —
    the product divides FIX_SCALE evenly), and [div x FIX_ONE FLOOR]
    likewise returns [x]. Composing the two is the identity. *)
Lemma mul_then_div_inverse_at_FIX_ONE (x : Z) :
  0 <= x ->
  div (mul x FIX_ONE RoundingMode.FLOOR) FIX_ONE RoundingMode.FLOOR = x.
Proof.
  intros Hx.
  unfold mul, div, divrnd, FIX_ONE, FIX_SCALE.
  rewrite Z.div_mul by (vm_compute; discriminate).
  rewrite Z.div_mul by (vm_compute; discriminate).
  reflexivity.
Qed.

(** ===== Chained FLOOR division =====

    [divrnd (divrnd a b FLOOR) c FLOOR = a / (b * c)] when [b, c > 0]
    and [a >= 0]. Reduces to [Z.div_div], a standard library identity. *)
Lemma divrnd_floor_chain (a b c : Z) :
  0 <= a ->
  0 < b ->
  0 < c ->
  divrnd (divrnd a b RoundingMode.FLOOR) c RoundingMode.FLOOR
    = a / (b * c).
Proof.
  intros Ha Hb Hc.
  unfold divrnd.
  rewrite Z.div_div by lia.
  reflexivity.
Qed.

End FixLibChain.
