(** GnosisTrade validity-preservation lemmas.

    Two narrow output-bound invariants on the [GnosisTrade] simulation
    that complement the safety properties already proved in
    [proofs/GnosisTrade.v]:

      1. [worstCasePrice_zero_mba] — when the input [minBuyAmount] is 0,
         the on-chain [worstCasePrice] also pegs at 0. Documents that
         the FLOOR-divu chain has no spurious lower-bound bias from a
         zero numerator: a zero-floor minBuyAmount really is a
         zero worst-case.

      2. [settlement_floor_le_ceil_raw] — the [settlement_floor] output
         is bounded above by the unclipped CEIL rational
         [ceil(worstCase * max(soldAmt, 1) / D27_ONE)]. This is a tight
         upper bound on the qBuyTok floor that the bidder must clear,
         and it propagates directly into the uint256-fit obligation on
         the on-chain settlement check.

    Companion proofs in [proofs/GnosisTrade.v] provide the matching
    lower bounds ([minBuyAmount_nonneg], [settlement_floor_nonneg])
    and monotonicity properties.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.GnosisTrade.

Module GnosisTradeValidity.

Import FixLib.
Import GnosisTrade.

(** ===== worstCasePrice_zero_mba: zero floor maps to zero price. =====

    The [sa = 0] branch of [worstCasePrice] returns 0 directly; the
    non-zero branch divides 0 by sa under FLOOR rounding, which is also
    0 (every rounding mode is 0-preserving on a zero numerator). *)
Lemma worstCasePrice_zero_mba (sa : Z) :
  worstCasePrice 0 sa = 0.
Proof.
  unfold worstCasePrice, shiftl_toFix_d27.
  destruct (sa =? 0) eqn:Hzero.
  - reflexivity.
  - apply Z.eqb_neq in Hzero.
    rewrite Z.mul_0_l.
    unfold FixLib.divrnd.
    rewrite Z.div_0_l by exact Hzero.
    reflexivity.
Qed.

(** ===== settlement_floor_le_ceil_raw: tight upper bound on the floor.

    The [settlement_floor] is defined as
       max(0, ceil(worstCase * max(soldAmt, 1) / D27_ONE) - 1)
    so given [0 <= worstCase] (the on-chain uint192 invariant on
    worstCasePrice), it is bounded above by the unclipped CEIL. This
    is the bound that justifies the on-chain settlement amount fitting
    in uint256 whenever the inputs do. *)
Lemma settlement_floor_le_ceil_raw (worstCase soldAmt : Z) :
  0 <= worstCase ->
  settlement_floor worstCase soldAmt
  <= divrnd (worstCase * Z.max soldAmt 1) D27_ONE RoundingMode.CEIL.
Proof.
  intros Hwcp.
  unfold settlement_floor.
  set (adj := Z.max soldAmt 1).
  assert (Hadj : 1 <= adj) by (unfold adj; lia).
  set (ceil := divrnd (worstCase * adj) D27_ONE RoundingMode.CEIL).
  assert (Hnum_nn : 0 <= worstCase * adj) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hd_pos : 0 < D27_ONE) by (unfold D27_ONE; lia).
  (* ceil is non-negative: numerator nonneg, denominator positive. *)
  assert (Hceil_nn : 0 <= ceil).
  { unfold ceil, FixLib.divrnd.
    assert (Hq : 0 <= (worstCase * adj) / D27_ONE)
      by (apply Z.div_pos; lia).
    destruct ((worstCase * adj) mod D27_ONE =? 0); lia. }
  unfold ceil in *. lia.
Qed.

End GnosisTradeValidity.
