(** Rebalance uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and
    [proofs/Throttle_uint256_bounds.v]. The Rebalance simulation's
    [Valid.inputs] predicate (in [simulations/Rebalance.v]) carries
    non-negativity, the bottom/top/supply ordering, slack non-negativity,
    and [supplyTotal <= FIX_MAX = 2^192 - 1]. It does *not* state
    explicit uint256 ceilings on the other [RangeInputs.t] scalar fields:

      - [basketsHeldBottom]
      - [basketsHeldTop]
      - [lowSlack]
      - [highSlack]

    Production has those ceilings by EVM semantics (every storage word is
    a [uint256], and arithmetic that would overflow reverts under Solidity
    0.8). This file closes the gap *without modifying the existing
    simulation or [Valid.inputs]* by introducing a separate [InputBounded]
    predicate that captures the missing upper bounds, derives that the
    [basketRange] outputs (high, low) both fit in uint256, and provides
    a joint bound for downstream callers.

    Preservation hypotheses are stated at the call boundary as "the
    next-state value still fits in uint256", mirroring the on-chain
    [_safeWrap] revert behaviour: production guarantees boundedness by
    reverting whenever the next-state arithmetic would overflow, so a
    successful return path is exactly the path on which the next-state
    bound holds. We model that here as input bounds plus a derivation
    on [basketRange]'s output, which is the cleanest available proxy
    for the EVM's revert.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Rebalance.
Require Import Reserve.proofs.Rebalance_validity.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(** [Z.min] / [Z.max] reduce poorly under [simpl] in this build context;
    keep them opaque so [lia] can manage the goals via the projection
    lemmas we prove below. *)
Opaque Z.min Z.max.

Module RebalanceUint256Bounds.

Import FixLib.
Import RebalanceLib.

(** ---------- InputBounded predicate ----------

    Captures the four uint256 upper bounds that [Valid.inputs] omits.
    Kept as a separate record so we can compose it with [Valid.inputs]
    at use sites without changing the existing module surface.

    [supplyTotal] already lives in [0, FIX_MAX = 2^192 - 1] under
    [Valid.inputs] and is therefore bounded by [UINT256_MAX] without
    further hypothesis. *)
Module InputBounded.
  Record t (i : RangeInputs.t) : Prop := {
    basketsHeldBottom_u256 : i.(RangeInputs.basketsHeldBottom) <= UINT256_MAX;
    basketsHeldTop_u256    : i.(RangeInputs.basketsHeldTop)    <= UINT256_MAX;
    lowSlack_u256          : i.(RangeInputs.lowSlack)          <= UINT256_MAX;
    highSlack_u256         : i.(RangeInputs.highSlack)         <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Trivial corollaries for use at integration sites that have
    [Valid.inputs i /\ InputBounded.t i] in scope and only need one
    of the field bounds. *)

Lemma Rebalance_basketsHeldBottom_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  InputBounded.t i ->
  i.(RangeInputs.basketsHeldBottom) <= UINT256_MAX.
Proof. intros _ [H _ _ _]. exact H. Qed.

Lemma Rebalance_basketsHeldTop_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  InputBounded.t i ->
  i.(RangeInputs.basketsHeldTop) <= UINT256_MAX.
Proof. intros _ [_ H _ _]. exact H. Qed.

Lemma Rebalance_lowSlack_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  InputBounded.t i ->
  i.(RangeInputs.lowSlack) <= UINT256_MAX.
Proof. intros _ [_ _ H _]. exact H. Qed.

Lemma Rebalance_highSlack_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  InputBounded.t i ->
  i.(RangeInputs.highSlack) <= UINT256_MAX.
Proof. intros _ [_ _ _ H]. exact H. Qed.

(** [supplyTotal] is bounded by FIX_MAX = 2^192 - 1 under [Valid.inputs]
    alone, hence by UINT256_MAX. No need for [InputBounded]. *)
Lemma Rebalance_supplyTotal_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  i.(RangeInputs.supplyTotal) <= UINT256_MAX.
Proof.
  intros [_ _ _ _ _ _ _ Hsup].
  unfold UINT256_MAX. unfold FIX_MAX in Hsup.
  assert (Hpow : 2 ^ 192 - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

(** ---------- output bounds: basketRange.high ----------

    The high field of [basketRange] is at most [supplyTotal] by
    [basketRange_high_le_supply] in [proofs/Rebalance_validity.v], and
    [supplyTotal <= FIX_MAX <= UINT256_MAX] under [Valid.inputs]. So
    high fits in uint256 from validity alone — [InputBounded] is not
    even needed for this one. *)
Lemma basketRange_high_le_uint256
    (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.high) <= UINT256_MAX.
Proof.
  intros V.
  pose proof RebalanceValidityProofs.basketRange_high_le_supply i as Hh.
  pose proof Rebalance_supplyTotal_bounded i V as Hs.
  lia.
Qed.

(** ---------- output bounds: basketRange.low ----------

    The low field is the inner [Z.min]: [low <= high]. By the high
    bound above, low <= UINT256_MAX as well. We use the existing
    [basket_range_low_le_high] in [proofs/Rebalance.v] (re-exposed
    via Rebalance_validity's [basketRange_gap_nonneg]). *)
Lemma basketRange_low_le_uint256
    (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.low) <= UINT256_MAX.
Proof.
  intros V.
  pose proof basketRange_high_le_uint256 i V as Hh.
  pose proof RebalanceValidityProofs.basketRange_gap_nonneg i as Hgap.
  lia.
Qed.

(** ---------- joint output bound ----------

    Both (low, high) outputs of [basketRange] fit in uint256 under
    [Valid.inputs]. Useful as a single hypothesis for downstream
    callers that store both bounds in uint256 storage slots. *)
Lemma basketRange_outputs_u256
    (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.low)  <= UINT256_MAX
  /\ (basketRange i).(BasketRange.high) <= UINT256_MAX.
Proof.
  intros V.
  split.
  - exact (basketRange_low_le_uint256 i V).
  - exact (basketRange_high_le_uint256 i V).
Qed.

(** ---------- composition: strengthened EndToEnd-style joint bound ----------

    Sums the five scalar fields the [RangeInputs.t] record carries.
    Each of:
      - [supplyTotal]       <= FIX_MAX   < UINT256_MAX (from Valid.inputs)
      - [basketsHeldBottom] <= UINT256_MAX (from InputBounded)
      - [basketsHeldTop]    <= UINT256_MAX (from InputBounded)
      - [lowSlack]          <= UINT256_MAX (from InputBounded)
      - [highSlack]         <= UINT256_MAX (from InputBounded)
    so the sum is at most [5 * UINT256_MAX]. *)
Lemma Rebalance_inputs_jointly_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  InputBounded.t i ->
  i.(RangeInputs.supplyTotal)
  + i.(RangeInputs.basketsHeldBottom)
  + i.(RangeInputs.basketsHeldTop)
  + i.(RangeInputs.lowSlack)
  + i.(RangeInputs.highSlack)
    <= 5 * UINT256_MAX.
Proof.
  intros V Hib.
  pose proof Rebalance_supplyTotal_bounded i V as Hsup.
  destruct Hib as [Hbb Hbt Hls Hhs].
  unfold UINT256_MAX in *.
  lia.
Qed.

(** Joint bound on the basketRange outputs together with the supply
    cap, for callers that need a "everything storage-sized" view. *)
Lemma Rebalance_outputs_jointly_bounded
    (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.low)
  + (basketRange i).(BasketRange.high)
  + i.(RangeInputs.supplyTotal)
    <= 3 * UINT256_MAX.
Proof.
  intros V.
  pose proof basketRange_low_le_uint256  i V as Hlo.
  pose proof basketRange_high_le_uint256 i V as Hhi.
  pose proof Rebalance_supplyTotal_bounded i V as Hsup.
  pose proof RebalanceValidityProofs.basketRange_low_nonneg as Hlow_nn.
  (* low_nonneg requires lowSlack <= bhBottom; we don't assume it here.
     But low could be negative — its upper bound still holds. We only
     need <=, not 0 <= low <=. *)
  unfold UINT256_MAX in *.
  lia.
Qed.

End RebalanceUint256Bounds.
