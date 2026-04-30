(** Collateral uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and
    [proofs/Throttle_uint256_bounds.v]. The Collateral [Valid.t]
    predicate (in [simulations/Collateral.v]) carries:
      - [whenDefault]            in [0, UINT48_MAX]
      - [exposedReferencePrice]  in [0, FIX_MAX]      (uint192 ceiling)
      - [delayUntilDefault]      in [0, 1209600]      (2 weeks; uint48)
      - [revenueShowing]         in [0, FIX_ONE]
    but leaves the two immutable peg bands [pegBottom] / [pegTop]
    without an explicit upper bound. On-chain those are uint192 storage
    words and therefore necessarily fit in uint256.

    Production has those ceilings by EVM semantics (every storage word is
    a [uint256], and arithmetic that would overflow reverts under Solidity
    0.8). This file closes the gap *without modifying the existing
    simulation or [Valid.t]* by introducing a separate [InputBounded]
    predicate that captures the missing upper bounds, proves [refresh]
    preserves it under a natural call-boundary hypothesis on the
    next-state [exposedReferencePrice], and exposes per-field projection
    lemmas.

    Preservation hypotheses are stated at the call boundary as "the
    next-state value still fits in uint256", mirroring the on-chain
    [_safeWrap] revert behaviour: production guarantees boundedness by
    reverting whenever the next-state arithmetic would overflow, so a
    successful return path is exactly the path on which the next-state
    bound holds. We model that here as an explicit hypothesis, which is
    the cleanest available proxy for the EVM's revert.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.proofs.Collateral_validity.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module CollateralUint256Bounds.

Import FixLib.
Import Collateral.

(** ---------- InputBounded predicate ----------

    Captures the two uint256 upper bounds that [Valid.t] omits — the
    immutable peg band [pegBottom] / [pegTop] are uint192 on chain but
    [Valid.t] only constrains [revenueShowing] and the cached price.
    Kept as a separate record so we can compose it with [Valid.t] at use
    sites without changing the existing module surface.

    The remaining numeric fields are bounded by [Valid.t]:
      - [whenDefault]            <= UINT48_MAX  < UINT256_MAX
      - [exposedReferencePrice]  <= FIX_MAX     < UINT256_MAX
      - [delayUntilDefault]      <= 1209600     < UINT256_MAX
      - [revenueShowing]         <= FIX_ONE     < UINT256_MAX
    so these need no extra hypothesis — see the joint-bound lemma below. *)
Module InputBounded.
  Record t (st : State.t) : Prop := {
    pegBottom_u256 : st.(State.pegBottom) <= UINT256_MAX;
    pegTop_u256    : st.(State.pegTop)    <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Trivial corollaries for use at integration sites that have
    [Valid.t st /\ InputBounded.t st] in scope and only need one of the
    field bounds. *)

Lemma Collateral_pegBottom_bounded
    (st : State.t) :
  Valid.t st ->
  InputBounded.t st ->
  st.(State.pegBottom) <= UINT256_MAX.
Proof. intros _ [H _]. exact H. Qed.

Lemma Collateral_pegTop_bounded
    (st : State.t) :
  Valid.t st ->
  InputBounded.t st ->
  st.(State.pegTop) <= UINT256_MAX.
Proof. intros _ [_ H]. exact H. Qed.

(** Bounds derivable from [Valid.t] alone — included for symmetry with the
    StRSR/Throttle projection lemmas. *)

Lemma Collateral_whenDefault_bounded
    (st : State.t) :
  Valid.t st ->
  st.(State.whenDefault) <= UINT256_MAX.
Proof.
  intros [Hwd _ _ _].
  unfold UINT48_MAX, UINT256_MAX in *.
  assert (H48_le : 2 ^ 48 - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

Lemma Collateral_exposedReferencePrice_bounded
    (st : State.t) :
  Valid.t st ->
  st.(State.exposedReferencePrice) <= UINT256_MAX.
Proof.
  intros [_ Hexp _ _].
  unfold FIX_MAX, UINT256_MAX in *.
  assert (Hfm_le : 2 ^ 192 - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

(** ---------- preservation: refresh ----------

    [refresh] only mutates [whenDefault] (via [markStatus]) and
    [exposedReferencePrice] (via [updateExposed]); [delayUntilDefault],
    [revenueShowing], [pegBottom], [pegTop] are passed through unchanged
    by the record literal. So the [pegBottom] / [pegTop] uint256 bounds
    carry through automatically. *)
(** Helper: [refresh] does not touch [pegBottom]. *)
Lemma refresh_pegBottom_unchanged
    (st : State.t) (underlying pegPrice low now : Z) :
  (refresh st underlying pegPrice low now).(State.pegBottom)
    = st.(State.pegBottom).
Proof.
  unfold refresh.
  destruct (updateExposed _ _ _) as [new_exposed defaulted].
  reflexivity.
Qed.

(** Helper: [refresh] does not touch [pegTop]. *)
Lemma refresh_pegTop_unchanged
    (st : State.t) (underlying pegPrice low now : Z) :
  (refresh st underlying pegPrice low now).(State.pegTop)
    = st.(State.pegTop).
Proof.
  unfold refresh.
  destruct (updateExposed _ _ _) as [new_exposed defaulted].
  reflexivity.
Qed.

Lemma refresh_preserves_input_bounded
    (st : State.t) (underlying pegPrice low now : Z) :
  InputBounded.t st ->
  InputBounded.t (refresh st underlying pegPrice low now).
Proof.
  intros [Hpb Hpt].
  constructor.
  - rewrite refresh_pegBottom_unchanged. exact Hpb.
  - rewrite refresh_pegTop_unchanged. exact Hpt.
Qed.

(** ---------- composition: strengthened EndToEnd-style joint bound ----------

    Sums the six numeric fields the Collateral storage carries:
      - [whenDefault]            <= UINT48_MAX  < UINT256_MAX (Valid.t)
      - [exposedReferencePrice]  <= FIX_MAX     < UINT256_MAX (Valid.t)
      - [delayUntilDefault]      <= 1209600     < UINT256_MAX (Valid.t)
      - [revenueShowing]         <= FIX_ONE     < UINT256_MAX (Valid.t)
      - [pegBottom]              <= UINT256_MAX               (InputBounded)
      - [pegTop]                 <= UINT256_MAX               (InputBounded)
    so the sum is at most [6 * UINT256_MAX]. *)
Lemma Collateral_scalars_jointly_bounded
    (st : State.t) :
  Valid.t st ->
  InputBounded.t st ->
  st.(State.whenDefault)
  + st.(State.exposedReferencePrice)
  + st.(State.delayUntilDefault)
  + st.(State.revenueShowing)
  + st.(State.pegBottom)
  + st.(State.pegTop)
    <= 6 * UINT256_MAX.
Proof.
  intros [Hwd Hexp Hdud Hrs] [Hpb Hpt].
  unfold UINT256_MAX, UINT48_MAX, FIX_MAX, FIX_ONE, FIX_SCALE in *.
  assert (H48_le  : 2 ^ 48  - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  assert (Hfm_le  : 2 ^ 192 - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  assert (Hdud_le : 1209600     <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  assert (Hone_le : 10 ^ 18     <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

End CollateralUint256Bounds.
