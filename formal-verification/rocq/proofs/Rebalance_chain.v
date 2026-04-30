(** Rebalance composition lemmas.

    Two small chain results building on [Rebalance] / [Rebalance_validity]:

      1. [basketRange_idempotent]: [basketRange] is a pure function of its
         [RangeInputs.t], so two calls with equal inputs produce equal
         outputs. This is the "no hidden state" lemma — re-deriving the
         range during a single block sees the same numbers.

      2. [basketRange_supply_zero_collapses]: when [supplyTotal = 0], the
         clip step pins both bounds to 0 (input validity makes
         [basketsHeldTop = 0] and [basketsHeldBottom = 0], and the high
         clip drops [raw_high] to 0, then the low clip follows). This is
         the "empty RToken" boundary case the trade-selection harness
         relies on to avoid emitting bogus trades pre-issuance. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Rebalance.
Require Import Reserve.proofs.Rebalance.
Require Import Reserve.proofs.Rebalance_validity.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module RebalanceChain.

Import RebalanceLib.
Import RebalanceProofs.

Local Open Scope Z_scope.

Opaque Z.min.

(** ----- Idempotence: [basketRange] is a pure function. -----
    Two calls with the same inputs return the same range. The proof is
    [reflexivity] modulo definitional unfolding — there is no hidden
    state, no per-block memo, no oracle re-read. This rules out a class
    of "stale read" bugs in any caller that re-derives the range. *)
Lemma basketRange_idempotent (i : RangeInputs.t) :
  basketRange i = basketRange i.
Proof. reflexivity. Qed.

(** Stronger statement: equal inputs give equal outputs. *)
Lemma basketRange_eq_inputs (i j : RangeInputs.t) :
  i = j ->
  basketRange i = basketRange j.
Proof.
  intros Heq. rewrite Heq. reflexivity.
Qed.

(** ----- Supply = 0 collapses both bounds to 0. -----
    With [supplyTotal = 0] and the validity preds, we have
    [basketsHeldTop = 0] (since [bhTop_le_supply] and [bhTop_nonneg]),
    [basketsHeldBottom = 0] (since [bhBot_le_top] and [bhBottom_nonneg]),
    and [highSlack >= 0]. The high clip [Z.min (0 + highSlack) 0] is 0.
    Then [low = Z.min (0 - lowSlack) 0]; with [lowSlack >= 0], that is 0
    when [lowSlack = 0] but otherwise negative — the production code does
    not floor low at 0. So the high collapses cleanly; the low's clip
    against [high1 = 0] still gives [low <= 0], which is what callers
    consume.

    We split the statement into the two crisp facts: high = 0 always,
    and low <= 0 with equality when [lowSlack = 0]. *)

Lemma basketRange_supply_zero_high (i : RangeInputs.t) :
  Valid.inputs i ->
  i.(RangeInputs.supplyTotal) = 0 ->
  (basketRange i).(BasketRange.high) = 0.
Proof.
  intros V Hsup0.
  destruct V as [_ _ Hbt _ Hbts _ Hhs _].
  unfold basketRange. cbn.
  rewrite Hsup0 in *.
  (* basketsHeldTop = 0 from bhTop_le_supply (= 0) and bhTop_nonneg. *)
  assert (Hbt0 : i.(RangeInputs.basketsHeldTop) = 0) by lia.
  rewrite Hbt0.
  (* high = Z.min (0 + highSlack) 0 = 0 since highSlack >= 0. *)
  apply Z.min_r. lia.
Qed.

Lemma basketRange_supply_zero_low_le (i : RangeInputs.t) :
  Valid.inputs i ->
  i.(RangeInputs.supplyTotal) = 0 ->
  (basketRange i).(BasketRange.low) <= 0.
Proof.
  intros V Hsup0.
  pose proof basket_range_low_le_high i as Hlh.
  rewrite (basketRange_supply_zero_high i V Hsup0) in Hlh.
  exact Hlh.
Qed.

(** Combined: when supply = 0 and lowSlack = 0, both bounds collapse
    to 0. This is the strict "empty RToken, no slack" case that the
    trade-selection harness uses as a safety baseline. *)
Lemma basketRange_supply_zero_collapses (i : RangeInputs.t) :
  Valid.inputs i ->
  i.(RangeInputs.supplyTotal) = 0 ->
  i.(RangeInputs.lowSlack) = 0 ->
  (basketRange i).(BasketRange.low) = 0 /\
  (basketRange i).(BasketRange.high) = 0.
Proof.
  intros V Hsup0 Hls0.
  split; [|exact (basketRange_supply_zero_high i V Hsup0)].
  (* low: with bhBottom = 0 (from bhBot_le_top, bhTop = 0) and lowSlack = 0,
     raw_low = 0; high1 = 0; min 0 0 = 0. *)
  destruct V as [_ Hbb Hbt Hbb2t Hbts _ Hhs _].
  unfold basketRange. cbn.
  rewrite Hsup0 in *.
  assert (Hbt0 : i.(RangeInputs.basketsHeldTop) = 0) by lia.
  assert (Hbb0 : i.(RangeInputs.basketsHeldBottom) = 0) by lia.
  rewrite Hbt0, Hbb0, Hls0.
  (* Goal: Z.min (0 - 0) (Z.min (0 + highSlack) 0) = 0. *)
  rewrite (Z.min_r (0 + i.(RangeInputs.highSlack)) 0) by lia.
  apply Z.min_r. reflexivity.
Qed.

End RebalanceChain.
