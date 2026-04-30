(** StRSR validity-preservation lemmas.

    Three small lemmas showing that the core StRSR transitions preserve the
    [Valid.t] invariant or its FIFO sub-invariant:

      1. [stake_preserves_validity] — [stake] preserves [Valid.t] given
         [0 <= amount]. Both branches (genesis / active) only add a
         non-negative quantity to [totalStRSR] / [totalRSRStaked] and leave
         [totalRewardsAccumulated], [ratio], [queue] untouched.

      2. [payoutRewards_preserves_validity] — [payoutRewards] preserves
         [Valid.t] given that the computed [payout] is non-negative. The
         early-return branch is identity; the active branch only bumps
         [totalRewardsAccumulated] by [payout] and pushes [lastPayout]
         forward, leaving stake / rate / queue alone.

      3. [enqueue_preserves_fifo] — restatement of [withdrawal_fifo]
         under the [enqueue_preserves_fifo] name; appending a withdrawal
         whose [availableAt] dominates every existing entry's keeps
         [queue_fifo].

    Proof note: we mark [FixLib] operations [Opaque] before the
    case-analysis on the active branch so Coq doesn't unfold [powu] /
    [mulu_toUint] (which contains [Z.to_nat (Z.log2 _)]) and explode the
    term during arithmetic.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Reserve.proofs.StRSR.
Require Import Coq.Lists.List.
Import ListNotations.

Module StRSRValidity.

Import FixLib.

Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd.

(** ---------- helpers ---------- *)

Lemma divrnd_floor_nonneg (n d : Z) :
  0 <= n -> 0 < d -> 0 <= FixLib.divrnd n d RoundingMode.FLOOR.
Proof.
  intros Hn Hd. Transparent FixLib.divrnd. unfold FixLib.divrnd.
  apply Z.div_pos; lia.
Qed.

Opaque FixLib.divrnd.

Lemma exchange_rate_nonneg (s : StRSR.Storage.t) :
  StRSR.Valid.t s -> 0 <= StRSR.exchange_rate s.
Proof.
  intros Hv. destruct Hv as [Hst Hstk Hrew _ _].
  unfold StRSR.exchange_rate.
  destruct (s.(StRSR.Storage.totalStRSR) =? 0) eqn:Heq.
  - unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE. lia.
  - apply Z.eqb_neq in Heq.
    apply divrnd_floor_nonneg.
    + apply Z.mul_nonneg_nonneg.
      * lia.
      * unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE. lia.
    + lia.
Qed.

(** ---------- stake_preserves_validity ---------- *)

Lemma stake_preserves_validity
    (s : StRSR.Storage.t) (amount : U256.t) :
  StRSR.Valid.t s ->
  0 <= amount ->
  StRSR.Valid.t (StRSR.stake s amount).
Proof.
  intros Hv Hamt.
  pose proof Hv as Hv0.
  destruct Hv as [Hst Hstk Hrew Hratio Hq].
  unfold StRSR.stake.
  destruct (s.(StRSR.Storage.totalStRSR) =? 0) eqn:Heq.
  - (* Genesis branch *)
    constructor; simpl.
    + lia.
    + lia.
    + exact Hrew.
    + exact Hratio.
    + exact Hq.
  - (* Active branch *)
    set (rate := StRSR.exchange_rate s).
    set (minted := FixLib.divrnd (amount * StRSR.FIX_ONE_Z) rate RoundingMode.FLOOR).
    apply Z.eqb_neq in Heq.
    assert (Hrate_nn : 0 <= rate) by (apply exchange_rate_nonneg; exact Hv0).
    assert (Hst_pos : 0 < s.(StRSR.Storage.totalStRSR)) by lia.
    (* rate may be 0 (e.g. divrnd of a small numerator); we just need
       0 <= minted, and FLOOR-divrnd by any d (including 0 via Z.div) is
       non-negative for a non-negative numerator. *)
    assert (Hmint_nn : 0 <= minted).
    { unfold minted.
      Transparent FixLib.divrnd. unfold FixLib.divrnd.
      destruct (Z.eq_dec rate 0) as [Hr0|Hr0].
      - rewrite Hr0. rewrite Zdiv_0_r. lia.
      - apply Z.div_pos.
        + apply Z.mul_nonneg_nonneg; [lia|].
          unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE. lia.
        + lia.
    }
    Opaque FixLib.divrnd.
    constructor; simpl.
    + lia.
    + lia.
    + exact Hrew.
    + exact Hratio.
    + exact Hq.
Qed.

(** ---------- payoutRewards_preserves_validity ---------- *)

Lemma payoutRewards_preserves_validity
    (s : StRSR.Storage.t) (now rewardsPool : U256.t) :
  StRSR.Valid.t s ->
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(StRSR.Storage.ratio))
                   (now - s.(StRSR.Storage.lastPayout))) in
  let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
  0 <= payout ->
  StRSR.Valid.t (StRSR.payoutRewards s now rewardsPool).
Proof.
  intros Hv payoutRatio payout Hpay_nn.
  destruct Hv as [Hst Hstk Hrew Hratio Hq].
  unfold StRSR.payoutRewards.
  destruct (now <? s.(StRSR.Storage.lastPayout) + 1) eqn:Hcond.
  - (* Early-return: returns s unchanged *)
    constructor; assumption.
  - (* Active branch *)
    constructor; simpl.
    + exact Hst.
    + exact Hstk.
    + fold payoutRatio. fold payout. lia.
    + exact Hratio.
    + exact Hq.
Qed.

(** ---------- enqueue_preserves_fifo ----------

    Restatement of [withdrawal_fifo] under the [enqueue_preserves_fifo]
    name. Appending [w] to a FIFO-ordered queue keeps the order if [w]'s
    [availableAt] dominates every existing entry's. *)

Lemma enqueue_preserves_fifo
    (q : list StRSR.Withdrawal.t) (w : StRSR.Withdrawal.t) :
  StRSR.queue_fifo q ->
  (forall w', List.In w' q ->
              w'.(StRSR.Withdrawal.availableAt) <= w.(StRSR.Withdrawal.availableAt)) ->
  StRSR.queue_fifo (StRSR.enqueue q w).
Proof.
  exact (StRSRProofs.withdrawal_fifo q w).
Qed.

(** [queue_fifo] is preserved by popping the head: if the cons-cell is
    ordered, so is its tail. Used directly by [withdraw_preserves_validity]
    below. *)
Lemma queue_fifo_tail (w : StRSR.Withdrawal.t) (rest : list StRSR.Withdrawal.t) :
  StRSR.queue_fifo (w :: rest) ->
  StRSR.queue_fifo rest.
Proof.
  intros Hfifo. destruct rest as [|w' rest'].
  - simpl. exact I.
  - simpl in Hfifo. destruct Hfifo as [_ Hrest]. exact Hrest.
Qed.

(** ===== withdraw_preserves_validity =====

    [withdraw] pops the head of the queue if it has matured, otherwise
    no-ops. In both cases the storage scalars are unchanged and the new
    queue is either [rest] (preserving FIFO via [queue_fifo_tail]) or
    the original queue. *)
Lemma withdraw_preserves_validity
    (s : StRSR.Storage.t) (now : U256.t) :
  StRSR.Valid.t s ->
  StRSR.Valid.t (fst (StRSR.withdraw s now)).
Proof.
  intros Hv. unfold StRSR.withdraw.
  destruct s.(StRSR.Storage.queue) as [|w rest] eqn:Hq.
  - (* empty queue: withdraw returns s unchanged. *)
    simpl. exact Hv.
  - (* nonempty queue. *)
    destruct (w.(StRSR.Withdrawal.availableAt) <=? now) eqn:Hready.
    + (* head ready: queue := rest, scalars unchanged. *)
      destruct Hv as [Hst Hstk Hrew Hratio Hfifo].
      simpl. constructor; simpl; auto.
      rewrite Hq in Hfifo. apply (queue_fifo_tail w rest Hfifo).
    + (* head not ready: returns s unchanged. *)
      simpl. exact Hv.
Qed.

End StRSRValidity.
