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
  destruct Hv as [Hst Hstk Hrew Hratio Hq Hdr Hcons Hent].
  unfold StRSR.stake.
  destruct (s.(StRSR.Storage.totalStRSR) =? 0) eqn:Heq.
  - (* Genesis branch *)
    constructor; simpl.
    + lia.
    + lia.
    + exact Hrew.
    + exact Hratio.
    + exact Hq.
    + exact Hdr.
    + exact Hcons.
    + exact Hent.
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
    + exact Hdr.
    + exact Hcons.
    + exact Hent.
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
  destruct Hv as [Hst Hstk Hrew Hratio Hq Hdr Hcons Hent].
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
    + exact Hdr.
    + exact Hcons.
    + exact Hent.
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

(** ===== sum_rsr_amounts auxiliary lemmas =====

    [sum_rsr_amounts] of [q ++ [w]] splits into [sum_rsr_amounts q +
    w.rsrAmount]. Used by [unstake_preserves_validity] (queue grows by
    a snoc) and by [seizeRSR_preserves_validity] (queue is wiped to
    [[]] in the era-reset case). *)

Lemma sum_rsr_amounts_snoc
    (q : list StRSR.Withdrawal.t) (w : StRSR.Withdrawal.t) :
  StRSR.sum_rsr_amounts (q ++ [w])
  = StRSR.sum_rsr_amounts q + w.(StRSR.Withdrawal.rsrAmount).
Proof.
  induction q as [|x rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** [sum_rsr_amounts] of a queue whose entries are all non-negative
    is non-negative. *)
Lemma sum_rsr_amounts_nonneg
    (q : list StRSR.Withdrawal.t) :
  (forall w, List.In w q -> 0 <= w.(StRSR.Withdrawal.rsrAmount)) ->
  0 <= StRSR.sum_rsr_amounts q.
Proof.
  induction q as [|w rest IH]; simpl.
  - lia.
  - intros Hall.
    assert (HwNN : 0 <= w.(StRSR.Withdrawal.rsrAmount))
      by (apply Hall; left; reflexivity).
    assert (HtailNN : forall w', List.In w' rest ->
                                 0 <= w'.(StRSR.Withdrawal.rsrAmount)).
    { intros w' Hin. apply Hall. right. exact Hin. }
    pose proof (IH HtailNN). lia.
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
    + (* head ready: queue := rest, draftRSR -= w.rsrAmount, other scalars unchanged. *)
      destruct Hv as [Hst Hstk Hrew Hratio Hfifo Hdr Hcons Hentries].
      (* The head's rsrAmount is non-negative by [queue_entries_nonneg]
         on the head; the tail keeps that property by the same
         predicate restricted to [rest]. *)
      assert (HwNN : 0 <= w.(StRSR.Withdrawal.rsrAmount)).
      { rewrite Hq in Hentries.
        apply (Hentries w). simpl. left. reflexivity. }
      assert (HtailNN :
        forall w', List.In w' rest ->
                   0 <= w'.(StRSR.Withdrawal.rsrAmount)).
      { intros w' Hin.
        rewrite Hq in Hentries.
        apply Hentries. simpl. right. exact Hin. }
      assert (HsumTail :
        StRSR.sum_rsr_amounts rest <=
          s.(StRSR.Storage.draftRSR) - w.(StRSR.Withdrawal.rsrAmount)).
      { rewrite Hq in Hcons. simpl in Hcons. lia. }
      assert (HsumTail_nn : 0 <= StRSR.sum_rsr_amounts rest)
        by (apply sum_rsr_amounts_nonneg; exact HtailNN).
      simpl. constructor; simpl.
      * exact Hst.
      * exact Hstk.
      * exact Hrew.
      * exact Hratio.
      * rewrite Hq in Hfifo. apply (queue_fifo_tail w rest Hfifo).
      * lia.
      * exact HsumTail.
      * exact HtailNN.
    + (* head not ready: returns s unchanged. *)
      simpl. exact Hv.
Qed.

(** ===== unstake_preserves_validity =====

    [unstake] pushes a withdrawal entry with [rsrAmount = floor(amount
    * rate / FIX_ONE)] (non-negative by FLOOR-divrnd) onto the back of
    the queue, decrements [totalStRSR] by [amount] and [totalRSRStaked]
    by [rsrAmount], and adds [rsrAmount] to [draftRSR]. The validity
    fields divide as:

      - [totalStRSR_nonneg]   needs amount <= totalStRSR (hyp).
      - [totalRSRStaked_nonneg] needs rsrAmount <= totalRSRStaked (hyp).
      - [rewards_nonneg]      unchanged.
      - [ratio_in_range]      unchanged.
      - [queue_ordered]       needs now + delay >= every existing
                              entry's availableAt (hyp; production's
                              [pushDraft] enforces this via the
                              [lastAvailableAt] computation).
      - [draftRSR_nonneg]     follows from old + nonneg.
      - [queue_drafts_le_draftRSR] follows from snoc bookkeeping.
      - [queue_entries_nonneg] follows from the head being non-negative
                              and the predicate on the existing tail. *)

Lemma divrnd_nonneg_floor (n d : Z) :
  0 <= n -> 0 <= d -> 0 <= FixLib.divrnd n d RoundingMode.FLOOR.
Proof.
  intros Hn Hd. Transparent FixLib.divrnd. unfold FixLib.divrnd.
  destruct (Z.eq_dec d 0) as [Hd0|Hd0].
  - rewrite Hd0. rewrite Zdiv_0_r. lia.
  - apply Z.div_pos; lia.
Qed.

Opaque FixLib.divrnd.

Lemma unstake_preserves_validity
    (s : StRSR.Storage.t) (amount now delay : U256.t) :
  StRSR.Valid.t s ->
  0 <= amount ->
  amount <= s.(StRSR.Storage.totalStRSR) ->
  let rate := StRSR.exchange_rate s in
  let rsrAmount :=
    FixLib.divrnd (amount * rate) StRSR.FIX_ONE_Z RoundingMode.FLOOR in
  rsrAmount <= s.(StRSR.Storage.totalRSRStaked) ->
  (forall w', List.In w' s.(StRSR.Storage.queue) ->
              w'.(StRSR.Withdrawal.availableAt) <= now + delay) ->
  StRSR.Valid.t (StRSR.unstake s amount now delay).
Proof.
  intros Hv Hamt_nn Hamt_le rate rsrAmount HrsrLe Hbound.
  pose proof Hv as Hv0.
  destruct Hv as [Hst Hstk Hrew Hratio Hq Hdr Hcons Hent].
  assert (Hrate_nn : 0 <= rate) by (apply exchange_rate_nonneg; exact Hv0).
  assert (HrsrAmt_nn : 0 <= rsrAmount).
  { unfold rsrAmount.
    apply divrnd_nonneg_floor.
    - apply Z.mul_nonneg_nonneg; [exact Hamt_nn|exact Hrate_nn].
    - unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE. lia.
  }
  unfold StRSR.unstake.
  fold rate. fold rsrAmount.
  constructor; simpl.
  - lia.
  - lia.
  - exact Hrew.
  - exact Hratio.
  - apply (enqueue_preserves_fifo s.(StRSR.Storage.queue)
             {| StRSR.Withdrawal.rsrAmount := rsrAmount;
                StRSR.Withdrawal.availableAt := now + delay |}).
    + exact Hq.
    + intros w' Hin. simpl. apply Hbound. exact Hin.
  - lia.
  - unfold StRSR.enqueue.
    rewrite sum_rsr_amounts_snoc.
    simpl.
    lia.
  - intros w' Hin.
    unfold StRSR.enqueue in Hin.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    + apply Hent. exact Hin.
    + simpl in Hin. destruct Hin as [Hweq|Hfalse]; [|contradiction].
      rewrite <- Hweq. simpl. exact HrsrAmt_nn.
Qed.

End StRSRValidity.
