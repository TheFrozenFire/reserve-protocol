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

(** ===== queue_fifo on rev: popping the back preserves FIFO =====

    If [q] is FIFO-ordered (non-decreasing [availableAt]) and [q = q'
    ++ [w]] (i.e., [w] is the back entry), then [q'] is also FIFO. *)
Lemma queue_fifo_removelast
    (q : list StRSR.Withdrawal.t) (w : StRSR.Withdrawal.t) :
  StRSR.queue_fifo (q ++ [w]) ->
  StRSR.queue_fifo q.
Proof.
  induction q as [|x rest IH]; intros Hfifo.
  - simpl. exact I.
  - destruct rest as [|y rest'] eqn:Erest.
    + simpl. exact I.
    + simpl in Hfifo. simpl.
      change ((x :: y :: rest') ++ [w]) with (x :: ((y :: rest') ++ [w])) in Hfifo.
      change (StRSR.queue_fifo (x :: ((y :: rest') ++ [w])))
        with (x.(StRSR.Withdrawal.availableAt) <=
              (match (y :: rest') ++ [w] with
               | [] => x
               | w' :: _ => w'
               end).(StRSR.Withdrawal.availableAt) /\
              StRSR.queue_fifo ((y :: rest') ++ [w]))
        in Hfifo.
      destruct Hfifo as [Hxy Hrest].
      change ((y :: rest') ++ [w]) with (y :: (rest' ++ [w])) in Hxy.
      simpl in Hxy.
      split.
      * exact Hxy.
      * apply IH. exact Hrest.
Qed.

(** ===== sum_rsr_amounts on rev: a snoc accounting helper =====

    Convenience wrapper of [sum_rsr_amounts_snoc] re-stating the
    decomposition for [rev (w :: rev_rest) = (rev rev_rest) ++ [w]]. *)
Lemma sum_rsr_amounts_app
    (q1 q2 : list StRSR.Withdrawal.t) :
  StRSR.sum_rsr_amounts (q1 ++ q2)
    = StRSR.sum_rsr_amounts q1 + StRSR.sum_rsr_amounts q2.
Proof.
  induction q1 as [|x rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** ===== cancelUnstake_last_preserves_validity =====

    [cancelUnstake_last] pops the back of the queue (the most recently
    enqueued entry) and re-stakes its [rsrAmount] at the current
    exchange rate. Validity preservation cases on whether the queue is
    empty (no-op) or non-empty (one-step LIFO pop).

    Field-by-field:
      - [totalStRSR_nonneg]   genesis branch: minted = rsrAmount >= 0
                              (entries are non-negative). Active
                              branch: minted = floor(rsrAmount * FIX_ONE
                              / rate) >= 0 by FLOOR-divrnd of
                              non-negative by non-negative.
      - [totalRSRStaked_nonneg] adds rsrAmount >= 0 to a non-negative
                              field.
      - [rewards_nonneg]      unchanged.
      - [ratio_in_range]      unchanged.
      - [queue_ordered]       removing the last entry of a FIFO-ordered
                              list keeps it FIFO ([queue_fifo_removelast]).
      - [draftRSR_nonneg]     draftRSR >= sum_rsr_amounts queue >=
                              rsrAmount, so draftRSR - rsrAmount >= 0.
      - [queue_drafts_le_draftRSR] sum_rsr_amounts (q' ++ [w]) =
                              sum(q') + rsrAmount, so post-cancel
                              sum(q') = sum(full queue) - rsrAmount
                              <= draftRSR - rsrAmount. *)

Lemma cancelUnstake_last_preserves_validity
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  StRSR.Valid.t (StRSR.cancelUnstake_last s).
Proof.
  intros Hv. pose proof Hv as Hv0.
  destruct Hv as [Hst Hstk Hrew Hratio Hfifo Hdr Hcons Hent].
  unfold StRSR.cancelUnstake_last.
  destruct (List.rev s.(StRSR.Storage.queue)) as [|w rest_rev] eqn:Erev.
  - (* empty rev -> queue is empty -> no-op *)
    exact Hv0.
  - (* non-empty rev: w is the original back of the queue *)
    set (qFront := List.rev rest_rev).
    (* From [rev queue = w :: rest_rev], the original queue is
       [rev (w :: rest_rev)] = [(rev rest_rev) ++ [w]] = [qFront ++ [w]]. *)
    assert (Hqdecomp : s.(StRSR.Storage.queue) = qFront ++ [w]).
    { unfold qFront.
      replace s.(StRSR.Storage.queue) with (List.rev (List.rev s.(StRSR.Storage.queue))).
      - rewrite Erev. simpl. reflexivity.
      - apply List.rev_involutive.
    }
    assert (HwIn : List.In w s.(StRSR.Storage.queue)).
    { rewrite Hqdecomp. apply List.in_or_app. right. simpl. left. reflexivity. }
    assert (HwNN : 0 <= w.(StRSR.Withdrawal.rsrAmount)) by (apply Hent; exact HwIn).
    assert (HfrontIn : forall w', List.In w' qFront ->
                                  List.In w' s.(StRSR.Storage.queue)).
    { intros w' Hin'. rewrite Hqdecomp. apply List.in_or_app. left. exact Hin'. }
    assert (HfrontNN : forall w', List.In w' qFront ->
                                  0 <= w'.(StRSR.Withdrawal.rsrAmount))
      by (intros w' Hin'; apply Hent; apply HfrontIn; exact Hin').
    assert (HfrontFIFO : StRSR.queue_fifo qFront).
    { rewrite Hqdecomp in Hfifo. apply (queue_fifo_removelast qFront w Hfifo). }
    assert (HsumDecomp :
              StRSR.sum_rsr_amounts s.(StRSR.Storage.queue) =
              StRSR.sum_rsr_amounts qFront + w.(StRSR.Withdrawal.rsrAmount)).
    { rewrite Hqdecomp. apply sum_rsr_amounts_snoc. }
    assert (HsumFront_nn : 0 <= StRSR.sum_rsr_amounts qFront)
      by (apply sum_rsr_amounts_nonneg; exact HfrontNN).
    assert (HwLeDR : w.(StRSR.Withdrawal.rsrAmount) <= s.(StRSR.Storage.draftRSR))
      by lia.
    set (minted :=
      if s.(StRSR.Storage.totalStRSR) =? 0 then
        w.(StRSR.Withdrawal.rsrAmount)
      else
        FixLib.divrnd (w.(StRSR.Withdrawal.rsrAmount) * StRSR.FIX_ONE_Z)
                      (StRSR.exchange_rate s) RoundingMode.FLOOR).
    assert (Hminted_nn : 0 <= minted).
    { unfold minted.
      destruct (s.(StRSR.Storage.totalStRSR) =? 0) eqn:Heq.
      - exact HwNN.
      - apply divrnd_nonneg_floor.
        + apply Z.mul_nonneg_nonneg; [exact HwNN|].
          unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE. lia.
        + apply exchange_rate_nonneg. exact Hv0.
    }
    constructor; simpl.
    + (* totalStRSR + minted >= 0 *)
      lia.
    + (* totalRSRStaked + rsrAmount >= 0 *)
      lia.
    + exact Hrew.
    + exact Hratio.
    + exact HfrontFIFO.
    + (* draftRSR - rsrAmount >= 0 *)
      lia.
    + (* sum_rsr_amounts qFront <= draftRSR - rsrAmount *)
      lia.
    + (* every entry in qFront has rsrAmount >= 0 *)
      exact HfrontNN.
Qed.

End StRSRValidity.
