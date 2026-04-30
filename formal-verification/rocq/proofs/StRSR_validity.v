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

(** ===== beginEra_preserves_validity =====

    [beginEra] zeros [totalStRSR] and [totalRSRStaked], increments
    [era], and leaves the draft side, queue, ratio, and rewards
    untouched. All [Valid.t] fields are trivially preserved. *)
Lemma beginEra_preserves_validity (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  StRSR.Valid.t (StRSR.beginEra s).
Proof.
  intros Hv. destruct Hv as [_ _ Hrew Hratio Hfifo Hdr Hcons Hent].
  unfold StRSR.beginEra.
  constructor; simpl.
  - lia.
  - lia.
  - exact Hrew.
  - exact Hratio.
  - exact Hfifo.
  - exact Hdr.
  - exact Hcons.
  - exact Hent.
Qed.

(** ===== beginDraftEra_preserves_validity =====

    [beginDraftEra] zeros [draftRSR] and the queue. All [Valid.t]
    fields are preserved or trivially discharged on the empty queue. *)
Lemma beginDraftEra_preserves_validity (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  StRSR.Valid.t (StRSR.beginDraftEra s).
Proof.
  intros Hv. destruct Hv as [Hst Hstk Hrew Hratio _ _ _ _].
  unfold StRSR.beginDraftEra.
  constructor; simpl.
  - exact Hst.
  - exact Hstk.
  - exact Hrew.
  - exact Hratio.
  - exact I.
  - lia.
  - simpl. lia.
  - intros w Hin. simpl in Hin. contradiction.
Qed.

(** ===== seizeRSR_preserves_validity =====

    [seizeRSR] has four branches:

      1. [totalRSR = 0]: no-op (returns [s] unchanged).
      2. neither stake_reset nor draft_reset: proportional split,
         pools shrink by [stake_share] and [draft_share].
      3. stake_reset only: post-split stake pool is wiped via
         [beginEra]; draft side keeps its split.
      4. both stake_reset and draft_reset: both pools wiped.
      5. draft_reset only: stake side keeps split, draft side wiped.

    Validity preservation in each branch reduces to:
      - non-negativity of the post-split residues (precondition that
        [rsrAmount <= totalRSR], which the proof carries explicitly);
      - the [stake_share + draft_share = rsrAmount] split (by
        construction of [draft_share = rsrAmount - stake_share]);
      - the conservation invariant on the draft side, which is
        preserved when the queue is left intact (the sum doesn't
        increase, draftRSR drops by draft_share which is at most
        draftRSR by precondition);
      - in the era-reset branches, the wiped pool's invariants are
        trivially restored. *)

(** ===== seizeRSR auxiliary lemmas =====

    Helper lemmas about the proportional split. Kept abstract over
    the storage so the main [seizeRSR_preserves_validity] proof
    factors cleanly. *)

(** [stake_share = ceil(stakeRSR * rsrAmount / totalRSR)] is
    non-negative when both inputs are non-negative. *)
Lemma stake_share_nonneg
    (stakeRSR rsrAmount totalRSR : Z) :
  0 <= stakeRSR ->
  0 <= rsrAmount ->
  0 < totalRSR ->
  0 <= FixLib.divrnd (stakeRSR * rsrAmount) totalRSR RoundingMode.CEIL.
Proof.
  intros Hs Hr Ht. Transparent FixLib.divrnd. unfold FixLib.divrnd.
  destruct ((stakeRSR * rsrAmount) mod totalRSR =? 0).
  - apply Z.div_pos; [apply Z.mul_nonneg_nonneg|]; lia.
  - assert (HM : 0 <= (stakeRSR * rsrAmount) / totalRSR).
    { apply Z.div_pos; [apply Z.mul_nonneg_nonneg|]; lia. }
    lia.
Qed.

Opaque FixLib.divrnd.

(** [stake_share <= rsrAmount] when [stakeRSR <= totalRSR]: the
    proportional split never gives the stake side more than the
    total to be seized. *)
Lemma stake_share_le_rsrAmount
    (stakeRSR rsrAmount totalRSR : Z) :
  0 <= stakeRSR ->
  0 <= rsrAmount ->
  0 < totalRSR ->
  stakeRSR <= totalRSR ->
  FixLib.divrnd (stakeRSR * rsrAmount) totalRSR RoundingMode.CEIL <= rsrAmount.
Proof.
  intros Hs Hr Ht Hsl. Transparent FixLib.divrnd. unfold FixLib.divrnd.
  set (n := stakeRSR * rsrAmount).
  assert (Hn_le : n <= rsrAmount * totalRSR).
  { unfold n. rewrite (Z.mul_comm rsrAmount totalRSR).
    apply Z.mul_le_mono_nonneg_r; lia. }
  destruct (n mod totalRSR =? 0) eqn:Hzero.
  - (* FLOOR branch *)
    apply Z.div_le_upper_bound; lia.
  - (* CEIL branch: result = floor + 1, need floor + 1 <= rsrAmount,
       i.e. n / totalRSR < rsrAmount. *)
    apply Z.eqb_neq in Hzero.
    pose proof (Z.div_mod n totalRSR ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound n totalRSR Ht) as [Hmlb Hmub].
    set (q := n / totalRSR).
    set (r := n mod totalRSR).
    fold q r in Hdm, Hmlb, Hmub, Hzero.
    (* Goal: q + 1 <= rsrAmount.
       From Hdm: n = totalRSR * q + r, with 0 <= r < totalRSR.
       Hzero: r != 0, so r >= 1.
       Hn_le: n <= rsrAmount * totalRSR.
       Combined: totalRSR * q + r <= rsrAmount * totalRSR,
       so totalRSR * q <= rsrAmount * totalRSR - r <= rsrAmount * totalRSR - 1
       so q <= (rsrAmount * totalRSR - 1) / totalRSR < rsrAmount.
       That is, q + 1 <= rsrAmount. *)
    assert (Hr_pos : 1 <= r) by lia.
    assert (Htot_q : totalRSR * q + 1 <= rsrAmount * totalRSR) by lia.
    nia.
Qed.

Opaque FixLib.divrnd.

Opaque FixLib.divrnd.

(** [stake_share <= stakeRSR]: the proportional split never takes more
    from the stake pool than the pool itself contains. *)
Lemma stake_share_le_stakeRSR
    (stakeRSR rsrAmount totalRSR : Z) :
  0 <= stakeRSR ->
  0 <= rsrAmount ->
  0 < totalRSR ->
  rsrAmount <= totalRSR ->
  FixLib.divrnd (stakeRSR * rsrAmount) totalRSR RoundingMode.CEIL <= stakeRSR.
Proof.
  intros Hs Hr Ht Hrl. Transparent FixLib.divrnd. unfold FixLib.divrnd.
  set (n := stakeRSR * rsrAmount).
  assert (Hn_le : n <= stakeRSR * totalRSR).
  { unfold n. apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (n mod totalRSR =? 0) eqn:Hzero.
  - apply Z.div_le_upper_bound; [lia|].
    rewrite Z.mul_comm. exact Hn_le.
  - apply Z.eqb_neq in Hzero.
    set (q := n / totalRSR).
    set (r := n mod totalRSR).
    pose proof (Z.div_mod n totalRSR ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound n totalRSR Ht) as [Hmlb Hmub].
    fold q r in Hdm, Hmlb, Hmub, Hzero.
    assert (Hr_pos : 1 <= r) by lia.
    (* From n = totalRSR*q + r, n <= stakeRSR*totalRSR, r >= 1:
       totalRSR*q + 1 <= stakeRSR*totalRSR, so q + 1 <= stakeRSR. *)
    assert (Htot_q : totalRSR * q + 1 <= stakeRSR * totalRSR) by lia.
    nia.
Qed.

Opaque FixLib.divrnd.

Opaque FixLib.divrnd.

(** [stake_share >= rsrAmount - draftRSR] when [rsrAmount <= stakeRSR
    + draftRSR] and the pool decomposition holds. By construction
    stake_share + draft_share = rsrAmount, so draft_share <= draftRSR
    iff stake_share >= rsrAmount - draftRSR. We prove this via the
    CEIL lower bound:
        stake_share >= stakeRSR * rsrAmount / totalRSR
    and the algebraic fact that
        rsrAmount - draftRSR <= stakeRSR * rsrAmount / totalRSR
    when rsrAmount <= totalRSR (= stakeRSR + draftRSR). *)
Lemma stake_share_ge_rsrAmount_minus_draftRSR
    (stakeRSR draftRSR rsrAmount : Z) :
  0 <= stakeRSR ->
  0 <= draftRSR ->
  0 <= rsrAmount ->
  rsrAmount <= stakeRSR + draftRSR ->
  0 < stakeRSR + draftRSR ->
  rsrAmount - draftRSR
    <= FixLib.divrnd (stakeRSR * rsrAmount) (stakeRSR + draftRSR)
                     RoundingMode.CEIL.
Proof.
  intros Hs Hd Hr Hra Htot.
  set (totalRSR := stakeRSR + draftRSR).
  fold totalRSR.
  Transparent FixLib.divrnd. unfold FixLib.divrnd.
  set (n := stakeRSR * rsrAmount).
  (* The key fact: rsrAmount - draftRSR <= n / totalRSR (FLOOR bound).
     Multiply by totalRSR: (rsrAmount - draftRSR) * totalRSR <= n.
     LHS = (rsrAmount - draftRSR) * (stakeRSR + draftRSR).
     RHS = stakeRSR * rsrAmount.
     LHS = stakeRSR * rsrAmount + draftRSR * rsrAmount
           - stakeRSR * draftRSR - draftRSR^2.
     LHS <= RHS iff
       draftRSR * rsrAmount - stakeRSR * draftRSR - draftRSR^2 <= 0
       iff draftRSR * (rsrAmount - stakeRSR - draftRSR) <= 0
       iff draftRSR * (rsrAmount - totalRSR) <= 0
       iff true (rsrAmount <= totalRSR, draftRSR >= 0). *)
  assert (Hkey : (rsrAmount - draftRSR) * totalRSR <= n).
  { unfold n, totalRSR.
    (* Expand and reduce. *)
    nia. }
  destruct (n mod totalRSR =? 0) eqn:Hzero.
  - (* FLOOR: result is exactly n/totalRSR. *)
    apply Z.le_trans with (m := n / totalRSR).
    + apply Z.div_le_lower_bound; [lia|].
      rewrite Z.mul_comm. exact Hkey.
    + lia.
  - (* CEIL: result is n/totalRSR + 1, even larger. *)
    assert (Hfloor : rsrAmount - draftRSR <= n / totalRSR).
    { apply Z.div_le_lower_bound; [lia|].
      rewrite Z.mul_comm. exact Hkey. }
    lia.
Qed.

Opaque FixLib.divrnd.

(** ===== seizeRSR_preserves_validity =====

    [seizeRSR] preserves [Valid.t] under the precondition that
    [rsrAmount <= totalRSRStaked + draftRSR] (production's
    [SeizeExceedsBalance] revert).

    The proof case-splits on the four reset configurations:
      - no stake reset, no draft reset
      - stake reset only
      - draft reset only
      - both resets fire.

    The reset triggers are designed to fire EXACTLY when the
    [Valid.t] invariants would otherwise break, so the validity is
    preserved in all four branches. *)

Lemma seizeRSR_preserves_validity
    (s : StRSR.Storage.t) (rsrAmount : U256.t) :
  StRSR.Valid.t s ->
  0 <= rsrAmount ->
  rsrAmount <= s.(StRSR.Storage.totalRSRStaked) + s.(StRSR.Storage.draftRSR) ->
  StRSR.Valid.t (StRSR.seizeRSR s rsrAmount).
Proof.
  intros Hv Hra_nn Hra_le.
  pose proof Hv as Hv0.
  destruct Hv as [Hst Hstk Hrew Hratio Hfifo Hdr Hcons Hent].
  unfold StRSR.seizeRSR.
  set (totalRSR := s.(StRSR.Storage.totalRSRStaked) + s.(StRSR.Storage.draftRSR)).
  fold totalRSR.
  destruct (totalRSR =? 0) eqn:Htot_eq.
  - (* Branch 1: totalRSR = 0 -> no-op *)
    exact Hv0.
  - apply Z.eqb_neq in Htot_eq.
    assert (Htot_pos : 0 < totalRSR) by lia.
    set (stake_share :=
      FixLib.divrnd (s.(StRSR.Storage.totalRSRStaked) * rsrAmount) totalRSR
                    RoundingMode.CEIL).
    fold stake_share.
    set (draft_share := rsrAmount - stake_share).
    fold draft_share.
    assert (Hss_nn : 0 <= stake_share)
      by (apply stake_share_nonneg; lia).
    assert (Hss_le_ra : stake_share <= rsrAmount).
    { unfold stake_share. apply stake_share_le_rsrAmount; lia. }
    assert (Hss_le_st : stake_share <= s.(StRSR.Storage.totalRSRStaked)).
    { unfold stake_share. apply stake_share_le_stakeRSR; lia. }
    assert (Hds_nn : 0 <= draft_share) by (unfold draft_share; lia).
    assert (Hss_ge_lo : rsrAmount - s.(StRSR.Storage.draftRSR) <= stake_share).
    { unfold stake_share, totalRSR.
      apply stake_share_ge_rsrAmount_minus_draftRSR; lia. }
    assert (Hds_le : draft_share <= s.(StRSR.Storage.draftRSR)).
    { unfold draft_share. lia. }
    set (stakeRSR_post := s.(StRSR.Storage.totalRSRStaked) - stake_share).
    set (draftRSR_post := s.(StRSR.Storage.draftRSR) - draft_share).
    fold stakeRSR_post draftRSR_post.
    assert (Hsp_nn : 0 <= stakeRSR_post) by (unfold stakeRSR_post; lia).
    assert (Hdp_nn : 0 <= draftRSR_post) by (unfold draftRSR_post; lia).
    (* Match on the boolean reset triggers in the same shape as
       [seizeRSR]'s definition, then discharge each branch. *)
    set (stake_reset_b :=
      (stakeRSR_post =? 0) ||
      ((0 <? s.(StRSR.Storage.totalStRSR)) &&
       (s.(StRSR.Storage.totalStRSR) * StRSR.FIX_ONE_Z >?
        stakeRSR_post * StRSR.MAX_STAKE_RATE))).
    set (draft_reset_b :=
      (draftRSR_post =? 0) ||
      (StRSR.sum_rsr_amounts s.(StRSR.Storage.queue) >? draftRSR_post)).
    fold stake_reset_b draft_reset_b.
    (* Case 1: draft_reset fires. Then the queue is wiped to [] and
       draftRSR := 0; whether stake_reset fires only affects the stake
       side (zero or proportional residue). Either way, the final
       state's queue is empty so the conservation invariant is trivial. *)
    destruct draft_reset_b eqn:Hdrb.
    + destruct stake_reset_b eqn:Hsrb.
      * (* Both fire: result = beginDraftEra (beginEra s_phase1). *)
        constructor; simpl.
        -- lia.
        -- lia.
        -- exact Hrew.
        -- exact Hratio.
        -- exact I.
        -- lia.
        -- simpl. lia.
        -- intros w Hin. simpl in Hin. contradiction.
      * (* Only draft fires: result = beginDraftEra s_phase1. *)
        constructor; simpl.
        -- exact Hst.
        -- lia.
        -- exact Hrew.
        -- exact Hratio.
        -- exact I.
        -- lia.
        -- simpl. lia.
        -- intros w Hin. simpl in Hin. contradiction.
    + (* Case 2: draft_reset doesn't fire. Then draftRSR_post != 0
         AND sum_rsr_amounts queue <= draftRSR_post. *)
      unfold draft_reset_b in Hdrb.
      assert (Hsum_le : StRSR.sum_rsr_amounts s.(StRSR.Storage.queue)
                       <= draftRSR_post).
      { destruct (draftRSR_post =? 0) eqn:Hzd.
        - simpl in Hdrb. discriminate.
        - simpl in Hdrb.
          rewrite Z.gtb_ltb in Hdrb. apply Z.ltb_ge in Hdrb. lia.
      }
      destruct stake_reset_b eqn:Hsrb.
      * (* Stake fires, draft doesn't: result = beginEra s_phase1. *)
        constructor; simpl.
        -- lia.
        -- lia.
        -- exact Hrew.
        -- exact Hratio.
        -- exact Hfifo.
        -- exact Hdp_nn.
        -- exact Hsum_le.
        -- exact Hent.
      * (* Neither fires: result = s_phase1 directly. *)
        constructor; simpl.
        -- exact Hst.
        -- exact Hsp_nn.
        -- exact Hrew.
        -- exact Hratio.
        -- exact Hfifo.
        -- exact Hdp_nn.
        -- exact Hsum_le.
        -- exact Hent.
Qed.

End StRSRValidity.

