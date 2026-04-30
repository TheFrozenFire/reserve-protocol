(** StRSR composition lemmas.

    Chain proofs over the StRSR transitions:

      1. [payoutRewards_no_period_idempotent] — when [now] is before the
         next payout boundary, [payoutRewards] is the identity function.
         Restatement of [payoutRewards_no_period] under the
         "idempotent" framing useful for chaining.

      2. [stake_then_payout_preserves_validity] — if [Valid.t s] holds,
         [stake] is run on [s] for a non-negative [amount], and
         [payoutRewards] is then run on the result with a non-negative
         computed payout, the final storage is still valid.

      3. [unstake_then_cancelUnstake_lossy_recovery] — quantifies the
         rounding loss between the original stRSR amount unstaked and
         what comes back after [cancelUnstake_last]. With a fresh
         genesis storage and rate = FIX_ONE the round-trip is exact.

      4. [payoutRewards_then_seizeRSR_preserves_validity] — chains
         payoutRewards followed by seizeRSR (Phase D integration).

      5. [unstake_then_seizeRSR_then_withdraw_preserves_validity] —
         the full unstake-during-seizure lifecycle preserves validity. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Reserve.proofs.StRSR.
Require Import Reserve.proofs.StRSR_validity.

Require Import Coq.Lists.List.
Import ListNotations.

Module StRSRChain.

Import FixLib.
Import Reserve.simulations.StRSR.StRSR.
Import Reserve.proofs.StRSR_validity.StRSRValidity.

(** ---------- payoutRewards_no_period_idempotent ----------

    Restatement of [payoutRewards_no_period]: when [now] is strictly
    less than [lastPayout + 1], [payoutRewards] returns its input
    unchanged. *)

Lemma payoutRewards_no_period_idempotent
    (s : Storage.t) (now rewardsPool : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  payoutRewards s now rewardsPool = s.
Proof.
  intros Hlt.
  exact (StRSRProofs.payoutRewards_no_period s now rewardsPool Hlt).
Qed.

(** ---------- stake_then_payout_preserves_validity ----------

    [stake] then [payoutRewards] preserves [Valid.t]. The hypothesis
    [0 <= payout] mirrors the precondition of
    [payoutRewards_preserves_validity]; note the [payoutRatio] /
    [payout] are computed against the post-[stake] storage [s1], whose
    [ratio] and [lastPayout] coincide with [s]'s (since [stake]
    leaves both untouched in either branch). *)

Lemma stake_then_payout_preserves_validity
    (s : Storage.t) (amount now rewardsPool : U256.t) :
  Valid.t s ->
  0 <= amount ->
  let s1 := stake s amount in
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s1.(Storage.ratio))
                   (now - s1.(Storage.lastPayout))) in
  let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
  0 <= payout ->
  Valid.t (payoutRewards s1 now rewardsPool).
Proof.
  intros Hv Hamt s1 payoutRatio payout Hpay.
  assert (Hv1 : Valid.t s1)
    by (apply stake_preserves_validity; assumption).
  apply payoutRewards_preserves_validity; assumption.
Qed.

(** ---------- unstake_then_cancelUnstake_lossy_recovery ----------

    [unstake] then [cancelUnstake_last] is a single round-trip on the
    queue: enqueue the back entry, then pop it. The composition is
    *not* the identity in general because:

    1. [unstake] uses the rate at unstake time to compute [rsrAmount]
       from [amount].
    2. [cancelUnstake_last] uses the rate AFTER unstake (which is
       different — totals dropped) to compute [minted] from [rsrAmount].

    With a fresh genesis storage ([rt_genesis_storage] from
    [proofs/StRSR.v]) the rate is fixed at [FIX_ONE_Z] before and after
    a single stake; in this calibration the round-trip is exact.

    The lemma states: from [rt_genesis_storage], stake [amount], then
    unstake [amount] at rate FIX_ONE, then cancel — recovers the
    original [totalStRSR] and [totalRSRStaked] exactly. *)

Lemma unstake_then_cancelUnstake_lossy_recovery
    (amount now delay : U256.t) :
  0 < amount ->
  let s0 := stake StRSRProofs.rt_genesis_storage amount in
  let s1 := unstake s0 amount now delay in
  let s2 := cancelUnstake_last s1 in
  s2.(Storage.totalStRSR) = amount /\
  s2.(Storage.totalRSRStaked) = amount.
Proof.
  intros Hpos s0 s1 s2.
  unfold s2, s1, s0.
  rewrite StRSRProofs.stake_genesis_eq.
  unfold unstake.
  rewrite (StRSRProofs.exchange_rate_balanced amount Hpos).
  unfold enqueue.
  cbn [Storage.queue].
  unfold cancelUnstake_last.
  cbn [Storage.queue].
  rewrite List.rev_app_distr. simpl.
  cbn [Storage.totalStRSR Storage.totalRSRStaked
       Storage.totalRewardsAccumulated Storage.ratio Storage.lastPayout
       Storage.queue Storage.era Storage.draftEra Storage.draftRSR].
  unfold divrnd, FIX_ONE_Z, FIX_ONE, FIX_SCALE.
  rewrite Z_div_mult_full by lia.
  (* totalStRSR = amount - amount + (rsrAmount = amount)
                = amount.
     totalRSRStaked = amount - amount + amount = amount.
     The genesis branch fires for cancelUnstake_last because
     totalStRSR after unstake is 0. *)
  cbn [Z.eqb Pos.eqb].
  destruct (amount - amount =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. cbn -[Z.add Z.sub].
    split; lia.
  - apply Z.eqb_neq in Hzero. lia.
Qed.

(** ---------- payoutRewards_then_seizeRSR_preserves_validity ----------

    Phase D integration: the natural pairing of [payoutRewards]
    (which adds to [totalRewardsAccumulated]) with [seizeRSR]
    (which proportionally removes from both pools). Production runs
    [_payoutRewards()] inline at the top of [seizeRSR] (line 450);
    this lemma captures the validity-preservation invariant of that
    composed transition.

    The hypothesis carries the [seizeRSR] precondition:
    [rsrAmount <= post-payout (totalRSRStaked + draftRSR)]. The
    payout step adds rewards to [totalRewardsAccumulated] but leaves
    [totalRSRStaked] and [draftRSR] alone, so the bound is the same
    pre- and post-payout. *)

Lemma payoutRewards_then_seizeRSR_preserves_validity
    (s : Storage.t) (now rewardsPool rsrAmount : U256.t) :
  Valid.t s ->
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
                   (now - s.(Storage.lastPayout))) in
  let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
  0 <= payout ->
  0 <= rsrAmount ->
  rsrAmount <= s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) ->
  Valid.t (seizeRSR (payoutRewards s now rewardsPool) rsrAmount).
Proof.
  intros Hv payoutRatio payout Hpay Hra_nn Hra_le.
  set (s1 := payoutRewards s now rewardsPool).
  fold s1.
  assert (Hv1 : Valid.t s1)
    by (apply payoutRewards_preserves_validity; assumption).
  apply seizeRSR_preserves_validity; try assumption.
  (* Show rsrAmount <= s1.totalRSRStaked + s1.draftRSR.
     The two scalars are unchanged by payoutRewards. *)
  unfold s1, payoutRewards.
  destruct (now <? s.(Storage.lastPayout) + 1).
  - exact Hra_le.
  - cbn [Storage.totalRSRStaked Storage.draftRSR]. exact Hra_le.
Qed.

(** ---------- unstake_then_seizeRSR_then_withdraw_preserves_validity ----------

    The full unstake-during-seizure lifecycle:
      unstake (queue grows by one entry; draftRSR grows by rsrAmount)
        -> seizeRSR  (proportional removal, possibly era-resetting)
          -> withdraw (one queue entry pops; draftRSR drops; OR no-op
                       if seizeRSR triggered draft_reset).

    The composition preserves [Valid.t]. Production carries this as
    the most stress-tested integration property: the unstake
    lifecycle interleaved with a seizure should not corrupt the
    storage invariants.

    The unstake step's preconditions (amount <= totalStRSR,
    rsrAmount <= totalRSRStaked, FIFO timestamp domination) are
    threaded through; the seizeRSR step adds [rsrAmount_seize <=
    totalRSRStaked + draftRSR] (post-unstake values). *)

Lemma unstake_then_seizeRSR_then_withdraw_preserves_validity
    (s : Storage.t)
    (amount now delay rsrAmount_seize now_w : U256.t) :
  Valid.t s ->
  0 <= amount ->
  amount <= s.(Storage.totalStRSR) ->
  let rate := exchange_rate s in
  let rsrAmount_un :=
    FixLib.divrnd (amount * rate) FIX_ONE_Z RoundingMode.FLOOR in
  rsrAmount_un <= s.(Storage.totalRSRStaked) ->
  (forall w', List.In w' s.(Storage.queue) ->
              w'.(Withdrawal.availableAt) <= now + delay) ->
  let s1 := unstake s amount now delay in
  0 <= rsrAmount_seize ->
  rsrAmount_seize <= s1.(Storage.totalRSRStaked) + s1.(Storage.draftRSR) ->
  let s2 := seizeRSR s1 rsrAmount_seize in
  Valid.t (fst (withdraw s2 now_w)).
Proof.
  intros Hv Hamt_nn Hamt_le rate rsrAmount_un HrsrLe Hbound s1 Hrs_nn Hrs_le s2.
  assert (Hv1 : Valid.t s1).
  { unfold s1. apply unstake_preserves_validity; assumption. }
  assert (Hv2 : Valid.t s2).
  { unfold s2. apply seizeRSR_preserves_validity; assumption. }
  apply withdraw_preserves_validity. exact Hv2.
Qed.

End StRSRChain.
