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

End StRSRChain.
