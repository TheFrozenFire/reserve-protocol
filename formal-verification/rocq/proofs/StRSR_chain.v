(** StRSR composition lemmas.

    Small chain proofs over the StRSR transitions:

      1. [payoutRewards_no_period_idempotent] — when [now] is before the
         next payout boundary, [payoutRewards] is the identity function.
         Restatement of [payoutRewards_no_period] under the
         "idempotent" framing useful for chaining.

      2. [stake_then_payout_preserves_validity] — if [Valid.t s] holds,
         [stake] is run on [s] for a non-negative [amount], and
         [payoutRewards] is then run on the result with a non-negative
         computed payout, the final storage is still valid.

    Both lemmas reuse the existing validity lemmas without any new
    arithmetic. *)

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

End StRSRChain.
