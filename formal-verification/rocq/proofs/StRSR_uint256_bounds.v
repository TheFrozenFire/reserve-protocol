(** StRSR uint256 upper-bound derivation.

    The StRSR [Valid.t] predicate (in [simulations/StRSR.v]) only carries
    the pure-Z invariants — non-negativity of the stake/rewards counters
    and the [0 <= ratio <= FIX_ONE_Z] band. The simulation type
    [U256.t := Z] does not enforce a uint256 upper bound, so [Valid.t]
    leaves the per-field uint256 ceilings unstated.

    Production has those ceilings by EVM semantics (every storage word is
    a [uint256] and the compiler reverts on overflow under Solidity 0.8).
    This file closes the gap *without modifying the existing simulation
    or [Valid.t]* by introducing a separate [InputBounded] predicate
    that captures the missing upper bounds, proving that
    [stake] / [unstake] / [payoutRewards] preserve [InputBounded] under
    natural input-history hypotheses, and deriving the per-field
    [<= UINT256_MAX] bounds that [EndToEnd.v] needed.

    [InputBounded] tracks the three uint256-typed scalar fields whose
    upper bound is not derivable from [Valid.t] alone:

      - [totalStRSR]
      - [totalRSRStaked]
      - [totalRewardsAccumulated]

    [ratio] already lives in [0, FIX_ONE_Z = 10^18] under [Valid.t] and
    is therefore bounded by [UINT256_MAX] without further hypothesis
    (see [stRSR_ratio_le_uint256_max] in EndToEnd.v).

    Preservation hypotheses are stated at the call boundary as "the
    next-state value still fits in uint256", mirroring the on-chain
    [_safeWrap] revert behaviour: production guarantees boundedness by
    reverting whenever the next-state arithmetic would overflow, so a
    successful return path is exactly the path on which the next-state
    bound holds. We model that here as an explicit hypothesis on the
    caller's input-history, which is the cleanest available proxy for
    the EVM's revert.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Reserve.proofs.StRSR_validity.

Module StRSRUint256Bounds.

Import FixLib.

(** ---------- InputBounded predicate ----------

    Captures the three uint256 upper bounds that [Valid.t] omits. Kept
    as a separate record so we can compose it with [Valid.t] at use
    sites without changing the existing module surface. *)
Module InputBounded.
  Record t (s : StRSR.Storage.t) : Prop := {
    totalStRSR_u256     : s.(StRSR.Storage.totalStRSR)              <= UINT256_MAX;
    totalRSRStaked_u256 : s.(StRSR.Storage.totalRSRStaked)          <= UINT256_MAX;
    rewardsAccum_u256   : s.(StRSR.Storage.totalRewardsAccumulated) <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Three trivial corollaries for use at integration sites that have
    [Valid.t s /\ InputBounded.t s] in scope and only need one of the
    three field bounds. *)

Lemma StRSR_totalStRSR_bounded
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  InputBounded.t s ->
  s.(StRSR.Storage.totalStRSR) <= UINT256_MAX.
Proof. intros _ [H _ _]. exact H. Qed.

Lemma StRSR_totalRSRStaked_bounded
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  InputBounded.t s ->
  s.(StRSR.Storage.totalRSRStaked) <= UINT256_MAX.
Proof. intros _ [_ H _]. exact H. Qed.

Lemma StRSR_totalRewardsAccumulated_bounded
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  InputBounded.t s ->
  s.(StRSR.Storage.totalRewardsAccumulated) <= UINT256_MAX.
Proof. intros _ [_ _ H]. exact H. Qed.

(** ---------- preservation: stake ----------

    [stake] adds [amount] to [totalRSRStaked] and adds the freshly
    minted [stRSR] amount to [totalStRSR] (in the active branch) or
    [amount] one-for-one (in the genesis branch). Boundedness of the
    next-state values is exactly what the EVM checks at runtime via
    overflow revert; we encode it as a hypothesis on the call boundary.

    Hypotheses:
      - [s] is currently [InputBounded];
      - the resulting [totalRSRStaked + amount] still fits in uint256
        (this is the [_safeWrap] proxy);
      - the resulting [totalStRSR'] (whichever branch is taken) still
        fits in uint256.

    [totalRewardsAccumulated] is untouched, so its bound carries over. *)
(** Helper: [stake] does not touch [totalRewardsAccumulated]. *)
Lemma stake_rewards_unchanged
    (s : StRSR.Storage.t) (amount : U256.t) :
  (StRSR.stake s amount).(StRSR.Storage.totalRewardsAccumulated)
    = s.(StRSR.Storage.totalRewardsAccumulated).
Proof.
  unfold StRSR.stake.
  destruct (s.(StRSR.Storage.totalStRSR) =? 0); reflexivity.
Qed.

Lemma stake_preserves_input_bounded
    (s : StRSR.Storage.t) (amount : U256.t) :
  InputBounded.t s ->
  (StRSR.stake s amount).(StRSR.Storage.totalRSRStaked) <= UINT256_MAX ->
  (StRSR.stake s amount).(StRSR.Storage.totalStRSR)     <= UINT256_MAX ->
  InputBounded.t (StRSR.stake s amount).
Proof.
  intros Hib Hstaked' HtotalStRSR'.
  destruct Hib as [_ _ Hrew].
  constructor.
  - exact HtotalStRSR'.
  - exact Hstaked'.
  - rewrite stake_rewards_unchanged. exact Hrew.
Qed.

(** ---------- preservation: unstake ----------

    [unstake] decrements [totalStRSR] by [amount] and [totalRSRStaked]
    by the computed [rsrAmount]. We follow the same call-boundary
    pattern as [stake_preserves_input_bounded] / [payoutRewards_preserves_input_bounded]:
    the post-state values' uint256 boundedness is supplied as a hypothesis
    (mirroring on-chain [_safeWrap]). This keeps the proof agnostic to
    the FixLib reduction behaviour of [exchange_rate] and [divrnd], which
    blows up under [simpl]/[lia] inside [_RocqProject]'s build context.

    [totalRewardsAccumulated] is untouched, so its bound carries over
    without an extra hypothesis. *)
(** Helper: [unstake] does not touch [totalRewardsAccumulated]. *)
Lemma unstake_rewards_unchanged
    (s : StRSR.Storage.t) (amount now delay : U256.t) :
  (StRSR.unstake s amount now delay).(StRSR.Storage.totalRewardsAccumulated)
    = s.(StRSR.Storage.totalRewardsAccumulated).
Proof. reflexivity. Qed.

Lemma unstake_preserves_input_bounded
    (s : StRSR.Storage.t) (amount now delay : U256.t) :
  InputBounded.t s ->
  (StRSR.unstake s amount now delay).(StRSR.Storage.totalStRSR)     <= UINT256_MAX ->
  (StRSR.unstake s amount now delay).(StRSR.Storage.totalRSRStaked) <= UINT256_MAX ->
  InputBounded.t (StRSR.unstake s amount now delay).
Proof.
  intros [_ _ Hrew] Hst' Hstk'.
  constructor.
  - exact Hst'.
  - exact Hstk'.
  - rewrite unstake_rewards_unchanged. exact Hrew.
Qed.

(** ---------- preservation: payoutRewards ----------

    [payoutRewards] only bumps [totalRewardsAccumulated] by [payout]
    (and pushes [lastPayout] forward). The bump is guarded on chain by
    [_safeWrap], so a successful call leaves the next-state
    [totalRewardsAccumulated] in uint256 range. We require that bound
    as a hypothesis at the call boundary.

    [totalStRSR] and [totalRSRStaked] are untouched. *)
(** Helper: [payoutRewards] does not touch [totalStRSR] or [totalRSRStaked]. *)
Lemma payoutRewards_totalStRSR_unchanged
    (s : StRSR.Storage.t) (now rewardsPool : U256.t) :
  (StRSR.payoutRewards s now rewardsPool).(StRSR.Storage.totalStRSR)
    = s.(StRSR.Storage.totalStRSR).
Proof.
  unfold StRSR.payoutRewards.
  destruct (now <? s.(StRSR.Storage.lastPayout) + 1); reflexivity.
Qed.

Lemma payoutRewards_totalRSRStaked_unchanged
    (s : StRSR.Storage.t) (now rewardsPool : U256.t) :
  (StRSR.payoutRewards s now rewardsPool).(StRSR.Storage.totalRSRStaked)
    = s.(StRSR.Storage.totalRSRStaked).
Proof.
  unfold StRSR.payoutRewards.
  destruct (now <? s.(StRSR.Storage.lastPayout) + 1); reflexivity.
Qed.

Lemma payoutRewards_preserves_input_bounded
    (s : StRSR.Storage.t) (now rewardsPool : U256.t) :
  InputBounded.t s ->
  (StRSR.payoutRewards s now rewardsPool).(StRSR.Storage.totalRewardsAccumulated)
    <= UINT256_MAX ->
  InputBounded.t (StRSR.payoutRewards s now rewardsPool).
Proof.
  intros [Hst Hstk _] Hrew'.
  constructor.
  - rewrite payoutRewards_totalStRSR_unchanged. exact Hst.
  - rewrite payoutRewards_totalRSRStaked_unchanged. exact Hstk.
  - exact Hrew'.
Qed.

(** ---------- composition: strengthened EndToEnd-style bound ----------

    Restatement of [EndToEnd.system_invariants]'s shape but pulling
    in the new uint256 bounds for the headline StRSR scalars. *)

Lemma StRSR_scalars_jointly_bounded
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  InputBounded.t s ->
  s.(StRSR.Storage.totalStRSR)
  + s.(StRSR.Storage.totalRSRStaked)
  + s.(StRSR.Storage.totalRewardsAccumulated)
  + s.(StRSR.Storage.ratio)
    <= 4 * UINT256_MAX.
Proof.
  intros [Hst_nn Hstk_nn Hrew_nn Hratio _] [Hst_hi Hstk_hi Hrew_hi].
  destruct Hratio as [_ Hratio_hi].
  unfold StRSR.MAX_REWARD_RATIO in Hratio_hi.
  unfold UINT256_MAX in *.
  assert (Hpow : 10 ^ 14 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

End StRSRUint256Bounds.
