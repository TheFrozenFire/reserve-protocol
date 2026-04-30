(** Throttle uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v]. The Throttle [Valid.throttle]
    predicate (in [simulations/Throttle.v]) carries [lastTimestamp <= UINT48_MAX]
    and [pctRate <= UINT192_MAX], but the two genuinely uint256-typed scalar
    fields — [lastAvailable] and [params.amtRate] — only get the [U256.Valid.t]
    non-negativity from [Valid.throttle], not an explicit upper bound.

    Production has those ceilings by EVM semantics (every storage word is a
    [uint256], and arithmetic that would overflow reverts under Solidity 0.8).
    This file closes the gap *without modifying the existing simulation or
    [Valid.throttle]* by introducing a separate [InputBounded] predicate that
    captures the missing upper bounds, proves [useAvailable] preserves it
    under a natural call-boundary hypothesis, and exposes per-field
    projection lemmas.

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
Require Import Reserve.simulations.Throttle.
Require Import Reserve.proofs.Throttle_validity.

Module ThrottleUint256Bounds.

Import FixLib.
Import ThrottleLib.

(** ---------- InputBounded predicate ----------

    Captures the two uint256 upper bounds that [Valid.throttle] omits.
    Kept as a separate record so we can compose it with [Valid.throttle] at
    use sites without changing the existing module surface.

    [params.pctRate] already lives in [0, UINT192_MAX] under [Valid.params]
    and is therefore bounded by [UINT256_MAX] without further hypothesis.
    [lastTimestamp] is bounded by [UINT48_MAX], also strictly below
    [UINT256_MAX]. *)
Module InputBounded.
  Record t (s : Throttle.t) : Prop := {
    lastAvailable_u256 : s.(Throttle.lastAvailable)                   <= UINT256_MAX;
    amtRate_u256       : s.(Throttle.params).(Params.amtRate)         <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Trivial corollaries for use at integration sites that have
    [Valid.throttle s /\ InputBounded.t s] in scope and only need one of
    the field bounds. *)

Lemma Throttle_lastAvailable_bounded
    (t : Throttle.t) :
  Valid.throttle t ->
  InputBounded.t t ->
  t.(Throttle.lastAvailable) <= UINT256_MAX.
Proof. intros _ [H _]. exact H. Qed.

Lemma Throttle_amtRate_bounded
    (t : Throttle.t) :
  Valid.throttle t ->
  InputBounded.t t ->
  t.(Throttle.params).(Params.amtRate) <= UINT256_MAX.
Proof. intros _ [_ H]. exact H. Qed.

(** ---------- preservation: useAvailable ----------

    [useAvailable] never modifies [params] in any branch — it only updates
    [lastTimestamp] and [lastAvailable] via record updates. So [amtRate]'s
    uint256 bound carries through automatically from the input state, and
    the only thing we need at the call boundary is that the post-state
    [lastAvailable'] still fits in uint256.

    Helper: [useAvailable] does not touch [params]. *)
Lemma useAvailable_params_unchanged
    (t t' : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  useAvailable t supply amount now = Result.Success t' ->
  t'.(Throttle.params) = t.(Throttle.params).
Proof.
  unfold useAvailable.
  destruct (andb (t.(Throttle.params).(Params.amtRate) =? 0)
                 (t.(Throttle.params).(Params.pctRate) =? 0)).
  - intros H. inversion H. reflexivity.
  - destruct (0 <? amount).
    + destruct (amount <=? _); [|discriminate].
      intros H. inversion H. reflexivity.
    + destruct (amount <? 0); intros H; inversion H; reflexivity.
Qed.

Lemma useAvailable_preserves_input_bounded
    (t t' : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  InputBounded.t t ->
  useAvailable t supply amount now = Result.Success t' ->
  t'.(Throttle.lastAvailable) <= UINT256_MAX ->
  InputBounded.t t'.
Proof.
  intros [_ Hamt] Hok Hav'.
  pose proof (useAvailable_params_unchanged _ _ _ _ _ Hok) as Hparams.
  constructor.
  - exact Hav'.
  - rewrite Hparams. exact Hamt.
Qed.

(** ---------- composition: strengthened EndToEnd-style joint bound ----------

    Sums the four scalar fields the throttle storage carries. Each of:
      - [lastAvailable]   <= UINT256_MAX (from InputBounded)
      - [amtRate]         <= UINT256_MAX (from InputBounded)
      - [pctRate]         <= UINT192_MAX < UINT256_MAX (from Valid.params)
      - [lastTimestamp]   <= UINT48_MAX  < UINT256_MAX (from Valid.throttle)
    so the sum is at most [4 * UINT256_MAX]. *)
Lemma Throttle_scalars_jointly_bounded
    (t : Throttle.t) :
  Valid.throttle t ->
  InputBounded.t t ->
  t.(Throttle.lastAvailable)
  + t.(Throttle.params).(Params.amtRate)
  + t.(Throttle.params).(Params.pctRate)
  + t.(Throttle.lastTimestamp)
    <= 4 * UINT256_MAX.
Proof.
  intros [Hp_valid Hts_uint48 _] [Hav_hi Hamt_hi].
  destruct Hp_valid as [_ _ Hpct_uint192].
  unfold UINT256_MAX, UINT192_MAX, UINT48_MAX in *.
  assert (Hpct_le : 2 ^ 192 - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  assert (Hts_le  : 2 ^ 48  - 1 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

End ThrottleUint256Bounds.
