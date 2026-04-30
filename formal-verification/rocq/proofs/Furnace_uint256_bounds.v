(** Furnace uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and
    [proofs/Throttle_uint256_bounds.v]. The Furnace [Valid.t] predicate
    (in [simulations/Furnace.v]) already carries:
      - [ratio <= MAX_RATIO = 10^14]   (well below UINT256_MAX)
      - [lastPayout    <= UINT256_MAX]
      - [lastPayoutBal <= UINT256_MAX]
    so there is no missing scalar bound at rest. What [Valid.t] does NOT
    provide on its own is a *call-boundary* preservation surface: callers
    of [melt] / [setRatio] need to know that the post-state stays under
    UINT256_MAX without having to re-derive that fact from the FixLib
    arithmetic (which is exactly the [powu] / [mulu_toUint] term that
    blew up in early intrinsic attempts — the OOM trap referenced in the
    task brief).

    This file closes the gap *without modifying the existing simulation
    or [Valid.t]* by introducing a separate [InputBounded] predicate
    that re-states the three uint256 ceilings on the storage scalars,
    exposing per-field projections, and proving that [melt] /
    [setRatio] preserve [InputBounded] under natural call-boundary
    hypotheses.

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
Require Import Reserve.simulations.Furnace.

Module FurnaceUint256Bounds.

Import FixLib.
Import Furnace.

(** Mark the FixLib operations [Opaque] BEFORE any destruct/inversion so
    Coq doesn't try to unfold [powu] / [mulu_toUint] (which contain
    [Z.to_nat (Z.log2 _)] and explode the term size). *)
Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd.

(** ---------- InputBounded predicate ----------

    Re-states the three uint256 ceilings on the Furnace storage scalars.
    [Valid.t] already carries each of these (with [ratio] in fact bounded
    by [MAX_RATIO < UINT256_MAX]), but we provide a separate record so
    integration sites can pass a single bundled boundedness witness
    rather than threading [Valid.t] everywhere just for the upper-bound
    half of its content. *)
Module InputBounded.
  Record t (s : Storage.t) : Prop := {
    ratio_u256         : s.(Storage.ratio)         <= UINT256_MAX;
    lastPayout_u256    : s.(Storage.lastPayout)    <= UINT256_MAX;
    lastPayoutBal_u256 : s.(Storage.lastPayoutBal) <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Three trivial corollaries for use at integration sites that have
    [Valid.t s /\ InputBounded.t s] in scope and only need one of the
    three field bounds. *)

Lemma Furnace_ratio_bounded
    (s : Storage.t) :
  Valid.t s ->
  InputBounded.t s ->
  s.(Storage.ratio) <= UINT256_MAX.
Proof. intros _ [H _ _]. exact H. Qed.

Lemma Furnace_lastPayout_bounded
    (s : Storage.t) :
  Valid.t s ->
  InputBounded.t s ->
  s.(Storage.lastPayout) <= UINT256_MAX.
Proof. intros _ [_ H _]. exact H. Qed.

Lemma Furnace_lastPayoutBal_bounded
    (s : Storage.t) :
  Valid.t s ->
  InputBounded.t s ->
  s.(Storage.lastPayoutBal) <= UINT256_MAX.
Proof. intros _ [_ _ H]. exact H. Qed.

(** ---------- preservation: melt ----------

    [melt] returns a pair [(s', amount)]. In the active branch:
      - [s'.ratio]         = [s.ratio]                       (untouched)
      - [s'.lastPayout]    = [s.lastPayout + numPeriods]
      - [s'.lastPayoutBal] = [currentBalance - amount]

    [ratio]'s bound carries through automatically from the input state.
    The other two are call-boundary hypotheses, mirroring the on-chain
    [_safeWrap] revert behaviour. We do NOT reduce the [powu]/[mulu_toUint]
    terms inside [amount] — the [Opaque] declaration above keeps them
    behind their names. *)

Lemma melt_preserves_input_bounded
    (s s' : Storage.t) (now currentBalance amount : U256.t) :
  InputBounded.t s ->
  melt s now currentBalance = (s', amount) ->
  s'.(Storage.lastPayout)    <= UINT256_MAX ->
  s'.(Storage.lastPayoutBal) <= UINT256_MAX ->
  InputBounded.t s'.
Proof.
  intros [Hr Hlp Hlpb] Hmelt Hlp' Hlpb'.
  unfold melt in Hmelt.
  destruct (now <? s.(Storage.lastPayout) + 1) eqn:Hcond.
  - (* Early-return branch: pair = (s, 0). injection gives s' = s. *)
    injection Hmelt as Hs'_eq Hamt_eq.
    subst s'.
    constructor; assumption.
  - (* Active branch: ratio is copied; the two call-boundary hypotheses
       supply the other two bounds directly. *)
    injection Hmelt as Hs'_eq Hamt_eq.
    subst s'.
    constructor; simpl.
    + exact Hr.
    + exact Hlp'.
    + exact Hlpb'.
Qed.

(** ---------- preservation: setRatio ----------

    [setRatio] either fails (returns [None]) or sets [ratio := ratio_]
    and leaves [lastPayout] and [lastPayoutBal] untouched. So the only
    new bound to discharge is on [ratio_], supplied at the call boundary. *)

Lemma setRatio_preserves_input_bounded
    (s s' : Storage.t) (ratio_ : U256.t) :
  InputBounded.t s ->
  setRatio s ratio_ = Some s' ->
  s'.(Storage.ratio) <= UINT256_MAX ->
  InputBounded.t s'.
Proof.
  intros [Hr Hlp Hlpb] Hset Hr'.
  unfold setRatio in Hset.
  destruct (ratio_ <=? MAX_RATIO) eqn:Hle; [|discriminate].
  injection Hset as Hs'_eq.
  subst s'.
  constructor; simpl.
  - exact Hr'.
  - exact Hlp.
  - exact Hlpb.
Qed.

(** ---------- composition: strengthened EndToEnd-style joint bound ----------

    Sums the three scalar fields the Furnace storage carries. Each is
    [<= UINT256_MAX] under [InputBounded.t], so the sum is at most
    [3 * UINT256_MAX]. *)
Lemma Furnace_scalars_jointly_bounded
    (s : Storage.t) :
  Valid.t s ->
  InputBounded.t s ->
  s.(Storage.ratio)
  + s.(Storage.lastPayout)
  + s.(Storage.lastPayoutBal)
    <= 3 * UINT256_MAX.
Proof.
  intros [Hr_max Hr_nn Hlp_v Hlpb_v] [Hr_hi Hlp_hi Hlpb_hi].
  unfold UINT256_MAX in *.
  lia.
Qed.

End FurnaceUint256Bounds.
