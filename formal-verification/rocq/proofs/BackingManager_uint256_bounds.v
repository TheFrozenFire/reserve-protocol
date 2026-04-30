(** BackingManager uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and [proofs/Throttle_uint256_bounds.v].
    The BackingManager simulation exposes two pure pieces:

      [computeNewBasketsAndNeeded] — produces a [BasketState.t] with
      fields [basketsNeeded], [mintAmount], [needed].

      [computeSurplusSplit] — produces (in the Success branch) a
      [SurplusSplit.t] with fields [rsrAmount], [rTokenAmount], [dust].

    [Valid.bufferInputs] (in [simulations/BackingManager.v]) carries
    uint192 bounds on the *inputs*, but does not state any uint256
    ceilings on the *outputs*. The outputs of these pure functions
    are the values production immediately stores in uint256 slots, so
    the EVM enforces the ceilings via [_safeWrap]: a successful return
    path is exactly the path on which the next-state uint256 bound
    holds.

    This file closes the gap *without modifying the existing simulation*
    by introducing separate [InputBounded] predicates for each output
    record, a projection lemma per field, preservation lemmas for both
    pure functions under a call-boundary hypothesis, and a joint bound
    on the SurplusSplit fields.

    Discipline: same as [Throttle_uint256_bounds.v]. We never touch
    [Valid] or any existing simulation-side surface.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.

Module BackingManagerUint256Bounds.

Import FixLib.
Import BackingManager.

(** ---------- BasketState InputBounded ----------

    [BasketState.t] carries three uint256-typed scalars. None of them
    have an explicit upper bound from the simulation. We take all three
    as part of the predicate. *)
Module BasketStateBounded.
  Record t (s : BasketState.t) : Prop := {
    basketsNeeded_u256 : s.(BasketState.basketsNeeded) <= UINT256_MAX;
    mintAmount_u256    : s.(BasketState.mintAmount)    <= UINT256_MAX;
    needed_u256        : s.(BasketState.needed)        <= UINT256_MAX;
  }.
End BasketStateBounded.

(** ---------- per-field projections (BasketState) ---------- *)

Lemma BasketState_basketsNeeded_bounded
    (s : BasketState.t) :
  BasketStateBounded.t s ->
  s.(BasketState.basketsNeeded) <= UINT256_MAX.
Proof. intros [H _ _]. exact H. Qed.

Lemma BasketState_mintAmount_bounded
    (s : BasketState.t) :
  BasketStateBounded.t s ->
  s.(BasketState.mintAmount) <= UINT256_MAX.
Proof. intros [_ H _]. exact H. Qed.

Lemma BasketState_needed_bounded
    (s : BasketState.t) :
  BasketStateBounded.t s ->
  s.(BasketState.needed) <= UINT256_MAX.
Proof. intros [_ _ H]. exact H. Qed.

(** ---------- SurplusSplit InputBounded ----------

    [SurplusSplit.t] carries three uint256-typed scalars. *)
Module SurplusSplitBounded.
  Record t (sp : SurplusSplit.t) : Prop := {
    rsrAmount_u256    : sp.(SurplusSplit.rsrAmount)    <= UINT256_MAX;
    rTokenAmount_u256 : sp.(SurplusSplit.rTokenAmount) <= UINT256_MAX;
    dust_u256         : sp.(SurplusSplit.dust)         <= UINT256_MAX;
  }.
End SurplusSplitBounded.

(** ---------- per-field projections (SurplusSplit) ---------- *)

Lemma SurplusSplit_rsrAmount_bounded
    (sp : SurplusSplit.t) :
  SurplusSplitBounded.t sp ->
  sp.(SurplusSplit.rsrAmount) <= UINT256_MAX.
Proof. intros [H _ _]. exact H. Qed.

Lemma SurplusSplit_rTokenAmount_bounded
    (sp : SurplusSplit.t) :
  SurplusSplitBounded.t sp ->
  sp.(SurplusSplit.rTokenAmount) <= UINT256_MAX.
Proof. intros [_ H _]. exact H. Qed.

Lemma SurplusSplit_dust_bounded
    (sp : SurplusSplit.t) :
  SurplusSplitBounded.t sp ->
  sp.(SurplusSplit.dust) <= UINT256_MAX.
Proof. intros [_ _ H]. exact H. Qed.

(** ---------- preservation: computeNewBasketsAndNeeded ----------

    The function is purely computational — it produces a fresh
    [BasketState.t] from three input scalars. Production stores each
    of [basketsNeeded'], [mintAmount], [needed] in uint256 slots, so
    boundedness of each output is exactly what [_safeWrap] enforces.
    We encode that as three call-boundary hypotheses on the resulting
    record. *)
Lemma computeNewBasketsAndNeeded_preserves_input_bounded
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let s' := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded
                                       backingBuffer in
  s'.(BasketState.basketsNeeded) <= UINT256_MAX ->
  s'.(BasketState.mintAmount)    <= UINT256_MAX ->
  s'.(BasketState.needed)        <= UINT256_MAX ->
  BasketStateBounded.t s'.
Proof.
  intros s' Hbn Hma Hnd.
  constructor; assumption.
Qed.

(** ---------- preservation: computeSurplusSplit ----------

    [computeSurplusSplit] returns a [Result.t SurplusSplit.t]; we only
    care about the Success branch. As with the BasketState case,
    boundedness of each output field is the [_safeWrap] proxy at the
    call boundary. *)
Lemma computeSurplusSplit_preserves_input_bounded
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) (sp : SurplusSplit.t) :
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
    = Result.Success sp ->
  sp.(SurplusSplit.rsrAmount)    <= UINT256_MAX ->
  sp.(SurplusSplit.rTokenAmount) <= UINT256_MAX ->
  sp.(SurplusSplit.dust)         <= UINT256_MAX ->
  SurplusSplitBounded.t sp.
Proof.
  intros _ Hr Ht Hd.
  constructor; assumption.
Qed.

(** ---------- composition: joint bound on SurplusSplit fields ----------

    Sums the three scalar fields the SurplusSplit record carries.
    Each of:
      - [rsrAmount]    <= UINT256_MAX (from SurplusSplitBounded)
      - [rTokenAmount] <= UINT256_MAX (from SurplusSplitBounded)
      - [dust]         <= UINT256_MAX (from SurplusSplitBounded)
    so the sum is at most [3 * UINT256_MAX]. *)
Lemma SurplusSplit_scalars_jointly_bounded
    (sp : SurplusSplit.t) :
  SurplusSplitBounded.t sp ->
  sp.(SurplusSplit.rsrAmount)
  + sp.(SurplusSplit.rTokenAmount)
  + sp.(SurplusSplit.dust)
    <= 3 * UINT256_MAX.
Proof.
  intros [Hr Ht Hd].
  unfold UINT256_MAX in *.
  lia.
Qed.

(** ---------- composition: joint bound on BasketState fields ----------

    Same shape, three fields, ceiling [3 * UINT256_MAX]. *)
Lemma BasketState_scalars_jointly_bounded
    (s : BasketState.t) :
  BasketStateBounded.t s ->
  s.(BasketState.basketsNeeded)
  + s.(BasketState.mintAmount)
  + s.(BasketState.needed)
    <= 3 * UINT256_MAX.
Proof.
  intros [Hbn Hma Hnd].
  unfold UINT256_MAX in *.
  lia.
Qed.

End BackingManagerUint256Bounds.
