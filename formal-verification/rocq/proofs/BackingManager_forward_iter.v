(** BackingManager.forwardRevenue iteration-framework proofs.

    Lifts the per-asset surplus-split invariants (in
    [proofs/BackingManager.v]) to the multi-asset iteration done by
    [forwardRevenueIter] and the full [forwardRevenue] composition.

    Key theorems:

      ITER-CONS  forwardRevenueIter_aux_conservation:
                 across the iteration, [rsrSum + rTokenSum + dustSum]
                 equals the sum of per-asset deltas (the sum-of-shares
                 conservation invariant lifted to a list).

      ITER-NN    forwardRevenueIter_aux_outputs_nonneg:
                 every aggregate field is non-negative when inputs are
                 non-negative — the validity-preservation companion to
                 the per-asset [computeSurplusSplit_outputs_nonneg] from
                 [BackingManager_validity.v].

      ITER-EMPTY forwardRevenueIter_empty:
                 empty asset list yields the zero aggregate (anchors
                 the induction).

      ITER-LEN   forwardRevenueIter_aux_splits_length:
                 success branch produces one [SurplusSplit.t] per asset.

      FWD-CONS   forwardRevenue_conservation:
                 the full [forwardRevenue] preserves the iteration's
                 conservation invariant when the basket-update succeeds.

      FWD-NN     forwardRevenue_outputs_nonneg:
                 [forwardRevenue] preserves non-negativity of every
                 aggregate field.

      FWD-PV     forwardRevenue_preserves_validity:
                 [forwardRevenue] preserves [Valid.storage] — basket
                 update only mutates [basketsNeeded]; [tradeStatus] /
                 [pendingTrade] are passed through.

    All conservation lemmas are stated at the [stepAggregate] level
    so the induction reduces to a single arithmetic step.

    Discipline: BACKING_MANAGER's [shiftl_toUint] operations are
    pre-evaluated under the [decimals >= 0] hypothesis carried in
    [Valid.assetState]. We don't [vm_compute] inside an induction —
    that would over-reduce.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Reserve.proofs.BackingManager.
Require Import Reserve.proofs.BackingManager_validity.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Module BackingManagerForwardIter.

Import FixLib.
Import Reserve.simulations.BackingManager.BackingManager.

Local Open Scope Z_scope.

(** WISDOM.md R001: mark the FixLib operations [Opaque] BEFORE any
    destruct/induction that case-analyses on [computeSurplusSplit] —
    otherwise Coq tries to unfold [FixLib.mul] / [shiftl_toUint] /
    [divrnd] inside the goal and the term explodes (this file took
    >5 min to compile without these declarations; with them, seconds). *)
Opaque FixLib.mul FixLib.divrnd FixLib.mulu_toUint FixLib.minus FixLib.powu.
Opaque BackingManager.shiftl_toUint
       BackingManager.computeNewBasketsAndNeeded.
(** [forwardRevenueIter_aux] left transparent so the inductive
    [conservation] / [outputs_nonneg] lemmas can [cbn] through nil/cons.
    [forwardRevenueIter] (the wrapper) is left transparent too — the
    [destruct] on it in [forwardRevenue_*] lemmas works because each
    proof first does [unfold forwardRevenue in Hsucc] to reach the
    explicit [forwardRevenueIter_aux IterAggregate.empty ...] form. *)

(** ---------- Helper: deltaSum over an asset list ---------- *)

(** Total per-asset delta for a list of assets, with respect to a
    common [needed]. *)
Fixpoint deltaSum (needed : U256.t) (assets : BackingManager.AssetList) : Z :=
  match assets with
  | nil => 0
  | a :: rest => assetDelta needed a + deltaSum needed rest
  end.

Lemma deltaSum_app (needed : U256.t) (xs ys : BackingManager.AssetList) :
  deltaSum needed (xs ++ ys) = deltaSum needed xs + deltaSum needed ys.
Proof.
  induction xs as [|a rest IH]; cbn; lia.
Qed.

(** ---------- stepAggregate facts ---------- *)

Lemma stepAggregate_rsrSum (acc : IterAggregate.t) (sp : SurplusSplit.t) :
  (stepAggregate acc sp).(IterAggregate.rsrSum)
  = acc.(IterAggregate.rsrSum) + sp.(SurplusSplit.rsrAmount).
Proof. unfold stepAggregate; reflexivity. Qed.

Lemma stepAggregate_rTokenSum (acc : IterAggregate.t) (sp : SurplusSplit.t) :
  (stepAggregate acc sp).(IterAggregate.rTokenSum)
  = acc.(IterAggregate.rTokenSum) + sp.(SurplusSplit.rTokenAmount).
Proof. unfold stepAggregate; reflexivity. Qed.

Lemma stepAggregate_dustSum (acc : IterAggregate.t) (sp : SurplusSplit.t) :
  (stepAggregate acc sp).(IterAggregate.dustSum)
  = acc.(IterAggregate.dustSum) + sp.(SurplusSplit.dust).
Proof. unfold stepAggregate; reflexivity. Qed.

Lemma stepAggregate_splits_length (acc : IterAggregate.t) (sp : SurplusSplit.t) :
  length (stepAggregate acc sp).(IterAggregate.splits)
  = (length acc.(IterAggregate.splits) + 1)%nat.
Proof.
  unfold stepAggregate; cbn.
  rewrite length_app; cbn; lia.
Qed.

(** ---------- Per-asset bridge: one iteration step's effect on the sum. ---------- *)

(** Whenever [computeSurplusSplit] succeeds, the per-asset split's three
    fields sum to the [assetDelta] for that asset. *)
Lemma computeSurplusSplit_sum_eq_assetDelta
    (needed : U256.t) (a : AssetState.t)
    (rTokenTotal rsrTotal : U256.t) (sp : SurplusSplit.t) :
  computeSurplusSplit needed a.(AssetState.quantity) a.(AssetState.bal)
                      a.(AssetState.decimals) rTokenTotal rsrTotal
    = Result.Success sp ->
  sp.(SurplusSplit.rsrAmount)
  + sp.(SurplusSplit.rTokenAmount)
  + sp.(SurplusSplit.dust)
  = assetDelta needed a.
Proof.
  intros Hsucc.
  unfold computeSurplusSplit, assetDelta in *.
  set (req := FixLib.mul needed a.(AssetState.quantity) RoundingMode.CEIL) in *.
  destruct (a.(AssetState.bal) <=? req) eqn:Hle.
  - injection Hsucc as Hsp; subst sp; cbn; lia.
  - set (delta := shiftl_toUint (a.(AssetState.bal) - req) a.(AssetState.decimals)) in *.
    set (totalShares := rTokenTotal + rsrTotal) in *.
    destruct (totalShares =? 0) eqn:Hts.
    + discriminate.
    + set (tps := delta / totalShares) in *.
      destruct (tps =? 0) eqn:Htps.
      * injection Hsucc as Hsp; subst sp; cbn; lia.
      * injection Hsucc as Hsp; subst sp; cbn.
        unfold totalShares; lia.
Qed.

(** ---------- ITER-CONS: aggregate conservation ---------- *)

(** Aggregate conservation across [forwardRevenueIter_aux]:

    [(acc.rsrSum + acc.rTokenSum + acc.dustSum) + deltaSum needed assets
     = agg.rsrSum + agg.rTokenSum + agg.dustSum]

    when the iteration succeeds with [agg]. The proof is a structural
    induction on [assets] that consumes one [stepAggregate] per
    iteration step. *)
Lemma forwardRevenueIter_aux_conservation
    (acc : IterAggregate.t) (needed : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  forwardRevenueIter_aux acc needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  acc.(IterAggregate.rsrSum)
  + acc.(IterAggregate.rTokenSum)
  + acc.(IterAggregate.dustSum)
  + deltaSum needed assets
  = agg.(IterAggregate.rsrSum)
  + agg.(IterAggregate.rTokenSum)
  + agg.(IterAggregate.dustSum).
Proof.
  revert acc agg.
  induction assets as [|a rest IH]; intros acc agg Hsucc; cbn in Hsucc.
  - injection Hsucc as Hagg; subst agg. cbn. lia.
  - destruct (computeSurplusSplit needed a.(AssetState.quantity)
                a.(AssetState.bal) a.(AssetState.decimals)
                rTokenTotal rsrTotal) as [sp | p q] eqn:Hcs.
    + pose proof (computeSurplusSplit_sum_eq_assetDelta
                    needed a rTokenTotal rsrTotal sp Hcs) as Hsum.
      specialize (IH (stepAggregate acc sp) agg Hsucc).
      rewrite stepAggregate_rsrSum, stepAggregate_rTokenSum,
              stepAggregate_dustSum in IH.
      cbn. lia.
    + discriminate Hsucc.
Qed.

(** Top-level [forwardRevenueIter] conservation: the empty initial
    aggregate has all sums = 0, so [deltaSum = aggregate sum]. *)
Theorem forwardRevenueIter_conservation
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  forwardRevenueIter needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  agg.(IterAggregate.rsrSum)
  + agg.(IterAggregate.rTokenSum)
  + agg.(IterAggregate.dustSum)
  = deltaSum needed assets.
Proof.
  intros Hsucc.
  unfold forwardRevenueIter in Hsucc.
  pose proof (forwardRevenueIter_aux_conservation
                IterAggregate.empty needed rTokenTotal rsrTotal
                assets agg Hsucc) as Hcons.
  cbn in Hcons. lia.
Qed.

(** ---------- ITER-EMPTY: empty asset list yields zero aggregate. ---------- *)
Theorem forwardRevenueIter_empty
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t) :
  forwardRevenueIter needed rTokenTotal rsrTotal nil
  = Result.Success IterAggregate.empty.
Proof. reflexivity. Qed.

(** ---------- ITER-LEN: one split per asset on success. ---------- *)
Lemma forwardRevenueIter_aux_splits_length
    (acc : IterAggregate.t) (needed : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  forwardRevenueIter_aux acc needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  length agg.(IterAggregate.splits)
  = (length acc.(IterAggregate.splits) + length assets)%nat.
Proof.
  revert acc agg.
  induction assets as [|a rest IH]; intros acc agg Hsucc; cbn in Hsucc.
  - injection Hsucc as Hagg; subst agg. cbn. lia.
  - destruct (computeSurplusSplit _ _ _ _ _ _) as [sp | p q] eqn:Hcs;
      [|discriminate].
    specialize (IH (stepAggregate acc sp) agg Hsucc).
    rewrite stepAggregate_splits_length in IH.
    cbn. lia.
Qed.

Theorem forwardRevenueIter_splits_length
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  forwardRevenueIter needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  length agg.(IterAggregate.splits) = length assets.
Proof.
  intros Hsucc.
  unfold forwardRevenueIter in Hsucc.
  pose proof (forwardRevenueIter_aux_splits_length
                IterAggregate.empty needed rTokenTotal rsrTotal
                assets agg Hsucc) as Hlen.
  cbn in Hlen. exact Hlen.
Qed.

(** ---------- ITER-NN: aggregate non-negativity ---------- *)

(** When inputs are non-negative and the iteration succeeds, every
    aggregate sum is non-negative. The per-asset
    [computeSurplusSplit_outputs_nonneg] from [BackingManager_validity]
    discharges the per-step case; we lift it. *)
Lemma forwardRevenueIter_aux_outputs_nonneg
    (acc : IterAggregate.t) (needed : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  0 <= needed ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  Valid.assetList assets ->
  0 <= acc.(IterAggregate.rsrSum) ->
  0 <= acc.(IterAggregate.rTokenSum) ->
  0 <= acc.(IterAggregate.dustSum) ->
  forwardRevenueIter_aux acc needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  0 <= agg.(IterAggregate.rsrSum) /\
  0 <= agg.(IterAggregate.rTokenSum) /\
  0 <= agg.(IterAggregate.dustSum).
Proof.
  revert acc agg.
  induction assets as [|a rest IH]; intros acc agg Hneeded HrT HrS Hval Hr Ht Hd Hsucc;
    cbn in Hsucc.
  - injection Hsucc as Hagg; subst agg. repeat split; assumption.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    destruct Hhd as [Hq Hbal Hdec].
    destruct Hq as [Hq_lo Hq_hi].
    destruct (computeSurplusSplit needed _ _ _ _ _) as [sp | p q] eqn:Hcs;
      [|discriminate].
    pose proof (BackingManagerValidityProofs.computeSurplusSplit_outputs_nonneg
                  needed a.(AssetState.quantity) a.(AssetState.bal)
                  a.(AssetState.decimals) rTokenTotal rsrTotal sp
                  Hneeded Hq_lo Hbal HrT HrS Hdec Hcs) as Hsp_nn.
    destruct Hsp_nn as (Hr_sp & Ht_sp & Hd_sp).
    apply (IH (stepAggregate acc sp) agg Hneeded HrT HrS Htl).
    + rewrite stepAggregate_rsrSum; lia.
    + rewrite stepAggregate_rTokenSum; lia.
    + rewrite stepAggregate_dustSum; lia.
    + exact Hsucc.
Qed.

Theorem forwardRevenueIter_outputs_nonneg
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (agg : IterAggregate.t) :
  0 <= needed ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  Valid.assetList assets ->
  forwardRevenueIter needed rTokenTotal rsrTotal assets
    = Result.Success agg ->
  0 <= agg.(IterAggregate.rsrSum) /\
  0 <= agg.(IterAggregate.rTokenSum) /\
  0 <= agg.(IterAggregate.dustSum).
Proof.
  intros Hneeded HrT HrS Hval Hsucc.
  unfold forwardRevenueIter in Hsucc.
  apply (forwardRevenueIter_aux_outputs_nonneg
           IterAggregate.empty needed rTokenTotal rsrTotal assets agg);
    try assumption; cbn; lia.
Qed.

(** ---------- FWD-CONS: full forwardRevenue conservation ---------- *)

(** When [forwardRevenue] succeeds, the result's
    [rsrSum + rTokenSum + dustSum] equals the deltaSum at the
    post-update [needed]. *)
Theorem forwardRevenue_conservation
    (s : Storage.t) (basketsHeldBottom : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (r : ForwardRevenueResult.t) :
  forwardRevenue s basketsHeldBottom rTokenTotal rsrTotal assets
    = Result.Success r ->
  r.(ForwardRevenueResult.rsrSum)
  + r.(ForwardRevenueResult.rTokenSum)
  + r.(ForwardRevenueResult.dustSum)
  = deltaSum r.(ForwardRevenueResult.needed) assets.
Proof.
  intros Hsucc.
  unfold forwardRevenue in Hsucc.
  set (bs := computeNewBasketsAndNeeded basketsHeldBottom
              s.(Storage.basketsNeeded) s.(Storage.backingBuffer)) in *.
  destruct (forwardRevenueIter bs.(BasketState.needed) rTokenTotal rsrTotal assets)
    as [agg | p q] eqn:Hiter; [|discriminate].
  injection Hsucc as Hr; subst r. cbn.
  apply (forwardRevenueIter_conservation
           bs.(BasketState.needed) rTokenTotal rsrTotal assets agg Hiter).
Qed.

(** ---------- FWD-NN: forwardRevenue outputs non-negative. ---------- *)
Theorem forwardRevenue_outputs_nonneg
    (s : Storage.t) (basketsHeldBottom : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (r : ForwardRevenueResult.t) :
  Valid.bufferInputs basketsHeldBottom s.(Storage.basketsNeeded)
                     s.(Storage.backingBuffer) ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  Valid.assetList assets ->
  forwardRevenue s basketsHeldBottom rTokenTotal rsrTotal assets
    = Result.Success r ->
  0 <= r.(ForwardRevenueResult.rsrSum) /\
  0 <= r.(ForwardRevenueResult.rTokenSum) /\
  0 <= r.(ForwardRevenueResult.dustSum) /\
  0 <= r.(ForwardRevenueResult.mintAmount) /\
  0 <= r.(ForwardRevenueResult.needed).
Proof.
  intros Hvalid HrT HrS Hassets Hsucc.
  unfold forwardRevenue in Hsucc.
  set (bs := computeNewBasketsAndNeeded basketsHeldBottom
              s.(Storage.basketsNeeded) s.(Storage.backingBuffer)) in *.
  pose proof (BackingManagerValidityProofs.computeNewBasketsAndNeeded_outputs_nonneg
                basketsHeldBottom s.(Storage.basketsNeeded)
                s.(Storage.backingBuffer) Hvalid) as [Hmint_nn Hneeded_nn].
  destruct (forwardRevenueIter bs.(BasketState.needed) rTokenTotal rsrTotal assets)
    as [agg | p q] eqn:Hiter; [|discriminate].
  injection Hsucc as Hr; subst r.
  pose proof (forwardRevenueIter_outputs_nonneg
                bs.(BasketState.needed) rTokenTotal rsrTotal assets agg
                Hneeded_nn HrT HrS Hassets Hiter) as Hnn.
  destruct Hnn as (Hr_nn & Ht_nn & Hd_nn).
  cbn. repeat split; assumption.
Qed.

(** ---------- FWD-PV: forwardRevenue preserves storage validity. ---------- *)

(** If the input storage is well-formed and the basket-update
    inputs are well-formed, the output storage is also well-formed.

    [tradeStatus] / [pendingTrade] consistency is preserved because
    [forwardRevenue] doesn't touch them. [basketsNeeded'] is bounded by
    its input — production-faithful inheritance via the call-boundary
    hypothesis [basketsNeeded' <= FIX_MAX].

    We thread the post-state uint192 bound for [basketsNeeded] as a
    hypothesis (this is the [_safeWrap] proxy at the call boundary;
    see WISDOM.md R008). *)
Theorem forwardRevenue_preserves_validity
    (s : Storage.t) (basketsHeldBottom : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList) (r : ForwardRevenueResult.t) :
  Valid.storage s ->
  uint192_valid basketsHeldBottom ->
  Valid.assetList assets ->
  forwardRevenue s basketsHeldBottom rTokenTotal rsrTotal assets
    = Result.Success r ->
  uint192_valid r.(ForwardRevenueResult.storage').(Storage.basketsNeeded) ->
  Valid.storage r.(ForwardRevenueResult.storage').
Proof.
  intros Hs Hbhb Hassets Hsucc Hbn'.
  destruct Hs as [Hbn Hbuf Hbufmax Hcons].
  unfold forwardRevenue in Hsucc.
  set (bs := computeNewBasketsAndNeeded basketsHeldBottom
              s.(Storage.basketsNeeded) s.(Storage.backingBuffer)) in *.
  destruct (forwardRevenueIter _ _ _ _) as [agg | p q] eqn:Hiter;
    [|discriminate].
  injection Hsucc as Hr; subst r. cbn in *.
  constructor; cbn; assumption.
Qed.

End BackingManagerForwardIter.
