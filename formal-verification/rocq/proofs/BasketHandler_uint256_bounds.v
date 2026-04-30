(** BasketHandler uint256 upper-bound derivation.

    Mirrors [proofs/Throttle_uint256_bounds.v],
    [proofs/IssuancePremium_uint256_bounds.v], and
    [proofs/Distributor_uint256_bounds.v]. The BasketHandler simulation
    in [simulations/BasketHandler.v] is the algebraic core of [quote()]
    — its [Storage] is an ordered list of [(asset, refAmt)] pairs and
    its primary entry points are the per-asset [quote_one] and the
    list-output [quoteQuantities].

    Production has uint256 ceilings on every output by EVM semantics —
    [quote()] returns a [uint256[]] and any internal multiplication that
    would not fit reverts under Solidity 0.8. This file packages those
    output bounds under the [_uint256_bounds] naming used by the other
    domains, gated on a small [InputBounded] predicate that captures
    the call-boundary fact that each per-asset quote fits in uint256.

    The pattern is identical to [DistributorUint256Bounds]: validity
    (here: [BasketHandlerValidityProofs.quoteQuantities_nonneg]) gives
    pointwise non-negativity, and the [InputBounded] hypothesis closes
    the upper bound — both lifted to a list-wide [Forall].

    Companion validity:
      proofs/BasketHandler_validity.v
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Reserve.proofs.BasketHandler_validity.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Module BasketHandlerUint256Bounds.

Import FixLib.
Import BasketHandler.
Import BasketHandlerValidityProofs.

(** ---------- FIX_MAX < UINT256_MAX ---------- *)
Lemma FIX_MAX_le_UINT256_MAX :
  FIX_MAX <= UINT256_MAX.
Proof.
  unfold FIX_MAX, UINT256_MAX.
  vm_compute. discriminate.
Qed.

(** ---------- InputBounded predicate ----------

    Captures the call-boundary uint256 bound on a per-asset quote. On
    chain this is structural — every value flowing through [quote()]
    must fit in [uint256] or the transaction reverts. We expose it
    here as an explicit hypothesis on the inputs so the bound carries
    through the kernel and lifts cleanly to the list output.

    [refAmt] and [baskets] are uint192 fixed-point values on chain, so
    they are individually bounded by [FIX_MAX]. Their product divided
    by [FIX_SCALE] is the {qTok} value which Solidity guarantees fits
    in uint256 by reverting otherwise — modeled here as the explicit
    [quote_u256] field. *)
Module InputBounded.
  Record t (refAmt baskets : U256.t) (mode : RoundingMode.t) : Prop := {
    refAmt_nonneg  : 0 <= refAmt;
    refAmt_u192    : refAmt  <= FIX_MAX;
    baskets_nonneg : 0 <= baskets;
    baskets_u192   : baskets <= FIX_MAX;
    quote_u256     : quote_one refAmt baskets mode <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-asset output bound ----------

    Re-packages the [quote_u256] field of [InputBounded] under the
    [_uint256_bounds] naming. *)
Lemma quote_one_uint256_bounds
    (refAmt baskets : U256.t) (mode : RoundingMode.t) :
  InputBounded.t refAmt baskets mode ->
  quote_one refAmt baskets mode <= UINT256_MAX.
Proof. intros [_ _ _ _ H]. exact H. Qed.

(** Companion: per-asset quote is non-negative and bounded by
    [UINT256_MAX]. Combines [quote_one_nonneg] (from
    [BasketHandler_validity.v]) with the upper bound above. *)
Lemma quote_one_uint256_range
    (refAmt baskets : U256.t) (mode : RoundingMode.t) :
  InputBounded.t refAmt baskets mode ->
  0 <= quote_one refAmt baskets mode <= UINT256_MAX.
Proof.
  intros Hib.
  pose proof Hib as [Hr_nn _ Hb_nn _ Hhi].
  split.
  - apply quote_one_nonneg; assumption.
  - exact Hhi.
Qed.

(** ---------- list-output bound: quoteQuantities ----------

    Storage-wide [InputBounded] predicate: every entry's [refAmt] is a
    valid uint192 fixed-point value, and the per-asset quote against
    [baskets] fits in uint256 for the chosen rounding mode. *)
Definition StorageInputBounded
    (s : BasketHandler.Storage) (baskets : U256.t) (mode : RoundingMode.t) : Prop :=
  Forall (fun e => InputBounded.t e.(BasketEntry.refAmt) baskets mode) s.

(** Every quantity in [quoteQuantities] is bounded by [UINT256_MAX].
    This is the headline list-output guarantee callers need — the
    full {qTok} payload returned to issuance / redemption fits in
    uint256. *)
Lemma quoteQuantities_uint256_bounds
    (s : BasketHandler.Storage) (baskets : U256.t) (mode : RoundingMode.t) :
  StorageInputBounded s baskets mode ->
  Forall (fun q => q <= UINT256_MAX) (quoteQuantities s baskets mode).
Proof.
  intros Hsib.
  unfold quoteQuantities.
  induction s as [|e rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hsib as [|? ? Hhd Htl]; subst.
    apply Forall_cons.
    + simpl. apply quote_one_uint256_bounds. exact Hhd.
    + apply IH. exact Htl.
Qed.

(** Companion: every quantity is non-negative and bounded by
    [UINT256_MAX]. Combines [quoteQuantities_nonneg] (validity) with
    the upper bound above. *)
Lemma quoteQuantities_uint256_range
    (s : BasketHandler.Storage) (baskets : U256.t) (mode : RoundingMode.t) :
  0 <= baskets ->
  StorageInputBounded s baskets mode ->
  Forall (fun q => 0 <= q <= UINT256_MAX) (quoteQuantities s baskets mode).
Proof.
  intros Hb Hsib.
  assert (Href_nn : Forall (fun e => 0 <= e.(BasketEntry.refAmt)) s).
  { induction Hsib as [|e rest Hhd Htl IH].
    - apply Forall_nil.
    - apply Forall_cons; [destruct Hhd as [Hr _ _ _ _]; exact Hr | exact IH]. }
  pose proof (quoteQuantities_nonneg s baskets mode Hb Href_nn) as Hge.
  pose proof (quoteQuantities_uint256_bounds s baskets mode Hsib) as Hle.
  clear Hb Hsib Href_nn.
  induction Hge as [|x xs Hx Hxs IH]; simpl.
  - apply Forall_nil.
  - inversion Hle as [|? ? Hxle Hxsle]; subst.
    apply Forall_cons.
    + split; assumption.
    + apply IH. exact Hxsle.
Qed.

(** ---------- storage bound: baskets count ----------

    The [Storage] is a [list] in Coq; on chain the corresponding
    [erc20s] array is indexed by [uint256] and so its length is
    structurally bounded by [UINT256_MAX]. We expose this as a
    standalone predicate so callers that range over basket entries
    can quote a uint256 cardinality without re-deriving it. *)
Definition StorageBounded (s : BasketHandler.Storage) : Prop :=
  Z.of_nat (length s) <= UINT256_MAX.

Lemma StorageBounded_nil : StorageBounded nil.
Proof.
  unfold StorageBounded; simpl.
  unfold UINT256_MAX. vm_compute. discriminate.
Qed.

End BasketHandlerUint256Bounds.
