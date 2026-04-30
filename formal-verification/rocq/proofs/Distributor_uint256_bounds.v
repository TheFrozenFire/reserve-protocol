(** Distributor uint256 upper-bound derivation.

    Mirrors [proofs/Throttle_uint256_bounds.v] and
    [proofs/StRSR_uint256_bounds.v]. The Distributor's storage shape is a
    list of [(address, RevenueShare)] pairs whose [rTokenDist] / [rsrDist]
    fields are uint16 in production — already structurally bounded by
    [UINT16_MAX <= UINT256_MAX]. So unlike StRSR/Throttle there are no
    "missing storage-scalar uint256 ceilings" for [Valid].

    What [DistributorProofs.validShares] does *not* express is that the
    [amount] flowing into [distributeAmounts] fits in uint256 (the EVM
    guarantees this by construction — [amount] arrives as a [uint256]
    function argument). Once [amount <= UINT256_MAX] is in scope, every
    output amount is bounded by [amount] (INV-4: [each_transfer_le_amount])
    and so by [UINT256_MAX], and the conservation law
    (INV-1: [share_conservation]) gives the joint sum bound on the
    transfer list plus dust.

    This file packages those output bounds under the [_uint256_bounds]
    naming convention used by the other domains, gated on a small
    [InputBounded] predicate that captures the call-boundary fact
    [0 <= amount <= UINT256_MAX]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Distributor.
Require Import Reserve.proofs.Distributor.
Require Import Reserve.proofs.Distributor_validity.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorUint256Bounds.

Import FixLib.
Import Distributor.
Import DistributorProofs.
Import DistributorValidity.

(** ---------- InputBounded predicate ----------

    Captures the call-boundary uint256 bound on [amount]. On chain this
    is structural — [distribute(erc20, amount)] takes [amount] as a
    [uint256] — so any successful invocation satisfies it. We expose it
    here as an explicit hypothesis so the bound carries through proof
    obligations symbolically. *)
Module InputBounded.
  Record t (amount : U256.t) : Prop := {
    amount_nonneg : 0 <= amount;
    amount_u256   : amount <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-output bound ----------

    Every transfer amount produced by [distributeAmounts] is at most
    [amount], hence at most [UINT256_MAX]. This re-packages
    [each_transfer_le_amount] under the [_uint256_bounds] naming. *)
Lemma distributeAmounts_transferAmts_uint256_bounds
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  InputBounded.t amount ->
  validShares s ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let amts := fst pair in
  Forall (fun a => a <= UINT256_MAX) amts.
Proof.
  intros [Hnn Hhi] Hval.
  pose proof (each_transfer_le_amount s amount isRSR Hnn Hval) as Hle.
  simpl in Hle |- *.
  eapply Forall_impl; [| exact Hle].
  simpl. intros a Ha. eapply Z.le_trans; [exact Ha | exact Hhi].
Qed.

(** Companion: every transfer amount is non-negative and bounded by
    [UINT256_MAX]. Combines [distributeAmounts_transferAmts_nonneg]
    (from [Distributor_validity.v]) with the upper bound above. *)
Lemma distributeAmounts_transferAmts_uint256_range
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  InputBounded.t amount ->
  validShares s ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let amts := fst pair in
  Forall (fun a => 0 <= a <= UINT256_MAX) amts.
Proof.
  intros Hib Hval.
  pose proof Hib as [Hnn _].
  pose proof (distributeAmounts_transferAmts_nonneg s amount isRSR Hnn Hval) as Hge.
  pose proof (distributeAmounts_transferAmts_uint256_bounds s amount isRSR Hib Hval) as Hle.
  simpl in Hge, Hle |- *.
  clear Hib Hval Hnn.
  induction Hge as [|x xs Hx Hxs IH]; simpl.
  - apply Forall_nil.
  - inversion Hle as [|? ? Hxle Hxsle]; subst.
    apply Forall_cons.
    + split; assumption.
    + apply IH. exact Hxsle.
Qed.

(** ---------- dust bound ----------

    [dust] is non-negative and bounded above by [amount <= UINT256_MAX].
    Follows from the share-conservation law plus
    [distributeAmounts_transferAmts_nonneg]. *)
Lemma distributeAmounts_dust_uint256_bounds
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  InputBounded.t amount ->
  validShares s ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let dust := snd pair in
  0 <= dust <= UINT256_MAX.
Proof.
  intros [Hnn Hhi] Hval.
  pose proof (distributeAmounts_dust_nonneg s amount isRSR Hnn Hval) as Hdge.
  pose proof (share_conservation s amount isRSR) as Hcons.
  simpl in Hdge, Hcons |- *.
  split; [exact Hdge|].
  (* dust <= amount <= UINT256_MAX, via sum(amts) >= 0 and conservation *)
  pose proof (distributeAmounts_transferAmts_nonneg s amount isRSR Hnn Hval) as Hamts_nn.
  simpl in Hamts_nn.
  assert (Hsum_nn : 0 <= sumZ (fst (Distributor.distributeAmounts s amount isRSR))).
  { apply sumZ_nonneg. exact Hamts_nn. }
  unfold sumZ in Hsum_nn, Hcons.
  lia.
Qed.

(** ---------- joint sum bound ----------

    The conservation law [sum(transferAmts) + dust = amount] combined
    with [amount <= UINT256_MAX] directly gives the joint bound. This
    is the headline output guarantee callers need: the entire
    distribution payload fits in uint256. *)
Lemma distributeAmounts_sum_uint256_bounds
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  InputBounded.t amount ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let amts := fst pair in
  let dust := snd pair in
  sumZ amts + dust = amount /\ amount <= UINT256_MAX.
Proof.
  intros [_ Hhi].
  pose proof (share_conservation s amount isRSR) as Hcons.
  simpl in Hcons |- *.
  split; [exact Hcons | exact Hhi].
Qed.

End DistributorUint256Bounds.
