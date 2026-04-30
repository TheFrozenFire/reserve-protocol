(** Integration lemma: BackingManager surplus split feeds Distributor cleanly.

    Cross-domain composition along the revenue path:

      BackingManager.computeSurplusSplit (per-asset surplus)
        --> rTokenAmount, rsrAmount  (non-negative under input validity)
        --> Distributor.distributeAmounts (consumes these as [amount])
        --> per-destination transferAmts and dust  (non-negative).

    This lemma stitches together the two existing per-domain outputs
    bounds:

      - [BackingManager_validity.computeSurplusSplit_outputs_nonneg]
      - [Distributor_validity.distributeAmounts_transferAmts_nonneg]
      - [Distributor_validity.distributeAmounts_dust_nonneg]

    so that a successful surplus split, fed directly into the
    distributor, never produces a negative transfer or negative dust on
    either revenue leg.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Reserve.simulations.Distributor.
Require Import Reserve.proofs.BackingManager_validity.
Require Import Reserve.proofs.Distributor_validity.
Require Import Reserve.proofs.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationRevenuePath.

Import BackingManagerValidityProofs.
Import DistributorValidity.

(** Composition lemma: when [computeSurplusSplit] succeeds with
    non-negative inputs and standard share-validity holds for the
    distributor, feeding either [rTokenAmount] or [rsrAmount] into
    [distributeAmounts] produces non-negative transfer amounts and
    non-negative dust.

    The result keeps the two legs symmetric so it covers both arms of
    the revenue path the BackingManager drives. *)
Lemma surplus_then_distribute_outputs_nonneg
    (needed quantity bal : U256.t)
    (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    (split : BackingManager.SurplusSplit.t)
    (s : Distributor.Storage)
    (isRSR : bool) :
  0 <= needed ->
  0 <= quantity ->
  0 <= bal ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  0 <= decimals ->
  BackingManager.computeSurplusSplit
    needed quantity bal decimals rTokenTotal rsrTotal
      = BackingManager.Result.Success split ->
  DistributorProofs.validShares s ->
  let amount :=
    if isRSR
    then split.(BackingManager.SurplusSplit.rsrAmount)
    else split.(BackingManager.SurplusSplit.rTokenAmount) in
  let pair := Distributor.distributeAmounts s amount isRSR in
  Forall (fun a => 0 <= a) (fst pair) /\ 0 <= snd pair.
Proof.
  intros Hneeded Hquantity Hbal HrT HrS Hdec Hsucc Hval.
  pose proof
    (computeSurplusSplit_outputs_nonneg
       needed quantity bal decimals rTokenTotal rsrTotal split
       Hneeded Hquantity Hbal HrT HrS Hdec Hsucc) as Hsplit_nn.
  destruct Hsplit_nn as (HrsrA & HrTokA & Hdust).
  set (amount :=
         if isRSR
         then split.(BackingManager.SurplusSplit.rsrAmount)
         else split.(BackingManager.SurplusSplit.rTokenAmount)).
  assert (Hamt_nn : 0 <= amount).
  { unfold amount. destruct isRSR; assumption. }
  split.
  - exact (distributeAmounts_transferAmts_nonneg s amount isRSR Hamt_nn Hval).
  - exact (distributeAmounts_dust_nonneg s amount isRSR Hamt_nn Hval).
Qed.

End IntegrationRevenuePath.
