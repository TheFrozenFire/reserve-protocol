(** Integration lemma: full revenue circuit conservation.

    Cross-domain composition closing the revenue accounting loop:

      BackingManager.computeSurplusSplit (per-asset surplus)
        --> SurplusSplit { rTokenAmount, rsrAmount, dust }
        --> Distributor.distributeAmounts (consumes rTokenAmount, rsrAmount)
        --> per-destination transferAmts + remainder dust

    The conservation property closes the loop on the Distributor side:
    each leg of the surplus split, when fed into [distributeAmounts],
    is exactly conserved as (sum of transfers) + dust. The total amount
    sent through the distributor equals the corresponding surplus
    component — no value vanishes between BackingManager output and
    Distributor inner-loop output.

    This composes:
      - the produced [SurplusSplit.rTokenAmount] / [.rsrAmount] from
        [BackingManager.computeSurplusSplit] (any inputs, any branch)
      - [DistributorProofs.share_conservation] (sum + dust = amount)

    Symmetric across both legs (rToken side: isRSR=false; RSR side:
    isRSR=true), so it covers both arms of the revenue circuit driven
    by the BackingManager forwardRevenue path.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Reserve.simulations.Distributor.
Require Import Reserve.proofs.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationRevenueFullCircuit.

Import DistributorProofs.

(** Full-circuit conservation: BackingManager surplus split feeds
    Distributor on both legs and the inner-loop arithmetic conserves
    every wei.

      sum(transfers_rt) + dust_rt = split.rTokenAmount
      sum(transfers_rs) + dust_rs = split.rsrAmount

    No preconditions on the BackingManager inputs — conservation is
    purely additive on the Distributor side and holds for any successful
    or unsuccessful surplus split (we only consume the produced output
    fields, whatever they are). The BackingManager output bounds are not
    required to close conservation; they're orthogonal. *)
Lemma revenue_full_circuit_conservation
    (needed quantity bal : U256.t)
    (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    (split : BackingManager.SurplusSplit.t)
    (ds : Distributor.Storage) :
  BackingManager.computeSurplusSplit
    needed quantity bal decimals rTokenTotal rsrTotal
      = BackingManager.Result.Success split ->
  let dist_rt :=
    Distributor.distributeAmounts ds
      split.(BackingManager.SurplusSplit.rTokenAmount) false in
  let dist_rs :=
    Distributor.distributeAmounts ds
      split.(BackingManager.SurplusSplit.rsrAmount) true in
  sumZ (fst dist_rt) + snd dist_rt
    = split.(BackingManager.SurplusSplit.rTokenAmount) /\
  sumZ (fst dist_rs) + snd dist_rs
    = split.(BackingManager.SurplusSplit.rsrAmount).
Proof.
  intros _ dist_rt dist_rs.
  split.
  - (* rToken leg: apply share_conservation with amount = rTokenAmount,
       isRSR = false. *)
    pose proof
      (share_conservation ds
         split.(BackingManager.SurplusSplit.rTokenAmount) false) as Hrt.
    simpl in Hrt. exact Hrt.
  - (* RSR leg: apply share_conservation with amount = rsrAmount,
       isRSR = true. *)
    pose proof
      (share_conservation ds
         split.(BackingManager.SurplusSplit.rsrAmount) true) as Hrs.
    simpl in Hrs. exact Hrs.
Qed.

End IntegrationRevenueFullCircuit.
