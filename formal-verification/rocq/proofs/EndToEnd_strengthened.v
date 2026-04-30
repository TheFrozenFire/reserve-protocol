(** Strengthened system-level end-to-end joint-bound theorem.

    [EndToEnd.v] composes per-domain validity invariants for three
    domains (Throttle, Furnace, StRSR). This module strengthens that
    statement by composing the ["scalars jointly bounded"] lemmas
    exported by each domain's [_uint256_bounds.v] file across **eight
    storage-state domains**:

      Throttle       (4 fields, <= 4 * UINT256_MAX)
      Furnace        (3 fields, <= 3 * UINT256_MAX)
      StRSR          (4 fields, <= 4 * UINT256_MAX)
      Collateral     (6 fields, <= 6 * UINT256_MAX)
      DutchTrade     (6 fields, <= 6 * UINT256_MAX)
      Rebalance      (5 fields, <= 5 * UINT256_MAX)
      BackingManager.BasketState  (3 fields, <= 3 * UINT256_MAX)
      BackingManager.SurplusSplit (3 fields, <= 3 * UINT256_MAX)

    Total: 34 storage scalars, jointly bounded by [34 * UINT256_MAX].

    The remaining domains (TradeLib, IssuancePremium, GnosisTrade,
    BasketHandler, Distributor) export joint bounds **parameterised by
    raw integer arguments and call-site hypotheses** (e.g. requiring
    [0 <= mba] and an envelope hypothesis on the divrnd output). Folding
    those into a single unified statement requires propagating their
    domain-specific call-site preconditions through the theorem; that
    materially obscures the storage-state composition statement that is
    the point of this lemma. They are intentionally skipped here. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

(** Domain simulations and validity. *)
Require Import Reserve.simulations.Throttle.
Require Import Reserve.simulations.Furnace.
Require Import Reserve.simulations.StRSR.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.DutchTrade.
Require Import Reserve.simulations.Rebalance.
Require Import Reserve.simulations.BackingManager.

(** Per-domain uint256-bounds modules. Required (not Imported) so the
    qualified module names remain explicit at the use sites — this
    avoids collisions on common names ([Valid], [InputBounded], [Storage],
    [Result], [BasketState]) that several domains share. *)
Require Reserve.proofs.Throttle_uint256_bounds.
Require Reserve.proofs.Furnace_uint256_bounds.
Require Reserve.proofs.StRSR_uint256_bounds.
Require Reserve.proofs.Collateral_uint256_bounds.
Require Reserve.proofs.DutchTrade_uint256_bounds.
Require Reserve.proofs.Rebalance_uint256_bounds.
Require Reserve.proofs.BackingManager_uint256_bounds.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module EndToEndStrengthened.

Import FixLib.

(** Headline strengthened end-to-end theorem.

    Across eight storage-state domains, the sum of all 34
    uint256-typed scalar fields is bounded by [34 * UINT256_MAX].

    This composes:
      - Throttle.t                  via Throttle_scalars_jointly_bounded
      - Furnace.Storage.t           via Furnace_scalars_jointly_bounded
      - StRSR.Storage.t             via StRSR_scalars_jointly_bounded
      - Collateral.State.t          via Collateral_scalars_jointly_bounded
      - DutchTrade.Auction.t        via DutchTrade_scalars_jointly_bounded
      - RebalanceLib.RangeInputs.t  via Rebalance_inputs_jointly_bounded
      - BackingManager.BasketState  via BasketState_scalars_jointly_bounded
      - BackingManager.SurplusSplit via SurplusSplit_scalars_jointly_bounded
*)
Theorem all_domain_scalars_jointly_bounded
    (t  : ThrottleLib.Throttle.t)
    (f  : Furnace.Storage.t)
    (s  : StRSR.Storage.t)
    (cd : Collateral.State.t)
    (a  : DutchTrade.Auction.t)
    (ri : RebalanceLib.RangeInputs.t)
    (bs : BackingManager.BasketState.t)
    (sp : BackingManager.SurplusSplit.t) :
  (* Throttle hypotheses. *)
  ThrottleLib.Valid.throttle t ->
  Throttle_uint256_bounds.ThrottleUint256Bounds.InputBounded.t t ->
  (* Furnace hypotheses. *)
  Furnace.Valid.t f ->
  Furnace_uint256_bounds.FurnaceUint256Bounds.InputBounded.t f ->
  (* StRSR hypotheses. *)
  StRSR.Valid.t s ->
  StRSR_uint256_bounds.StRSRUint256Bounds.InputBounded.t s ->
  (* Collateral hypotheses. *)
  Collateral.Valid.t cd ->
  Collateral_uint256_bounds.CollateralUint256Bounds.InputBounded.t cd ->
  (* DutchTrade hypotheses. *)
  DutchTrade.Valid.t a ->
  DutchTrade_uint256_bounds.DutchTradeUint256Bounds.InputBounded.t a ->
  (* Rebalance hypotheses. *)
  RebalanceLib.Valid.inputs ri ->
  Rebalance_uint256_bounds.RebalanceUint256Bounds.InputBounded.t ri ->
  (* BackingManager BasketState + SurplusSplit hypotheses. *)
  BackingManager_uint256_bounds.BackingManagerUint256Bounds.BasketStateBounded.t bs ->
  BackingManager_uint256_bounds.BackingManagerUint256Bounds.SurplusSplitBounded.t sp ->
  (* Conclusion: sum of all 34 storage scalars across 8 domains. *)
  (* Throttle: 4 fields *)
    t.(ThrottleLib.Throttle.lastAvailable)
  + t.(ThrottleLib.Throttle.params).(ThrottleLib.Params.amtRate)
  + t.(ThrottleLib.Throttle.params).(ThrottleLib.Params.pctRate)
  + t.(ThrottleLib.Throttle.lastTimestamp)
  (* Furnace: 3 fields *)
  + f.(Furnace.Storage.ratio)
  + f.(Furnace.Storage.lastPayout)
  + f.(Furnace.Storage.lastPayoutBal)
  (* StRSR: 4 fields *)
  + s.(StRSR.Storage.totalStRSR)
  + s.(StRSR.Storage.totalRSRStaked)
  + s.(StRSR.Storage.totalRewardsAccumulated)
  + s.(StRSR.Storage.ratio)
  (* Collateral: 6 fields *)
  + cd.(Collateral.State.whenDefault)
  + cd.(Collateral.State.exposedReferencePrice)
  + cd.(Collateral.State.delayUntilDefault)
  + cd.(Collateral.State.revenueShowing)
  + cd.(Collateral.State.pegBottom)
  + cd.(Collateral.State.pegTop)
  (* DutchTrade: 6 fields *)
  + a.(DutchTrade.Auction.startTime)
  + a.(DutchTrade.Auction.endTime)
  + a.(DutchTrade.Auction.bestPrice)
  + a.(DutchTrade.Auction.worstPrice)
  + a.(DutchTrade.Auction.sellAmount)
  + a.(DutchTrade.Auction.buyDecimals)
  (* Rebalance: 5 fields *)
  + ri.(RebalanceLib.RangeInputs.supplyTotal)
  + ri.(RebalanceLib.RangeInputs.basketsHeldBottom)
  + ri.(RebalanceLib.RangeInputs.basketsHeldTop)
  + ri.(RebalanceLib.RangeInputs.lowSlack)
  + ri.(RebalanceLib.RangeInputs.highSlack)
  (* BackingManager.BasketState: 3 fields *)
  + bs.(BackingManager.BasketState.basketsNeeded)
  + bs.(BackingManager.BasketState.mintAmount)
  + bs.(BackingManager.BasketState.needed)
  (* BackingManager.SurplusSplit: 3 fields *)
  + sp.(BackingManager.SurplusSplit.rsrAmount)
  + sp.(BackingManager.SurplusSplit.rTokenAmount)
  + sp.(BackingManager.SurplusSplit.dust)
    <= 34 * UINT256_MAX.
Proof.
  intros HtV HtB HfV HfB HsV HsB HcV HcB HaV HaB HrV HrB HbsB HspB.
  pose proof
    (Throttle_uint256_bounds.ThrottleUint256Bounds.Throttle_scalars_jointly_bounded
       t HtV HtB) as HT.
  pose proof
    (Furnace_uint256_bounds.FurnaceUint256Bounds.Furnace_scalars_jointly_bounded
       f HfV HfB) as HF.
  pose proof
    (StRSR_uint256_bounds.StRSRUint256Bounds.StRSR_scalars_jointly_bounded
       s HsV HsB) as HS.
  pose proof
    (Collateral_uint256_bounds.CollateralUint256Bounds.Collateral_scalars_jointly_bounded
       cd HcV HcB) as HC.
  pose proof
    (DutchTrade_uint256_bounds.DutchTradeUint256Bounds.DutchTrade_scalars_jointly_bounded
       a HaV HaB) as HA.
  pose proof
    (Rebalance_uint256_bounds.RebalanceUint256Bounds.Rebalance_inputs_jointly_bounded
       ri HrV HrB) as HR.
  pose proof
    (BackingManager_uint256_bounds.BackingManagerUint256Bounds.BasketState_scalars_jointly_bounded
       bs HbsB) as HBS.
  pose proof
    (BackingManager_uint256_bounds.BackingManagerUint256Bounds.SurplusSplit_scalars_jointly_bounded
       sp HspB) as HSS.
  lia.
Qed.

End EndToEndStrengthened.
