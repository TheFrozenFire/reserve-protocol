(** Complete system-level end-to-end joint-bound theorem.

    Extends [EndToEnd_strengthened.v]'s 8-storage-state composition with
    the five remaining domains whose joint output bounds are
    *call-arg-bounded* rather than storage-state-bounded:

      TradeLib         (2 outputs: buyAmount, buyAmountPre)
      IssuancePremium  (2 inputs + 1 output: pegPrice, targetPerRef, premium)
      GnosisTrade      (2 outputs: worstCasePrice, settlement_floor)
      BasketHandler    (1 output: quote_one for a single asset)
      Distributor      (1 input: amount; sum of transfers + dust = amount)

    Strategy: take the per-call inputs as additional universally
    quantified arguments, take each domain's call-site envelope
    hypothesis as an additional `Prop`, and compose all 13 joint bounds
    (8 storage-state + 5 functional) into a single inequality.

    Total scalars composed: 34 (storage) + 2 (TradeLib) + 3
    (IssuancePremium) + 2 (GnosisTrade) + 1 (BasketHandler) + 1
    (Distributor amount) = 43, jointly bounded by [43 * UINT256_MAX].

    Each functional domain contributes its previously proved
    [_outputs_jointly_bounded] / [_inputs_outputs_jointly_bounded] /
    [quote_one_uint256_bounds] / [distributeAmounts_sum_uint256_bounds]
    lemma; the proof body is a fan of [pose proof] followed by [lia]. *)

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
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.simulations.IssuancePremium.
Require Import Reserve.simulations.GnosisTrade.
Require Import Reserve.simulations.BasketHandler.
Require Import Reserve.simulations.Distributor.

(** Per-domain uint256-bounds modules. Required (not Imported) so the
    qualified module names remain explicit at use sites — this avoids
    collisions on common names ([Valid], [InputBounded], [Storage],
    [Result], [BasketState]) that several domains share. *)
Require Reserve.proofs.Throttle_uint256_bounds.
Require Reserve.proofs.Furnace_uint256_bounds.
Require Reserve.proofs.StRSR_uint256_bounds.
Require Reserve.proofs.Collateral_uint256_bounds.
Require Reserve.proofs.DutchTrade_uint256_bounds.
Require Reserve.proofs.Rebalance_uint256_bounds.
Require Reserve.proofs.BackingManager_uint256_bounds.
Require Reserve.proofs.TradeLib_uint256_bounds.
Require Reserve.proofs.IssuancePremium_uint256_bounds.
Require Reserve.proofs.GnosisTrade_uint256_bounds.
Require Reserve.proofs.BasketHandler_uint256_bounds.
Require Reserve.proofs.Distributor_uint256_bounds.
Require Reserve.proofs.Distributor_validity.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module EndToEndComplete.

Import FixLib.

(** Headline complete end-to-end theorem.

    Across **thirteen** domains — eight storage-state plus five
    call-arg-bounded functional — the sum of all composed scalars is
    bounded by [43 * UINT256_MAX]. The five functional domains each
    take their own call inputs as explicit universally quantified
    arguments and their own envelope hypotheses as explicit [Prop]s. *)
Theorem all_domain_outputs_jointly_bounded
    (* ---- 8 storage states (same as EndToEnd_strengthened) ---- *)
    (t  : ThrottleLib.Throttle.t)
    (f  : Furnace.Storage.t)
    (s  : StRSR.Storage.t)
    (cd : Collateral.State.t)
    (a  : DutchTrade.Auction.t)
    (ri : RebalanceLib.RangeInputs.t)
    (bs : BackingManager.BasketState.t)
    (sp : BackingManager.SurplusSplit.t)
    (* ---- TradeLib call args ---- *)
    (tl_s tl_slippage tl_sellLow tl_buyHigh : Z)
    (* ---- IssuancePremium call args ---- *)
    (ip_enable ip_lastSaveIsNow : bool)
    (ip_pegPrice ip_targetPerRef : Z)
    (* ---- GnosisTrade call args ---- *)
    (gt_mba gt_sa gt_wcp gt_soldAmt : Z)
    (* ---- BasketHandler call args ---- *)
    (bh_refAmt bh_baskets : U256.t)
    (bh_mode : RoundingMode.t)
    (* ---- Distributor call args ---- *)
    (di_storage : Distributor.Storage)
    (di_amount : U256.t)
    (di_isRSR : bool) :
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
  (* IssuancePremium call envelope. *)
  0 <= ip_targetPerRef <= FIX_MAX ->
  0 <= ip_pegPrice <= FIX_MAX ->
  (* GnosisTrade call envelope. *)
  0 <= gt_mba ->
  0 <= gt_sa ->
  0 <= gt_wcp ->
  gt_mba * GnosisTrade.GnosisTrade.D27_ONE / Z.max gt_sa 1 <= UINT256_MAX ->
  divrnd (gt_wcp * Z.max gt_soldAmt 1) GnosisTrade.GnosisTrade.D27_ONE RoundingMode.CEIL <= UINT256_MAX ->
  (* BasketHandler call envelope. *)
  BasketHandler_uint256_bounds.BasketHandlerUint256Bounds.InputBounded.t
    bh_refAmt bh_baskets bh_mode ->
  (* Distributor call envelope. *)
  Distributor_uint256_bounds.DistributorUint256Bounds.InputBounded.t di_amount ->
  (* ----------------- Conclusion ----------------- *)
  (* 34 storage scalars (as in EndToEnd_strengthened) ... *)
    t.(ThrottleLib.Throttle.lastAvailable)
  + t.(ThrottleLib.Throttle.params).(ThrottleLib.Params.amtRate)
  + t.(ThrottleLib.Throttle.params).(ThrottleLib.Params.pctRate)
  + t.(ThrottleLib.Throttle.lastTimestamp)
  + f.(Furnace.Storage.ratio)
  + f.(Furnace.Storage.lastPayout)
  + f.(Furnace.Storage.lastPayoutBal)
  + s.(StRSR.Storage.totalStRSR)
  + s.(StRSR.Storage.totalRSRStaked)
  + s.(StRSR.Storage.totalRewardsAccumulated)
  + s.(StRSR.Storage.ratio)
  + cd.(Collateral.State.whenDefault)
  + cd.(Collateral.State.exposedReferencePrice)
  + cd.(Collateral.State.delayUntilDefault)
  + cd.(Collateral.State.revenueShowing)
  + cd.(Collateral.State.pegBottom)
  + cd.(Collateral.State.pegTop)
  + a.(DutchTrade.Auction.startTime)
  + a.(DutchTrade.Auction.endTime)
  + a.(DutchTrade.Auction.bestPrice)
  + a.(DutchTrade.Auction.worstPrice)
  + a.(DutchTrade.Auction.sellAmount)
  + a.(DutchTrade.Auction.buyDecimals)
  + ri.(RebalanceLib.RangeInputs.supplyTotal)
  + ri.(RebalanceLib.RangeInputs.basketsHeldBottom)
  + ri.(RebalanceLib.RangeInputs.basketsHeldTop)
  + ri.(RebalanceLib.RangeInputs.lowSlack)
  + ri.(RebalanceLib.RangeInputs.highSlack)
  + bs.(BackingManager.BasketState.basketsNeeded)
  + bs.(BackingManager.BasketState.mintAmount)
  + bs.(BackingManager.BasketState.needed)
  + sp.(BackingManager.SurplusSplit.rsrAmount)
  + sp.(BackingManager.SurplusSplit.rTokenAmount)
  + sp.(BackingManager.SurplusSplit.dust)
  (* ... + 9 functional outputs/inputs ... *)
  + TradeLib.TradeLib.buyAmount tl_s tl_slippage tl_sellLow tl_buyHigh
  + TradeLib.TradeLib.buyAmountPre tl_s tl_slippage tl_sellLow tl_buyHigh
  + ip_pegPrice
  + ip_targetPerRef
  + IssuancePremium.IssuancePremium.issuancePremium
      ip_enable ip_lastSaveIsNow ip_pegPrice ip_targetPerRef
  + GnosisTrade.GnosisTrade.worstCasePrice gt_mba gt_sa
  + GnosisTrade.GnosisTrade.settlement_floor gt_wcp gt_soldAmt
  + BasketHandler.BasketHandler.quote_one bh_refAmt bh_baskets bh_mode
  + di_amount
    <= 43 * UINT256_MAX.
Proof.
  intros HtV HtB HfV HfB HsV HsB HcV HcB HaV HaB HrV HrB HbsB HspB
         Hip_t Hip_p Hgt_mba Hgt_sa Hgt_wcp Hgt_envWcp Hgt_envSf
         Hbh Hdi.
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
  pose proof
    (TradeLib_uint256_bounds.TradeLibUint256Bounds.buyAmount_outputs_jointly_bounded
       tl_s tl_slippage tl_sellLow tl_buyHigh) as HTL.
  pose proof
    (IssuancePremium_uint256_bounds.IssuancePremiumUint256Bounds.issuancePremium_inputs_outputs_jointly_bounded
       ip_enable ip_lastSaveIsNow ip_pegPrice ip_targetPerRef Hip_t Hip_p) as HIP.
  pose proof
    (GnosisTrade_uint256_bounds.GnosisTradeUint256Bounds.gnosis_trade_outputs_jointly_bounded
       gt_mba gt_sa gt_wcp gt_soldAmt
       Hgt_mba Hgt_sa Hgt_wcp Hgt_envWcp Hgt_envSf) as HGT.
  pose proof
    (BasketHandler_uint256_bounds.BasketHandlerUint256Bounds.quote_one_uint256_bounds
       bh_refAmt bh_baskets bh_mode Hbh) as HBH.
  destruct Hdi as [Hdi_nn Hdi_hi].
  lia.
Qed.

End EndToEndComplete.
