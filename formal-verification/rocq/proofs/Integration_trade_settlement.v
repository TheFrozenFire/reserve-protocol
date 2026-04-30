(** Integration lemma: TradeLib.buyAmount feeds GnosisTrade.settlement_floor.

    Cross-domain composition along the trade-settlement path:

      TradeLib.buyAmount  (under Valid.buyInputs)
        --> non-negative qBuyTok lower-bound
        --> consumed as worstCase by GnosisTrade.settlement_floor
        --> settlement_floor is monotone non-decreasing in soldAmt.

    Both libraries operate over the same qBuyTok unit space; the
    [Valid.buyInputs] preconditions ([buyAmount_nonneg]) discharge the
    [0 <= worstCase] hypothesis required by
    [GnosisTradeChain.settlement_floor_monotone_in_soldAmt] without any
    further side-conditions, so this is the clean joint-shape lemma:
    a TradeLib output, fed as a settlement floor input, preserves the
    GnosisTrade soldAmt-monotonicity invariant on the auction floor.

    Composes:
      - [TradeLibValidityProofs.buyAmount_nonneg]
      - [GnosisTradeChain.settlement_floor_monotone_in_soldAmt]
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.simulations.GnosisTrade.
Require Import Reserve.proofs.TradeLib_validity.
Require Import Reserve.proofs.GnosisTrade_chain.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module IntegrationTradeSettlement.

Import FixLib.
Import Reserve.simulations.TradeLib.TradeLib.
Import Reserve.simulations.GnosisTrade.GnosisTrade.

(** Composition lemma: when [Valid.buyInputs] holds, [TradeLib.buyAmount]
    produces a non-negative qBuyTok value; feeding that value as the
    [worstCase] parameter to [GnosisTrade.settlement_floor] yields a
    settlement floor that is monotone non-decreasing in [soldAmt].

    Reads as: a winning bid against a TradeLib-derived floor scales
    monotonically with the realized sold amount. *)
Lemma tradeLib_buy_then_gnosis_settlement_consistent
    (s slippage sellLow buyHigh : Z)
    (soldAmt1 soldAmt2 : Z) :
  Valid.buyInputs s slippage sellLow buyHigh ->
  soldAmt1 <= soldAmt2 ->
  settlement_floor (buyAmount s slippage sellLow buyHigh) soldAmt1
    <= settlement_floor (buyAmount s slippage sellLow buyHigh) soldAmt2.
Proof.
  intros Hv Hsa.
  apply GnosisTradeChain.settlement_floor_monotone_in_soldAmt.
  - apply TradeLibValidityProofs.buyAmount_nonneg; exact Hv.
  - exact Hsa.
Qed.

End IntegrationTradeSettlement.
