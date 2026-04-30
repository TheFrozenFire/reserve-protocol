(** GnosisTrade simulation.

    Mirrors protocol/contracts/plugins/trading/GnosisTrade.sol — the
    Reserve batch-auction wrapper around Gnosis EasyAuction.

    Two pieces of math drive the contract's safety:

      (A) [minBuyAmount] — derived in TradeLib.prepareTradeSell and lifted
          to qBuyTok before being handed to GnosisTrade.init. Composes:
            inner = mul_ceil(sellAmount, FIX_ONE - slippage)
            b     = safeMulDiv_ceil(inner, sellLow, buyHigh)
            mba   = shiftl_toUint(b, buyDecimals, CEIL)
          Every step rounds CEIL — bidder-favorable.

      (B) [worstCasePrice] / settlement floor — set in init() and checked
          in settle():
            worstCasePrice = shiftl_toFix(minBuyAmount, 9).divu(sellAmount, FLOOR)
            clearingPrice  = shiftl_toFix(boughtAmt+1, 9).divu(max(soldAmt,1), FLOOR)
            violation iff clearingPrice < worstCasePrice
          The +1 pads in adjustedBuyAmt absorb 1 wei of Gnosis-side
          defensive rounding.

    Companion CAS witnesses:
      cas/gnosis_trade/min_buy_amount.gp
      cas/gnosis_trade/settlement_floor.gp

    Revert coverage:
      Modeled:  [worstCasePrice] returns 0 on [sellAmount = 0]
                (avoids div-by-zero). [settle] early-returns with
                [checked = false] when the trade returned 100% of
                the sell tokens (matches production line 219 guard).
      Deferred: well-formed inputs at the calling boundary.
      Not modeled: any auth or status-machine reverts (init / settle
                gating), Gnosis EasyAuction interaction failures,
                cancellation-window enforcement (the boundary at
                [cancellationEndTime] is computed but the revert if
                cancellation is attempted past it lives in production
                only).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module GnosisTrade.

Import FixLib.

(** Auction-fee denominator (matches [FEE_DENOMINATOR] in the contract). *)
Definition FEE_DENOMINATOR : Z := 1000.

(** Cancellation window: the first 90% of an auction is cancellable. *)
Definition CANCEL_WINDOW : Z := 9 * 10^17.    (** 0.9 in D18 *)

(** D27 scale used for [worstCasePrice] / [clearingPrice]. *)
Definition D27_ONE : Z := 10^27.

(** ===== minBuyAmount derivation =====
    Mirrors TradeLib.prepareTradeSell L76-84 plus GnosisTrade.init's
    interpretation. We expose it as one composed function on the D18-scale
    inputs the production code uses, parameterized on the buy-token
    decimals so 6-dec USDC and 18-dec ERC20s both round through.

    All three internal rounding decisions are CEIL: [fix_mul] inner,
    [safeMulDiv] outer, [shiftl_toUint] decimal-lift. CEIL-everywhere keeps
    the contract's settlement floor at-or-above the exact-rational ideal.

    Inputs:
      sellAmount {sellTok, D18 wei}
      slippage   {1, D18}                 0 <= slippage <= FIX_ONE
      sellLow    {UoA/sellTok, D18}       > 0
      buyHigh    {UoA/buyTok,  D18}       > 0
      buyDec     {1}                       buy-token decimals (uint8)
*)

(** [shiftl_toUint] for the buy-token decimal lift, CEIL mode.
    Mirrors FixLib.shiftl_toUint at the L173 call site in TradeLib. For
    [d <= 18] we divide by [10^(18-d)] with CEIL; for [d > 18] we
    multiply. Pure on Z — no uint256 cap modeled here. *)
Definition shiftl_toUint_ceil (x : Z) (d : Z) : Z :=
  let sh := 18 - d in
  if 0 <=? sh then divrnd x (10 ^ sh) RoundingMode.CEIL
  else x * 10 ^ (- sh).

Definition shiftl_toUint_floor (x : Z) (d : Z) : Z :=
  let sh := 18 - d in
  if 0 <=? sh then divrnd x (10 ^ sh) RoundingMode.FLOOR
  else x * 10 ^ (- sh).

(** [shiftl_toFix x 9]: lift a uint qBuyTok to D27 by multiplying by
    [10^(9 + 18) = 10^27]. Used inside [worstCasePrice] / [clearingPrice]. *)
Definition shiftl_toFix_d27 (x : Z) : Z := x * 10^27.

(** safeMulDiv with CEIL rounding: ceil((a * b) / c).
    No FIX_MAX cap modeled at the Z level — the Solidity wrapper reverts
    on overflow; the simulation assumes inputs in range. *)
Definition safeMulDiv_ceil (a b c : Z) : Z :=
  if c =? 0 then 0   (* avoid 0/0 — production assumes c > 0 *)
  else if andb (a =? 0) (b =? 0) then 0
  else divrnd (a * b) c RoundingMode.CEIL.

(** [minBuyAmount(sellAmount, slippage, sellLow, buyHigh, buyDec)]: the
    full TradeLib.prepareTradeSell chain into qBuyTok.

    The inner CEIL on [mul (FIX_ONE - slippage)] is bidder-favorable: a
    higher [b] means a higher floor on the auction return.
*)
Definition minBuyAmount
    (sellAmount slippage sellLow buyHigh : Z) (buyDec : Z) : Z :=
  let inner := mul sellAmount (minus FIX_ONE slippage) RoundingMode.CEIL in
  let b     := safeMulDiv_ceil inner sellLow buyHigh in
  shiftl_toUint_ceil b buyDec.

(** [worstCasePrice(minBuyAmount_qBuy, sellAmount_qSell)]: D27{qBuy/qSell}.
    Production: shiftl_toFix(minBuyAmount, 9).divu(sellAmount, FLOOR).
    The FLOOR rounding is trader-favorable (lowers the floor by < 1 D27 wei). *)
Definition worstCasePrice
    (minBuyAmount_qBuy sellAmount_qSell : Z) : Z :=
  if sellAmount_qSell =? 0 then 0
  else divrnd (shiftl_toFix_d27 minBuyAmount_qBuy)
              sellAmount_qSell
              RoundingMode.FLOOR.

(** ===== Settlement-floor math =====
    Mirrors [GnosisTrade.settle()] at L185-230.

    Inputs:
      initBal       {qSellTok}  — sell-token balance at init()
      sellBalAfter  {qSellTok}  — sell-token balance after the auction
      boughtAmt     {qBuyTok}   — buy-token balance after the auction

    Outputs:
      [soldAmt] = initBal - sellBalAfter
      [clearingPrice] = (boughtAmt+1) * 1e27 / max(soldAmt, 1)
      [violation] = clearingPrice < worstCasePrice

    The [if (sellBal < initBal)] guard at L219 means a trade that returned
    100% of the sell tokens skips the violation check entirely; we model
    that with an explicit early-return in [settle].
*)

Module SettleResult.
  Record t : Set := {
    soldAmt       : Z;       (** {qSellTok} *)
    clearingPrice : Z;       (** D27{qBuy/qSell}; 0 in the no-fill branch *)
    violation     : bool;    (** clearingPrice < worstCasePrice (when checked) *)
    checked       : bool;    (** false when the L219 guard skipped the check *)
  }.
End SettleResult.

Definition settle
    (initBal sellBalAfter boughtAmt worstCase : Z)
    : SettleResult.t :=
  if initBal <=? sellBalAfter then
    {| SettleResult.soldAmt := 0;
       SettleResult.clearingPrice := 0;
       SettleResult.violation := false;
       SettleResult.checked := false |}
  else
    let soldAmt := initBal - sellBalAfter in
    let adjustedSoldAmt := Z.max soldAmt 1 in
    let adjustedBuyAmt  := boughtAmt + 1 in
    let clearingPrice :=
      divrnd (shiftl_toFix_d27 adjustedBuyAmt)
             adjustedSoldAmt
             RoundingMode.FLOOR in
    {| SettleResult.soldAmt := soldAmt;
       SettleResult.clearingPrice := clearingPrice;
       SettleResult.violation := clearingPrice <? worstCase;
       SettleResult.checked := true |}.

(** Settlement floor: minimum [boughtAmt] (given a fixed [soldAmt]) that
    keeps [clearingPrice >= worstCasePrice]. Inverting:
        (boughtAmt + 1) * 1e27 / max(soldAmt, 1) >= worstCasePrice
    With FLOOR division, this holds iff
        (boughtAmt + 1) * 1e27 >= worstCasePrice * max(soldAmt, 1).
    Solving for boughtAmt:
        boughtAmt >= ceil(worstCasePrice * max(soldAmt, 1) / 1e27) - 1
    The settlement floor is the right-hand side, clipped at 0. *)
Definition settlement_floor (worstCase soldAmt : Z) : Z :=
  let adj := Z.max soldAmt 1 in
  let raw := divrnd (worstCase * adj) D27_ONE RoundingMode.CEIL - 1 in
  Z.max raw 0.

(** [canSettle now endTime status_open]: settle() is callable when status
    is OPEN and now >= endTime. *)
Definition canSettle (now endTime : Z) (status_open : bool) : bool :=
  andb status_open (endTime <=? now).

(** [cancellationEndTime startTime auctionLength]: matches the contract's
    formula at L150-152. The first [auctionLength * CANCEL_WINDOW / FIX_ONE]
    seconds are cancellable; the residual (auctionLength * 0.1) is locked. *)
Definition cancellationEndTime (startTime auctionLength : Z) : Z :=
  startTime + (auctionLength * CANCEL_WINDOW) / FIX_ONE.

End GnosisTrade.
