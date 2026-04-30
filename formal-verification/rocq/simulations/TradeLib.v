(** TradeLib simulation.

    Mirrors protocol/contracts/p1/mixins/TradeLib.sol — specifically the
    buy-amount computation in [prepareTradeSell] (Solidity line 76):

      uint192 b = s.mul(FIX_ONE.minus(maxTradeSlippage), CEIL)
                   .safeMulDiv(trade.prices.sellLow, trade.prices.buyHigh, CEIL);

    This is the load-bearing math behind the slippage-sufficiency guarantee
    audited in cas/trade_lib/slippage_sufficiency.gp and the CEIL rounding
    direction witnessed in cas/trade_lib/ceil_rounding_witness.gp.

    Modeled here (pure Z, no Solidity runtime):
      - safeMulDiv (saturating on FIX_MAX, returns 0 when a = 0 or b = 0)
      - buyAmount (post-#1283 mitigation: CEIL inner mul + CEIL outer)
      - buyAmountPre (pre-mitigation: FLOOR inner mul + CEIL outer)
      - minTradeSize (price = 0 saturates to FIX_MAX, otherwise CEIL)
      - the comparison kernel from isEnoughToSell (whole-token side; the
        [shiftl_toUint > 1] qTok check is decimals-dependent and out of
        scope at this level)

    Out of scope (not needed for the slippage / ceil-rounding witnesses):
      - the asset-registry indirection (sell.maxTradeVolume, etc.)
      - prepareTradeToCoverDeficit: it composes prepareTradeSell with one
        extra div(_, FIX_ONE - slippage, CEIL); we expose the kernel piece
        as [coverDeficitSellAmount] and leave the full call as a follow-up
        when the harness needs it.

    Revert coverage:
      Modeled:  saturation behavior of [safeMulDiv] (returns
                [FIX_MAX] on FIX_MAX-input or division by zero, instead
                of reverting). Matches production semantics — these
                are NOT revert paths in production either, they are
                explicit saturation paths in [FixLib.safeMulDiv].
      Deferred: input bounds via [Valid.buyInputs]: uint192 on each
                scalar, [slippage <= FIX_ONE], [buyHigh > 0]. The last
                two correspond to production [require]s in
                [prepareTradeSell].
      Not modeled: revert paths on the unchecked [mul] (uint192
                overflow) — sim works in [Z]. Caller-context reverts
                in [prepareTradeSell] (asset-registry lookups, etc.).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module TradeLib.

Import FixLib.

(** ---------------------------------------------------------------- *)
(** safeMulDiv: saturating uint192 a*b/c with an explicit rounding   *)
(** mode. Mirrors Fixed.sol#L562-L609.                                *)
(** ---------------------------------------------------------------- *)

(** Pure-Z model of [safeMulDiv(a, b, c, mode)].

    Edge cases (matching production):
      - a = 0 OR b = 0   ->  0
      - a = FIX_MAX OR b = FIX_MAX OR c = 0   ->  FIX_MAX  (saturate)
      - else: divrnd (a*b) c mode, clamped to <= FIX_MAX.

    The pure FLOOR/CEIL kernel here ignores the unchecked-block 256-bit
    intermediate the production code uses for overflow avoidance — that's
    a numerical-precision detail the production proof of correctness
    handles separately (it's the [mulDiv256] muldiv-by-Newton-iteration
    inversion). For the slippage-sufficiency reasoning we only need the
    rounding direction; the inner mul-div is exact arithmetic over Z. *)
Definition safeMulDiv (a b c : Z) (mode : RoundingMode.t) : Z :=
  if orb (a =? 0) (b =? 0) then 0
  else if orb (orb (a =? FIX_MAX) (b =? FIX_MAX)) (c =? 0) then FIX_MAX
  else
    let raw := divrnd (a * b) c mode in
    if FIX_MAX <=? raw then FIX_MAX else raw.

(** ---------------------------------------------------------------- *)
(** TradeLib buy-amount kernel                                       *)
(** ---------------------------------------------------------------- *)

(** Post-#1283-mitigation buy amount. The inner [mul(s, FIX_ONE - slippage, CEIL)]
    is bounded by FIX_MAX in production via [_safeWrap] (revert if the
    rounded product overflows uint192). For the algebraic model we expose
    the unchecked variant; bounded callers gate it with a uint192_valid
    side-condition.

    This is the formula at TradeLib.sol#L76-L80. *)
Definition buyAmount (s slippage sellLow buyHigh : Z) : Z :=
  let inner := mul s (FIX_ONE - slippage) RoundingMode.CEIL in
  safeMulDiv inner sellLow buyHigh RoundingMode.CEIL.

(** Pre-mitigation buy amount: inner mul defaults to FLOOR (Fixed.sol#L253
    overload). Same outer composition. We model this so the rounding-direction
    witness can show [buyAmount >= buyAmountPre] across the boundary corpus. *)
Definition buyAmountPre (s slippage sellLow buyHigh : Z) : Z :=
  let inner := mul s (FIX_ONE - slippage) RoundingMode.FLOOR in
  safeMulDiv inner sellLow buyHigh RoundingMode.CEIL.

(** ---------------------------------------------------------------- *)
(** prepareTradeToCoverDeficit kernel                                *)
(** ---------------------------------------------------------------- *)

(** [coverDeficitSellAmount(b, slippage, sellLow, buyHigh)] models the
    per-deficit slippage-adjusted sell amount used inside
    [prepareTradeToCoverDeficit] (TradeLib.sol#L137-L145):

       exactSell    = mulDiv(b, buyHigh, sellLow, CEIL)
       slippedSell  = div(exactSell, FIX_ONE - slippage, CEIL)

    Assumes sellLow > 0 and 0 <= slippage < FIX_ONE (the [require]s in
    the caller). *)
Definition coverDeficitSellAmount (b slippage sellLow buyHigh : Z) : Z :=
  let exactSell := divrnd (b * buyHigh) sellLow RoundingMode.CEIL in
  div exactSell (FIX_ONE - slippage) RoundingMode.CEIL.

(** ---------------------------------------------------------------- *)
(** minTradeSize / isEnoughToSell                                    *)
(** ---------------------------------------------------------------- *)

(** [minTradeSize(minTradeVolume, price)]: TradeLib.sol#L174-L178.

    When price = 0, the function returns FIX_MAX. Otherwise it is the
    CEIL-rounded division minTradeVolume / price, clamped up to 1 if
    the result rounds to 0. *)
Definition minTradeSize (minTradeVolume price : Z) : Z :=
  if price =? 0 then FIX_MAX
  else
    let size := div minTradeVolume price RoundingMode.CEIL in
    if size =? 0 then 1 else size.

(** [isEnoughToSell] whole-token component: amt >= minTradeSize.

    The full production check also ANDs in [shiftl_toUint(amt, decimals) > 1]
    to defend against trading-platform quanta rounding; that branch is
    decimals-dependent and orthogonal to the slippage math, so we factor
    it out and prove the whole-token side here. *)
Definition isEnoughToSell_whole
    (amt price minTradeVolume : Z) : bool :=
  minTradeSize minTradeVolume price <=? amt.

(** ---------------------------------------------------------------- *)
(** Validity predicate                                               *)
(** ---------------------------------------------------------------- *)
Module Valid.

  (** Inputs to [buyAmount] under uint192 storage:
        s, sellLow, buyHigh, slippage all live in [0, FIX_MAX].
        slippage <= FIX_ONE  (the production assert in TradeLib.sol).
        buyHigh > 0          (production [require]).
      The [s] term comes in capped at min(maxTradeSize, sellAmount), but
      the algebraic kernel works for any uint192-valid s. *)
  Record buyInputs (s slippage sellLow buyHigh : Z) : Prop := {
    s_u192        : uint192_valid s;
    slippage_u192 : uint192_valid slippage;
    sellLow_u192  : uint192_valid sellLow;
    buyHigh_u192  : uint192_valid buyHigh;
    slippage_lim  : slippage <= FIX_ONE;
    buyHigh_pos   : 0 < buyHigh;
  }.

End Valid.

End TradeLib.
