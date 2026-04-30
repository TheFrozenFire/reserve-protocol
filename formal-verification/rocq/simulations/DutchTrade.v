(** DutchTrade simulation.

    Mirrors protocol/contracts/plugins/trading/DutchTrade.sol — a 4-piecewise
    falling-price dutch auction. The protocol exposes:

      bidAmount(timestamp) = _bidAmount(_price(timestamp))

    where [_price] decays from ~1000x bestPrice down to worstPrice over
    [startTime, endTime]:

      0%-20%   : geometric  ~1000*best -> 1.5*best   (price = best * 1.5 / BASE^k, CEIL)
      20%-45%  : linear     1.5*best -> 1.0*best     (FLOOR drop)
      45%-95%  : linear     best -> worst            (FLOOR drop)
      95%-100% : constant   worst                    (flat)

    [_bidAmount(price)] = sellAmount.mul(price, CEIL).shiftl_toUint(buyDecimals, CEIL).

    On-chain reads of [block.timestamp] are passed as explicit [now]; the
    sim is pure. We model the curve as a function of progression in D18
    (FIX_ONE = 10^18 scale) — same vocabulary as the production code.

    Revert coverage:
      Modeled:  none — [bidPrice] is total. Out-of-range [t] returns
                the nearest endpoint instead of reverting.
      Deferred: well-formedness of the auction via [Valid.t]
                ([startTime < endTime], [worstPrice <= bestPrice],
                positive bestPrice, decimals in range).
      Not modeled: production's revert when called outside
                [[startTime, endTime]]. Production's status-machine
                guards on [bid()] / [settle()] (not modeled at the
                state-transition level here). External transfer
                failures during [bid()].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module DutchTrade.

Import FixLib.

(** ---- Curve constants (mirror DutchTrade.sol) ---- *)
Definition FIVE_PERCENT       : Z := 5  * 10^16.
Definition TWENTY_PERCENT     : Z := 20 * 10^16.
Definition TWENTY_FIVE_PERCENT: Z := 25 * 10^16.
Definition FORTY_FIVE_PERCENT : Z := 45 * 10^16.
Definition FIFTY_PERCENT      : Z := 50 * 10^16.
Definition NINETY_FIVE_PERCENT: Z := 95 * 10^16.

Definition MAX_EXP        : Z := 6502287 * 10^18.
Definition BASE_DEC       : Z := 999999  * 10^12.   (* 0.999999 in D18 *)
Definition ONE_POINT_FIVE : Z := 150 * 10^16.       (* 1.5 in D18 *)

(** ---- Auction parameters ----
    [startTime, endTime] are uint48 timestamps; [bestPrice] and [worstPrice]
    are D18 fixed-point with [worstPrice <= bestPrice]. *)
Module Auction.
  Record t : Set := {
    startTime  : U256.t;
    endTime    : U256.t;
    bestPrice  : U256.t;
    worstPrice : U256.t;
    sellAmount : U256.t;   (** {sellTok} as D18, i.e. wei *)
    buyDecimals : Z;        (** decimals of buy ERC20, used by shiftl_toUint *)
  }.
End Auction.

(** ---- progression(t) = (t - startTime) * FIX_ONE / (endTime - startTime), FLOOR ---- *)
Definition progression (a : Auction.t) (t : U256.t) : U256.t :=
  ((t - a.(Auction.startTime)) * FIX_ONE) / (a.(Auction.endTime) - a.(Auction.startTime)).

(** ---- Phase 1: geometric. -----
    exp_fix   = MAX_EXP * (TWENTY_PERCENT - prog) / TWENTY_PERCENT, ROUND
    exp_int   = exp_fix / FIX_ONE, ROUND  (toUint with ROUND)
    price     = bestPrice * 1.5 / BASE^exp_int, CEIL

    The CAS witness expands [BASE^exp_int / FIX_ONE^(exp_int - 1)] to keep
    the denominator in D18 units. Here we keep the production formulation:
    [powu BASE_DEC exp_int] is in D18, and [mul bestPrice * 1.5 / D18, CEIL]
    follows. *)
Definition phase1_price (a : Auction.t) (prog : Z) : Z :=
  let exp_fix := divrnd (MAX_EXP * (TWENTY_PERCENT - prog)) TWENTY_PERCENT
                        RoundingMode.ROUND in
  let exp_int := divrnd exp_fix FIX_ONE RoundingMode.ROUND in
  let denom_d18 := powu BASE_DEC exp_int in
  (* bestPrice.mulDiv(ONE_POINT_FIVE, denom_d18, CEIL) *)
  divrnd (a.(Auction.bestPrice) * ONE_POINT_FIVE) denom_d18 RoundingMode.CEIL.

(** ---- Phase 2: linear 1.5*best -> best ----
    highPrice = best.mul(1.5, CEIL)
    return    = highPrice - (highPrice - best) * (prog - 20%) / 25%, FLOOR *)
Definition phase2_price (a : Auction.t) (prog : Z) : Z :=
  let highPrice := mul a.(Auction.bestPrice) ONE_POINT_FIVE RoundingMode.CEIL in
  let drop := ((highPrice - a.(Auction.bestPrice)) * (prog - TWENTY_PERCENT))
                / TWENTY_FIVE_PERCENT in
  highPrice - drop.

(** ---- Phase 3: linear best -> worst ---- *)
Definition phase3_price (a : Auction.t) (prog : Z) : Z :=
  let drop := ((a.(Auction.bestPrice) - a.(Auction.worstPrice))
                 * (prog - FORTY_FIVE_PERCENT))
                / FIFTY_PERCENT in
  a.(Auction.bestPrice) - drop.

(** ---- Phase 4: flat at worstPrice ---- *)
Definition phase4_price (a : Auction.t) : Z :=
  a.(Auction.worstPrice).

(** ---- bidPrice: top-level dispatcher (the model of [_price]). -----
    Defined for [t in [startTime, endTime]]. Outside the range, the
    contract reverts; here we return the closest endpoint as a total
    function so we can reason without preconditions cluttering each
    statement. The lemmas restrict to the in-range case. *)
Definition bidPrice (a : Auction.t) (t : U256.t) : U256.t :=
  let prog := progression a t in
  if prog <? TWENTY_PERCENT then phase1_price a prog
  else if prog <? FORTY_FIVE_PERCENT then phase2_price a prog
  else if prog <? NINETY_FIVE_PERCENT then phase3_price a prog
  else phase4_price a.

(** ---- bidAmount: the model of [_bidAmount] composed with [_price]. -----
    bidAmount(t) = sellAmount.mul(price, CEIL).shiftl_toUint(buyDecimals, CEIL)

    With [buyDecimals = 18] the shiftl_toUint(., 18, CEIL) call has shift = 0
    and acts as identity. With [buyDecimals < 18] it divides by 10^(18 - d)
    using CEIL rounding. With [buyDecimals > 18] it multiplies. *)
Definition bidAmount_at_price (a : Auction.t) (price : Z) : Z :=
  let mul_ceil := mul a.(Auction.sellAmount) price RoundingMode.CEIL in
  let shift := 18 - a.(Auction.buyDecimals) in
  if 0 <=? shift then
    (* shift positive: divide by 10^shift, CEIL. *)
    divrnd mul_ceil (10 ^ shift) RoundingMode.CEIL
  else
    (* shift negative: multiply by 10^(-shift). *)
    mul_ceil * (10 ^ (- shift)).

Definition bidAmount (a : Auction.t) (t : U256.t) : U256.t :=
  bidAmount_at_price a (bidPrice a t).

(** ---- bidAmount FLOOR variant. -----
    The hypothetical "bug" version where both rounding stages use FLOOR.
    Defined here so it's visible to both the proofs and the xcheck files
    when stating CEIL >= FLOOR rounding-direction invariants. *)
Definition bidAmount_floor_variant (a : Auction.t) (price : Z) : Z :=
  let mul_floor := mul a.(Auction.sellAmount) price RoundingMode.FLOOR in
  let shift := 18 - a.(Auction.buyDecimals) in
  if 0 <=? shift then
    divrnd mul_floor (10 ^ shift) RoundingMode.FLOOR
  else
    mul_floor * (10 ^ (- shift)).

(** ---- Validity predicate: the type-level invariants the contract enforces. ---- *)
Module Valid.
  Record t (a : Auction.t) : Prop := {
    times_ordered : a.(Auction.startTime) < a.(Auction.endTime);
    prices_ordered : a.(Auction.worstPrice) <= a.(Auction.bestPrice);
    bestPrice_pos : 0 < a.(Auction.bestPrice);
    worstPrice_nonneg : 0 <= a.(Auction.worstPrice);
    sellAmount_nonneg : 0 <= a.(Auction.sellAmount);
    buyDecimals_range : 0 <= a.(Auction.buyDecimals) <= 36;
  }.
End Valid.

End DutchTrade.
