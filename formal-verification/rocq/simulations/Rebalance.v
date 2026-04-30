(** RecollateralizationLib.basketRange simulation.

    Mirrors protocol/contracts/p1/mixins/RecollateralizationLib.sol —
    the [basketRange()] function that produces the (low, high) BU range
    used by trade selection during recollateralization.

    Production [basketRange] does a per-asset loop over the registry,
    summing oracle-priced surplus / deficit contributions and folding
    in [minTradeVolume] dust-loss + [maxTradeSlippage]. The full
    function is stack-deep and entangled with the asset registry; this
    simulation extracts the *algebraic skeleton* — the relationship
    between the inputs basketsHeldBottom / basketsHeldTop / per-asset
    price-error contributions and the resulting (low, high).

    The companion CAS scripts in cas/rebalance/ work at the same level
    of abstraction: the noise bound is derived as a function of
    (basketLength, minTradeVolume, buPriceHigh) without simulating the
    full per-asset oracle loop.

    Modeled here:
      - the "rounding noise" terms used to give (low, high) headroom
      - the production bound  noise_loose(bl, mtv, bup) = bl * dust + bl^2 + 2
      - the tight alternative bound  noise_tight(bl, mtv, bup) = bl * dust + 4*bl + 4
      - an abstract [basketRange] that encloses any (low, high) inside the
        algebraic envelope
        [basketsHeldBottom - lowSlack <= low <= basketsHeldBottom]
        [basketsHeldTop <= high <= basketsHeldTop + highSlack]

    Out of scope (handled in the production `*MathHarness` files):
      - per-asset oracle calls
      - the basketHandler / assetRegistry indirection
      - reverts on FIX_MAX overflow

    Revert coverage:
      Modeled:  none — pure algebra over [RangeInputs].
      Deferred: well-formedness of inputs via [Valid.inputs]
                (8-field record).
      Not modeled: FIX_MAX overflow on the inner per-asset
                arithmetic (handled by [_safeWrap] in production), any
                oracle-failure reverts.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module RebalanceLib.

Definition FIX_ONE : Z := 10 ^ 18.
Definition FIX_MAX : Z := 2 ^ 192 - 1.

(** --------------------------------------------------------------- *)
(** Noise / headroom primitives                                     *)
(** --------------------------------------------------------------- *)

(** Ceiling division over [Z]. CAS uses
      [if num % d == 0 then num \ d else num \ d + 1]; we match. *)
Definition ceil_div (num d : Z) : Z :=
  if (num mod d) =? 0 then num / d else num / d + 1.

(** The BU-equivalent of one [minTradeVolume] dust threshold.
    Source: cas/rebalance/basket_range_noise.gp:41
      [dustNoiseBU(mtv, buPriceHigh) = ceil(mtv * FIX_ONE / buPriceHigh)]. *)
Definition dustNoiseBU (mtv buPriceHigh : Z) : Z :=
  ceil_div (mtv * FIX_ONE) buPriceHigh.

(** Production rounding-noise bound from FuzzP1.sol::isBasketRangeSmaller:
      [bl * (dustNoiseBU + bl) + 2] = [bl * dust + bl^2 + 2].
    Used by Echidna to decide whether the "post <= pre + noise"
    property check is meaningful. *)
Definition noise_loose (bl mtv buPriceHigh : Z) : Z :=
  bl * dustNoiseBU mtv buPriceHigh + bl * bl + 2.

(** Tight alternative bound (cas/rebalance/noise_bound_tightness.gp):
      [bl * dust + 4*bl + 4].
    Strictly smaller than [noise_loose] for [bl >= 5], by the comment's
    claim [4*bl + 2 <= bl^2] for [bl >= 5]. *)
Definition noise_tight (bl mtv buPriceHigh : Z) : Z :=
  bl * dustNoiseBU mtv buPriceHigh + 4 * bl + 4.

(** --------------------------------------------------------------- *)
(** Abstract basketRange                                            *)
(** --------------------------------------------------------------- *)

(** A range output. *)
Module BasketRange.
  Record t : Set := {
    low  : Z;   (** {BU} pessimistic lower bound (range.bottom in Solidity) *)
    high : Z;   (** {BU} optimistic  upper bound (range.top    in Solidity) *)
  }.
End BasketRange.

(** Inputs to the algebraic skeleton. We carry just the supply / held
    figures plus aggregate dust-and-slack budgets, parameterized so the
    proofs can quantify over any oracle / per-asset breakdown. *)
Module RangeInputs.
  Record t : Set := {
    supplyTotal       : Z;   (** {BU} basketsNeeded *)
    basketsHeldBottom : Z;   (** {BU} pessimistic-priced basket count *)
    basketsHeldTop    : Z;   (** {BU} optimistic-priced  basket count *)
    lowSlack          : Z;   (** {BU} signed slack subtracted from bottom *)
    highSlack         : Z;   (** {BU} signed slack added    to    top    *)
  }.
End RangeInputs.

(** The clipped basketRange. After the per-asset accumulation,
    Solidity does:
      if range.top    > basketsNeeded then range.top    := basketsNeeded
      if range.bottom > range.top      then range.bottom := range.top
    We model exactly that final clipping over abstract inputs. *)
Definition basketRange (i : RangeInputs.t) : BasketRange.t :=
  let raw_high := i.(RangeInputs.basketsHeldTop) + i.(RangeInputs.highSlack) in
  let raw_low  := i.(RangeInputs.basketsHeldBottom) - i.(RangeInputs.lowSlack) in
  let high1 := Z.min raw_high i.(RangeInputs.supplyTotal) in
  let low1  := Z.min raw_low  high1 in
  {| BasketRange.low  := low1;
     BasketRange.high := high1; |}.

(** --------------------------------------------------------------- *)
(** Validity predicate                                              *)
(** --------------------------------------------------------------- *)
Module Valid.

  (** The well-formedness predicate the production code maintains:

      - non-negative supply / held figures,
      - basketsHeldBottom <= basketsHeldTop  (the price-low/high ordering),
      - basketsHeldTop <= supplyTotal       (the [Cap basketsHeld.top] step),
      - non-negative slack,
      - supplyTotal bounded by uint192 (FIX_MAX).

      The slack is bounded above by the tight noise envelope when the
      caller's noise model holds — proofs that depend on a specific
      bound carry it as a hypothesis. *)
  Record inputs (i : RangeInputs.t) : Prop := {
    supplyTotal_nonneg : 0 <= i.(RangeInputs.supplyTotal);
    bhBottom_nonneg    : 0 <= i.(RangeInputs.basketsHeldBottom);
    bhTop_nonneg       : 0 <= i.(RangeInputs.basketsHeldTop);
    bhBot_le_top       : i.(RangeInputs.basketsHeldBottom)
                          <= i.(RangeInputs.basketsHeldTop);
    bhTop_le_supply    : i.(RangeInputs.basketsHeldTop)
                          <= i.(RangeInputs.supplyTotal);
    lowSlack_nonneg    : 0 <= i.(RangeInputs.lowSlack);
    highSlack_nonneg   : 0 <= i.(RangeInputs.highSlack);
    supplyTotal_u192   : i.(RangeInputs.supplyTotal) <= FIX_MAX;
  }.
End Valid.

End RebalanceLib.
