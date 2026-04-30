(** BasketHandler simulation.

    Mirrors protocol/contracts/p1/BasketHandler.sol — specifically the
    [quote(amount, rounding)] entry point that converts a {BU} basket-units
    quantity into per-asset {qTok} token quantities.

    On-chain, [quote] iterates over [basket.erc20s], looks up each token's
    [refAmt] and [refPerTok], and returns

        qTok_i = (refAmt_i / refPerTok_i) * amount * (premium_i?)
                 |> shiftl_toUint(decimals_i, rounding)

    The asset-registry / oracle / decimals layer is intentionally OUT of
    scope here. We model just the algebraic quote conversion that the
    rounding-direction and round-trip safety claims rest on:

        qTok_i = refAmt_i * baskets / FIX_ONE   (rounded by [mode])

    The "{BU}" amount is a uint192 fixed-point value, [refAmt] is also
    uint192 fixed-point (ref/BU), and [FIX_ONE = 10^18] is the scaling
    factor. The result is an integer token quantity — rounded UP for
    issuance (so the protocol receives at least enough collateral) and
    DOWN for redemption (so the protocol does not over-pay).

    Storage here is simply the ordered list of [(asset_id, refAmt)] pairs —
    the part of the [Basket] struct relevant to [quote].

    Companion CAS witnesses:
      cas/basket_handler/quote_rounding_direction.gp
      cas/basket_handler/quote_round_trip.gp

    Revert coverage:
      Modeled:  [redeem_one] returns 0 on [refAmt = 0] (avoids
                div-by-zero; algebraically vacuous because production
                doesn't store zero refAmts in the basket).
      Deferred: well-formed basket as a precondition on [Storage].
      Not modeled: basket-not-set lifecycle reverts, oracle-failure
                reverts, asset-registry-mismatch reverts. The whole
                basket-management lifecycle is outside this kernel.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module BasketHandler.

Import FixLib.

(** A [BasketEntry] is a single (asset id, refAmount) pair. The asset id
    is an opaque token identifier; we model it as [U256.t] (matching
    Address.t = U256.t in the rocq-of-solidity tree). [refAmt] is in
    {ref/BU}, uint192 fixed-point. *)
Module BasketEntry.
  Record t : Set := {
    asset  : U256.t;
    refAmt : U256.t;   (** {ref/BU}, uint192 fixed-point *)
  }.
End BasketEntry.

(** Storage = ordered list of basket entries. *)
Definition Storage : Set := list BasketEntry.t.

(** Per-asset quote: [refAmt * baskets / FIX_ONE], rounded by [mode].
    Mirrors the algebraic core of [quote()]; see BasketHandler.sol#L487-L517.

    Concretely this is [FixLib.mulu_toUint refAmt baskets mode] specialised
    to "two fixed-point factors, integer result". *)
Definition quote_one
    (refAmt baskets : U256.t) (mode : RoundingMode.t) : U256.t :=
  FixLib.mulu_toUint refAmt baskets mode.

(** [quote(s, baskets, mode)] returns the per-asset {qTok} list, in the
    storage order. The on-chain [quote] also returns the parallel array of
    asset addresses; we keep them paired here so callers can reconstruct
    the (asset, qTok) tuples without an extra zip. *)
Fixpoint quote
    (s : Storage) (baskets : U256.t) (mode : RoundingMode.t)
    : list (U256.t * U256.t) :=
  match s with
  | nil => nil
  | cons e rest =>
    cons (e.(BasketEntry.asset),
          quote_one e.(BasketEntry.refAmt) baskets mode)
         (quote rest baskets mode)
  end.

(** Just the per-asset quantities, dropping the asset id. *)
Definition quoteQuantities
    (s : Storage) (baskets : U256.t) (mode : RoundingMode.t)
    : list U256.t :=
  List.map snd (quote s baskets mode).

(** FLOOR-inverse of [quote_one]: given an actual token quantity [qTok]
    held by the protocol, the maximum number of {BU} that can be
    redeemed against entry [e] without over-paying. This is the
    "user can't extract more than they put in" inverse used in the
    round-trip safety claim. *)
Definition redeem_one
    (refAmt qTok : U256.t) : U256.t :=
  if refAmt =? 0 then 0
  else (qTok * FIX_ONE) / refAmt.

End BasketHandler.
