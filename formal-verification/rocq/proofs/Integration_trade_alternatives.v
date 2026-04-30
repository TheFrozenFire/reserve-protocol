(** Integration lemma: joint output non-negativity across the two
    auction alternatives.

    Reserve protocol exposes two trade systems that revenue / rebalance
    flows can route through:

      - DutchTrade  (4-piecewise dutch auction, [bidPrice] dispatcher)
      - GnosisTrade (batch auction wrapper, [settlement_floor] guard)

    The two systems have non-overlapping input types — DutchTrade is
    parameterized by a falling-price [Auction.t] curve and a timestamp,
    GnosisTrade by a [worstCase] floor and a realized [soldAmt]. They
    don't share a single input record, but a higher-layer dispatcher
    (rebalance / revenue path) chooses between them on identical
    economic preconditions: a positive sell amount, a non-negative
    floor price, and validated bounds.

    The composition below states the shared output-bound invariant:
    given a valid DutchTrade auction in its phase-4 (flat) range AND a
    non-negative worstCase fed to GnosisTrade, *both* alternatives
    produce non-negative bidder-facing outputs simultaneously. This is
    the joint-shape statement the rebalance dispatcher relies on when
    it doesn't have to know in advance which auction kind a particular
    surplus / deficit pair will route to.

    Composes:
      - [DutchTradeValidity.bidPrice_phase4_nonneg]
      - [GnosisTrade.settlement_floor_nonneg] (re-proved here from
        [GnosisTradeValidity]'s sibling bound, but the canonical proof
        lives in [proofs/GnosisTrade.v])

    Module-collision discipline: both simulations export a module also
    named [DutchTrade] / [GnosisTrade], so we keep the long-form
    [Reserve.simulations.X.X] qualification at the imports.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Reserve.simulations.DutchTrade.
Require Reserve.simulations.GnosisTrade.
Require Reserve.proofs.DutchTrade_validity.
Require Reserve.proofs.GnosisTrade.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module IntegrationTradeAlternatives.

Import FixLib.
Import Reserve.simulations.DutchTrade.DutchTrade.
Import Reserve.simulations.GnosisTrade.GnosisTrade.
Import Reserve.proofs.DutchTrade_validity.DutchTradeValidity.
Import Reserve.proofs.GnosisTrade.GnosisTradeProofs.

(** Joint output-bound: in the phase-4 flat range of a valid DutchTrade
    auction, [bidPrice] is non-negative; concurrently, on any inputs to
    GnosisTrade's [settlement_floor], the floor is non-negative.

    The two arms are independent (the auctions take separate input
    records), so the lemma quantifies over both input shapes. *)
Lemma both_trades_outputs_nonneg
    (a : Reserve.simulations.DutchTrade.DutchTrade.Auction.t)
    (t : U256.t)
    (worstCase soldAmt : Z) :
  Reserve.simulations.DutchTrade.DutchTrade.Valid.t a ->
  Reserve.simulations.DutchTrade.DutchTrade.NINETY_FIVE_PERCENT
    <= Reserve.simulations.DutchTrade.DutchTrade.progression a t ->
  Reserve.simulations.DutchTrade.DutchTrade.progression a t <= FIX_ONE ->
  0 <= Reserve.simulations.DutchTrade.DutchTrade.bidPrice a t
  /\ 0 <= Reserve.simulations.GnosisTrade.GnosisTrade.settlement_floor
            worstCase soldAmt.
Proof.
  intros Hv Hge Hle.
  split.
  - apply bidPrice_phase4_nonneg; assumption.
  - apply settlement_floor_nonneg.
Qed.

End IntegrationTradeAlternatives.
