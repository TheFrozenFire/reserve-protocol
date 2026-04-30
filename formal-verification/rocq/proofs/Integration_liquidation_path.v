(** Integration lemma: BackingManager surplus split feeds DutchTrade cleanly.

    Cross-domain composition along the liquidation path:

      BackingManager.computeSurplusSplit (per-asset surplus)
        --> rTokenAmount  (non-negative under input validity)
        --> DutchTrade.Auction.t.sellAmount  (carries that non-neg amount)
        --> DutchTrade.bidPrice on a valid auction
              (non-negative at every phase-4 progression point).

    The Solidity flow: BackingManager forwards a per-asset surplus to a
    revenue trader, which opens a [DutchTrade] over that surplus. The
    trade's [sellAmount] is exactly the [rTokenAmount] (or [rsrAmount])
    from the surplus split. This lemma stitches the two existing
    output-bound lemmas:

      - [BackingManager_validity.computeSurplusSplit_outputs_nonneg]
      - [DutchTrade_validity.bidPrice_phase4_nonneg]

    so that — given a successful surplus split with non-negative inputs,
    a valid auction whose sellAmount comes from that split, and a time
    [t] in the phase-4 range — the bidPrice is non-negative.

    Phase 4 is the natural composition target: it's flat at [worstPrice],
    [worstPrice >= 0] is one of the [Valid.t] invariants, and the proof
    is a one-step rewrite to the per-domain [bidPrice_phase4_nonneg].
    The non-negativity of [rTokenAmount] is what justifies wiring it
    into [Auction.sellAmount] in the first place.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Reserve.simulations.DutchTrade.
Require Import Reserve.proofs.BackingManager_validity.
Require Reserve.proofs.DutchTrade_validity.

Module IntegrationLiquidationPath.

Import FixLib.
Import BackingManagerValidityProofs.
Import Reserve.simulations.DutchTrade.DutchTrade.
Import Reserve.proofs.DutchTrade_validity.DutchTradeValidity.

(** Composition lemma: when [computeSurplusSplit] succeeds with
    non-negative inputs, the resulting [rTokenAmount] is non-negative,
    so it is a legitimate [sellAmount] for an auction. For any valid
    auction [a] whose sellAmount equals that [rTokenAmount], and any
    time [t] whose progression is in the phase-4 range, the bidPrice is
    non-negative.

    Discipline: pure re-use. The non-negativity of [rTokenAmount] is the
    BackingManager output bound; the non-negativity of [bidPrice] in
    phase 4 is the DutchTrade output bound. The composition just notes
    that the wiring from one to the other respects both. *)
Lemma surplus_then_dutchtrade_outputs_nonneg
    (needed quantity bal : U256.t)
    (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    (split : BackingManager.SurplusSplit.t)
    (a : Auction.t)
    (t : U256.t) :
  0 <= needed ->
  0 <= quantity ->
  0 <= bal ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  0 <= decimals ->
  BackingManager.computeSurplusSplit
    needed quantity bal decimals rTokenTotal rsrTotal
      = BackingManager.Result.Success split ->
  Valid.t a ->
  a.(Auction.sellAmount) = split.(BackingManager.SurplusSplit.rTokenAmount) ->
  NINETY_FIVE_PERCENT <= progression a t ->
  progression a t <= FIX_ONE ->
  0 <= bidPrice a t /\
  0 <= split.(BackingManager.SurplusSplit.rTokenAmount).
Proof.
  intros Hneeded Hquantity Hbal HrT HrS Hdec Hsucc Hva Hwire Hge Hle.
  pose proof
    (computeSurplusSplit_outputs_nonneg
       needed quantity bal decimals rTokenTotal rsrTotal split
       Hneeded Hquantity Hbal HrT HrS Hdec Hsucc) as Hsplit_nn.
  destruct Hsplit_nn as (_ & HrTokA & _).
  split.
  - exact (bidPrice_phase4_nonneg a t Hva Hge Hle).
  - exact HrTokA.
Qed.

End IntegrationLiquidationPath.
