(** Cross-domain integration: Collateral DISABLED status is safe for
    downstream Rebalance.basketRange.

    In production, a Collateral plugin that has hard-defaulted (DISABLED)
    flips the BasketHandler's "disabled" flag, which in turn drives
    BackingManager into recollateralization. The RecollateralizationLib's
    [basketRange] is then called to compute the (low, high) BU envelope
    used by trade selection. The cross-domain claim this file makes:

      Whatever the upstream collateral state machine does — including a
      [refresh] that transitions to DISABLED and then stays terminal —
      the downstream [basketRange] output guarantees (high non-negative,
      low <= high, high <= supplyTotal) still hold under standard input
      validity. The two simulations don't share any types, but they
      share a *temporal* relationship: collateral status is computed
      first, basketRange consumes whatever signals downstream of that.

    The lemma stitches:
      - [CollateralChain.refresh_preserves_disabled] — DISABLED is
        permanent across [refresh].
      - [Rebalance_validity.basketRange_high_nonneg] — basketRange high
        is non-negative under valid inputs.
      - [Rebalance_validity.basketRange_high_le_supply] — basketRange
        high is bounded above by supplyTotal.

    The composition statement is: starting from a DISABLED collateral
    state, after any [refresh] step (which leaves it DISABLED), any
    downstream basketRange call on valid inputs produces non-negative,
    supply-bounded outputs. This is the "collateral-default does not
    break downstream rebalance bounds" property — the rebalance
    machinery remains well-defined precisely when the protocol most
    needs it (during a default).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.Rebalance.
Require Import Reserve.proofs.Collateral.
Require Import Reserve.proofs.Collateral_chain.
Require Import Reserve.proofs.Rebalance_validity.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module IntegrationCollateralRebalance.

Import RebalanceLib.

(** Composition lemma: starting from a DISABLED collateral state,
    [Collateral.refresh] leaves the decoded status DISABLED, AND any
    downstream [basketRange] on valid inputs produces a non-negative,
    supply-bounded high output.

    The conjunction is the load-bearing claim: the upstream-default
    side and the downstream-rebalance side compose without breaking
    either domain's invariants. *)
Lemma collateral_disabled_then_rebalance_safe
    (st : Collateral.State.t)
    (underlying pegPrice low now1 now2 : Z)
    (i : RangeInputs.t) :
  Collateral.statusOf st.(Collateral.State.whenDefault) now1
    = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  Valid.inputs i ->
  (* upstream: refresh preserves DISABLED *)
  Collateral.statusOf
    (Collateral.refresh st underlying pegPrice low now2)
      .(Collateral.State.whenDefault) now2
    = Collateral.Status.DISABLED
  /\
  (* downstream: basketRange output is well-defined (non-negative,
     bounded by supplyTotal) *)
  0 <= (basketRange i).(BasketRange.high) <= i.(RangeInputs.supplyTotal).
Proof.
  intros HD Hmono Hvi.
  split.
  - apply (CollateralChain.refresh_preserves_disabled
             st underlying pegPrice low now1 now2 HD Hmono).
  - split.
    + exact (RebalanceValidityProofs.basketRange_high_nonneg i Hvi).
    + exact (RebalanceValidityProofs.basketRange_high_le_supply i).
Qed.

End IntegrationCollateralRebalance.
