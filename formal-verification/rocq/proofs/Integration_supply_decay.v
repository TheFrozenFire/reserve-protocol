(** Cross-domain integration: Furnace.melt vs notional RToken total supply.

    [Furnace.melt] returns an [amount] which the production code interprets as
    the quantity of RToken to burn from the Furnace's cached balance — i.e. a
    decrement of total supply. The headline composition lemma here states:

      melted amount, treated as RToken burned, never increases total supply.

    Equivalently, [totalSupply - amount <= totalSupply]. This is just
    [0 <= amount] lifted to the supply level, but it ties the Furnace
    simulation result to an externally-tracked supply quantity, making the
    cross-domain coupling explicit.

    The proof composes:
      - early-return branch: [amount = 0] from [melt_amount_zero_when_too_early];
      - active branch: [amount = divrnd (payoutRatio * lastPayoutBal) FIX_SCALE
        FLOOR], non-negative when [0 <= payoutRatio] and [0 <= lastPayoutBal].

    The [payoutRatio] non-negativity is taken as a hypothesis (the same way
    [melt_amount_bounded_by_balance] in [proofs/Furnace.v] does); on chain it
    is automatic from the algebraic identity [payoutRatio = 1 - (1-r)^N] with
    [r] in [0, MAX_RATIO] and [N >= 0].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.

Module IntegrationSupplyDecay.

Import FixLib.
Import Furnace.

Opaque FixLib.powu FixLib.minus.

(** Helper: the melted amount is always non-negative, given the standing
    assumption that [payoutRatio >= 0] (which the on-chain identity
    [payoutRatio = 1 - (1-r)^N] guarantees for [r in [0,1]]). *)
Lemma melt_amount_nonneg
    (s : Storage.t) (now currentBalance : U256.t) :
  0 <= s.(Storage.lastPayoutBal) ->
  let numPeriods := now - s.(Storage.lastPayout) in
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio)) numPeriods) in
  0 <= payoutRatio ->
  0 <= snd (melt s now currentBalance).
Proof.
  cbv zeta. intros Hbal Hpr_lo.
  unfold melt.
  destruct (now <? s.(Storage.lastPayout) + 1) eqn:Hcond.
  - cbn. lia.
  - cbn [snd].
    unfold FixLib.mulu_toUint, FixLib.divrnd.
    apply Z.div_pos; [|unfold FixLib.FIX_SCALE; lia].
    apply Z.mul_nonneg_nonneg; assumption.
Qed.

(** ===== Headline integration lemma. =====

    If [Furnace.melt] returns [amount], then treating that amount as RToken
    burned from a notional [totalSupply], the resulting supply [totalSupply -
    amount] does not exceed [totalSupply].

    The hypothesis [0 <= currentBalance <= totalSupply] reflects on-chain
    reality (the Furnace's RToken balance is part of the total supply), and
    [0 <= s.(Storage.lastPayoutBal)] follows from [Valid.t s]. *)
Lemma melt_decreases_or_preserves_total_supply
    (s : Storage.t) (now currentBalance totalSupply : U256.t) :
  Valid.t s ->
  0 <= currentBalance <= totalSupply ->
  let numPeriods := now - s.(Storage.lastPayout) in
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio)) numPeriods) in
  0 <= payoutRatio ->
  let '(_, amount) := melt s now currentBalance in
  totalSupply - amount <= totalSupply.
Proof.
  cbv zeta. intros Hvalid Hbal_le Hpr_lo.
  destruct Hvalid as [_ _ _ Hlpb].
  destruct Hlpb as [Hlpb_lo _].
  set (p := melt s now currentBalance).
  assert (Hamt_nn : 0 <= snd p).
  { unfold p.
    apply (melt_amount_nonneg s now currentBalance Hlpb_lo Hpr_lo). }
  destruct p as [s' amount] eqn:Hp.
  cbn [snd] in Hamt_nn.
  lia.
Qed.

End IntegrationSupplyDecay.
