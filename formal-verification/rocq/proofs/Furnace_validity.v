(** Furnace validity preservation.

    Headline lemma: [melt] preserves the [Valid.t] storage invariant, given:
      - [now] fits in uint256 (the new [lastPayout] is [now]);
      - [currentBalance] fits in uint256 (the source for [lastPayoutBal']);
      - [0 <= amount <= currentBalance] (so [currentBalance - amount] is a
        nonneg uint256).

    The bound [0 <= amount <= currentBalance] is the on-chain reality: the
    melted amount is computed from a fixed-point ratio applied to the cached
    balance and is then transferred (burned) out of the contract's RToken
    balance, which cannot go negative.

    Proof note: we mark the FixLib operations [Opaque] before the
    [destruct]/[injection] step so Coq doesn't try to unfold [powu] (which
    contains [Z.to_nat (Z.log2 _)] and explodes the term size during
    [inversion] / [lia]).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.

Module FurnaceValidity.

Import FixLib.
Import Furnace.

Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd.

Lemma melt_preserves_validity
    (s s' : Storage.t) (now currentBalance amount : U256.t) :
  Valid.t s ->
  0 <= now <= UINT256_MAX ->
  0 <= currentBalance <= UINT256_MAX ->
  0 <= amount <= currentBalance ->
  melt s now currentBalance = (s', amount) ->
  Valid.t s'.
Proof.
  intros Hvalid Hnow Hbal Hamt Hmelt.
  destruct Hvalid as [Hr_hi Hr_lo Hlp Hlpb].
  unfold melt in Hmelt.
  destruct (now <? s.(Storage.lastPayout) + 1) eqn:Hcond.
  - (* Early-return branch: pair = (s, 0). injection gives s' = s and amount = 0. *)
    injection Hmelt as Hs'_eq Hamt_eq.
    subst s'.
    constructor; assumption.
  - (* Active branch: extract the two component equalities explicitly so
       the giant arithmetic expression for amount stays behind a name. *)
    injection Hmelt as Hs'_eq Hamt_eq.
    subst s'.
    constructor; simpl.
    + exact Hr_hi.
    + exact Hr_lo.
    + (* lastPayout' = lastPayout + (now - lastPayout) = now in [0, UINT256_MAX]. *)
      assert (Heq : s.(Storage.lastPayout) + (now - s.(Storage.lastPayout)) = now)
        by lia.
      rewrite Heq. exact Hnow.
    + (* lastPayoutBal' = currentBalance - <giant>. Use Hamt_eq to rename
         <giant> back to [amount], then close with the user-supplied bound
         [0 <= amount <= currentBalance] plus [Hbal]. The injection direction
         is [<giant> = amount], so [rewrite Hamt_eq] replaces it. *)
      rewrite Hamt_eq. lia.
Qed.

(** [setRatio] preserves [Valid.t] given a non-negativity precondition on
    [ratio_]. The precondition is necessary: [setRatio] only checks the
    upper bound [<=? MAX_RATIO], but [Valid.t.ratio_nonneg] requires
    [0 <= ratio]. On chain, this nonneg-ness is automatic (uint192), but
    in the simulation [U256.t := Z] carries no refinement, so the
    hypothesis must be explicit. *)
Lemma setRatio_preserves_validity
    (s s' : Storage.t) (ratio_ : U256.t) :
  Valid.t s ->
  0 <= ratio_ ->
  setRatio s ratio_ = Some s' ->
  Valid.t s'.
Proof.
  intros Hvalid Hnn Hset.
  destruct Hvalid as [Hr_hi Hr_lo Hlp Hlpb].
  unfold setRatio in Hset.
  destruct (ratio_ <=? MAX_RATIO) eqn:Hle; [|discriminate].
  injection Hset as Hs'_eq.
  subst s'.
  apply Z.leb_le in Hle.
  constructor; simpl; assumption.
Qed.

End FurnaceValidity.
