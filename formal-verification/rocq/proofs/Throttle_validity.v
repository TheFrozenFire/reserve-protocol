(** Throttle validity preservation.

    Headline lemma: [useAvailable] preserves the [Valid.throttle] storage
    invariant.

    Three things have to fit:

      1. [lastTimestamp'] fits in uint48: the value is either [now] (bounded
         by the [now <= UINT48_MAX] precondition) or unchanged from [t], in
         which case it inherits validity from [Valid.throttle t].

      2. [lastAvailable'] fits in uint256. The new value is bounded above by
         [currentlyAvailable + |amount|]. The cleanest precondition is to
         take that bound directly: it's the on-chain reality (lastAvailable
         is a uint256 that the contract refuses to overflow), and deriving
         it from supply / amount bounds individually would require a
         hourlyLimit-bound lemma we don't have here.

      3. [params] are unchanged in every branch, so their validity transfers
         trivially via the original [Valid.throttle t] hypothesis.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Throttle.
Require Import Reserve.proofs.Throttle.
Require Import Coq.Bool.Bool.

Module ThrottleValidity.

Import ThrottleLib.
Import ThrottleProofs.

Lemma useAvailable_preserves_validity
    (t t' : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  Valid.throttle t ->
  0 <= now <= UINT48_MAX ->
  0 <= supply ->
  t.(Throttle.lastTimestamp) <= now ->
  0 <= hourlyLimit t supply ->
  currentlyAvailable t (hourlyLimit t supply) now + Z.abs amount < 2 ^ 256 ->
  useAvailable t supply amount now = Result.Success t' ->
  Valid.throttle t'.
Proof.
  intros Hvalid Hnow Hsupply Hts Hlim_nn Hbound Hok.
  destruct Hvalid as [Hp_valid Hts_uint48 Hav_u256].
  unfold useAvailable in Hok.
  set (limit := hourlyLimit t supply) in *.
  set (avail := currentlyAvailable t limit now) in *.
  assert (Havail_nn : 0 <= avail).
  { unfold avail. apply currentlyAvailable_nonneg.
    - exact (proj1 Hav_u256).
    - exact Hlim_nn.
    - exact Hts. }
  assert (Havail_le : avail <= limit).
  { unfold avail, limit. apply currentlyAvailable_le_limit. }
  (* Both candidate timestamps fit in uint48. *)
  assert (Hnew_ts_uint48 :
    forall b : bool,
      0 <= (if b then now else t.(Throttle.lastTimestamp)) <= UINT48_MAX).
  { intros [|]; [exact Hnow|exact Hts_uint48]. }
  destruct (andb (t.(Throttle.params).(Params.amtRate) =? 0)
                 (t.(Throttle.params).(Params.pctRate) =? 0)) eqn:Hzero.
  - (* Both rates zero: t' = t. *)
    inversion Hok; subst t'.
    constructor; assumption.
  - (* Active branch. *)
    destruct (0 <? amount) eqn:Hpos.
    + (* amount > 0: success requires amount <= avail. *)
      apply Z.ltb_lt in Hpos.
      destruct (amount <=? _) eqn:Hle; [|discriminate].
      apply Z.leb_le in Hle.
      inversion Hok; subst t'. clear Hok.
      constructor; simpl.
      * exact Hp_valid.
      * apply Hnew_ts_uint48.
      * (* avail - amount: 0 <= avail - amount <= avail < 2^256 (via Hav_u256? not quite) *)
        split.
        -- lia.
        -- (* avail - amount <= avail <= 2^256 - 1 (need bound on avail) *)
           (* avail + |amount| < 2^256 and amount > 0 so |amount| = amount,
              avail + amount < 2^256, so avail - amount < 2^256. *)
           assert (Habs : Z.abs amount = amount) by lia.
           rewrite Habs in Hbound. lia.
    + (* amount <= 0 *)
      apply Z.ltb_ge in Hpos.
      destruct (amount <? 0) eqn:Hneg.
      * (* amount < 0: lastAvailable' = avail + (-amount) *)
        apply Z.ltb_lt in Hneg.
        inversion Hok; subst t'. clear Hok.
        constructor; simpl.
        -- exact Hp_valid.
        -- apply Hnew_ts_uint48.
        -- split.
           ++ lia.
           ++ assert (Habs : Z.abs amount = - amount) by lia.
              rewrite Habs in Hbound. lia.
      * (* amount = 0 *)
        apply Z.ltb_ge in Hneg.
        assert (Hzeroamt : amount = 0) by lia.
        inversion Hok; subst t'. clear Hok.
        constructor; simpl.
        -- exact Hp_valid.
        -- apply Hnew_ts_uint48.
        -- split.
           ++ exact Havail_nn.
           ++ assert (Habs : Z.abs amount = 0) by lia.
              rewrite Habs in Hbound. lia.
Qed.

End ThrottleValidity.
