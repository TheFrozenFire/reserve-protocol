(** Throttle composition lemmas.

    Two small chain results building on [Throttle] / [Throttle_validity]:

      1. [useAvailable_zero_lastAvailable]: when [amount = 0] and the rates
         are not both zero, [useAvailable] succeeds and the resulting
         [lastAvailable] is exactly [currentlyAvailable] of the input.
         This is the "amount = 0 is a refresh" lemma — the third branch of
         [useAvailable] sets [lastAvailable := available] directly, with
         no add/subtract.

      2. [useAvailable_twice_preserves_validity]: composing
         [useAvailable_preserves_validity] with itself gives validity
         preservation across two sequential calls. No new arithmetic;
         just propagation of [Valid.throttle]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Throttle.
Require Import Reserve.proofs.Throttle.
Require Import Reserve.proofs.Throttle_validity.
Require Import Coq.Bool.Bool.

Module ThrottleChain.

Import ThrottleLib.
Import ThrottleProofs.
Import ThrottleValidity.

(** ----- Amount = 0: lastAvailable refreshes to currentlyAvailable. -----
    Precondition rules out the early-return branch where the throttle is
    inert (both rates zero), in which case [useAvailable] returns [t]
    unchanged and the equation would only hold accidentally. *)
Lemma useAvailable_zero_lastAvailable
    (t t' : Throttle.t) (supply now : U256.t) :
  ~ (t.(Throttle.params).(Params.amtRate) = 0 /\
     t.(Throttle.params).(Params.pctRate) = 0) ->
  useAvailable t supply 0 now = Result.Success t' ->
  t'.(Throttle.lastAvailable) =
    currentlyAvailable t (hourlyLimit t supply) now.
Proof.
  intros Hnz Hok.
  unfold useAvailable in Hok.
  destruct (andb (t.(Throttle.params).(Params.amtRate) =? 0)
                 (t.(Throttle.params).(Params.pctRate) =? 0)) eqn:Hzero.
  - apply andb_true_iff in Hzero. destruct Hzero as [Ha Hp].
    apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hp.
    exfalso. apply Hnz. split; assumption.
  - (* 0 <? 0 = false; 0 <? 0 = false again — falls through to amount = 0
       branch, which sets lastAvailable := available. *)
    simpl in Hok.
    injection Hok as Hok; subst t'. reflexivity.
Qed.

(** ----- Two sequential calls preserve [Valid.throttle]. -----
    Direct composition of [useAvailable_preserves_validity] with itself.
    The intermediate-state preconditions get re-quantified at the chain
    level — there's no way to derive them from the first call's bound
    without a hourlyLimit upper-bound lemma we don't have. *)
Lemma useAvailable_twice_preserves_validity
    (t t1 t' : Throttle.t)
    (supply1 supply2 : U256.t)
    (amount1 amount2 : Z)
    (now1 now2 : U256.t) :
  Valid.throttle t ->
  (* Bounds for the first call. *)
  0 <= now1 <= UINT48_MAX ->
  0 <= supply1 ->
  t.(Throttle.lastTimestamp) <= now1 ->
  0 <= hourlyLimit t supply1 ->
  currentlyAvailable t (hourlyLimit t supply1) now1 + Z.abs amount1 < 2 ^ 256 ->
  (* Bounds for the second call (against the intermediate storage [t1]). *)
  0 <= now2 <= UINT48_MAX ->
  0 <= supply2 ->
  t1.(Throttle.lastTimestamp) <= now2 ->
  0 <= hourlyLimit t1 supply2 ->
  currentlyAvailable t1 (hourlyLimit t1 supply2) now2 + Z.abs amount2 < 2 ^ 256 ->
  useAvailable t  supply1 amount1 now1 = Result.Success t1 ->
  useAvailable t1 supply2 amount2 now2 = Result.Success t' ->
  Valid.throttle t'.
Proof.
  intros Hvalid Hnow1 Hsup1 Hts1 Hlim1 Hbnd1
         Hnow2 Hsup2 Hts2 Hlim2 Hbnd2 Hok1 Hok2.
  assert (Hvalid1 : Valid.throttle t1).
  { eapply useAvailable_preserves_validity with
      (t := t) (supply := supply1) (amount := amount1) (now := now1);
    eassumption. }
  eapply useAvailable_preserves_validity with
    (t := t1) (supply := supply2) (amount := amount2) (now := now2);
  eassumption.
Qed.

End ThrottleChain.
