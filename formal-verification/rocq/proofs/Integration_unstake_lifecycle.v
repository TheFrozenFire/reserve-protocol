(** Cross-domain integration: StRSR unstake lifecycle conservation.

    The unstake transition moves RSR principal from the
    [totalRSRStaked] pool into a queued [Withdrawal] entry, where it
    will sit until [availableAt] elapses and the entry is paid out.
    During the lifecycle the system-wide RSR backing the staking module
    -- the sum of [totalRSRStaked] and the rsrAmount of every queued
    withdrawal -- must be conserved by the unstake operation itself
    (no rewards are credited and no payouts are made on this leg).

    The headline composition lemma here states exactly that
    conservation, by chaining

      [unstake_conservation] from proofs/StRSR.v
        -- giving us the post-unstake totalRSRStaked and queue layout --

    with a small list-fold lemma about
      sum_rsr_amounts (q ++ [w]) = sum_rsr_amounts q + w.(rsrAmount)

    so that the system-wide invariant

      totalRSRStaked + sum_rsr_amounts queue = const

    is preserved across [StRSR.unstake]. This stitches the per-domain
    [unstake_conservation] result to a queue-shape fact, making the
    cross-domain RSR-counting invariant explicit.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Reserve.proofs.StRSR.
Require Import Reserve.proofs.StRSR_validity.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module IntegrationUnstakeLifecycle.

Import Reserve.simulations.StRSR.StRSR.

(** Sum of [rsrAmount] across a withdrawal queue. *)
Definition sum_rsr_amounts (q : list Withdrawal.t) : Z :=
  fold_right (fun w acc => w.(Withdrawal.rsrAmount) + acc) 0 q.

(** Snoc: the rsrAmount sum splits cleanly across queue ++ [w]. *)
Lemma sum_rsr_amounts_snoc (q : list Withdrawal.t) (w : Withdrawal.t) :
  sum_rsr_amounts (q ++ [w]) = sum_rsr_amounts q + w.(Withdrawal.rsrAmount).
Proof.
  induction q as [|x rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** ===== Headline integration lemma. =====

    [StRSR.unstake] preserves the system-wide RSR conservation
    invariant: the sum of [totalRSRStaked] and the queued [rsrAmount]s
    is the same before and after the unstake.

    Compose: [unstake_conservation] gives the post-state shape
    componentwise; [sum_rsr_amounts_snoc] discharges the queue side. *)
Lemma unstake_preserves_total_RSR_in_system
    (s : Storage.t) (amount now delay : U256.t) :
  let s' := unstake s amount now delay in
  s'.(Storage.totalRSRStaked) + sum_rsr_amounts s'.(Storage.queue)
    = s.(Storage.totalRSRStaked) + sum_rsr_amounts s.(Storage.queue).
Proof.
  cbv zeta.
  pose proof (StRSRProofs.unstake_conservation s amount now delay)
    as Hcons.
  cbv zeta in Hcons.
  destruct Hcons as (_ & HrSt & Hq).
  rewrite HrSt, Hq.
  rewrite sum_rsr_amounts_snoc.
  simpl.
  lia.
Qed.

End IntegrationUnstakeLifecycle.
