(** Distributor composition lemmas — amount = 0 degenerate case.

    When [amount = 0], [tokensPerShare = 0 / totalShares = 0] (or 0 by the
    [totalShares = 0] short-circuit), so every transfer amount is zero and
    the dust returned is zero. This is a clean degenerate case — no
    arithmetic content beyond unfolding the definition.

    Two lemmas:

      1. [distributeAmounts_zero] — at amount = 0 every transfer is 0 and
         dust = 0.
      2. [distributeAmounts_conservation_holds_at_zero] — the share
         conservation identity [sum(amts) + dust = amount] specialized to
         amount = 0, given here for free as a corollary.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Distributor.
Require Import Reserve.proofs.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorChain.

Import Distributor.
Import DistributorProofs.

(** At [amount = 0], every per-destination transfer is 0 and the dust is 0. *)
Lemma distributeAmounts_zero
    (s : Distributor.Storage) (isRSR : bool) :
  let pair := Distributor.distributeAmounts s 0 isRSR in
  let amts := fst pair in
  let dust := snd pair in
  Forall (fun a => a = 0) amts /\ dust = 0.
Proof.
  unfold Distributor.distributeAmounts.
  destruct (totalSharesOf isRSR s =? 0) eqn:Hzero;
    unfold totalSharesOf in Hzero; rewrite Hzero.
  - (* totalShares = 0: amts = [], dust = 0. *)
    simpl. split; [apply Forall_nil | reflexivity].
  - (* totalShares > 0: tps = 0/T = 0. *)
    apply Z.eqb_neq in Hzero.
    set (T := if isRSR then snd (Distributor.totals s) else fst (Distributor.totals s)) in *.
    replace (0 / T) with 0 by (symmetry; apply Z.div_0_l; exact Hzero).
    simpl.
    rewrite transferAmts_aux_zero.
    split.
    + clear. induction s as [|p rest IH]; simpl.
      * apply Forall_nil.
      * apply Forall_cons; [reflexivity | exact IH].
    + rewrite sumZ_zeros. lia.
Qed.

(** Share conservation specialized to amount = 0: sum(amts) + dust = 0. *)
Lemma distributeAmounts_conservation_holds_at_zero
    (s : Distributor.Storage) (isRSR : bool) :
  let pair := Distributor.distributeAmounts s 0 isRSR in
  let amts := fst pair in
  let dust := snd pair in
  sumZ amts + dust = 0.
Proof.
  pose proof (share_conservation s 0 isRSR) as H.
  simpl in H. exact H.
Qed.

End DistributorChain.
