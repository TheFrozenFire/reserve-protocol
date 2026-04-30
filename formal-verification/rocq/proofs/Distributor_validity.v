(** Distributor validity-preservation lemmas.

    Two small structural facts about [distributeAmounts]:

      1. [distributeAmounts_transferAmts_nonneg] — every per-destination
         transfer amount is non-negative, given a non-negative [amount] and
         non-negative shares. Each transfer is [tokensPerShare * shareOf],
         and both factors are non-negative, so their product is too.

      2. [distributeAmounts_dust_nonneg] — the dust returned from
         [distributeAmounts] is non-negative. The conservation lemma already
         gives [sum(transferAmts) + dust = amount]; combined with
         [each_transfer_le_amount], we get [paidOut <= amount], so
         [dust = amount - paidOut] is non-negative.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Distributor.
Require Import Reserve.proofs.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorValidity.

Import Distributor.
Import DistributorProofs.

(** Per-destination transfer amounts are all non-negative. *)
Lemma distributeAmounts_transferAmts_nonneg
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  0 <= amount ->
  DistributorProofs.validShares s ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let amts := fst pair in
  Forall (fun a => 0 <= a) amts.
Proof.
  intros Hamt Hval.
  unfold Distributor.distributeAmounts.
  destruct (DistributorProofs.totalSharesOf isRSR s =? 0) eqn:Hzero;
    unfold DistributorProofs.totalSharesOf in Hzero; rewrite Hzero.
  - simpl. apply Forall_nil.
  - simpl. rewrite DistributorProofs.transferAmts_aux_eq_map.
    apply Z.eqb_neq in Hzero.
    assert (HTnn : 0 <= DistributorProofs.totalSharesOf isRSR s).
    { rewrite DistributorProofs.totalSharesOf_eq_sum.
      apply DistributorProofs.sumZ_nonneg.
      apply DistributorProofs.rowShares_nonneg. exact Hval. }
    assert (HTpos : 0 < DistributorProofs.totalSharesOf isRSR s)
      by (unfold DistributorProofs.totalSharesOf in HTnn |- *; lia).
    unfold DistributorProofs.totalSharesOf in HTpos.
    set (T := if isRSR then snd (Distributor.totals s) else fst (Distributor.totals s)) in *.
    set (tps := amount / T).
    assert (Htps_nn : 0 <= tps).
    { unfold tps. apply Z.div_pos; lia. }
    pose proof (DistributorProofs.rowShares_nonneg s isRSR Hval) as Hnn.
    apply Forall_map.
    eapply Forall_impl; [|exact Hnn].
    intros shr Hshr_nn. simpl.
    apply Z.mul_nonneg_nonneg; assumption.
Qed.

(** Dust returned from [distributeAmounts] is non-negative. *)
Lemma distributeAmounts_dust_nonneg
    (s : Distributor.Storage) (amount : U256.t) (isRSR : bool) :
  0 <= amount ->
  DistributorProofs.validShares s ->
  let pair := Distributor.distributeAmounts s amount isRSR in
  let dust := snd pair in
  0 <= dust.
Proof.
  intros Hamt Hval.
  unfold Distributor.distributeAmounts.
  destruct (DistributorProofs.totalSharesOf isRSR s =? 0) eqn:Hzero;
    unfold DistributorProofs.totalSharesOf in Hzero; rewrite Hzero.
  - simpl. lia.
  - simpl.
    apply Z.eqb_neq in Hzero.
    assert (HTnn : 0 <= DistributorProofs.totalSharesOf isRSR s).
    { rewrite DistributorProofs.totalSharesOf_eq_sum.
      apply DistributorProofs.sumZ_nonneg.
      apply DistributorProofs.rowShares_nonneg. exact Hval. }
    assert (HTpos : 0 < DistributorProofs.totalSharesOf isRSR s)
      by (unfold DistributorProofs.totalSharesOf in HTnn |- *; lia).
    unfold DistributorProofs.totalSharesOf in HTpos.
    set (T := if isRSR then snd (Distributor.totals s) else fst (Distributor.totals s)) in *.
    (* Goal: 0 <= amount - fold_right Z.add 0 (transferAmts_aux s (amount/T) isRSR) *)
    pose proof (DistributorProofs.sum_transferAmts_aux s (amount / T) isRSR) as Hsum.
    unfold DistributorProofs.sumZ in Hsum.
    unfold DistributorProofs.totalSharesOf in Hsum.
    fold T in Hsum.
    rewrite Hsum.
    pose proof (Z.mul_div_le amount T HTpos) as Hle.
    lia.
Qed.

End DistributorValidity.
