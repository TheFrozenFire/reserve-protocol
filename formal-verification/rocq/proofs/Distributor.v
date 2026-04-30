(** Distributor simulation invariant proofs.

    Proves the safety invariants on the [Distributor] simulation defined
    in [Reserve.simulations.Distributor]:

      INV-1   share_conservation:          sum(transferAmts) + dust = amount
      INV-2   dust_bounded:                dust < totalShares  (totalShares > 0)
      INV-3   tokensPerShare_zero_means_zero_paid:
                amount < totalShares ⟹  all transfers = 0 ∧ dust = amount
      INV-4   each_transfer_le_amount:     each transfer[i] ≤ amount

    These mirror the CAS witness corpus in cas/distributor/share_conservation.gp
    and the harness contract in contracts/DistributorMathHarness.sol.

    "Validity" here is the natural sanity precondition that every declared
    share is non-negative (production stores them in uint16, so this is
    automatic on-chain). The conservation lemma itself is purely additive
    and needs no precondition.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorProofs.

Import Distributor.

(** A storage row's relevant share for the current leg, given [isRSR]. *)
Definition rowShares (isRSR : bool) (s : Storage) : list U256.t :=
  List.map (fun p => shareOf isRSR (snd p)) s.

(** [totalSharesOf isRSR s] = the totalShares used by [distributeAmounts]. *)
Definition totalSharesOf (isRSR : bool) (s : Storage) : U256.t :=
  if isRSR then snd (totals s) else fst (totals s).

(** Sum of a list of [Z]s. *)
Definition sumZ (xs : list Z) : Z := List.fold_right Z.add 0 xs.

(** Validity: every declared share is non-negative.
    On-chain this is automatic — RevenueShare fields are uint16. *)
Definition validShares (s : Storage) : Prop :=
  Forall (fun p => 0 <= (snd p).(RevenueShare.rTokenDist)
                /\ 0 <= (snd p).(RevenueShare.rsrDist)) s.

(** ---------- Helper: totals matches sum of share columns. ---------- *)

Lemma totals_eq_sum (s : Storage) :
  fst (totals s) = sumZ (List.map (fun p => (snd p).(RevenueShare.rTokenDist)) s)
  /\ snd (totals s) = sumZ (List.map (fun p => (snd p).(RevenueShare.rsrDist)) s).
Proof.
  induction s as [|[a sh] rest IH]; simpl.
  - split; reflexivity.
  - destruct IH as [IHr IHs].
    unfold sumZ in *. simpl.
    rewrite IHr, IHs.
    split; lia.
Qed.

Lemma totalSharesOf_eq_sum (isRSR : bool) (s : Storage) :
  totalSharesOf isRSR s = sumZ (rowShares isRSR s).
Proof.
  unfold totalSharesOf, rowShares.
  destruct (totals_eq_sum s) as [Hr Hs].
  destruct isRSR.
  - rewrite Hs. reflexivity.
  - rewrite Hr. reflexivity.
Qed.

(** ---------- Helper: transferAmts_aux distributes the constant tps across the shares. ---------- *)

Lemma transferAmts_aux_eq_map
    (s : Storage) (tps : U256.t) (isRSR : bool) :
  transferAmts_aux s tps isRSR
  = List.map (fun shr => tps * shr) (rowShares isRSR s).
Proof.
  unfold rowShares. induction s as [|[a sh] rest IH]; simpl; [reflexivity|].
  f_equal. apply IH.
Qed.

(** Sum of [tps * shr] over a list = tps * sum(shr). *)
Lemma sumZ_map_mul (tps : Z) (xs : list Z) :
  sumZ (List.map (fun shr => tps * shr) xs) = tps * sumZ xs.
Proof.
  induction xs as [|x rest IH]; simpl.
  - lia.
  - unfold sumZ in *. simpl. rewrite IH. lia.
Qed.

(** Sum of transferAmts equals tps * totalShares. *)
Lemma sum_transferAmts_aux (s : Storage) (tps : U256.t) (isRSR : bool) :
  sumZ (transferAmts_aux s tps isRSR) = tps * totalSharesOf isRSR s.
Proof.
  rewrite transferAmts_aux_eq_map.
  rewrite sumZ_map_mul.
  rewrite totalSharesOf_eq_sum.
  reflexivity.
Qed.

(** ---------- INV-1: share conservation. ----------
    [sum(transferAmts) + dust = amount] for any storage / amount / leg. *)
Lemma share_conservation
    (s : Storage) (amount : U256.t) (isRSR : bool) :
  let pair := distributeAmounts s amount isRSR in
  let amts := fst pair in
  let dust := snd pair in
  sumZ amts + dust = amount.
Proof.
  unfold distributeAmounts.
  destruct (totalSharesOf isRSR s =? 0) eqn:Hzero;
  unfold totalSharesOf in Hzero; rewrite Hzero.
  - (* totalShares = 0 case: amts = [], dust = amount. *)
    simpl. unfold sumZ. simpl. lia.
  - (* totalShares > 0 case. *)
    simpl.
    remember (transferAmts_aux s _ isRSR) as amts eqn:Hamts.
    set (paidOut := List.fold_right Z.add 0 amts).
    assert (Hsum : sumZ amts = paidOut) by reflexivity.
    lia.
Qed.

(** ---------- INV-2: dust < totalShares (when totalShares > 0). ---------- *)
Lemma dust_bounded
    (s : Storage) (amount : U256.t) (isRSR : bool) :
  0 <= amount ->
  0 < totalSharesOf isRSR s ->
  let pair := distributeAmounts s amount isRSR in
  snd pair < totalSharesOf isRSR s.
Proof.
  intros Hamt Hpos.
  unfold distributeAmounts, totalSharesOf in *.
  destruct isRSR; simpl in *.
  - assert (Hne : (snd (totals s) =? 0) = false)
      by (apply Z.eqb_neq; lia).
    rewrite Hne. simpl.
    rewrite sum_transferAmts_aux.
    unfold totalSharesOf. simpl.
    set (T := snd (totals s)) in *.
    (* dust = amount - (amount / T) * T = amount mod T. *)
    assert (HT : T > 0) by lia.
    pose proof (Z.mod_eq amount T) as Hmod.
    assert (Hne' : T <> 0) by lia.
    specialize (Hmod Hne').
    pose proof (Z.mod_pos_bound amount T Hpos) as Hbound.
    lia.
  - assert (Hne : (fst (totals s) =? 0) = false)
      by (apply Z.eqb_neq; lia).
    rewrite Hne. simpl.
    rewrite sum_transferAmts_aux.
    unfold totalSharesOf. simpl.
    set (T := fst (totals s)) in *.
    assert (HT : T > 0) by lia.
    pose proof (Z.mod_eq amount T) as Hmod.
    assert (Hne' : T <> 0) by lia.
    specialize (Hmod Hne').
    pose proof (Z.mod_pos_bound amount T Hpos) as Hbound.
    lia.
Qed.

(** ---------- INV-3: amount < totalShares ⇒ every transfer is zero, dust = amount. ---------- *)

(** All-zero list. *)
Lemma transferAmts_aux_zero (s : Storage) (isRSR : bool) :
  transferAmts_aux s 0 isRSR
  = List.map (fun _ => 0) s.
Proof.
  induction s as [|[a sh] rest IH]; simpl; [reflexivity|].
  rewrite IH.
  replace (0 * shareOf isRSR sh) with 0 by lia.
  reflexivity.
Qed.

Lemma sumZ_zeros (s : Storage) :
  sumZ (List.map (fun _ => 0) s) = 0.
Proof.
  induction s as [|p rest IH]; simpl; [reflexivity|].
  unfold sumZ in *. simpl. rewrite IH. lia.
Qed.

Lemma tokensPerShare_zero_means_zero_paid
    (s : Storage) (amount : U256.t) (isRSR : bool) :
  0 <= amount ->
  0 < totalSharesOf isRSR s ->
  amount < totalSharesOf isRSR s ->
  let pair := distributeAmounts s amount isRSR in
  let amts := fst pair in
  let dust := snd pair in
  Forall (fun a => a = 0) amts /\ dust = amount.
Proof.
  intros Hamt Hpos Hlt.
  unfold distributeAmounts, totalSharesOf in *.
  destruct isRSR; simpl in *.
  - set (T := snd (totals s)) in *.
    assert (HTne : (T =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite HTne. simpl.
    assert (Htps : amount / T = 0).
    { apply Z.div_small. lia. }
    rewrite Htps.
    rewrite transferAmts_aux_zero.
    split.
    + clear. induction s as [|p rest IH]; simpl.
      * apply Forall_nil.
      * apply Forall_cons; [reflexivity|exact IH].
    + rewrite sumZ_zeros. lia.
  - set (T := fst (totals s)) in *.
    assert (HTne : (T =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite HTne. simpl.
    assert (Htps : amount / T = 0).
    { apply Z.div_small. lia. }
    rewrite Htps.
    rewrite transferAmts_aux_zero.
    split.
    + clear. induction s as [|p rest IH]; simpl.
      * apply Forall_nil.
      * apply Forall_cons; [reflexivity|exact IH].
    + rewrite sumZ_zeros. lia.
Qed.

(** ---------- INV-4: each transfer is bounded by amount. ----------
    transfer[i] = tps * share[i], tps = amount / totalShares,
    and share[i] <= totalShares (since totalShares is the sum of non-negative shares).
    So tps * share[i] <= tps * totalShares <= amount. *)

(** validShares ⇒ each share is non-negative on the chosen leg. *)
Lemma rowShares_nonneg (s : Storage) (isRSR : bool) :
  validShares s ->
  Forall (fun shr => 0 <= shr) (rowShares isRSR s).
Proof.
  intros Hval. unfold rowShares.
  induction s as [|[a sh] rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    cbn in Hhd. destruct Hhd as [HrTok HrSr].
    apply Forall_cons.
    + unfold shareOf. destruct isRSR; lia.
    + apply IH. exact Htl.
Qed.

Lemma sumZ_nonneg (xs : list Z) :
  Forall (fun x => 0 <= x) xs ->
  0 <= sumZ xs.
Proof.
  intros Hall. induction xs as [|x rest IH]; simpl.
  - unfold sumZ. simpl. lia.
  - inversion Hall as [|? ? Hhd Htl]; subst.
    apply IH in Htl. unfold sumZ in *. simpl. lia.
Qed.

Lemma share_le_totalShares
    (s : Storage) (isRSR : bool) :
  validShares s ->
  Forall (fun shr => 0 <= shr <= totalSharesOf isRSR s) (rowShares isRSR s).
Proof.
  intros Hval.
  rewrite totalSharesOf_eq_sum.
  pose proof (rowShares_nonneg s isRSR Hval) as Hnn.
  unfold rowShares, sumZ in *.
  induction s as [|[a sh] rest IH]; simpl in *.
  - apply Forall_nil.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    destruct Hhd as [HrTok HrSr].
    inversion Hnn as [|? ? Hhdn Htln]; subst.
    specialize (IH Htl Htln).
    apply Forall_cons.
    + (* head: 0 <= shareOf isRSR sh <= shareOf + sum(rest) *)
      assert (Hsum_nn : 0 <= List.fold_right Z.add 0
        (List.map (fun p => shareOf isRSR (snd p)) rest)).
      { apply (sumZ_nonneg (rowShares isRSR rest)).
        apply rowShares_nonneg. exact Htl. }
      lia.
    + (* tail: each remaining share is <= sum (induction hypothesis) *)
      eapply Forall_impl; [|exact IH].
      intros shr [Hge Hle]. simpl. lia.
Qed.

Lemma each_transfer_le_amount
    (s : Storage) (amount : U256.t) (isRSR : bool) :
  0 <= amount ->
  validShares s ->
  let pair := distributeAmounts s amount isRSR in
  let amts := fst pair in
  Forall (fun a => a <= amount) amts.
Proof.
  intros Hamt Hval.
  unfold distributeAmounts.
  destruct (totalSharesOf isRSR s =? 0) eqn:Hzero;
    unfold totalSharesOf in Hzero; rewrite Hzero.
  - simpl. apply Forall_nil.
  - simpl. rewrite transferAmts_aux_eq_map.
    pose proof (share_le_totalShares s isRSR Hval) as Hbnd.
    apply Z.eqb_neq in Hzero.
    (* totalShares is non-negative (sum of non-negs). *)
    assert (HTnn : 0 <= totalSharesOf isRSR s).
    { rewrite totalSharesOf_eq_sum.
      apply sumZ_nonneg. apply rowShares_nonneg. exact Hval. }
    assert (HTpos : 0 < totalSharesOf isRSR s)
      by (unfold totalSharesOf in HTnn |- *; lia).
    unfold totalSharesOf in HTpos.
    set (T := if isRSR then snd (totals s) else fst (totals s)) in *.
    set (tps := amount / T).
    assert (Htps_nn : 0 <= tps).
    { unfold tps. apply Z.div_pos; lia. }
    assert (Htps_T_le : tps * T <= amount).
    { unfold tps.
      pose proof (Z.mul_div_le amount T HTpos). lia. }
    (* Each shr in (rowShares isRSR s) is in [0, T]; so tps*shr <= tps*T <= amount. *)
    apply Forall_map.
    eapply Forall_impl; [|exact Hbnd].
    intros shr [Hshr_nn Hshr_le]. simpl.
    fold T in Hshr_le.
    assert (Hmul : tps * shr <= tps * T).
    { apply Z.mul_le_mono_nonneg_l;
        [exact Htps_nn|unfold totalSharesOf in Hshr_le; exact Hshr_le]. }
    lia.
Qed.

End DistributorProofs.
