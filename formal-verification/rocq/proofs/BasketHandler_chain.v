(** BasketHandler composition lemmas.

    Two layers, paralleling the simulation's split:

      Layer 1 — Quote math compositions (legacy):
        1. [quote_zero_baskets] — quoting any basket with [baskets = 0]
           produces an all-zero per-asset quantity list, regardless of
           rounding mode.
        2. [quote_FLOOR_le_quote_CEIL_pointwise] — pointwise FLOOR <= CEIL
           on the bare {qTok} lists.

      Layer 2 — Lifecycle compositions (new):
        3. [setPrimeBasket_then_quote_consistent] — quote semantics are
           well-defined after a [setPrimeBasket] call (the basket field
           is unchanged so quoting against it is unaffected).
        4. [refreshBasket_then_quote_consistent] — quote semantics are
           well-defined after a [refreshBasket] call (relies on
           [refreshBasket_preserves_validity]).
        5. [setPrimeBasket_then_refreshBasket_no_disable_when_all_sound]
           — if every prime erc20 is good, [refreshBasket] does not
           flip [disabled] to [true].
        6. [refreshBasket_targetAmt_conservation_all_sound] — when every
           prime is sound, sum(new basket refAmts) = sum(prime
           targetAmts) — exact conservation.
        7. [refreshBasket_disabled_implies_no_backup_available] —
           contrapositive: a [disabled = true] post-state implies
           [build_all_backups] returned [None] (no backup available
           for some target with positive unsound weight) or the new
           basket is empty.

    All lemmas are pure compositions of the simulation definitions — no
    new arithmetic content. Companion to [BasketHandler_validity.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Reserve.proofs.BasketHandler.
Require Import Reserve.proofs.BasketHandler_validity.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Module BasketHandlerChain.

Import FixLib.
Import BasketHandler.
Import BasketHandlerProofs.
Import BasketHandlerValidityProofs.

(** =================================================================
    Layer 1 — quote math compositions.
    =================================================================
*)

Lemma quote_zero_baskets
    (s : BasketHandler.Basket) (mode : RoundingMode.t) :
  Forall (fun q => q = 0) (BasketHandler.quoteQuantities s 0 mode).
Proof.
  unfold BasketHandler.quoteQuantities.
  pose proof (quote_empty_baskets_zero s mode) as H.
  induction H as [|p rest Hp _ IH]; simpl.
  - apply Forall_nil.
  - apply Forall_cons; [exact Hp | exact IH].
Qed.

Lemma quote_FLOOR_le_quote_CEIL_pointwise
    (s : BasketHandler.Basket) (baskets : U256.t) :
  Forall2 Z.le
          (BasketHandler.quoteQuantities s baskets RoundingMode.FLOOR)
          (BasketHandler.quoteQuantities s baskets RoundingMode.CEIL).
Proof.
  unfold BasketHandler.quoteQuantities.
  induction s as [|e rest IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + apply quote_one_floor_le_ceil.
    + exact IH.
Qed.

(** =================================================================
    Layer 2 — lifecycle compositions.
    =================================================================
*)

(** Helper: [setPrimeBasket] does NOT mutate the live [basket] field. *)
Lemma setPrimeBasket_keeps_basket
    (s s' : BasketHandler.Storage.t) (entries : list BasketHandler.PrimeEntry.t) :
  BasketHandler.setPrimeBasket s entries = Some s' ->
  s'.(BasketHandler.Storage.basket) = s.(BasketHandler.Storage.basket).
Proof.
  unfold BasketHandler.setPrimeBasket.
  destruct (_ || _); [discriminate|].
  destruct (negb (BasketHandler.all_targetAmts_valid entries)); [discriminate|].
  destruct (negb (BasketHandler.erc20s_unique _)); [discriminate|].
  intro H. injection H as H'. subst s'. reflexivity.
Qed.

(** ===== setPrimeBasket_then_quote_consistent =====
    Quoting after a successful [setPrimeBasket] call yields the same
    quotation as quoting against the pre-state's basket. *)
Lemma setPrimeBasket_then_quote_consistent
    (s s' : BasketHandler.Storage.t) (entries : list BasketHandler.PrimeEntry.t)
    (baskets : U256.t) (mode : RoundingMode.t) :
  BasketHandler.setPrimeBasket s entries = Some s' ->
  BasketHandler.quote (BasketHandler.basket_of s') baskets mode =
  BasketHandler.quote (BasketHandler.basket_of s) baskets mode.
Proof.
  intro H.
  unfold BasketHandler.basket_of.
  rewrite (setPrimeBasket_keeps_basket s s' entries H).
  reflexivity.
Qed.

(** ===== refreshBasket_then_quote_consistent =====
    Quoting after a [refreshBasket] call gives non-negative {qTok}
    amounts, given a valid pre-state. *)
Lemma refreshBasket_then_quote_consistent
    (s : BasketHandler.Storage.t) (statuses : list BasketHandler.AssetStatus.t)
    (baskets : U256.t) (mode : RoundingMode.t) :
  BasketHandler.Valid.t s ->
  s.(BasketHandler.Storage.nonce) + 1 <= UINT256_MAX ->
  0 <= baskets ->
  Forall (fun q => 0 <= q)
         (BasketHandler.quoteQuantities
            (BasketHandler.basket_of (BasketHandler.refreshBasket s statuses))
            baskets mode).
Proof.
  intros Hv Hnonce Hb.
  pose proof (refreshBasket_preserves_validity s statuses Hv Hnonce) as Hv'.
  destruct Hv' as [_ _ _ _ Hbask].
  apply quoteQuantities_nonneg; assumption.
Qed.

(** ----- helper lemmas to characterize the all-sound path. ----- *)

(** When every prime erc20 is good, [unsound_weight] is zero. *)
Lemma unsound_weight_zero_when_all_sound
    (name : U256.t) (primes : list BasketHandler.PrimeEntry.t)
    (statuses : list BasketHandler.AssetStatus.t) :
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true) primes ->
  BasketHandler.unsound_weight name primes statuses = 0.
Proof.
  induction primes as [|p rest IH]; simpl; intros; auto.
  inversion H as [|? ? Hhd Htl]; subst.
  rewrite Hhd. simpl.
  rewrite Bool.andb_false_r.
  apply IH. exact Htl.
Qed.

(** When [unsound_weight] is zero for every name, [build_all_backups]
    returns [Some nil]. *)
Lemma build_all_backups_zero_when_no_unsound
    (names : list U256.t) (primes : list BasketHandler.PrimeEntry.t)
    (statuses : list BasketHandler.AssetStatus.t)
    (configs : list BasketHandler.BackupEntry.t) :
  Forall (fun n => BasketHandler.unsound_weight n primes statuses = 0) names ->
  BasketHandler.build_all_backups names primes statuses configs = Some nil.
Proof.
  induction names as [|n rest IH]; simpl; intros; [reflexivity|].
  inversion H as [|? ? Hhd Htl]; subst.
  unfold BasketHandler.build_backups_for_target.
  rewrite Hhd. simpl.
  rewrite (IH Htl).
  reflexivity.
Qed.

(** When all primes are sound, [good_prime_entries] equals the
    [erc20, targetAmt]-projection of the prime list. *)
Lemma good_prime_entries_when_all_sound
    (primes : list BasketHandler.PrimeEntry.t) (statuses : list BasketHandler.AssetStatus.t) :
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true) primes ->
  BasketHandler.good_prime_entries primes statuses =
  List.map
    (fun p =>
       {| BasketHandler.BasketEntry.asset := p.(BasketHandler.PrimeEntry.erc20);
          BasketHandler.BasketEntry.refAmt := p.(BasketHandler.PrimeEntry.targetAmt) |})
    primes.
Proof.
  induction primes as [|p rest IH]; simpl; intros; [reflexivity|].
  inversion H as [|? ? Hhd Htl]; subst.
  rewrite Hhd. f_equal. apply IH. exact Htl.
Qed.

(** ===== refreshBasket_no_disable_when_all_sound =====
    If every prime erc20 is good, [refreshBasket] succeeds with
    disabled=false and the new basket = projection of primeBasket. *)
Lemma refreshBasket_no_disable_when_all_sound
    (s : BasketHandler.Storage.t) (statuses : list BasketHandler.AssetStatus.t) :
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true)
         s.(BasketHandler.Storage.primeBasket) ->
  s.(BasketHandler.Storage.primeBasket) <> nil ->
  (BasketHandler.refreshBasket s statuses).(BasketHandler.Storage.disabled) = false /\
  (BasketHandler.refreshBasket s statuses).(BasketHandler.Storage.basket) =
    List.map
      (fun p =>
         {| BasketHandler.BasketEntry.asset := p.(BasketHandler.PrimeEntry.erc20);
            BasketHandler.BasketEntry.refAmt := p.(BasketHandler.PrimeEntry.targetAmt) |})
      s.(BasketHandler.Storage.primeBasket).
Proof.
  intros Hall Hnz.
  unfold BasketHandler.refreshBasket.
  assert (Hzero : forall n,
            BasketHandler.unsound_weight n s.(BasketHandler.Storage.primeBasket) statuses = 0).
  { intros. apply unsound_weight_zero_when_all_sound. exact Hall. }
  assert (Hnames :
            Forall
              (fun n => BasketHandler.unsound_weight n s.(BasketHandler.Storage.primeBasket) statuses = 0)
              (BasketHandler.unique_target_names s.(BasketHandler.Storage.primeBasket))).
  { apply Forall_forall. intros n _. apply Hzero. }
  pose proof (build_all_backups_zero_when_no_unsound
                (BasketHandler.unique_target_names s.(BasketHandler.Storage.primeBasket))
                s.(BasketHandler.Storage.primeBasket) statuses
                s.(BasketHandler.Storage.backupConfigs) Hnames) as Hbab.
  rewrite Hbab.
  rewrite app_nil_r.
  rewrite (good_prime_entries_when_all_sound _ _ Hall).
  destruct s.(BasketHandler.Storage.primeBasket) as [|p ps] eqn:Hpb; [contradiction|].
  simpl. split; reflexivity.
Qed.

Lemma setPrimeBasket_then_refreshBasket_no_disable_when_all_sound
    (s s' : BasketHandler.Storage.t) (entries : list BasketHandler.PrimeEntry.t)
    (statuses : list BasketHandler.AssetStatus.t) :
  BasketHandler.setPrimeBasket s entries = Some s' ->
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true) entries ->
  (BasketHandler.refreshBasket s' statuses).(BasketHandler.Storage.disabled) = false /\
  (BasketHandler.refreshBasket s' statuses).(BasketHandler.Storage.basket) =
    List.map
      (fun p =>
         {| BasketHandler.BasketEntry.asset := p.(BasketHandler.PrimeEntry.erc20);
            BasketHandler.BasketEntry.refAmt := p.(BasketHandler.PrimeEntry.targetAmt) |})
      entries.
Proof.
  intros Hset Hall.
  assert (Hpb_eq : s'.(BasketHandler.Storage.primeBasket) = entries).
  { unfold BasketHandler.setPrimeBasket in Hset.
    destruct (_ || _); [discriminate|].
    destruct (negb (BasketHandler.all_targetAmts_valid entries)); [discriminate|].
    destruct (negb (BasketHandler.erc20s_unique _)); [discriminate|].
    injection Hset as <-. reflexivity. }
  assert (Hpb_nz : entries <> nil).
  { intro Heq. rewrite Heq in Hset.
    unfold BasketHandler.setPrimeBasket in Hset. simpl in Hset.
    discriminate. }
  pose proof (refreshBasket_no_disable_when_all_sound s' statuses) as Hno.
  rewrite Hpb_eq in Hno.
  apply Hno; assumption.
Qed.

(** ===== refreshBasket_disabled_implies_no_backup_available =====
    Contrapositive: if [refreshBasket] sets [disabled = true], the
    [build_all_backups] call failed (no available backup for some
    target with positive unsound weight) OR the new basket is empty. *)
Lemma refreshBasket_disabled_implies_no_backup_available
    (s : BasketHandler.Storage.t) (statuses : list BasketHandler.AssetStatus.t) :
  (BasketHandler.refreshBasket s statuses).(BasketHandler.Storage.disabled) = true ->
  BasketHandler.build_all_backups
    (BasketHandler.unique_target_names s.(BasketHandler.Storage.primeBasket))
    s.(BasketHandler.Storage.primeBasket) statuses
    s.(BasketHandler.Storage.backupConfigs) = None
  \/ BasketHandler.good_prime_entries s.(BasketHandler.Storage.primeBasket) statuses = nil
     /\ BasketHandler.build_all_backups
          (BasketHandler.unique_target_names s.(BasketHandler.Storage.primeBasket))
          s.(BasketHandler.Storage.primeBasket) statuses
          s.(BasketHandler.Storage.backupConfigs) = Some nil.
Proof.
  intros Hd.
  unfold BasketHandler.refreshBasket in Hd.
  destruct (BasketHandler.build_all_backups _ _ _ _) as [backups|] eqn:Hb;
    [|left; reflexivity].
  simpl in Hd.
  destruct (Z.of_nat (List.length _) =? 0) eqn:Hlen.
  - apply Z.eqb_eq in Hlen.
    assert (Hnat : Datatypes.length
                     (BasketHandler.good_prime_entries
                        s.(BasketHandler.Storage.primeBasket) statuses ++ backups)
                   = O) by lia.
    apply length_zero_iff_nil in Hnat.
    apply List.app_eq_nil in Hnat.
    destruct Hnat as [Hgp Hbp]. subst.
    right. split; [exact Hgp|reflexivity].
  - simpl in Hd. discriminate.
Qed.

(** =================================================================
    Sum-based weight conservation
    =================================================================
*)

Fixpoint sum_refAmts (es : list BasketHandler.BasketEntry.t) : Z :=
  match es with
  | nil => 0
  | cons e rest => e.(BasketHandler.BasketEntry.refAmt) + sum_refAmts rest
  end.

Lemma sum_refAmts_app (xs ys : list BasketHandler.BasketEntry.t) :
  sum_refAmts (xs ++ ys) = sum_refAmts xs + sum_refAmts ys.
Proof.
  induction xs; simpl; lia.
Qed.

Fixpoint sum_targetAmts (ps : list BasketHandler.PrimeEntry.t) : Z :=
  match ps with
  | nil => 0
  | cons p rest => p.(BasketHandler.PrimeEntry.targetAmt) + sum_targetAmts rest
  end.

(** When all primes are sound, [good_prime_entries] preserves the
    sum of targetAmts. *)
Lemma sum_refAmts_good_prime_entries_all_sound
    (primes : list BasketHandler.PrimeEntry.t) (statuses : list BasketHandler.AssetStatus.t) :
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true) primes ->
  sum_refAmts (BasketHandler.good_prime_entries primes statuses) = sum_targetAmts primes.
Proof.
  induction primes as [|p rest IH]; simpl; intros; [reflexivity|].
  inversion H as [|? ? Hhd Htl]; subst.
  rewrite Hhd. simpl. rewrite (IH Htl). reflexivity.
Qed.

(** ===== refreshBasket_targetAmt_conservation_all_sound =====
    When every prime is sound, the sum of new-basket refAmts equals
    the sum of prime targetAmts — exact conservation, no rounding loss. *)

(** Auxiliary lemma: sum of refAmts over the projection of a prime
    list (mapping each PrimeEntry to a BasketEntry with the same
    targetAmt) equals the sum of the original targetAmts. *)
Lemma sum_refAmts_projection (ps : list BasketHandler.PrimeEntry.t) :
  sum_refAmts
    (List.map
       (fun p =>
          {| BasketHandler.BasketEntry.asset := p.(BasketHandler.PrimeEntry.erc20);
             BasketHandler.BasketEntry.refAmt := p.(BasketHandler.PrimeEntry.targetAmt) |})
       ps)
  = sum_targetAmts ps.
Proof.
  induction ps as [|p rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma refreshBasket_targetAmt_conservation_all_sound
    (s : BasketHandler.Storage.t) (statuses : list BasketHandler.AssetStatus.t) :
  Forall (fun p => BasketHandler.lookup_status p.(BasketHandler.PrimeEntry.erc20) statuses = true)
         s.(BasketHandler.Storage.primeBasket) ->
  s.(BasketHandler.Storage.primeBasket) <> nil ->
  sum_refAmts (BasketHandler.refreshBasket s statuses).(BasketHandler.Storage.basket) =
  sum_targetAmts s.(BasketHandler.Storage.primeBasket).
Proof.
  intros Hall Hnz.
  pose proof (refreshBasket_no_disable_when_all_sound s statuses Hall Hnz) as [_ Hbeq].
  rewrite Hbeq.
  apply sum_refAmts_projection.
Qed.

End BasketHandlerChain.
