(** BasketHandler validity / output-bound lemmas.

    Two layers, mirroring the simulation's split:

      Layer 1 — Quote math kernel:
        1. [quote_one_nonneg] — given non-negative [refAmt] and [baskets],
           the per-asset quote [quote_one refAmt baskets mode] is
           non-negative for any rounding mode.
        2. [quoteQuantities_nonneg] — pointwise non-negativity of every
           entry in [quoteQuantities b baskets mode], lifted from the
           per-asset claim above.

      Layer 2 — Storage lifecycle:
        3. [setPrimeBasket_preserves_validity] — a successful
           [setPrimeBasket s entries] yields a valid storage given a
           valid input storage.
        4. [refreshBasket_preserves_validity] — [refreshBasket s
           statuses] always yields a valid storage given a valid input
           storage. (Total operation; no [option] return.)

    The Layer-1 proofs lean on the same FixLib round-direction discipline
    used in the BackingManager validity lemmas: [divrnd] is non-negative
    whenever the numerator is non-negative and the divisor is positive.

    The Layer-2 proofs are essentially structural — [setPrimeBasket] and
    [refreshBasket] only mutate fields that [Valid.t] tracks, and the
    pre-condition / write logic ensures the new field values satisfy
    the invariants by construction.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Module BasketHandlerValidityProofs.

Import FixLib.
Import BasketHandler.

(** =================================================================
    Layer 1 — quote math kernel.
    =================================================================
*)

(** Helper: [divrnd n d mode] is non-negative whenever the numerator is
    non-negative and the divisor is positive. (Same shape as the
    BackingManager validity helper — duplicated locally to keep this
    module self-contained.) *)
Lemma divrnd_nonneg (n d : Z) (mode : RoundingMode.t) :
  0 <= n -> 0 < d -> 0 <= divrnd n d mode.
Proof.
  intros Hn Hd.
  unfold divrnd.
  assert (Hq : 0 <= n / d) by (apply Z.div_pos; [exact Hn|exact Hd]).
  destruct mode.
  - exact Hq.
  - destruct (n mod d >? (d - 1) / 2); lia.
  - destruct (n mod d =? 0); lia.
Qed.

(** ===== INV-V1 (kernel): per-asset quote is non-negative. =====
    [quote_one refAmt baskets mode = divrnd (refAmt*baskets) FIX_SCALE mode]
    is >= 0 whenever both inputs are non-negative, because the numerator
    [refAmt * baskets] is then non-negative and [FIX_SCALE > 0]. *)
Lemma quote_one_nonneg
    (refAmt baskets : U256.t) (mode : RoundingMode.t) :
  0 <= refAmt ->
  0 <= baskets ->
  0 <= quote_one refAmt baskets mode.
Proof.
  intros Hr Hb.
  unfold quote_one, FixLib.mulu_toUint.
  apply divrnd_nonneg.
  - apply Z.mul_nonneg_nonneg; assumption.
  - unfold FIX_SCALE; lia.
Qed.

(** ===== INV-V2 (lifted): every per-asset quote in the list is non-negative.

    Given a basket where every [refAmt] is non-negative and a non-negative
    [baskets] input, every {qTok} amount in [quoteQuantities] is non-negative.
    This is the load-bearing "no negative {qTok}" claim. *)
Lemma quoteQuantities_nonneg
    (b : Basket) (baskets : U256.t) (mode : RoundingMode.t) :
  0 <= baskets ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) b ->
  Forall (fun q => 0 <= q) (quoteQuantities b baskets mode).
Proof.
  intros Hb Hval.
  unfold quoteQuantities.
  induction b as [|e rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    apply Forall_cons.
    + simpl. apply quote_one_nonneg; assumption.
    + apply IH. exact Htl.
Qed.

(** =================================================================
    Layer 2 — storage lifecycle.
    =================================================================
*)

(** Helper: [targetAmt_valid a = true] iff [MIN_TARGET_AMT <= a <=
    MAX_TARGET_AMT]. *)
Lemma targetAmt_valid_iff (a : Z) :
  targetAmt_valid a = true <->
  MIN_TARGET_AMT <= a <= MAX_TARGET_AMT.
Proof.
  unfold targetAmt_valid.
  rewrite Bool.andb_true_iff.
  rewrite !Z.leb_le. tauto.
Qed.

(** ===== setPrimeBasket preserves validity. =====

    Given a valid pre-state and a successful [setPrimeBasket] call, the
    post-state is still valid. The proof unpacks the pre-conditions
    encoded in [setPrimeBasket]'s validation gates and copies the
    [nonce_u256] field forward (the +1 is small relative to the
    UINT256_MAX ceiling, and the pre-state's [nonce_u256] is
    weakened — practically the nonce is uint48 in production but we
    state the bound at uint256 here matching the simulation's looser
    [nonce : U256.t] type). The extra hypothesis
    [nonce_le_pred] is the call-boundary EVM bound [nonce + 1 <=
    UINT256_MAX], structurally equivalent to "the nonce hasn't
    overflowed uint48".
*)
Lemma setPrimeBasket_preserves_validity
    (s s' : Storage.t) (entries : list PrimeEntry.t) :
  Valid.t s ->
  s.(Storage.nonce) + 1 <= UINT256_MAX ->
  setPrimeBasket s entries = Some s' ->
  Valid.t s'.
Proof.
  intros Hv Hnonce_pre Hcall.
  destruct Hv as [Hsz Htgt Huniq Hnonce Hbask].
  unfold setPrimeBasket in Hcall.
  destruct (_ || _) eqn:Hbad_len; [discriminate|].
  destruct (negb (all_targetAmts_valid entries)) eqn:Hbad_amts; [discriminate|].
  destruct (negb (erc20s_unique _)) eqn:Hbad_dup; [discriminate|].
  injection Hcall as Hs'_eq.
  subst s'.
  apply Bool.orb_false_iff in Hbad_len.
  destruct Hbad_len as [Hlen_nz Hlen_max].
  apply Z.eqb_neq in Hlen_nz.
  rewrite Z.gtb_ltb in Hlen_max.
  apply Z.ltb_ge in Hlen_max.
  apply Bool.negb_false_iff in Hbad_amts.
  apply Bool.negb_false_iff in Hbad_dup.
  split; simpl.
  - exact Hlen_max.
  - exact Hbad_amts.
  - exact Hbad_dup.
  - destruct Hnonce as [Hn_lo _].
    split; lia.
  - exact Hbask.
Qed.

(** ----- Helpers used by refreshBasket validity -----

    [refreshBasket] only writes the [basket], [nonce], and [disabled]
    fields. It does NOT touch [primeBasket] or [backupConfigs] — those
    are governance-set and remain unchanged by basket refresh. So the
    [Valid.t] invariants on [primeBasket] (size, targetAmts, unique)
    transfer trivially. The [nonce] either stays the same (failure
    path) or is incremented by 1 (success path). *)

Lemma refreshBasket_keeps_primeBasket
    (s : Storage.t) (statuses : list AssetStatus.t) :
  (refreshBasket s statuses).(Storage.primeBasket) = s.(Storage.primeBasket).
Proof.
  unfold refreshBasket.
  destruct (build_all_backups _ _ _ _) as [backups|]; simpl.
  - destruct (Z.of_nat (List.length _) =? 0); reflexivity.
  - reflexivity.
Qed.

Lemma refreshBasket_keeps_backupConfigs
    (s : Storage.t) (statuses : list AssetStatus.t) :
  (refreshBasket s statuses).(Storage.backupConfigs) = s.(Storage.backupConfigs).
Proof.
  unfold refreshBasket.
  destruct (build_all_backups _ _ _ _) as [backups|]; simpl.
  - destruct (Z.of_nat (List.length _) =? 0); reflexivity.
  - reflexivity.
Qed.

(** Nonce monotonicity for refreshBasket: the post-state nonce is
    either equal to the pre-state nonce (failure path) or incremented
    by exactly 1 (success path). *)
Lemma refreshBasket_nonce_step
    (s : Storage.t) (statuses : list AssetStatus.t) :
  (refreshBasket s statuses).(Storage.nonce) = s.(Storage.nonce) \/
  (refreshBasket s statuses).(Storage.nonce) = s.(Storage.nonce) + 1.
Proof.
  unfold refreshBasket.
  destruct (build_all_backups _ _ _ _) as [backups|]; simpl.
  - destruct (Z.of_nat (List.length _) =? 0); simpl.
    + left. reflexivity.
    + right. reflexivity.
  - left. reflexivity.
Qed.

(** ===== refreshBasket preserves validity. =====

    [refreshBasket] is total. It either:
    - writes a fresh basket and increments [nonce] (success path), or
    - keeps the basket as-is and leaves [nonce] alone (failure path).

    Both paths preserve [Valid.t] because:
    - [primeBasket], [backupConfigs] are not touched (helpers above).
    - [nonce] either stays the same or grows by 1 (still <= UINT256_MAX
      under the call-boundary hypothesis [nonce + 1 <= UINT256_MAX]). *)
(** ----- Helpers for new-basket non-negativity. -----

    The construction in [refreshBasket]:
    - [good_prime_entries] copies prime targetAmts (which by Valid.t are
      in [MIN_TARGET_AMT, MAX_TARGET_AMT], hence positive);
    - [build_backups_for_target] divides a non-negative [unsound_weight]
      by a positive [size], producing non-negative quotients.

    Both compose to "every entry in the new basket has non-negative
    refAmt". *)

Lemma targetAmt_valid_iff_pos (a : Z) :
  targetAmt_valid a = true ->
  MIN_TARGET_AMT <= a <= MAX_TARGET_AMT.
Proof.
  unfold targetAmt_valid.
  rewrite Bool.andb_true_iff.
  rewrite !Z.leb_le. tauto.
Qed.

Lemma MIN_TARGET_AMT_pos : 0 < MIN_TARGET_AMT.
Proof. unfold MIN_TARGET_AMT, FIX_ONE, FIX_SCALE. lia. Qed.

Lemma all_targetAmts_valid_pos (primes : list PrimeEntry.t) :
  all_targetAmts_valid primes = true ->
  Forall (fun p => 0 <= p.(PrimeEntry.targetAmt)) primes.
Proof.
  induction primes as [|p rest IH]; simpl; [auto|].
  intros H. apply Bool.andb_true_iff in H as [Hp Hrest].
  apply targetAmt_valid_iff_pos in Hp.
  pose proof MIN_TARGET_AMT_pos as Hmin.
  apply Forall_cons; [lia|]. apply IH. exact Hrest.
Qed.

Lemma good_prime_entries_nonneg
    (primes : list PrimeEntry.t) (statuses : list AssetStatus.t) :
  all_targetAmts_valid primes = true ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) (good_prime_entries primes statuses).
Proof.
  intros Hv.
  induction primes as [|p rest IH]; simpl; [apply Forall_nil|].
  apply Bool.andb_true_iff in Hv as [Hp Hrest].
  apply targetAmt_valid_iff_pos in Hp.
  pose proof MIN_TARGET_AMT_pos as Hmin.
  destruct (lookup_status p.(PrimeEntry.erc20) statuses); simpl.
  - apply Forall_cons.
    + simpl. lia.
    + apply IH. exact Hrest.
  - apply IH. exact Hrest.
Qed.

Lemma unsound_weight_nonneg
    (name : U256.t) (primes : list PrimeEntry.t)
    (statuses : list AssetStatus.t) :
  all_targetAmts_valid primes = true ->
  0 <= unsound_weight name primes statuses.
Proof.
  induction primes as [|p rest IH]; simpl; [lia|].
  intros Hv.
  apply Bool.andb_true_iff in Hv as [Hp Hrest].
  apply targetAmt_valid_iff_pos in Hp.
  pose proof MIN_TARGET_AMT_pos as Hmin.
  pose proof (IH Hrest) as IHrest.
  destruct (_ && _); lia.
Qed.

Lemma build_backups_for_target_nonneg
    (name : U256.t) (primes : list PrimeEntry.t)
    (statuses : list AssetStatus.t) (configs : list BackupEntry.t)
    (entries : list BasketEntry.t) :
  all_targetAmts_valid primes = true ->
  build_backups_for_target name primes statuses configs = Some entries ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) entries.
Proof.
  intros Hv Hcall.
  unfold build_backups_for_target in Hcall.
  destruct (unsound_weight name primes statuses =? 0) eqn:Hzero.
  - injection Hcall as <-. apply Forall_nil.
  - destruct (find_backup_config name configs) as [bc|] eqn:Hbc; [|discriminate].
    set (avail := select_backups statuses bc.(BackupEntry.erc20s)
                    (Z.to_nat bc.(BackupEntry.max))) in *.
    destruct (Z.of_nat (Datatypes.length avail) =? 0) eqn:Hsize;
      [discriminate|].
    injection Hcall as <-.
    apply Z.eqb_neq in Hzero.
    apply Z.eqb_neq in Hsize.
    pose proof (unsound_weight_nonneg name primes statuses Hv) as Hsm.
    apply Forall_forall.
    intros e Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [erc Hand]. destruct Hand as [Heq Hin2].
    subst e. simpl.
    apply Z.div_pos.
    + lia.
    + assert (0 <= Z.of_nat (Datatypes.length avail)) by lia. lia.
Qed.

Lemma build_all_backups_nonneg
    (names : list U256.t) (primes : list PrimeEntry.t)
    (statuses : list AssetStatus.t) (configs : list BackupEntry.t)
    (entries : list BasketEntry.t) :
  all_targetAmts_valid primes = true ->
  build_all_backups names primes statuses configs = Some entries ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) entries.
Proof.
  intros Hv. revert entries.
  induction names as [|n rest IH]; simpl; intros entries Hcall.
  - injection Hcall as <-. apply Forall_nil.
  - destruct (build_backups_for_target n primes statuses configs) as [this|] eqn:Hthis;
      [|discriminate].
    destruct (build_all_backups rest primes statuses configs) as [others|] eqn:Hothers;
      [|discriminate].
    pose proof (IH others eq_refl) as IHothers.
    injection Hcall as <-.
    apply Forall_app. split.
    + eapply build_backups_for_target_nonneg; eassumption.
    + exact IHothers.
Qed.

Lemma refreshBasket_preserves_validity
    (s : Storage.t) (statuses : list AssetStatus.t) :
  Valid.t s ->
  s.(Storage.nonce) + 1 <= UINT256_MAX ->
  Valid.t (refreshBasket s statuses).
Proof.
  intros Hv Hnonce_pre.
  destruct Hv as [Hsz Htgt Huniq Hnonce Hbask].
  pose proof (refreshBasket_keeps_primeBasket s statuses) as Hp.
  pose proof (refreshBasket_keeps_backupConfigs s statuses) as Hb.
  pose proof (refreshBasket_nonce_step s statuses) as Hn.
  split.
  - rewrite Hp. exact Hsz.
  - rewrite Hp. exact Htgt.
  - rewrite Hp. exact Huniq.
  - destruct Hn as [Heq|Hsucc].
    + rewrite Heq. exact Hnonce.
    + rewrite Hsucc.
      destruct Hnonce as [Hlo _].
      split; lia.
  - (* basket_refAmts_nonneg *)
    unfold refreshBasket.
    destruct (build_all_backups _ _ _ _) as [backups|] eqn:Hbackups; simpl.
    + destruct (Z.of_nat (List.length _) =? 0); simpl.
      * exact Hbask.
      * apply Forall_app. split.
        -- apply good_prime_entries_nonneg. exact Htgt.
        -- eapply build_all_backups_nonneg; eassumption.
    + exact Hbask.
Qed.

End BasketHandlerValidityProofs.
