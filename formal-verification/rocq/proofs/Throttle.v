(** Throttle simulation invariant proofs.

    Proves the load-bearing safety invariants on the [ThrottleLib]
    simulation defined in [Reserve.simulations.Throttle]:

      INV-1   currentlyAvailable t limit now <= limit
      INV-1'  currentlyAvailable t limit now >= 0  (under input sanity)
      INV-3   useAvailable with amount > 0 ⟹ lastAvailable = avail - amount
      INV-4   useAvailable with amount < 0 ⟹ lastAvailable = avail + |amount|
      INV-5   useAvailable reverts iff amount > 0 ∧ amount > avail
      Mono    currentlyAvailable is non-decreasing in [now]

    These propagate to the on-chain code through the (still-pending)
    [run_useAvailable] equivalence lemma, which lives in a separate file
    because it depends on the Yul-runtime semantics (proofs/RocqOfSolidity).

    INV-2 (validity preservation) is intentionally omitted from this file —
    it requires uint256-overflow analysis on the addition path that needs
    a separate lemma about [currentlyAvailable]'s upper bound under valid
    inputs. Tracked as follow-up.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Throttle.
Require Import Coq.Bool.Bool.

Module ThrottleProofs.

Import ThrottleLib.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** ----- INV-1: currentlyAvailable is bounded above by the limit. ----- *)
Lemma currentlyAvailable_le_limit
    (t : Throttle.t) (limit now : U256.t) :
  currentlyAvailable t limit now <= limit.
Proof.
  unfold currentlyAvailable. apply Z.le_min_l.
Qed.

(** ----- INV-1': non-negativity, under sane inputs. -----
    [lastAvailable >= 0], [limit >= 0], and [now >= lastTimestamp]
    suffice. The first is part of [Valid.throttle]; the third is the
    natural assumption that the current block timestamp is no earlier
    than the throttle was last touched. *)
Lemma currentlyAvailable_nonneg
    (t : Throttle.t) (limit now : U256.t) :
  0 <= t.(Throttle.lastAvailable) ->
  0 <= limit ->
  t.(Throttle.lastTimestamp) <= now ->
  0 <= currentlyAvailable t limit now.
Proof.
  intros Hav Hlim Hts.
  unfold currentlyAvailable.
  apply Z.min_glb; [exact Hlim|].
  enough (0 <= (limit * (now - t.(Throttle.lastTimestamp))) / ONE_HOUR) by lia.
  apply Z.div_pos.
  - apply Z.mul_nonneg_nonneg; lia.
  - unfold ONE_HOUR; lia.
Qed.

(** ----- INV-3: positive amount, on success, decreases lastAvailable
    by exactly [amount]. ----- *)
Lemma useAvailable_positive_success
    (t t' : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  ~ (t.(Throttle.params).(Params.amtRate) = 0 /\
     t.(Throttle.params).(Params.pctRate) = 0) ->
  0 < amount ->
  useAvailable t supply amount now = Result.Success t' ->
  amount <= currentlyAvailable t (hourlyLimit t supply) now /\
  t'.(Throttle.lastAvailable) =
    currentlyAvailable t (hourlyLimit t supply) now - amount.
Proof.
  intros Hnz Hpos Hok.
  unfold useAvailable in Hok.
  destruct (andb _ _) eqn:Hzero.
  - apply andb_true_iff in Hzero. destruct Hzero as [Ha Hp].
    apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hp.
    exfalso. apply Hnz. split; assumption.
  - assert (Hpos' : (0 <? amount) = true) by (apply Z.ltb_lt; lia).
    rewrite Hpos' in Hok.
    destruct (amount <=? _) eqn:Hle; [|discriminate].
    apply Z.leb_le in Hle.
    inversion Hok; subst.
    split; [exact Hle|reflexivity].
Qed.

(** ----- INV-4: negative amount, on success, increases lastAvailable by |amount|. ----- *)
Lemma useAvailable_negative_success
    (t t' : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  ~ (t.(Throttle.params).(Params.amtRate) = 0 /\
     t.(Throttle.params).(Params.pctRate) = 0) ->
  amount < 0 ->
  useAvailable t supply amount now = Result.Success t' ->
  t'.(Throttle.lastAvailable) =
    currentlyAvailable t (hourlyLimit t supply) now + (- amount).
Proof.
  intros Hnz Hneg Hok.
  unfold useAvailable in Hok.
  destruct (andb _ _) eqn:Hzero.
  - apply andb_true_iff in Hzero. destruct Hzero as [Ha Hp].
    apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hp.
    exfalso. apply Hnz. split; assumption.
  - assert (Hpos' : (0 <? amount) = false) by (apply Z.ltb_ge; lia).
    rewrite Hpos' in Hok.
    assert (Hneg' : (amount <? 0) = true) by (apply Z.ltb_lt; lia).
    rewrite Hneg' in Hok.
    inversion Hok; subst. reflexivity.
Qed.

(** ----- INV-5: revert iff amount > 0 ∧ amount > available. -----
    Note the precondition on rates: when amtRate = pctRate = 0 the
    function early-returns Success and never reverts. *)
Lemma useAvailable_revert_iff
    (t : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t) :
  ~ (t.(Throttle.params).(Params.amtRate) = 0 /\
     t.(Throttle.params).(Params.pctRate) = 0) ->
  ((exists ps qs, useAvailable t supply amount now = Result.Revert ps qs)
     <-> (0 < amount /\
          currentlyAvailable t (hourlyLimit t supply) now < amount)).
Proof.
  intros Hnz.
  unfold useAvailable.
  destruct (andb _ _) eqn:Hzero.
  - apply andb_true_iff in Hzero. destruct Hzero as [Ha Hp].
    apply Z.eqb_eq in Ha. apply Z.eqb_eq in Hp.
    exfalso. apply Hnz. split; assumption.
  - destruct (0 <? amount) eqn:Hpos.
    + apply Z.ltb_lt in Hpos.
      destruct (amount <=? _) eqn:Hle.
      * apply Z.leb_le in Hle. split.
        -- intros HR; destruct HR as [ps HR1]; destruct HR1 as [qs HR2];
           discriminate.
        -- intros HC; destruct HC as [_ Hlt]; lia.
      * apply Z.leb_gt in Hle. split.
        -- intros _. split; [exact Hpos|exact Hle].
        -- intros _. unfold revert_throttled. exists 0. exists 32. reflexivity.
    + apply Z.ltb_ge in Hpos.
      destruct (amount <? 0) eqn:Hneg.
      * split.
        -- intros HR; destruct HR as [ps HR1]; destruct HR1 as [qs HR2];
           discriminate.
        -- intros HC; destruct HC as [Hcontra _]; lia.
      * split.
        -- intros HR; destruct HR as [ps HR1]; destruct HR1 as [qs HR2];
           discriminate.
        -- intros HC; destruct HC as [Hcontra _]; lia.
Qed.

(** ----- Monotonicity: currentlyAvailable non-decreasing in [now]. -----
    Combined with [currentlyAvailable_le_limit], this is the "throttle
    refills monotonically up to the cap" property. *)
Lemma currentlyAvailable_monotone
    (t : Throttle.t) (limit now1 now2 : U256.t) :
  0 <= limit ->
  t.(Throttle.lastTimestamp) <= now1 <= now2 ->
  currentlyAvailable t limit now1 <= currentlyAvailable t limit now2.
Proof.
  intros Hlim [Ht1 Ht2].
  unfold currentlyAvailable.
  apply Z.min_le_compat_l.
  apply Z.add_le_mono_l.
  apply Z.div_le_mono; [unfold ONE_HOUR; lia|].
  apply Z.mul_le_mono_nonneg_l; lia.
Qed.

(** ----- Sanity: zero amount is always a no-op success (modulo timestamp). ----- *)
Lemma useAvailable_zero_succeeds
    (t : Throttle.t) (supply : U256.t) (now : U256.t) :
  exists t', useAvailable t supply 0 now = Result.Success t'.
Proof.
  unfold useAvailable.
  destruct (andb _ _).
  - exists t. reflexivity.
  - cbn. eexists; reflexivity.
Qed.

End ThrottleProofs.
