(** Furnace simulation invariant proofs.

    Proves the load-bearing safety invariants on the [Furnace] simulation
    defined in [Reserve.simulations.Furnace]:

      INV-EARLY     melt is a no-op when now < lastPayout + 1
      INV-BOUND     amount <= lastPayoutBal (under payoutRatio <= FIX_ONE)
      INV-ADVANCE   on a non-trivial call, lastPayout' = now exactly
      INV-RATIO     setRatio with ratio_ <= MAX_RATIO returns Some s' valid
      INV-RATIO-NEG setRatio with ratio_ > MAX_RATIO returns None
      INV-NUMPER    numPeriods = now - lastPayout in the non-trivial branch

    These mirror the Solidity comments at protocol/contracts/p1/Furnace.sol
    lines 26-31 (the "Invariants" block) and the comments above [melt]
    (lines 55-63: lastPayout' = lastPayout + numPeriods, etc.).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.

Module FurnaceProofs.

Import FixLib.
Import Furnace.

(** ===== INV-EARLY: melt is a no-op when now < lastPayout + 1. ===== *)
Lemma melt_no_op_when_too_early
    (s : Storage.t) (now currentBalance : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  melt s now currentBalance = (s, 0).
Proof.
  intros Hlt.
  unfold melt.
  assert (Hcond : (now <? s.(Storage.lastPayout) + 1) = true)
    by (apply Z.ltb_lt; exact Hlt).
  rewrite Hcond. reflexivity.
Qed.

(** ===== INV-NUMPER: in the non-trivial branch, numPeriods = now - lastPayout
    and the new lastPayout = now. ===== *)
Lemma melt_advances_lastPayout
    (s : Storage.t) (now currentBalance : U256.t) :
  s.(Storage.lastPayout) + 1 <= now ->
  exists amount,
    melt s now currentBalance =
      ({| Storage.ratio := s.(Storage.ratio);
          Storage.lastPayout := now;
          Storage.lastPayoutBal := currentBalance - amount; |}, amount).
Proof.
  intros Hge.
  unfold melt.
  assert (Hcond : (now <? s.(Storage.lastPayout) + 1) = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hcond.
  set (numPeriods := now - s.(Storage.lastPayout)).
  set (payoutRatio :=
         FixLib.minus FixLib.FIX_ONE
           (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
              numPeriods)).
  set (amount :=
         FixLib.mulu_toUint payoutRatio s.(Storage.lastPayoutBal)
           RoundingMode.FLOOR).
  exists amount.
  assert (Hsum : s.(Storage.lastPayout) + numPeriods = now).
  { unfold numPeriods. lia. }
  rewrite Hsum.
  reflexivity.
Qed.

(** ===== INV-BOUND: the melted amount is bounded above by [lastPayoutBal]
    when [payoutRatio <= FIX_ONE]. -----

    The Solidity-level [require] guarantees [ratio <= MAX_RATIO < FIX_ONE],
    and the algebraic identity [payoutRatio = 1 - (1-ratio)^N] keeps it in
    [0, FIX_ONE]. The CAS script cas/furnace/melt_curve.gp confirms this
    bound holds across N up to 5e5. *)
Lemma melt_amount_bounded_by_balance
    (s : Storage.t) (now currentBalance : U256.t) :
  0 <= s.(Storage.lastPayoutBal) ->
  let numPeriods := now - s.(Storage.lastPayout) in
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio)) numPeriods) in
  payoutRatio <= FIX_ONE ->
  0 <= payoutRatio ->
  snd (melt s now currentBalance) <= s.(Storage.lastPayoutBal).
Proof.
  cbv zeta. intros Hbal Hpr_hi Hpr_lo.
  unfold melt.
  destruct (now <? s.(Storage.lastPayout) + 1) eqn:Hcond.
  - cbn. exact Hbal.
  - cbn [snd].
    (* amount = (payoutRatio * lastPayoutBal) / 10^18.
       Since payoutRatio <= 10^18 and lastPayoutBal >= 0,
       (payoutRatio * lastPayoutBal) / 10^18 <= lastPayoutBal. *)
    unfold FixLib.mulu_toUint, FixLib.divrnd.
    apply Z.div_le_upper_bound.
    + unfold FixLib.FIX_SCALE. lia.
    + apply Z.mul_le_mono_nonneg_r; [exact Hbal|].
      unfold FIX_ONE, FixLib.FIX_SCALE in Hpr_hi. exact Hpr_hi.
Qed.

(** ===== INV-RATIO: setRatio with ratio_ <= MAX_RATIO succeeds and the
    resulting state is valid. ===== *)
Lemma setRatio_preserves_validity
    (s : Storage.t) (ratio_ : U256.t) :
  Valid.t s ->
  0 <= ratio_ ->
  ratio_ <= MAX_RATIO ->
  exists s', setRatio s ratio_ = Some s' /\ Valid.t s'.
Proof.
  intros Hvalid Hpos Hle.
  unfold setRatio.
  assert (Hcond : (ratio_ <=? MAX_RATIO) = true)
    by (apply Z.leb_le; exact Hle).
  rewrite Hcond.
  eexists. split; [reflexivity|].
  destruct Hvalid as [_ _ Hlp Hbal].
  constructor; simpl.
  - exact Hle.
  - exact Hpos.
  - exact Hlp.
  - exact Hbal.
Qed.

(** ===== INV-RATIO-NEG: setRatio with ratio_ > MAX_RATIO returns None. ===== *)
Lemma setRatio_rejects_over_max
    (s : Storage.t) (ratio_ : U256.t) :
  MAX_RATIO < ratio_ ->
  setRatio s ratio_ = None.
Proof.
  intros Hgt.
  unfold setRatio.
  assert (Hcond : (ratio_ <=? MAX_RATIO) = false)
    by (apply Z.leb_gt; exact Hgt).
  rewrite Hcond. reflexivity.
Qed.

(** ===== INV-RATIO-PRESERVES: setRatio leaves lastPayout and lastPayoutBal
    unchanged. ===== *)
Lemma setRatio_preserves_payout_state
    (s s' : Storage.t) (ratio_ : U256.t) :
  setRatio s ratio_ = Some s' ->
  s'.(Storage.lastPayout) = s.(Storage.lastPayout) /\
  s'.(Storage.lastPayoutBal) = s.(Storage.lastPayoutBal) /\
  s'.(Storage.ratio) = ratio_.
Proof.
  intros Hok.
  unfold setRatio in Hok.
  destruct (ratio_ <=? MAX_RATIO) eqn:Hcond; [|discriminate].
  inversion Hok; subst. simpl.
  split; [reflexivity|].
  split; reflexivity.
Qed.

(** ===== Storage shape on early return: a no-op leaves storage exactly
    as it was. ===== *)
Lemma melt_storage_unchanged_when_too_early
    (s : Storage.t) (now currentBalance : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  fst (melt s now currentBalance) = s.
Proof.
  intros Hlt.
  rewrite (melt_no_op_when_too_early s now currentBalance Hlt).
  reflexivity.
Qed.

(** ===== Amount on early return is zero. ===== *)
Lemma melt_amount_zero_when_too_early
    (s : Storage.t) (now currentBalance : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  snd (melt s now currentBalance) = 0.
Proof.
  intros Hlt.
  rewrite (melt_no_op_when_too_early s now currentBalance Hlt).
  reflexivity.
Qed.

(** ===== ratio is preserved by every melt call (governance-only mutation). ===== *)
Lemma melt_preserves_ratio
    (s : Storage.t) (now currentBalance : U256.t) :
  (fst (melt s now currentBalance)).(Storage.ratio) = s.(Storage.ratio).
Proof.
  unfold melt.
  destruct (now <? s.(Storage.lastPayout) + 1); reflexivity.
Qed.

End FurnaceProofs.
