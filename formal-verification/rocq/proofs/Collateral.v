(** Collateral state-machine invariant proofs.

    Proves the load-bearing safety invariants on the [Collateral]
    simulation defined in [Reserve.simulations.Collateral]:

      disabled_is_terminal:
        Once the [statusOf] decoder reports DISABLED, [markStatus] for
        any new status is a no-op — _whenDefault stays put. Composing
        this with [statusOf] gives "DISABLED is terminal".

      refPerTok_max_monotone:
        In the no-default case, the cached [exposedReferencePrice] is
        non-decreasing across [updateExposed] applications. Equivalently,
        the only way [exposedReferencePrice] can drop is through a
        hard-default flag.

      iffy_to_disabled_after_delay:
        After [markStatus IFFY] is applied, _whenDefault is set so that
        [statusOf] returns DISABLED at any [now' >= now + delayUntilDefault]
        (under the natural wd-was-NEVER-or-later precondition). This is
        the SM-9 boundary in cas/collateral/status_state_machine.gp.

    Mirrors the CAS witness corpus in
      cas/collateral/status_state_machine.gp        (state machine probes)
      cas/collateral/ref_per_tok_monotonicity.gp    (M-1..M-7 monotonicity)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Coq.Bool.Bool.

Module CollateralProofs.

Import FixLib.
Import Collateral.

(** ===== Helper: DISABLED status decodes as [wd <= now]. ===== *)
Lemma statusOf_disabled_iff (wd now : Z) :
  statusOf wd now = Status.DISABLED <-> (wd <> NEVER /\ wd <= now).
Proof.
  unfold statusOf. split.
  - intros H.
    destruct (wd =? NEVER) eqn:HN.
    + discriminate.
    + apply Z.eqb_neq in HN.
      destruct (now <? wd) eqn:HL.
      * discriminate.
      * apply Z.ltb_ge in HL. split; [exact HN|exact HL].
  - intros [HN HL].
    apply Z.eqb_neq in HN. rewrite HN.
    assert (HL' : (now <? wd) = false) by (apply Z.ltb_ge; exact HL).
    rewrite HL'. reflexivity.
Qed.

(** ===== disabled_is_terminal: once DISABLED, always DISABLED. =====

    Statement: if [statusOf] of [wd] is DISABLED at [now], then
    [markStatus wd s now dud] = wd, for any new status s and any new
    "now" >= now. The latter is Solidity's monotone-clock assumption. *)
Lemma markStatus_terminal_when_disabled
    (wd : Z) (s : Status.t) (now1 now2 dud : Z) :
  statusOf wd now1 = Status.DISABLED ->
  now1 <= now2 ->
  markStatus wd s now2 dud = wd.
Proof.
  intros HD Hmono.
  apply statusOf_disabled_iff in HD. destruct HD as [_ HL].
  unfold markStatus.
  assert (Hcond : (wd <=? now2) = true) by (apply Z.leb_le; lia).
  rewrite Hcond. reflexivity.
Qed.

(** Corollary: once DISABLED at any earlier time, the decoder reports
    DISABLED at every later time after any [markStatus] call. *)
Lemma disabled_is_terminal
    (wd : Z) (s : Status.t) (now1 now2 dud : Z) :
  statusOf wd now1 = Status.DISABLED ->
  now1 <= now2 ->
  statusOf (markStatus wd s now2 dud) now2 = Status.DISABLED.
Proof.
  intros HD Hmono.
  rewrite (markStatus_terminal_when_disabled wd s now1 now2 dud HD Hmono).
  apply statusOf_disabled_iff in HD. destruct HD as [HN HL].
  apply statusOf_disabled_iff. split; [exact HN|lia].
Qed.

(** ===== refPerTok_max_monotone: exposedReferencePrice is non-decreasing
    across [updateExposed] when no hard default fires.

    Equivalently: if [updateExposed] returns [defaulted = false], then
    the new exposed >= old exposed. *)
Lemma updateExposed_monotone_when_not_defaulted
    (exposed underlying revenueShowing : Z) :
  let '(new_exposed, defaulted) :=
    updateExposed exposed underlying revenueShowing in
  defaulted = false -> exposed <= new_exposed.
Proof.
  unfold updateExposed.
  destruct (underlying <? exposed) eqn:Hlt.
  - intros Hno. discriminate.
  - apply Z.ltb_ge in Hlt.
    destruct (exposed <?
                FixLib.mul underlying revenueShowing RoundingMode.FLOOR)
             eqn:Hlt2.
    + apply Z.ltb_lt in Hlt2. intros _. lia.
    + apply Z.ltb_ge in Hlt2. intros _. lia.
Qed.

(** Strong monotonicity (root form): the [updateExposed] output
    [new_exposed] is always at least [exposed] OR strictly less than
    [exposed] with the [defaulted] flag set. *)
Lemma updateExposed_dichotomy
    (exposed underlying revenueShowing : Z) :
  let '(new_exposed, defaulted) :=
    updateExposed exposed underlying revenueShowing in
  (defaulted = true /\ new_exposed = underlying /\ underlying < exposed)
  \/ (defaulted = false /\ exposed <= new_exposed).
Proof.
  unfold updateExposed.
  destruct (underlying <? exposed) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    left. split; [reflexivity|]. split; [reflexivity|exact Hlt].
  - apply Z.ltb_ge in Hlt.
    destruct (exposed <?
                FixLib.mul underlying revenueShowing RoundingMode.FLOOR)
             eqn:Hlt2.
    + apply Z.ltb_lt in Hlt2.
      right. split; [reflexivity|lia].
    + apply Z.ltb_ge in Hlt2.
      right. split; [reflexivity|lia].
Qed.

(** Corollary at the [refresh] level: if [refresh] does not hard-default
    on this step, the cached exposed price is non-decreasing. *)
Lemma refPerTok_max_monotone
    (st : State.t) (underlying pegPrice low now : Z) :
  let '(_, defaulted) :=
    updateExposed st.(State.exposedReferencePrice)
                  underlying st.(State.revenueShowing) in
  defaulted = false ->
  st.(State.exposedReferencePrice) <=
    (refresh st underlying pegPrice low now).(State.exposedReferencePrice).
Proof.
  unfold refresh.
  pose proof (updateExposed_monotone_when_not_defaulted
                st.(State.exposedReferencePrice)
                underlying st.(State.revenueShowing)) as Hmono.
  destruct (updateExposed st.(State.exposedReferencePrice)
                          underlying st.(State.revenueShowing))
    as [new_exposed defaulted] eqn:Hupd.
  intros Hno. simpl. apply Hmono. exact Hno.
Qed.

(** ===== iffy_to_disabled_after_delay: after a markStatus(IFFY) call
    starting from a SOUND state, statusOf transitions to DISABLED at
    any time >= now + delayUntilDefault.

    Precondition: starting from SOUND (whenDefault = NEVER); and
    [now + delayUntilDefault < NEVER] so the sentinel guard at
    FiatCollateral.sol#L191 does not fire. The CAS script SM-9 probes
    this exact boundary. *)
Lemma iffy_to_disabled_after_delay
    (now dud now' : Z) :
  0 <= dud ->
  now + dud < NEVER ->
  now + dud <= now' ->
  statusOf (markStatus NEVER Status.IFFY now dud) now' = Status.DISABLED.
Proof.
  intros Hdud Hbound Hpost.
  unfold markStatus.
  assert (HnotDis : (NEVER <=? now) = false).
  { apply Z.leb_gt. unfold NEVER in *. lia. }
  rewrite HnotDis.
  assert (Hguard : (NEVER <=? now + dud) = false).
  { apply Z.leb_gt. lia. }
  rewrite Hguard.
  assert (Hsum : (now + dud <? NEVER) = true).
  { apply Z.ltb_lt. exact Hbound. }
  rewrite Hsum.
  apply statusOf_disabled_iff. split.
  - intros Hcontra. rewrite Hcontra in Hbound. lia.
  - exact Hpost.
Qed.

(** ===== Auxiliary: markStatus(IFFY) never extends an existing IFFY
    deadline (SM-3 in the CAS script), under the non-saturating
    precondition [now + dud < NEVER] that the L191 guard does not fire. *)
Lemma markStatus_iffy_deadline_monotone
    (wd now dud : Z) :
  wd <> NEVER ->
  now < wd ->
  0 <= dud ->
  now + dud < NEVER ->
  markStatus wd Status.IFFY now dud <= wd.
Proof.
  intros HN Hlt Hdud Hsum.
  unfold markStatus.
  assert (Hcond : (wd <=? now) = false) by (apply Z.leb_gt; lia).
  rewrite Hcond.
  assert (Hg : (NEVER <=? now + dud) = false) by (apply Z.leb_gt; lia).
  rewrite Hg.
  destruct (now + dud <? wd) eqn:Hlt2.
  - apply Z.ltb_lt in Hlt2. lia.
  - apply Z.ltb_ge in Hlt2. lia.
Qed.

End CollateralProofs.
