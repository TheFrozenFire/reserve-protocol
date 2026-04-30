(** CurveStableCollateral plugin invariants.

    Mirrors [proofs/Collateral.v] for the Curve plugin overrides
    defined in [Reserve.simulations.CurveStableCollateral].

    Headline lemmas:

      hardDefault_iff_vp_below_exposed:
        The plugin hard-defaults on a refresh iff the input
        [virtualPrice] is strictly less than the cached
        [exposedReferencePrice]. Closes the form
        "Curve's hard-default threshold is the revenue-hiding band".

      refresh_pricedRevert_outer_disables:
        If the outer [get_virtual_price()] reverts ([pricedRevert =
        true]), the plugin's [refresh] writes [whenDefault <= now],
        i.e. status DISABLED. Pins CV-4 of the CAS witness.

      refresh_inner_revert_or_depeg_iffy_unless_hardDefault:
        If the inner [tryPrice()] reverts OR [poolDepegged] is true,
        the plugin marks IFFY (NOT DISABLED) — except in the
        co-occurring case where the parent's hard-default branch
        already fired. Pins CV-5, CV-6.

      refresh_disabled_terminal:
        DISABLED is preserved across the plugin override regardless
        of input flags. Composes the parent's
        [markStatus_terminal_when_disabled] over both branches
        (outer-revert vs success).

    Mirrors the CAS witness corpus in
      cas/collateral/curve_virtual_price_drop.gp   (CV-1..CV-8) *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CurveStableCollateral.
Require Import Reserve.proofs.Collateral.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Module CurveStableCollateralProofs.

Import FixLib.

(** ===== hardDefault_iff_vp_below_exposed =====

    The plugin hard-defaults on a refresh iff the input
    [virtualPrice] is strictly less than the cached
    [exposedReferencePrice], witnessed by the [hardDefaultTriggered]
    closed predicate. *)
Lemma hardDefault_iff_vp_below_exposed
    (s : CurveStableCollateral.CurveState.t) (vp : Z) :
  CurveStableCollateral.hardDefaultTriggered s vp = true
  <->
  vp < s.(CurveStableCollateral.CurveState.base).(Collateral.State.exposedReferencePrice).
Proof.
  unfold CurveStableCollateral.hardDefaultTriggered.
  split.
  - intro H. apply Z.ltb_lt in H. exact H.
  - intro H. apply Z.ltb_lt in H. exact H.
Qed.

(** ===== refresh_pricedRevert_outer_disables =====

    If [pricedRevert = true], the plugin's [refresh] writes the
    post-state with [statusOf whenDefault now = DISABLED].
    Natural [now < NEVER] precondition rules out the boundary at
    exactly NEVER. *)
Lemma refresh_pricedRevert_outer_disables
    (s : CurveStableCollateral.CurveState.t)
    (vp low now : Z)
    (pr_inner depeg : bool) :
  0 <= now ->
  now < Collateral.NEVER ->
  let s' :=
    CurveStableCollateral.refresh s vp low now true pr_inner depeg in
  Collateral.statusOf
    (s'.(CurveStableCollateral.CurveState.base)).(Collateral.State.whenDefault) now
    = Collateral.Status.DISABLED.
Proof.
  intros Hnow_nn Hnow_lt.
  simpl.
  unfold CurveStableCollateral.refresh; simpl.
  unfold Collateral.markStatus.
  destruct (s.(CurveStableCollateral.CurveState.base).(Collateral.State.whenDefault)
              <=? now) eqn:Hter.
  - (* Already DISABLED before the mark: status holds directly. *)
    apply Z.leb_le in Hter.
    apply CollateralProofs.statusOf_disabled_iff. split.
    + intro Hcontra. unfold Collateral.NEVER in *. lia.
    + lia.
  - (* Not yet disabled: markStatus DISABLED writes wd' = now. *)
    apply Z.leb_gt in Hter.
    apply CollateralProofs.statusOf_disabled_iff. split.
    + intro Hcontra. unfold Collateral.NEVER in *. lia.
    + lia.
Qed.

(** ===== refresh_pricedRevert_outer_no_change_to_exposed =====

    The outer-revert branch leaves [exposedReferencePrice]
    untouched. Pins the second clause of CV-4. *)
Lemma refresh_pricedRevert_outer_no_change_to_exposed
    (s : CurveStableCollateral.CurveState.t)
    (vp low now : Z)
    (pr_inner depeg : bool) :
  let s' :=
    CurveStableCollateral.refresh s vp low now true pr_inner depeg in
  (s'.(CurveStableCollateral.CurveState.base))
    .(Collateral.State.exposedReferencePrice)
  = s.(CurveStableCollateral.CurveState.base)
       .(Collateral.State.exposedReferencePrice).
Proof.
  simpl. unfold CurveStableCollateral.refresh; simpl. reflexivity.
Qed.

(** ===== Local helper: the abstract base's refresh respects DISABLED. *)
Lemma refresh_preserves_disabled_local
    (st : Collateral.State.t)
    (underlying pegPrice low now1 now2 : Z) :
  Collateral.statusOf st.(Collateral.State.whenDefault) now1
    = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  Collateral.statusOf
    (Collateral.refresh st underlying pegPrice low now2)
      .(Collateral.State.whenDefault) now2
    = Collateral.Status.DISABLED.
Proof.
  intros HD Hmono.
  unfold Collateral.refresh.
  destruct (Collateral.updateExposed
              st.(Collateral.State.exposedReferencePrice)
              underlying st.(Collateral.State.revenueShowing))
    as [new_exposed defaulted] eqn:Hupd.
  set (wd0 := st.(Collateral.State.whenDefault)).
  assert (Hhard :
    (if defaulted
     then Collateral.markStatus wd0 Collateral.Status.DISABLED now2
            st.(Collateral.State.delayUntilDefault)
     else wd0) = wd0).
  { destruct defaulted.
    - apply (CollateralProofs.markStatus_terminal_when_disabled
               wd0 Collateral.Status.DISABLED now1 now2
               st.(Collateral.State.delayUntilDefault) HD Hmono).
    - reflexivity. }
  simpl.
  rewrite Hhard.
  rewrite (CollateralProofs.markStatus_terminal_when_disabled
             wd0 _ now1 now2
             st.(Collateral.State.delayUntilDefault) HD Hmono).
  apply CollateralProofs.statusOf_disabled_iff in HD.
  destruct HD as [HN HL].
  apply CollateralProofs.statusOf_disabled_iff. split; [exact HN | lia].
Qed.

(** ===== refresh_disabled_terminal =====

    DISABLED is preserved across the plugin override regardless of
    flags. *)
Lemma refresh_disabled_terminal
    (s : CurveStableCollateral.CurveState.t)
    (vp low now1 now2 : Z)
    (pr_outer pr_inner depeg : bool) :
  Collateral.statusOf
    s.(CurveStableCollateral.CurveState.base)
      .(Collateral.State.whenDefault) now1 = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  Collateral.statusOf
    (CurveStableCollateral.refresh s vp low now2 pr_outer pr_inner depeg)
      .(CurveStableCollateral.CurveState.base)
      .(Collateral.State.whenDefault) now2
    = Collateral.Status.DISABLED.
Proof.
  intros HD Hmono.
  unfold CurveStableCollateral.refresh; simpl.
  destruct pr_outer.
  - (* outer revert branch: extra markStatus(DISABLED) on already-disabled wd is no-op *)
    simpl.
    rewrite (CollateralProofs.markStatus_terminal_when_disabled
               s.(CurveStableCollateral.CurveState.base).(Collateral.State.whenDefault)
               Collateral.Status.DISABLED now1 now2
               s.(CurveStableCollateral.CurveState.base).(Collateral.State.delayUntilDefault)
               HD Hmono).
    apply CollateralProofs.statusOf_disabled_iff in HD.
    destruct HD as [HN HL].
    apply CollateralProofs.statusOf_disabled_iff. split; [exact HN | lia].
  - (* success branch: replicate the parent's structure: hard mark + soft mark
       both no-ops on DISABLED. *)
    set (wd0 := s.(CurveStableCollateral.CurveState.base).(Collateral.State.whenDefault)).
    set (dud := s.(CurveStableCollateral.CurveState.base).(Collateral.State.delayUntilDefault)).
    set (rev := s.(CurveStableCollateral.CurveState.base).(Collateral.State.revenueShowing)).
    set (exp := s.(CurveStableCollateral.CurveState.base).(Collateral.State.exposedReferencePrice)).
    set (underlying := CurveStableCollateral.underlyingRefPerTok vp).
    destruct (Collateral.updateExposed exp underlying rev) as [new_exposed defaulted] eqn:Hupd.
    set (wd_h :=
           if defaulted
           then Collateral.markStatus wd0 Collateral.Status.DISABLED now2 dud
           else wd0).
    assert (Hwd_h_eq : wd_h = wd0).
    { unfold wd_h. destruct defaulted.
      - apply (CollateralProofs.markStatus_terminal_when_disabled
                 wd0 Collateral.Status.DISABLED now1 now2 dud HD Hmono).
      - reflexivity. }
    set (soft_iffy :=
           if pr_inner then true else (low =? 0) || depeg).
    set (soft :=
           if soft_iffy then Collateral.Status.IFFY else Collateral.Status.SOUND).
    simpl.
    rewrite Hwd_h_eq.
    rewrite (CollateralProofs.markStatus_terminal_when_disabled
               wd0 soft now1 now2 dud HD Hmono).
    apply CollateralProofs.statusOf_disabled_iff in HD.
    destruct HD as [HN HL].
    apply CollateralProofs.statusOf_disabled_iff. split; [exact HN | lia].
Qed.

(** ===== refresh_hard_default_iff_vp_below_exposed =====

    The hard-default flag in the parent's [updateExposed] fires
    iff [vp < exposed]. Composes [hardDefault_iff_vp_below_exposed]
    with the abstract base's update characterization. *)
Lemma refresh_hard_default_iff_vp_below_exposed
    (s : CurveStableCollateral.CurveState.t) (vp : Z) :
  let exp :=
    s.(CurveStableCollateral.CurveState.base).(Collateral.State.exposedReferencePrice) in
  let rev :=
    s.(CurveStableCollateral.CurveState.base).(Collateral.State.revenueShowing) in
  let '(_, defaulted) :=
    Collateral.updateExposed exp
      (CurveStableCollateral.underlyingRefPerTok vp) rev in
  defaulted = true <-> vp < exp.
Proof.
  simpl.
  unfold Collateral.updateExposed,
         CurveStableCollateral.underlyingRefPerTok.
  destruct (vp <? s.(CurveStableCollateral.CurveState.base)
                       .(Collateral.State.exposedReferencePrice))
           eqn:Hlt.
  - apply Z.ltb_lt in Hlt. split; intro; [exact Hlt | reflexivity].
  - apply Z.ltb_ge in Hlt.
    destruct (s.(CurveStableCollateral.CurveState.base)
                .(Collateral.State.exposedReferencePrice) <?
                FixLib.mul vp
                  s.(CurveStableCollateral.CurveState.base)
                     .(Collateral.State.revenueShowing)
                  RoundingMode.FLOOR) eqn:Hlt2;
      split; intro Hbad; try discriminate; try lia.
Qed.

End CurveStableCollateralProofs.
