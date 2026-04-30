(** CurveStableCollateral validity preservation.

    Headline lemma: the plugin's [refresh] preserves
    [CurveStableCollateral.Valid.t] under the natural per-call
    preconditions:
      - [virtualPrice] fits in uint192 (the production [_safeWrap]
        revert path inside [underlyingRefPerTok]).
      - [now] is uint48.

    Both [refresh] branches are validity-preserving:
      - The outer-revert branch: only mutates [whenDefault] via
        [markStatus(DISABLED, now)]; preserved by
        [markStatus_uint48_bound]. All other base fields and the
        plugin-extension fields ([virtualPriceLast], [poolNTokens],
        [pegBottom > 0]) are unchanged.
      - The success branch: composes the abstract base's
        [updateExposed] (uint192-bound preservation) with two
        [markStatus] calls; mirrors the structure of
        [Collateral.refresh_preserves_validity]. The [virtualPriceLast]
        update is bounded by the call hypothesis on [virtualPrice]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CurveStableCollateral.
Require Import Reserve.proofs.Collateral.
Require Import Reserve.proofs.Collateral_validity.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Module CurveStableCollateralValidity.

Import FixLib.

(** Helper: the success-branch composition matches
    [Collateral.refresh] up to the soft-default branch's [Status]
    expression. We re-derive the joint uint48 / uint192 bounds
    directly. *)

Lemma refresh_preserves_validity :
  forall (s : CurveStableCollateral.CurveState.t)
         (vp low now : Z)
         (pr_outer pr_inner depeg : bool),
    CurveStableCollateral.Valid.t s ->
    0 <= now <= Collateral.UINT48_MAX ->
    0 <= vp <= FIX_MAX ->
    CurveStableCollateral.Valid.t
      (CurveStableCollateral.refresh s vp low now pr_outer pr_inner depeg).
Proof.
  intros s vp low now pr_outer pr_inner depeg Hv Hnow Hvp.
  destruct Hv as [Hbase HvpLast HnTokens_min HnTokens_max HpegB_pos].
  destruct Hbase as [Hwd Hexp Hdud Hrev].
  destruct Hdud as [Hdud_nn Hdud_lim].
  pose proof Hrev as Hrev_split. destruct Hrev_split as [Hrev_nn Hrev_lim].
  pose proof Hvp as Hvp_split. destruct Hvp_split as [Hvp_nn Hvp_lim].
  pose proof
       (CollateralValidity.updateExposed_uint192_bound
          s.(CurveStableCollateral.CurveState.base)
            .(Collateral.State.exposedReferencePrice)
          (CurveStableCollateral.underlyingRefPerTok vp)
          s.(CurveStableCollateral.CurveState.base)
            .(Collateral.State.revenueShowing)
          Hexp Hvp Hrev) as Hupd_bound.
  unfold CurveStableCollateral.refresh.
  destruct pr_outer.
  - (* outer-revert branch *)
    constructor; simpl.
    + (* base Valid.t after the markStatus(DISABLED) *)
      constructor; simpl.
      * apply CollateralValidity.markStatus_uint48_bound; auto.
      * exact Hexp.
      * split; [exact Hdud_nn | exact Hdud_lim].
      * exact Hrev.
    + exact HvpLast.
    + exact HnTokens_min.
    + exact HnTokens_max.
    + exact HpegB_pos.
  - (* success branch: replicate Collateral.refresh shape inline *)
    set (exp :=
           s.(CurveStableCollateral.CurveState.base)
             .(Collateral.State.exposedReferencePrice)).
    set (rev :=
           s.(CurveStableCollateral.CurveState.base)
             .(Collateral.State.revenueShowing)).
    set (underlying := CurveStableCollateral.underlyingRefPerTok vp).
    destruct (Collateral.updateExposed exp underlying rev)
      as [new_exposed defaulted] eqn:Hupd.
    (* The bound is on [fst] of the updateExposed pair. *)
    assert (Hexp_bnd : 0 <= new_exposed <= FIX_MAX).
    { (* Re-derive directly since Hupd_bound is hidden behind the
         original [let '(_, _) := ...]. *)
      unfold Collateral.updateExposed in Hupd.
      destruct (underlying <? exp) eqn:Hlt1.
      - injection Hupd as Hexp_eq Hdef_eq. subst new_exposed. exact Hvp.
      - apply Z.ltb_ge in Hlt1.
        destruct (exp <? FixLib.mul underlying rev RoundingMode.FLOOR)
                 eqn:Hlt2.
        + injection Hupd as Hexp_eq Hdef_eq. subst new_exposed.
          apply Z.ltb_lt in Hlt2.
          unfold FixLib.mul, FixLib.divrnd. split.
          * apply Z.div_pos.
            -- apply Z.mul_nonneg_nonneg; [unfold underlying,
                 CurveStableCollateral.underlyingRefPerTok; lia | exact Hrev_nn].
            -- unfold FIX_SCALE; lia.
          * apply Z.div_le_upper_bound; [unfold FIX_SCALE; lia |].
            assert (Hund_le : underlying <= FIX_MAX).
            { unfold underlying, CurveStableCollateral.underlyingRefPerTok.
              exact Hvp_lim. }
            assert (Hbnd : underlying * rev <= FIX_MAX * FIX_SCALE).
            { apply Z.le_trans with (m := FIX_MAX * rev).
              - apply Z.mul_le_mono_nonneg_r; [exact Hrev_nn | exact Hund_le].
              - apply Z.mul_le_mono_nonneg_l; [unfold FIX_MAX; lia |].
                unfold FIX_ONE in Hrev_lim. lia. }
            lia.
        + injection Hupd as Hexp_eq Hdef_eq. subst new_exposed. exact Hexp. }
    set (wd_after_hard :=
           if defaulted
           then Collateral.markStatus
                  s.(CurveStableCollateral.CurveState.base)
                    .(Collateral.State.whenDefault)
                  Collateral.Status.DISABLED now
                  s.(CurveStableCollateral.CurveState.base)
                    .(Collateral.State.delayUntilDefault)
           else s.(CurveStableCollateral.CurveState.base)
                  .(Collateral.State.whenDefault)).
    assert (Hhard : 0 <= wd_after_hard <= Collateral.UINT48_MAX).
    { unfold wd_after_hard. destruct defaulted.
      - apply CollateralValidity.markStatus_uint48_bound; auto.
      - exact Hwd. }
    set (soft_iffy :=
           if pr_inner then true else (low =? 0) || depeg).
    set (soft :=
           if soft_iffy then Collateral.Status.IFFY
           else Collateral.Status.SOUND).
    assert (Hsoft :
              0 <= Collateral.markStatus wd_after_hard soft now
                     s.(CurveStableCollateral.CurveState.base)
                       .(Collateral.State.delayUntilDefault)
              <= Collateral.UINT48_MAX).
    { apply CollateralValidity.markStatus_uint48_bound; auto. }
    constructor; simpl.
    + constructor; simpl.
      * exact Hsoft.
      * exact Hexp_bnd.
      * split; [exact Hdud_nn | exact Hdud_lim].
      * exact Hrev.
    + exact Hvp.
    + exact HnTokens_min.
    + exact HnTokens_max.
    + exact HpegB_pos.
Qed.

End CurveStableCollateralValidity.
