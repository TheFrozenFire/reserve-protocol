(** CTokenFiatCollateral plugin invariants.

    Mirrors [proofs/Collateral.v] for the CToken plugin overrides
    defined in [Reserve.simulations.CTokenFiatCollateral].

    Headline lemmas:

      refPerTok_of_rate_monotone:
        Plugin's [refPerTok_of_rate] is monotone in the rate input.
        For any [refDecimals >= 1], a non-decreasing exchange rate
        produces a non-decreasing ref-per-tok. Composes with the
        abstract base's [updateExposed] to give exposed-monotonicity
        under monotone accrual.

      refresh_accrual_revert_disables:
        If [accrued = false] (i.e. [exchangeRateCurrent()] reverted),
        the plugin [refresh] writes a post-state with
        [statusOf whenDefault now = DISABLED]. The plugin-specific
        revert path always disables — pinning CT-7 of the CAS witness.

      refresh_disabled_terminal:
        DISABLED is preserved across the plugin override regardless
        of [accrued] flag and rate input. Composes
        [Collateral.disabled_is_terminal] with the plugin's extra
        markStatus(DISABLED) on the [accrued = false] branch.

    Mirrors the CAS witness corpus in
      cas/collateral/ctoken_refresh.gp        (CT-1..CT-8) *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CTokenFiatCollateral.
Require Import Reserve.proofs.Collateral.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Module CTokenFiatCollateralProofs.

Import FixLib.
Import Collateral.
Import CTokenFiatCollateral.

(** ===== refPerTok monotone in rate =====

    For any [refDecimals >= 1], if [rate1 <= rate2], then
    [refPerTok_of_rate rate1 refDecimals <= refPerTok_of_rate rate2 refDecimals].

    Branches:
      - [refDecimals <= 8]: multiplication by a non-negative constant.
      - [refDecimals  > 8]: floor-division by a positive constant; the
        quotient is monotone in the dividend over Z.

    Both branches are monotone, both transitively from [rate1 <= rate2]. *)
Lemma refPerTok_of_rate_monotone
    (rate1 rate2 refDec : Z) :
  1 <= refDec ->
  0 <= rate1 ->
  rate1 <= rate2 ->
  refPerTok_of_rate rate1 refDec <= refPerTok_of_rate rate2 refDec.
Proof.
  intros Hpos Hr1 Hle.
  unfold refPerTok_of_rate.
  destruct (refDec <=? 8) eqn:Hbranch.
  - (* multiplication branch *)
    apply Z.leb_le in Hbranch.
    apply Z.mul_le_mono_nonneg_r.
    + apply Z.pow_nonneg. lia.
    + exact Hle.
  - (* division branch *)
    apply Z.leb_gt in Hbranch.
    apply Z.div_le_mono.
    + apply Z.pow_pos_nonneg; lia.
    + exact Hle.
Qed.

(** Corollary: [underlyingRefPerTok] is monotone in [rate] for any
    [Valid] CToken state. *)
Lemma underlyingRefPerTok_monotone_in_rate
    (s : CTokenState.t) (rate1 rate2 : Z) :
  Valid.t s ->
  0 <= rate1 ->
  rate1 <= rate2 ->
  underlyingRefPerTok s rate1 <= underlyingRefPerTok s rate2.
Proof.
  intros Hv Hr1 Hle.
  unfold underlyingRefPerTok.
  destruct Hv as [_ Hpos _ _].
  apply refPerTok_of_rate_monotone; auto.
Qed.

(** ===== Local helper: refresh of a disabled state stays disabled =====

    Mirrors [proofs/Collateral_chain.refresh_preserves_disabled] but
    inlined here to avoid an extra dependency. *)
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

(** ===== refresh accrual revert disables =====

    If [accrued = false], the plugin [refresh] writes a post-state
    with [statusOf whenDefault now = DISABLED]. The natural
    [now < NEVER] precondition rules out the boundary at exactly
    [now = NEVER = UINT48_MAX]; on chain block.timestamp would saturate
    long before approaching this. *)
Lemma refresh_accrual_revert_disables
    (s : CTokenState.t)
    (rate pegPrice low now : Z) :
  0 <= now ->
  now < Collateral.NEVER ->
  let s' := refresh s rate pegPrice low now false in
  Collateral.statusOf
    (s'.(CTokenState.base)).(Collateral.State.whenDefault) now
    = Collateral.Status.DISABLED.
Proof.
  intros Hnow_nn Hnow_lt.
  simpl.
  unfold refresh; simpl.
  set (base_after :=
         Collateral.refresh s.(CTokenState.base)
           (refPerTok_of_rate rate s.(CTokenState.refDecimals))
           pegPrice low now).
  unfold Collateral.markStatus.
  destruct (base_after.(Collateral.State.whenDefault) <=? now) eqn:Hter.
  - (* Already DISABLED before the extra mark: status holds directly. *)
    apply Z.leb_le in Hter.
    apply CollateralProofs.statusOf_disabled_iff. split.
    + intro Hcontra. unfold Collateral.NEVER in *. lia.
    + lia.
  - (* Not yet disabled: extra DISABLED mark writes wd' = now. *)
    apply Z.leb_gt in Hter.
    apply CollateralProofs.statusOf_disabled_iff. split.
    + intro Hcontra. unfold Collateral.NEVER in *. lia.
    + lia.
Qed.

(** ===== refresh disabled terminal =====

    DISABLED is preserved across the plugin override regardless of
    [accrued] flag and rate input. Both branches preserve the parent's
    DISABLED preservation; the [accrued = false] branch additionally
    applies a markStatus(DISABLED) which is a no-op when wd is already
    DISABLED. *)
Lemma refresh_disabled_terminal
    (s : CTokenState.t)
    (rate pegPrice low now1 now2 : Z)
    (accrued : bool) :
  Collateral.statusOf
    s.(CTokenState.base).(Collateral.State.whenDefault) now1 = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  Collateral.statusOf
    (refresh s rate pegPrice low now2 accrued).(CTokenState.base).(Collateral.State.whenDefault)
    now2
    = Collateral.Status.DISABLED.
Proof.
  intros HD Hmono.
  unfold refresh; simpl.
  set (underlying := refPerTok_of_rate rate s.(CTokenState.refDecimals)).
  set (base_after := Collateral.refresh s.(CTokenState.base) underlying pegPrice low now2).
  assert (Hbase_dis :
            Collateral.statusOf base_after.(Collateral.State.whenDefault) now2 = Collateral.Status.DISABLED).
  { unfold base_after.
    apply (refresh_preserves_disabled_local
             s.(CTokenState.base) underlying pegPrice low now1 now2 HD Hmono). }
  destruct accrued; simpl.
  - exact Hbase_dis.
  - rewrite (CollateralProofs.markStatus_terminal_when_disabled
               base_after.(Collateral.State.whenDefault) Collateral.Status.DISABLED now2 now2
               base_after.(Collateral.State.delayUntilDefault) Hbase_dis (Z.le_refl _)).
    exact Hbase_dis.
Qed.

(** ===== Hard default characterisation =====

    [updateExposed] hard-defaults iff [underlying < exposed]. For the
    CToken plugin, [underlying = refPerTok_of_rate rate refDecimals],
    so a hard-default trigger is equivalent to a sufficiently large
    rate decrease. *)
Lemma refresh_hard_default_iff_rate_drops_below_exposed
    (s : CTokenState.t)
    (rate pegPrice low now : Z) :
  let underlying := refPerTok_of_rate rate s.(CTokenState.refDecimals) in
  let '(_, defaulted) :=
    Collateral.updateExposed
      s.(CTokenState.base).(Collateral.State.exposedReferencePrice)
      underlying s.(CTokenState.base).(Collateral.State.revenueShowing) in
  defaulted = (underlying <? s.(CTokenState.base).(Collateral.State.exposedReferencePrice))%Z.
Proof.
  simpl.
  unfold Collateral.updateExposed.
  destruct (refPerTok_of_rate rate s.(CTokenState.refDecimals)
              <? s.(CTokenState.base).(Collateral.State.exposedReferencePrice)) eqn:Hlt.
  - reflexivity.
  - destruct (s.(CTokenState.base).(Collateral.State.exposedReferencePrice) <?
                FixLib.mul (refPerTok_of_rate rate s.(CTokenState.refDecimals))
                           s.(CTokenState.base).(Collateral.State.revenueShowing)
                           RoundingMode.FLOOR) eqn:Hlt2.
    + reflexivity.
    + reflexivity.
Qed.

End CTokenFiatCollateralProofs.
