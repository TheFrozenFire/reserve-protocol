(** CTokenFiatCollateral validity preservation.

    Headline lemma: the plugin's [refresh] preserves
    [CTokenFiatCollateral.Valid.t] under the natural per-call
    preconditions:
      - the underlying [refPerTok_of_rate rate refDecimals] fits in
        uint192 (FIX_MAX) — this is the production [_safeWrap] revert
        path inside [shiftl_toFix];
      - [now] is a uint48 (block.timestamp).

    The plugin's [refresh] composes the abstract base's [refresh]
    with an extra markStatus(DISABLED) on the [accrued = false]
    branch. Both layers are validity-preserving:
      - The base [refresh] is handled by
        [CollateralValidity.refresh_preserves_validity].
      - The extra markStatus(DISABLED) preserves the uint48 bound
        via [CollateralValidity.markStatus_uint48_bound].
    The plugin extension fields ([refDecimals], [rateSnapshot]) are
    immutable across [refresh] up to the [rateSnapshot := rate]
    write, which is bounded by the call-boundary hypothesis on
    [rate]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.simulations.CTokenFiatCollateral.
Require Import Reserve.proofs.Collateral.
Require Import Reserve.proofs.Collateral_validity.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Module CTokenFiatCollateralValidity.

Import FixLib.

(** ===== Plugin refresh preserves the plugin Valid.t =====

    The post-state's plugin extension fields:
      - [refDecimals] is unchanged.
      - [rateSnapshot] is overwritten with the new [rate]; its bound
        is the call-boundary [0 <= rate <= UINT256_MAX].
      - The base state is updated by [Collateral.refresh] composed
        (on the [accrued = false] branch) with a markStatus(DISABLED).

    Preconditions:
      - [Valid.t] of the input state.
      - [now] uint48.
      - [refPerTok_of_rate rate refDecimals] fits in uint192 — this
        is the production [_safeWrap] success precondition for
        [shiftl_toFix].
      - [rate] uint256.
*)
Lemma refresh_preserves_validity :
  forall (s : CTokenFiatCollateral.CTokenState.t)
         (rate pegPrice low now : Z) (accrued : bool),
    CTokenFiatCollateral.Valid.t s ->
    0 <= now <= Collateral.UINT48_MAX ->
    0 <= CTokenFiatCollateral.refPerTok_of_rate
           rate s.(CTokenFiatCollateral.CTokenState.refDecimals)
      <= FIX_MAX ->
    0 <= rate <= UINT256_MAX ->
    CTokenFiatCollateral.Valid.t
      (CTokenFiatCollateral.refresh s rate pegPrice low now accrued).
Proof.
  intros s rate pegPrice low now accrued Hv Hnow Hund Hrate.
  destruct Hv as [Hbase HrefP HrefL Hrate_old].
  set (underlying :=
         CTokenFiatCollateral.refPerTok_of_rate
           rate s.(CTokenFiatCollateral.CTokenState.refDecimals)).
  pose proof
       (CollateralValidity.refresh_preserves_validity
          s.(CTokenFiatCollateral.CTokenState.base)
          underlying pegPrice low now Hbase Hnow Hund) as Hbase'.
  unfold CTokenFiatCollateral.refresh.
  fold underlying.
  set (base_after :=
         Collateral.refresh
           s.(CTokenFiatCollateral.CTokenState.base)
           underlying pegPrice low now).
  set (base_final :=
         if accrued then base_after
         else
           {| Collateral.State.whenDefault :=
                Collateral.markStatus
                  base_after.(Collateral.State.whenDefault)
                  Collateral.Status.DISABLED now
                  base_after.(Collateral.State.delayUntilDefault);
              Collateral.State.exposedReferencePrice :=
                base_after.(Collateral.State.exposedReferencePrice);
              Collateral.State.delayUntilDefault :=
                base_after.(Collateral.State.delayUntilDefault);
              Collateral.State.revenueShowing :=
                base_after.(Collateral.State.revenueShowing);
              Collateral.State.pegBottom :=
                base_after.(Collateral.State.pegBottom);
              Collateral.State.pegTop :=
                base_after.(Collateral.State.pegTop); |}).
  assert (Hfinal : Collateral.Valid.t base_final).
  { destruct accrued; subst base_final.
    - exact Hbase'.
    - destruct Hbase' as [Hwd Hexp Hdud Hrev].
      destruct Hdud as [Hdud_nn Hdud_lim].
      constructor; simpl.
      + apply CollateralValidity.markStatus_uint48_bound.
        * exact Hwd.
        * exact Hnow.
        * exact Hdud_nn.
      + exact Hexp.
      + split; [exact Hdud_nn | exact Hdud_lim].
      + exact Hrev. }
  constructor; simpl.
  - exact Hfinal.
  - exact HrefP.
  - exact HrefL.
  - split; [apply Hrate | apply Hrate].
Qed.

End CTokenFiatCollateralValidity.
