(** Collateral validity preservation.

    Headline lemma: [refresh] preserves the [Collateral.Valid.t] invariant
    under the natural per-call preconditions that on-chain code derives
    from EVM type widths (now : uint48, underlying : uint192).

    Strategy mirrors the CAS state-machine corpus: every transition
    [markStatus] can take lands in [0, UINT48_MAX], and the new
    [exposedReferencePrice] from [updateExposed] stays in [0, FIX_MAX].
    [refresh] only mutates these two fields; the rest are passed through.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module CollateralValidity.

Import FixLib.
Import Collateral.

(** ===== markStatus stays in uint48 ===== *)
Lemma markStatus_uint48_bound
    (wd : Z) (s : Status.t) (now dud : Z) :
  0 <= wd <= UINT48_MAX ->
  0 <= now <= UINT48_MAX ->
  0 <= dud ->
  0 <= markStatus wd s now dud <= UINT48_MAX.
Proof.
  intros Hwd Hnow Hdud.
  unfold markStatus, NEVER, UINT48_MAX in *.
  destruct (wd <=? now) eqn:Hter.
  - exact Hwd.
  - destruct s.
    + (* SOUND -> NEVER *)
      lia.
    + (* IFFY *)
      destruct (2 ^ 48 - 1 <=? now + dud) eqn:Hsat.
      * lia.
      * apply Z.leb_gt in Hsat.
        destruct (now + dud <? wd) eqn:Hlt2.
        -- apply Z.ltb_lt in Hlt2. lia.
        -- exact Hwd.
    + (* DISABLED -> now *)
      exact Hnow.
Qed.

(** ===== updateExposed stays in uint192 ===== *)
Lemma updateExposed_uint192_bound
    (exposed underlying revenueShowing : Z) :
  0 <= exposed <= FIX_MAX ->
  0 <= underlying <= FIX_MAX ->
  0 <= revenueShowing <= FIX_ONE ->
  let '(new_exposed, _) :=
    updateExposed exposed underlying revenueShowing in
  0 <= new_exposed <= FIX_MAX.
Proof.
  intros Hexp Hund Hrev.
  unfold updateExposed.
  destruct (underlying <? exposed) eqn:Hlt1.
  - exact Hund.
  - destruct (exposed <? FixLib.mul underlying revenueShowing RoundingMode.FLOOR)
             eqn:Hlt2.
    + (* new_exposed = hidden = (underlying * revenueShowing) / FIX_SCALE *)
      apply Z.ltb_lt in Hlt2.
      unfold FixLib.mul, divrnd.
      split.
      * apply Z.div_pos.
        -- apply Z.mul_nonneg_nonneg; lia.
        -- unfold FIX_SCALE; lia.
      * (* (underlying * revenueShowing) / FIX_SCALE <= FIX_MAX
           since revenueShowing <= FIX_ONE = FIX_SCALE,
           underlying * revenueShowing <= underlying * FIX_SCALE,
           divided by FIX_SCALE => underlying <= FIX_MAX. *)
        apply Z.div_le_upper_bound; [unfold FIX_SCALE; lia|].
        assert (Hbnd : underlying * revenueShowing <= FIX_MAX * FIX_SCALE).
        { apply Z.le_trans with (m := FIX_MAX * revenueShowing).
          - apply Z.mul_le_mono_nonneg_r; lia.
          - apply Z.mul_le_mono_nonneg_l; [|unfold FIX_ONE in Hrev; lia].
            unfold FIX_MAX; lia. }
        lia.
    + exact Hexp.
Qed.

(** ===== Headline: refresh_preserves_validity =====

    Preconditions:
      - [now], [underlying] are within their EVM-type widths
        (uint48 and uint192 respectively). On-chain these come from
        block.timestamp and the underlying-collateral price oracle.
      - [pegPrice], [low] are unconstrained (only compared).
*)
Lemma refresh_preserves_validity :
  forall (s : State.t) (underlying pegPrice low now : Z),
    Valid.t s ->
    0 <= now <= UINT48_MAX ->
    0 <= underlying <= FIX_MAX ->
    Valid.t (refresh s underlying pegPrice low now).
Proof.
  intros s underlying pegPrice low now Hv Hnow Hund.
  destruct Hv as [Hwd Hexp Hdud Hrev].
  pose proof (updateExposed_uint192_bound
                s.(State.exposedReferencePrice)
                underlying s.(State.revenueShowing)
                Hexp Hund Hrev) as Hupd.
  unfold refresh.
  destruct (updateExposed s.(State.exposedReferencePrice)
                          underlying s.(State.revenueShowing))
    as [new_exposed defaulted] eqn:Hue.
  set (wd_after_hard :=
         if defaulted then
           markStatus s.(State.whenDefault) Status.DISABLED now
                      s.(State.delayUntilDefault)
         else s.(State.whenDefault)).
  assert (Hhard : 0 <= wd_after_hard <= UINT48_MAX).
  { unfold wd_after_hard. destruct defaulted.
    - apply markStatus_uint48_bound; [exact Hwd|exact Hnow|lia].
    - exact Hwd. }
  assert (Hsoft :
            0 <= markStatus wd_after_hard
                   (softDefaultStatus pegPrice low
                      s.(State.pegBottom) s.(State.pegTop))
                   now s.(State.delayUntilDefault)
              <= UINT48_MAX).
  { apply markStatus_uint48_bound; [exact Hhard|exact Hnow|lia]. }
  constructor; simpl.
  - exact Hsoft.
  - exact Hupd.
  - exact Hdud.
  - exact Hrev.
Qed.

End CollateralValidity.
