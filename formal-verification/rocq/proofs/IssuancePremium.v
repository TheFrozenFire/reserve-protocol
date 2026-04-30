(** IssuancePremium invariant proofs.

    Proves the load-bearing safety invariants on the [IssuancePremium]
    simulation defined in [Reserve.simulations.IssuancePremium]:

      premium_at_zero:
        At [pegPrice = 0] (the "no peg-price reported" sentinel) the
        premium is [FIX_ONE], NOT [FIX_MAX]. This is the deliberate
        fall-back wired in by PR #1175 to keep a collateral that
        doesn't expose [savedPegPrice] from bricking issuance.

      premium_monotone:
        The premium curve is non-increasing in [pegPrice] across the
        active branch (and trivially monotone in the fall-back arms).
        Equivalently, the premium is a non-decreasing function of
        [uncertainty := targetPerRef - pegPrice].

      premium_bounded:
        The premium is bounded above by [FIX_MAX]. This combined with
        [premium_at_zero / >= FIX_ONE] gives the full envelope.

    These mirror the CAS witness corpus in
      cas/issuance_premium/premium_curve.gp  (INV-P1..P6)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.

Module IssuancePremiumProofs.

Import FixLib.
Import IssuancePremium.

(** ===== premium_at_zero: pegPrice = 0 returns FIX_ONE. =====
    INV-P4b in the CAS script. *)
Lemma premium_at_zero
    (enable lastSaveIsNow : bool) (targetPerRef : Z) :
  issuancePremium enable lastSaveIsNow 0 targetPerRef = FIX_ONE.
Proof.
  unfold issuancePremium.
  destruct enable; [|reflexivity].
  destruct lastSaveIsNow; [|reflexivity].
  simpl. reflexivity.
Qed.

(** Companion: when feature flag is off, premium is FIX_ONE. *)
Lemma premium_disabled
    (lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  issuancePremium false lastSaveIsNow pegPrice targetPerRef = FIX_ONE.
Proof. reflexivity. Qed.

(** Companion: stale lastSave -> FIX_ONE. *)
Lemma premium_stale
    (enable : bool) (pegPrice targetPerRef : Z) :
  issuancePremium enable false pegPrice targetPerRef = FIX_ONE.
Proof.
  unfold issuancePremium. destruct enable; reflexivity.
Qed.

(** ===== premium_at_peg: pegPrice = targetPerRef -> FIX_ONE.
    INV-P2 in the CAS script. The strict-equality boundary of the
    [pegPrice >= targetPerRef] guard. *)
Lemma premium_at_peg
    (enable lastSaveIsNow : bool) (targetPerRef : Z) :
  0 < targetPerRef ->
  issuancePremium enable lastSaveIsNow targetPerRef targetPerRef = FIX_ONE.
Proof.
  intros Hpos. unfold issuancePremium.
  destruct enable; [|reflexivity].
  destruct lastSaveIsNow; [|reflexivity].
  assert (Hne : (targetPerRef =? 0) = false)
    by (apply Z.eqb_neq; lia).
  rewrite Hne.
  assert (Hge : (targetPerRef <=? targetPerRef) = true)
    by (apply Z.leb_le; lia).
  rewrite Hge. reflexivity.
Qed.

(** ===== Helper: divrnd is monotone non-increasing in the divisor
    (when numerator non-negative and divisors are positive), under CEIL. =====

    Proof: ceil(n/d) is the unique integer q such that q*d >= n and (q-1)*d < n
    (for n > 0). We prove [divrnd n d2 CEIL <= divrnd n d1 CEIL] using
    [Z.div_le_lower_bound] together with the floor->multiplication bound. *)
Lemma divrnd_ceil_monotone_in_divisor
    (n d1 d2 : Z) :
  0 <= n ->
  0 < d1 ->
  d1 <= d2 ->
  divrnd n d2 RoundingMode.CEIL <= divrnd n d1 RoundingMode.CEIL.
Proof.
  intros Hn Hd1 Hd12.
  unfold divrnd.
  set (q1 := n / d1).
  set (r1 := n mod d1).
  set (q2 := n / d2).
  set (r2 := n mod d2).
  pose proof (Z.div_mod n d1 ltac:(lia)) as Hd1eq.
  pose proof (Z.div_mod n d2 ltac:(lia)) as Hd2eq.
  pose proof (Z.mod_pos_bound n d1 Hd1) as [Hr1lb Hr1ub].
  assert (Hd2pos : 0 < d2) by lia.
  pose proof (Z.mod_pos_bound n d2 Hd2pos) as [Hr2lb Hr2ub].
  fold q1 r1 in Hd1eq, Hr1lb, Hr1ub.
  fold q2 r2 in Hd2eq, Hr2lb, Hr2ub.
  (* Both q1, q2 are non-negative. *)
  assert (Hq1nn : 0 <= q1) by (unfold q1; apply Z.div_pos; lia).
  assert (Hq2nn : 0 <= q2) by (unfold q2; apply Z.div_pos; lia).
  (* Claim: q2 * d1 <= n (for r2 = 0) and (q2 + 1) * d1 <= n + d1 (for r2 != 0). *)
  destruct (r1 =? 0) eqn:H1; destruct (r2 =? 0) eqn:H2;
    [ apply Z.eqb_eq in H1; apply Z.eqb_eq in H2
    | apply Z.eqb_eq in H1; apply Z.eqb_neq in H2
    | apply Z.eqb_neq in H1; apply Z.eqb_eq in H2
    | apply Z.eqb_neq in H1; apply Z.eqb_neq in H2 ].
  - (* r1 = 0, r2 = 0: ceil = q on both. q2 <= q1 since n = q1*d1 = q2*d2,
       and d1 <= d2 with both >= 1 forces q1 >= q2. *)
    nia.
  - (* r1 = 0, r2 != 0: need q2 + 1 <= q1.
       n = q1*d1 = q2*d2 + r2 with 0 < r2 < d2.
       So (q2+1)*d2 > n = q1*d1, hence (q2+1)*d2 > q1*d1.
       But d2 >= d1, so (q2+1)*d1 <= (q2+1)*d2; that's the wrong direction.
       Use: (q2+1)*d1 <= q1*d1 + d1 - r2*(d1/d2) ... too messy.
       Instead: q2 = (q2*d2 + r2) / d2 and we need q2 + 1 <= n/d1 = q1.
       Since r1 = 0, n/d1 is exact. n = q2*d2 + r2 >= q2*d2 + 1.
       Want: q1 >= q2 + 1, i.e., n >= (q2+1)*d1.
       n = q2*d2 + r2 >= q2*d1 + 1. Want: q2*d1 + 1 >= (q2+1)*d1,
       i.e., 1 >= d1. So only if d1 = 1. Not true in general.
       So we need: n >= (q2+1)*d1. We have n = q2*d2 + r2 with 0 < r2 < d2.
       n >= q2*d1 + 1 (since d2 >= d1, r2 >= 1).
       We need n >= q2*d1 + d1, equivalently n - q2*d1 >= d1.
       n - q2*d1 = q2*(d2-d1) + r2. Since q2 might be 0 and r2 < d2,
       this might be < d1 when d2 - d1 small.
       Actually let's reason directly: n is divisible by d1 (r1 = 0), so
       n is a multiple of d1: n = k*d1 for some k = q1 >= 0.
       n = q2*d2 + r2 with 0 < r2 < d2.
       Hence k*d1 = q2*d2 + r2, so k*d1 - q2*d2 = r2 > 0, k*d1 > q2*d2 >= q2*d1.
       So k > q2, hence k >= q2 + 1, i.e., q1 >= q2 + 1. *)
    nia.
  - (* r1 != 0, r2 = 0: need q2 <= q1 + 1, equivalently q2 <= q1 (we have it).
       n = q1*d1 + r1 = q2*d2.
       Want q2 <= q1 + 1. Stronger: q2 <= q1.
       q2*d2 = q1*d1 + r1 < q1*d1 + d1 = (q1+1)*d1 <= (q1+1)*d2.
       So q2*d2 < (q1+1)*d2 ⟹ q2 < q1 + 1 ⟹ q2 <= q1. So q2 <= q1 <= q1 + 1. *)
    nia.
  - (* r1 != 0, r2 != 0: want q2 + 1 <= q1 + 1, i.e., q2 <= q1.
       n = q1*d1 + r1 = q2*d2 + r2, with 0 < r1 < d1, 0 < r2 < d2.
       q2*d2 + r2 = q1*d1 + r1.
       Suppose q2 > q1, i.e., q2 >= q1 + 1.
       q2*d2 >= (q1+1)*d2 >= (q1+1)*d1 = q1*d1 + d1 > q1*d1 + r1 = n.
       So q2*d2 > n, but q2*d2 + r2 = n with r2 > 0, contradiction
       (we'd have q2*d2 < n). So q2 <= q1. *)
    nia.
Qed.

(** ===== safeDiv_ceil monotone non-increasing in divisor (premium curve). =====

    For [a > 0], [a <= FIX_MAX], [a < FIX_MAX]: as the divisor [b]
    grows, the result drops or saturates the same way. *)
Lemma safeDiv_ceil_monotone_in_divisor
    (a b1 b2 : Z) :
  0 < a ->
  a < FIX_MAX ->
  0 < b1 ->
  b1 <= b2 ->
  safeDiv_ceil a b2 <= safeDiv_ceil a b1.
Proof.
  intros Hap Halt Hb1 Hb12.
  unfold safeDiv_ceil.
  assert (Hane0 : (a =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hane0.
  assert (HaneM : (a =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  rewrite HaneM.
  assert (Hb1ne : (b1 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hb1ne.
  assert (Hb2ne : (b2 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hb2ne.
  set (raw1 := FixLib.div a b1 RoundingMode.CEIL).
  set (raw2 := FixLib.div a b2 RoundingMode.CEIL).
  assert (Hmono : raw2 <= raw1).
  { unfold raw1, raw2, FixLib.div.
    apply divrnd_ceil_monotone_in_divisor;
      [ apply Z.mul_nonneg_nonneg; [lia | unfold FIX_SCALE; lia]
      | lia | lia ]. }
  destruct (FIX_MAX <=? raw1) eqn:H1; destruct (FIX_MAX <=? raw2) eqn:H2.
  - lia.
  - apply Z.leb_le in H1. apply Z.leb_gt in H2. lia.
  - apply Z.leb_gt in H1. apply Z.leb_le in H2. lia.
  - apply Z.leb_gt in H1. apply Z.leb_gt in H2. lia.
Qed.

(** ===== premium_monotone: issuancePremium is non-increasing in
    pegPrice over the active branch. =====

    Concretely: if [0 < pegPrice1 <= pegPrice2 < targetPerRef] and
    [0 < targetPerRef < FIX_MAX], then
    [issuancePremium pegPrice2 <= issuancePremium pegPrice1]. *)
Lemma premium_monotone_in_pegPrice
    (targetPerRef pegPrice1 pegPrice2 : Z) :
  0 < targetPerRef < FIX_MAX ->
  0 < pegPrice1 ->
  pegPrice1 <= pegPrice2 ->
  pegPrice2 < targetPerRef ->
  issuancePremium true true pegPrice2 targetPerRef
  <= issuancePremium true true pegPrice1 targetPerRef.
Proof.
  intros [HtPos HtMax] Hp1Pos Hp12 Hp2T.
  unfold issuancePremium.
  assert (Hp1ne : (pegPrice1 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hp1ne.
  assert (Hp2ne : (pegPrice2 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hp2ne.
  assert (Ht1 : (targetPerRef <=? pegPrice1) = false)
    by (apply Z.leb_gt; lia).
  rewrite Ht1.
  assert (Ht2 : (targetPerRef <=? pegPrice2) = false)
    by (apply Z.leb_gt; lia).
  rewrite Ht2.
  apply safeDiv_ceil_monotone_in_divisor; lia.
Qed.

(** ===== premium_bounded: issuancePremium is bounded above by FIX_MAX. =====
    This is the saturation property — INV-P4 in the CAS script. *)
Lemma premium_bounded
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 <= targetPerRef <= FIX_MAX ->
  0 <= pegPrice <= FIX_MAX ->
  issuancePremium enable lastSaveIsNow pegPrice targetPerRef <= FIX_MAX.
Proof.
  intros [_ HtMax] _.
  assert (Hone_le_max : FIX_ONE <= FIX_MAX) by (vm_compute; discriminate).
  assert (Hzero_le_max : 0 <= FIX_MAX) by (vm_compute; discriminate).
  unfold issuancePremium.
  destruct enable; cbn [negb].
  2: { exact Hone_le_max. }
  destruct lastSaveIsNow; cbn [negb].
  2: { exact Hone_le_max. }
  destruct (pegPrice =? 0).
  - exact Hone_le_max.
  - destruct (targetPerRef <=? pegPrice).
    + exact Hone_le_max.
    + unfold safeDiv_ceil.
      destruct (targetPerRef =? 0).
      * exact Hzero_le_max.
      * destruct (targetPerRef =? FIX_MAX).
        -- apply Z.le_refl.
        -- destruct (pegPrice =? 0).
           ++ apply Z.le_refl.
           ++ destruct (FIX_MAX <=?
                          FixLib.div targetPerRef pegPrice
                                     RoundingMode.CEIL) eqn:Hsat.
              ** apply Z.le_refl.
              ** apply Z.leb_gt in Hsat. lia.
Qed.

(** ===== premium_at_least_one: under the active branch, premium >= FIX_ONE.
    INV-P1 in the CAS script. =====

    The CEIL divide of [targetPerRef * FIX_ONE] by [pegPrice] with
    [pegPrice < targetPerRef] yields strictly more than [FIX_ONE]. *)
Lemma premium_at_least_one
    (enable lastSaveIsNow : bool) (pegPrice targetPerRef : Z) :
  0 < targetPerRef ->
  0 <= pegPrice ->
  FIX_ONE <= issuancePremium enable lastSaveIsNow pegPrice targetPerRef.
Proof.
  intros HtPos HpNN.
  assert (Hone_le_max : FIX_ONE <= FIX_MAX) by (vm_compute; discriminate).
  unfold issuancePremium.
  destruct enable; cbn [negb].
  2: { apply Z.le_refl. }
  destruct lastSaveIsNow; cbn [negb].
  2: { apply Z.le_refl. }
  destruct (pegPrice =? 0) eqn:Hp0.
  - apply Z.le_refl.
  - apply Z.eqb_neq in Hp0.
    destruct (targetPerRef <=? pegPrice) eqn:Htp.
    + apply Z.le_refl.
    + apply Z.leb_gt in Htp.
      unfold safeDiv_ceil.
      assert (Htne : (targetPerRef =? 0) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Htne.
      destruct (targetPerRef =? FIX_MAX) eqn:HtM.
      * exact Hone_le_max.
      * assert (Hpne : (pegPrice =? 0) = false)
          by (apply Z.eqb_neq; exact Hp0).
        rewrite Hpne.
        destruct (FIX_MAX <=?
                    FixLib.div targetPerRef pegPrice
                               RoundingMode.CEIL) eqn:Hsat.
        -- exact Hone_le_max.
        -- apply Z.leb_gt in Hsat.
           (* div a b CEIL = (a*FIX_SCALE) / b rounded up.
              With a > b > 0 we have a*FIX_SCALE / b > FIX_SCALE = FIX_ONE.
              Show: FIX_ONE <= div a b CEIL. *)
           unfold FixLib.div, divrnd.
           set (q := targetPerRef * FIX_SCALE / pegPrice).
           set (r := targetPerRef * FIX_SCALE mod pegPrice).
           assert (Hbound : FIX_SCALE <= q).
           { unfold q.
             apply Z.div_le_lower_bound; [lia|].
             assert (FIX_SCALE * pegPrice <= targetPerRef * FIX_SCALE).
             { rewrite (Z.mul_comm FIX_SCALE pegPrice).
               apply Z.mul_le_mono_nonneg_r;
               [unfold FIX_SCALE; lia | lia]. }
             lia. }
           destruct (r =? 0); unfold FIX_ONE; lia.
Qed.

End IssuancePremiumProofs.
