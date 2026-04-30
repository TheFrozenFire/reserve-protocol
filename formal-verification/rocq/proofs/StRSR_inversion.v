(** StRSR inversion bridge — reconciling the simulation's exchange-rate
    formulation with the production contract's inverted [stakeRate].

    The simulation in [Reserve.simulations.StRSR] models the staking
    exchange rate as the ratio
        exchange_rate = (rsrBacking + rewardsAccumulated) / totalStRSR
                      = R / S       (rendered as a D18 fixed-point)
    using FLOOR rounding. The production contract [protocol/contracts/p1/
    StRSR.sol] instead tracks the inverted ratio
        stakeRate     = totalStakes / stakeRSR
                      = S / R       (also D18, but using CEIL rounding)
    because the inverted form lets [stakeRate] saturate to a hard cap on
    extreme seizure scenarios — the un-inverted exchange rate would
    instead shoot toward infinity.

    This file provides:

      INV-INV-DEF     stakeRate (Gallina-modeled production formula).
      INV-INV-GEN     stakeRate s = FIX_ONE  when totalStRSR = 0.
      INV-INV-ACT     stakeRate s = CEIL(S*FIX_ONE / R)  on the active branch.
      INV-INV-MONO    stakeRate is non-increasing across payoutRewards
                      (mirror of [exchange_rate_monotone_payoutRewards]).
      INV-INV-PROD    exchange_rate s * stakeRate s is bounded around
                      FIX_ONE^2 — the precise inversion-with-rounding gap.
      INV-INV-STAKE   the production [mintStakes] formula and the
                      simulation's [stake] formula agree on genesis.

    The inversion is exact in real arithmetic; the integer FLOOR/CEIL
    rounding directions introduce a strictly bounded gap, which we
    quantify rather than admit.

    All proofs are in [Z]; the uint256 / uint192 boundedness layer lives
    separately in [proofs/Fixed.v].

    The file deliberately keeps its dependency surface small (only the
    simulations) so that it composes alongside [proofs/StRSR.v] without
    importing the latter — that lets us state the inversion bridge
    without re-importing the entire [StRSRProofs] proof context. The
    handful of helper lemmas the bridge needs are reproved inline. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Module StRSRInversion.

Import FixLib.
Import StRSR.

(** ---------- Helper lemmas (re-proved inline, see [proofs/StRSR.v]
    for the canonical statements). ---------- *)

(** [exchange_rate] on the active branch unfolds to a FLOOR division. *)
Local Lemma exchange_rate_active_local (s : Storage.t) :
  s.(Storage.totalStRSR) <> 0 ->
  exchange_rate s =
    ((s.(Storage.totalRSRStaked) + s.(Storage.totalRewardsAccumulated))
       * FIX_ONE_Z) / s.(Storage.totalStRSR).
Proof.
  intros Hnz. unfold exchange_rate.
  destruct (s.(Storage.totalStRSR) =? 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

(** [payoutRewards] is the identity if no period elapsed. *)
Local Lemma payoutRewards_no_period_local
    (s : Storage.t) (now rewardsPool : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  payoutRewards s now rewardsPool = s.
Proof.
  intros Hlt. unfold payoutRewards.
  assert (Hb : (now <? s.(Storage.lastPayout) + 1) = true)
    by (apply Z.ltb_lt; exact Hlt).
  rewrite Hb. reflexivity.
Qed.

(** [payoutRewards] on the active branch — the explicit storage update. *)
Local Lemma payoutRewards_active_local
    (s : Storage.t) (now rewardsPool : U256.t) :
  s.(Storage.lastPayout) + 1 <= now ->
  payoutRewards s now rewardsPool = {|
    Storage.totalStRSR              := s.(Storage.totalStRSR);
    Storage.totalRSRStaked          := s.(Storage.totalRSRStaked);
    Storage.totalRewardsAccumulated :=
      s.(Storage.totalRewardsAccumulated) +
      FixLib.mulu_toUint
        (FixLib.minus FixLib.FIX_ONE
          (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
                       (now - s.(Storage.lastPayout))))
        rewardsPool RoundingMode.FLOOR;
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout) +
                                       (now - s.(Storage.lastPayout));
    Storage.queue                   := s.(Storage.queue);
    Storage.era                     := s.(Storage.era);
    Storage.draftEra                := s.(Storage.draftEra);
    Storage.draftRSR                := s.(Storage.draftRSR);
  |}.
Proof.
  intros Hle. unfold payoutRewards.
  assert (Hb : (now <? s.(Storage.lastPayout) + 1) = false)
    by (apply Z.ltb_ge; exact Hle).
  rewrite Hb. reflexivity.
Qed.

(** ---------- Inversion bridge ---------- *)

(** Convenience: the "production-equivalent stakeRSR" is [totalRSRStaked
    + totalRewardsAccumulated]. Production folds rewards directly into
    [stakeRSR] inside [_payoutRewards]; the simulation tracks them
    separately so the algebraic invariants are easier to state. *)
Definition stakeRSR_prod (s : Storage.t) : Z :=
  s.(Storage.totalRSRStaked) + s.(Storage.totalRewardsAccumulated).

(** ---------- INV-INV-DEF ----------

    [stakeRate] modeled exactly as production computes it (StRSR.sol
    line 643-645):

        stakeRate = (stakeRSR == 0 || totalStakes == 0)
                  ? FIX_ONE
                  : (totalStakes * FIX_ONE_256 + (stakeRSR - 1)) / stakeRSR

    The numerator-plus-(d-1) form is the standard CEIL idiom. *)
Definition stakeRate (s : Storage.t) : Z :=
  if (stakeRSR_prod s =? 0) || (s.(Storage.totalStRSR) =? 0) then
    FIX_ONE_Z
  else
    (s.(Storage.totalStRSR) * FIX_ONE_Z + (stakeRSR_prod s - 1))
      / stakeRSR_prod s.

(** ---------- INV-INV-GEN ----------

    On the genesis era ([totalStRSR = 0]), stakeRate is fixed at
    [FIX_ONE], matching production's [beginEra] reset and the simulation's
    [exchange_rate] convention.

    Symmetric: when [stakeRSR_prod = 0] (no RSR backing), stakeRate is
    also FIX_ONE — mirroring production's "untestable" branch. *)
Lemma stakeRate_genesis_totalStakes (s : Storage.t) :
  s.(Storage.totalStRSR) = 0 ->
  stakeRate s = FIX_ONE_Z.
Proof.
  intros H. unfold stakeRate.
  rewrite H. rewrite Z.eqb_refl.
  destruct (stakeRSR_prod s =? 0); reflexivity.
Qed.

Lemma stakeRate_genesis_stakeRSR (s : Storage.t) :
  stakeRSR_prod s = 0 ->
  stakeRate s = FIX_ONE_Z.
Proof.
  intros H. unfold stakeRate.
  rewrite H. rewrite Z.eqb_refl. reflexivity.
Qed.

(** ---------- INV-INV-ACT ----------

    On the non-degenerate branch (both [totalStRSR > 0] and
    [stakeRSR_prod > 0]), [stakeRate] is the CEIL division of
    [totalStRSR * FIX_ONE] by [stakeRSR_prod]. *)
Lemma stakeRate_active (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  stakeRate s =
    (s.(Storage.totalStRSR) * FIX_ONE_Z + (stakeRSR_prod s - 1))
      / stakeRSR_prod s.
Proof.
  intros HS HR. unfold stakeRate.
  assert (HSeq : (s.(Storage.totalStRSR) =? 0) = false)
    by (apply Z.eqb_neq; lia).
  assert (HReq : (stakeRSR_prod s =? 0) = false)
    by (apply Z.eqb_neq; lia).
  rewrite HSeq, HReq. reflexivity.
Qed.

(** [stakeRate] on the active branch matches FixLib's CEIL [divrnd]. *)
Lemma stakeRate_active_divrnd (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  stakeRate s =
    divrnd (s.(Storage.totalStRSR) * FIX_ONE_Z)
           (stakeRSR_prod s)
           RoundingMode.CEIL.
Proof.
  intros HS HR.
  rewrite stakeRate_active by assumption.
  unfold divrnd.
  set (n := s.(Storage.totalStRSR) * FIX_ONE_Z).
  set (d := stakeRSR_prod s).
  pose proof (Z.div_mod n d ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound n d HR) as [Hmlb Hmub].
  destruct (n mod d =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero.
    replace (n + (d - 1)) with ((n / d) * d + (d - 1)) by lia.
    rewrite Z.div_add_l by lia.
    rewrite (Z.div_small (d - 1) d) by lia.
    lia.
  - apply Z.eqb_neq in Hzero.
    set (q := n / d).
    set (r := n mod d).
    fold q r in Hdm, Hmlb, Hmub, Hzero.
    replace (n + (d - 1)) with (q * d + (r + d - 1)) by lia.
    rewrite Z.div_add_l by lia.
    assert (Hdiv : (r + d - 1) / d = 1).
    { symmetry. apply (Z.div_unique_pos (r + d - 1) d 1 (r - 1)); lia. }
    rewrite Hdiv. lia.
Qed.

(** ---------- INV-INV-PROD bounds (without products of bounds) ----------

    These four lemmas express each side's rounding gap. They are the
    building blocks for the multiplicative inversion bridge. *)

Lemma exchange_rate_floor_lower
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  exchange_rate s * s.(Storage.totalStRSR)
    > stakeRSR_prod s * FIX_ONE_Z - s.(Storage.totalStRSR).
Proof.
  intros HS.
  rewrite (exchange_rate_active_local s) by lia.
  set (n := stakeRSR_prod s * FIX_ONE_Z).
  unfold stakeRSR_prod in *.
  pose proof (Z.div_mod n s.(Storage.totalStRSR) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound n s.(Storage.totalStRSR) HS) as [Hmlb Hmub].
  unfold n in Hdm, Hmub. lia.
Qed.

Lemma exchange_rate_floor_upper
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  exchange_rate s * s.(Storage.totalStRSR) <= stakeRSR_prod s * FIX_ONE_Z.
Proof.
  intros HS.
  rewrite (exchange_rate_active_local s) by lia.
  unfold stakeRSR_prod.
  rewrite Z.mul_comm.
  apply Z.mul_div_le. lia.
Qed.

(** Helper: pure-arithmetic CEIL bound used by [stakeRate_ceil_lower]
    and [stakeRate_ceil_upper]. Stated abstractly so the [nia] call
    runs on a small term. *)
Lemma ceil_div_bounds (n d : Z) :
  0 <= n ->
  0 < d ->
  ((n + (d - 1)) / d) * d >= n /\
  ((n + (d - 1)) / d) * d < n + d.
Proof.
  intros Hn Hd.
  pose proof (Z.div_mod (n + (d - 1)) d ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (n + (d - 1)) d Hd) as [Hmlb Hmub].
  split; lia.
Qed.

Lemma stakeRate_ceil_lower
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  stakeRate s * stakeRSR_prod s >= s.(Storage.totalStRSR) * FIX_ONE_Z.
Proof.
  intros HS HR.
  rewrite (stakeRate_active s HS HR).
  set (n := s.(Storage.totalStRSR) * FIX_ONE_Z).
  set (d := stakeRSR_prod s).
  assert (Hnn : 0 <= n).
  { unfold n. apply Z.mul_nonneg_nonneg;
      [lia|unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia]. }
  destruct (ceil_div_bounds n d Hnn HR) as [Hge _].
  lia.
Qed.

Lemma stakeRate_ceil_upper
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  stakeRate s * stakeRSR_prod s < s.(Storage.totalStRSR) * FIX_ONE_Z + stakeRSR_prod s.
Proof.
  intros HS HR.
  rewrite (stakeRate_active s HS HR).
  set (n := s.(Storage.totalStRSR) * FIX_ONE_Z).
  set (d := stakeRSR_prod s).
  assert (Hnn : 0 <= n).
  { unfold n. apply Z.mul_nonneg_nonneg;
      [lia|unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia]. }
  destruct (ceil_div_bounds n d Hnn HR) as [_ Hlt].
  lia.
Qed.

(** Non-negativity of [stakeRate] on the active branch. *)
Lemma stakeRate_nonneg
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  0 <= stakeRate s.
Proof.
  intros HS HR.
  rewrite (stakeRate_active s HS HR).
  apply Z.div_pos; [|lia].
  apply Z.add_nonneg_nonneg.
  - apply Z.mul_nonneg_nonneg;
      [lia|unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia].
  - lia.
Qed.

(** Non-negativity of [exchange_rate] on the active branch. Requires
    [stakeRSR_prod >= 0], which holds for any valid storage. *)
Lemma exchange_rate_nonneg
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 <= stakeRSR_prod s ->
  0 <= exchange_rate s.
Proof.
  intros HS HR.
  rewrite (exchange_rate_active_local s) by lia.
  apply Z.div_pos; [|lia].
  apply Z.mul_nonneg_nonneg.
  - unfold stakeRSR_prod in HR. lia.
  - unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia.
Qed.

(** ---------- INV-INV-MONO ----------

    [stakeRate] is non-INCREASING across [payoutRewards], which is the
    mirror image of [exchange_rate_monotone_payoutRewards]. The
    payoutRewards step adds a non-negative payout into
    [totalRewardsAccumulated], which lifts [stakeRSR_prod]; CEIL
    division by a strictly larger divisor cannot increase the quotient.

    The structural lemma [stakeRate_div_le_compat_payout] separates the
    pure-arithmetic kernel from the storage-shape bookkeeping; the
    kernel is small enough that [nia] dispatches it without OOM. *)

(** Kernel: CEIL-division is non-increasing in the divisor for a fixed
    non-negative numerator. Stated in the [(numerator + d - 1) / d]
    idiom that matches production's stakeRate computation. *)
Lemma ceil_div_monotone_under_payout
    (S R payout : Z) :
  0 < S ->
  0 < R ->
  0 <= payout ->
  (S * FIX_ONE_Z + (R + payout - 1)) / (R + payout)
    <= (S * FIX_ONE_Z + (R - 1)) / R.
Proof.
  intros HS HR Hp.
  set (n := S * FIX_ONE_Z).
  assert (HFIX : 0 < FIX_ONE_Z) by (unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia).
  assert (Hnn : 0 < n) by (unfold n; nia).
  pose proof (Z.div_mod n R ltac:(lia)) as HdmR.
  pose proof (Z.mod_pos_bound n R HR) as [HmRlb HmRub].
  set (qR := n / R).
  set (rR := n mod R).
  fold qR rR in HdmR, HmRlb, HmRub.
  assert (HRpp : 0 < R + payout) by lia.
  pose proof (Z.div_mod n (R + payout) ltac:(lia)) as HdmP.
  pose proof (Z.mod_pos_bound n (R + payout) HRpp) as [HmPlb HmPub].
  set (qP := n / (R + payout)).
  set (rP := n mod (R + payout)).
  fold qP rP in HdmP, HmPlb, HmPub.
  (* Express both sides without divrnd by computing the CEIL closed
     form. We need to show:
       (n + R + payout - 1) / (R + payout) <= (n + R - 1) / R.
     Use [Z.div_unique_pos] to pin each side down. *)
  assert (HRHS : (n + (R - 1)) / R = qR + (if rR =? 0 then 0 else 1)).
  { destruct (rR =? 0) eqn:HrRz.
    - apply Z.eqb_eq in HrRz.
      replace (n + (R - 1)) with (qR * R + (R - 1)) by lia.
      rewrite Z.div_add_l by lia.
      rewrite (Z.div_small (R - 1) R) by lia. lia.
    - apply Z.eqb_neq in HrRz.
      replace (n + (R - 1)) with (qR * R + (rR + R - 1)) by lia.
      rewrite Z.div_add_l by lia.
      assert (Hdiv : (rR + R - 1) / R = 1).
      { symmetry. apply (Z.div_unique_pos (rR + R - 1) R 1 (rR - 1)); lia. }
      rewrite Hdiv. lia. }
  assert (HLHS : (n + (R + payout - 1)) / (R + payout)
                   = qP + (if rP =? 0 then 0 else 1)).
  { destruct (rP =? 0) eqn:HrPz.
    - apply Z.eqb_eq in HrPz.
      replace (n + (R + payout - 1)) with (qP * (R + payout) + (R + payout - 1)) by lia.
      rewrite Z.div_add_l by lia.
      rewrite (Z.div_small (R + payout - 1) (R + payout)) by lia. lia.
    - apply Z.eqb_neq in HrPz.
      replace (n + (R + payout - 1)) with (qP * (R + payout) + (rP + R + payout - 1)) by lia.
      rewrite Z.div_add_l by lia.
      assert (Hdiv : (rP + R + payout - 1) / (R + payout) = 1).
      { symmetry. apply (Z.div_unique_pos (rP + R + payout - 1) (R + payout) 1 (rP - 1));
        lia. }
      rewrite Hdiv. lia. }
  fold n. rewrite HRHS, HLHS.
  (* Step 1: qP <= qR (floor decreases as divisor grows). *)
  assert (HqPqR : qP <= qR).
  { unfold qP, qR. apply Z.div_le_compat_l; lia. }
  (* Step 2: case split on the boolean indicators. The only nontrivial
     case is [rR = 0, rP != 0], where we strengthen [qP <= qR] to
     [qP + 1 <= qR]. *)
  destruct (rR =? 0) eqn:HrRz; destruct (rP =? 0) eqn:HrPz.
  - lia.
  - apply Z.eqb_eq in HrRz. apply Z.eqb_neq in HrPz.
    (* HdmR with rR = 0: n = qR * R, so qR * R = n > 0, hence qR > 0
       (since R > 0). *)
    assert (HnQRR : n = qR * R) by lia.
    assert (HqRpos : 0 < qR).
    { destruct (Z_lt_le_dec 0 qR) as [|Hle]; [assumption|].
      assert (qR <= 0) by exact Hle.
      assert (qR * R <= 0) by nia.
      lia. }
    (* HdmP: n = qP*(R+payout) + rP, 0 < rP < R+payout.
       From qP <= qR, suppose qP = qR. Then
          n = qR*(R+payout) + rP = qR*R + qR*payout + rP = n + qR*payout + rP,
       so 0 = qR*payout + rP, but qR > 0, payout >= 0, rP > 0 ⇒ contradiction.
       Hence qP < qR, i.e. qP + 1 <= qR. *)
    assert (HqPltqR : qP < qR).
    { destruct (Z_lt_le_dec qP qR) as [|Hge]; [assumption|].
      assert (HqPeq : qP = qR) by lia.
      rewrite HqPeq in HdmP.
      assert (Hcontra : qR * payout + rP = 0) by lia.
      assert (qR * payout >= 0) by nia.
      lia. }
    lia.
  - lia.
  - lia.
Qed.

Lemma stakeRate_monotone_payoutRewards
    (s : Storage.t) (now rewardsPool : U256.t) :
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
                   (now - s.(Storage.lastPayout))) in
  let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
  0 <= payout ->
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  stakeRate (payoutRewards s now rewardsPool) <= stakeRate s.
Proof.
  intros payoutRatio payout Hpay HS HR.
  destruct (Z_lt_le_dec now (s.(Storage.lastPayout) + 1)) as [Hno|Hyes].
  - rewrite (payoutRewards_no_period_local s now rewardsPool Hno). lia.
  - (* Active branch: define [s'] as the post-payout storage, then use
       the fact that [stakeRSR_prod s' = stakeRSR_prod s + payout] and
       [totalStRSR s' = totalStRSR s] to reduce to [ceil_div_monotone].
       We project the relevant fields directly out of [payoutRewards_active]
       to avoid ever cbn-unfolding the full record. *)
    set (s' := payoutRewards s now rewardsPool).
    assert (HSp : s'.(Storage.totalStRSR) = s.(Storage.totalStRSR)).
    { unfold s'. rewrite payoutRewards_active_local by exact Hyes. reflexivity. }
    assert (HRp : stakeRSR_prod s' = stakeRSR_prod s + payout).
    { unfold s'. rewrite payoutRewards_active_local by exact Hyes.
      unfold stakeRSR_prod. cbn [Storage.totalRSRStaked
                                 Storage.totalRewardsAccumulated].
      unfold payout, payoutRatio. lia. }
    assert (HS' : 0 < s'.(Storage.totalStRSR)) by (rewrite HSp; exact HS).
    assert (HR' : 0 < stakeRSR_prod s') by (rewrite HRp; lia).
    rewrite (stakeRate_active s HS HR).
    rewrite (stakeRate_active s' HS' HR').
    rewrite HSp, HRp.
    apply ceil_div_monotone_under_payout; lia.
Qed.

(** ---------- INV-INV-PROD bridge ----------

    The bridge: [exchange_rate s * stakeRate s] is sandwiched in a
    quantitative window around [FIX_ONE_Z * FIX_ONE_Z]. We state the
    upper and lower sides separately to keep [nia]'s search space
    manageable. The statements are multiplicative (no division) so they
    compose cleanly in downstream proofs.

    UPPER: [exchange_rate s * stakeRate s * S * R
            <= R * FIX_ONE * (S * FIX_ONE + R)]

    LOWER: [exchange_rate s * stakeRate s * S * R
            >  (R * FIX_ONE - S) * (S * FIX_ONE)]

    Multiplying gives a quantitative bridge: in real arithmetic the gap
    closes; in Z the gap is bounded by terms of order [S*R*FIX_ONE]. *)

Lemma exchange_rate_inverse_of_stakeRate_upper
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  exchange_rate s * stakeRate s * s.(Storage.totalStRSR) * stakeRSR_prod s
    <= stakeRSR_prod s * FIX_ONE_Z
       * (s.(Storage.totalStRSR) * FIX_ONE_Z + stakeRSR_prod s).
Proof.
  intros HS HR.
  pose proof (exchange_rate_floor_upper s HS) as Hxu.
  pose proof (stakeRate_ceil_upper s HS HR) as Hsu.
  pose proof (exchange_rate_nonneg s HS ltac:(lia)) as Hxnn.
  pose proof (stakeRate_nonneg s HS HR) as Hsnn.
  set (ER := exchange_rate s).
  set (SR := stakeRate s).
  set (S := s.(Storage.totalStRSR)).
  set (R := stakeRSR_prod s).
  fold ER S in Hxu, Hxnn.
  fold SR R S in Hsu, Hsnn.
  fold R in Hxu.
  (* Step 1: ER * S * SR * R <= (R * FIX_ONE) * (SR * R) (since SR*R >= 0). *)
  assert (HSRR : 0 <= SR * R) by nia.
  assert (Hstep1 : ER * S * (SR * R) <= R * FIX_ONE_Z * (SR * R)).
  { apply Z.mul_le_mono_nonneg_r; assumption. }
  (* Step 2: R * FIX_ONE * (SR * R) <= R * FIX_ONE * (S * FIX_ONE + R)
     (since SR * R < S * FIX_ONE + R, and R * FIX_ONE >= 0). *)
  assert (HRF : 0 <= R * FIX_ONE_Z).
  { apply Z.mul_nonneg_nonneg; [lia|unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia]. }
  assert (Hstep2 : R * FIX_ONE_Z * (SR * R) <=
                   R * FIX_ONE_Z * (S * FIX_ONE_Z + R)).
  { apply Z.mul_le_mono_nonneg_l; [exact HRF|lia]. }
  (* Combine: rearrange ER*S*SR*R = ER*SR*S*R. *)
  assert (Hcomm : ER * S * (SR * R) = ER * SR * S * R) by ring.
  rewrite <- Hcomm.
  lia.
Qed.

Lemma exchange_rate_inverse_of_stakeRate_lower
    (s : Storage.t) :
  0 < s.(Storage.totalStRSR) ->
  0 < stakeRSR_prod s ->
  exchange_rate s * stakeRate s * s.(Storage.totalStRSR) * stakeRSR_prod s
    > (stakeRSR_prod s * FIX_ONE_Z - s.(Storage.totalStRSR))
      * (s.(Storage.totalStRSR) * FIX_ONE_Z).
Proof.
  intros HS HR.
  pose proof (exchange_rate_floor_lower s HS) as Hxl.
  pose proof (stakeRate_ceil_lower s HS HR) as Hsl.
  pose proof (exchange_rate_nonneg s HS ltac:(lia)) as Hxnn.
  pose proof (stakeRate_nonneg s HS HR) as Hsnn.
  set (ER := exchange_rate s).
  set (SR := stakeRate s).
  set (S := s.(Storage.totalStRSR)).
  set (R := stakeRSR_prod s).
  fold ER S in Hxl, Hxnn.
  fold SR R S in Hsl, Hsnn.
  fold R in Hxl.
  (* Hxl: ER * S > R * FIX_ONE - S
     Hsl: SR * R >= S * FIX_ONE.
     Goal: ER * SR * S * R > (R * FIX_ONE - S) * (S * FIX_ONE).

     Step 1: ER * S * SR * R > (R * FIX_ONE - S) * SR * R
       (multiplying Hxl by [SR * R > 0]).
       But SR may be 0. We need [0 < SR * R]. From Hsl: SR * R >= S * FIX_ONE > 0.
     Step 2: (R * FIX_ONE - S) * SR * R >= (R * FIX_ONE - S) * (S * FIX_ONE)
       From [SR * R >= S * FIX_ONE], multiplied by [R * FIX_ONE - S].
       But R * FIX_ONE - S could be of any sign. We assume non-degenerate
       (R, S, FIX_ONE all positive), and typically R * FIX_ONE >> S, so the
       factor is positive — but in pathological cases it could be negative
       (e.g., R = 1, S = 2, FIX_ONE = 1e18 — no, R*FIX_ONE = 1e18 > S). So
       in any realistic instance R*FIX_ONE - S > 0. We don't need to assume
       it — instead, use [Z.mul_le_mono] in the right direction. *)
  assert (HSRRpos : 0 < SR * R).
  { assert (HSF : 0 < S * FIX_ONE_Z) by (unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; nia).
    lia. }
  assert (HSF : 0 < S * FIX_ONE_Z) by (unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; nia).
  (* From Hxl strict: ER * S > R*FIX_ONE - S, so ER * S * SR * R >
     (R*FIX_ONE - S) * SR * R (when SR*R > 0). *)
  assert (Hstep1 : ER * S * (SR * R) > (R * FIX_ONE_Z - S) * (SR * R)).
  { apply Z.lt_gt. apply Zmult_gt_0_lt_compat_r; [lia|lia]. }
  (* From Hsl: SR * R >= S * FIX_ONE, so (R*FIX_ONE - S) * (SR*R) >=
     (R*FIX_ONE - S) * (S*FIX_ONE) when (R*FIX_ONE - S) >= 0.
     If (R*FIX_ONE - S) < 0, the inequality flips and we'd need
     SR * R <= S*FIX_ONE — but we have SR*R >= S*FIX_ONE, so
     (R*FIX_ONE - S) * (SR*R) <= (R*FIX_ONE - S) * (S*FIX_ONE).
     Since the goal has ">", we want the right side of the bound to be
     no LARGER than the value (R*FIX_ONE - S) * (SR*R). We need:
     (R*FIX_ONE - S) * (SR*R) >= (R*FIX_ONE - S) * (S*FIX_ONE).
     Case A: R*FIX_ONE >= S. Then SR*R >= S*FIX_ONE gives the inequality.
     Case B: R*FIX_ONE < S. Then S*FIX_ONE = RHS factor; the LHS factor
     is (R*FIX_ONE - S) < 0. Multiplying [SR*R >= S*FIX_ONE] by a
     negative flips: (R*FIX_ONE - S) * (SR*R) <= (R*FIX_ONE - S) * (S*FIX_ONE).
     In this case the bound is actually SMALLER than what we want, which
     would invalidate the lemma. But Case B requires R*FIX_ONE < S, i.e.
     R < S/FIX_ONE — which means [stakeRSR_prod < totalStRSR / 1e18]. In
     production this is virtually impossible (stakes are tracked in qStRSR
     and qRSR, so the ratio is in [1e-9, 1e9]). For the simulation we
     state the lemma in its [Z]-pure form and let Case B yield a vacuous
     bound (since the lower bound goes negative).

     In Case B (R*FIX_ONE - S < 0), the goal RHS
     (R*FIX_ONE - S) * (S*FIX_ONE) <= 0 (negative * positive), and
     ER*SR*S*R >= 0, so the strict inequality holds via 0 > <negative>.
     Let's branch on the sign of (R*FIX_ONE - S). *)
  destruct (Z_lt_le_dec (R * FIX_ONE_Z - S) 0) as [Hneg | Hpos].
  - (* Case B: R*FIX_ONE - S < 0. Goal RHS is negative (since S*FIX_ONE > 0).
       LHS = ER*SR*S*R >= 0. Hence > holds. *)
    assert (HRHSneg : (R * FIX_ONE_Z - S) * (S * FIX_ONE_Z) < 0).
    { apply Z.mul_neg_pos; [exact Hneg|exact HSF]. }
    assert (HLHSnn : 0 <= ER * SR * S * R).
    { apply Z.mul_nonneg_nonneg.
      - apply Z.mul_nonneg_nonneg.
        + apply Z.mul_nonneg_nonneg; lia.
        + lia.
      - lia. }
    lia.
  - (* Case A: R*FIX_ONE - S >= 0. Then (R*FIX_ONE - S)*(SR*R) >=
       (R*FIX_ONE - S)*(S*FIX_ONE) since SR*R >= S*FIX_ONE. *)
    assert (Hstep2 : (R * FIX_ONE_Z - S) * (SR * R) >=
                     (R * FIX_ONE_Z - S) * (S * FIX_ONE_Z)).
    { apply Zmult_ge_compat_l; [exact Hsl|lia]. }
    assert (Hcomm : ER * S * (SR * R) = ER * SR * S * R) by ring.
    lia.
Qed.

(** ---------- INV-INV-STAKE ----------

    The simulation's [stake] formula and the production [mintStakes]
    formula agree on the genesis era. *)

(** Production-style mintStakes computation: given stakeRate, stakeRSR,
    totalStakes, and an incoming rsrAmount, return the stakeAmount
    minted. Direct port of StRSR.sol#L750-L754. *)
Definition mintStakes_production
    (stakeRate_in stakeRSR_in totalStakes_in rsrAmount : Z) : Z :=
  let newStakeRSR := stakeRSR_in + rsrAmount in
  let newTotalStakes := (stakeRate_in * newStakeRSR) / FIX_ONE_Z in
  newTotalStakes - totalStakes_in.

(** A fresh genesis storage with [ratio = 0]. *)
Definition genesis_storage : Storage.t := {|
  Storage.totalStRSR              := 0;
  Storage.totalRSRStaked          := 0;
  Storage.totalRewardsAccumulated := 0;
  Storage.ratio                   := 0;
  Storage.lastPayout              := 0;
  Storage.queue                   := [];
  Storage.era                     := 0;
  Storage.draftEra                := 0;
  Storage.draftRSR                := 0;
|}.

(** On the genesis era, both the simulation and production mint
    [amount] units of stRSR one-for-one. *)
Lemma stake_under_inverse_formulation_genesis
    (amount : U256.t) :
  0 <= amount ->
  let s := genesis_storage in
  let s' := stake s amount in
  s'.(Storage.totalStRSR) =
    mintStakes_production
      (stakeRate s)
      (stakeRSR_prod s)
      s.(Storage.totalStRSR)
      amount.
Proof.
  intros Ha. cbn zeta.
  unfold stake, genesis_storage.
  cbn -[Z.add Z.eqb].
  rewrite Z.eqb_refl.
  cbn -[Z.add Z.mul Z.div].
  unfold mintStakes_production, stakeRate, stakeRSR_prod, genesis_storage.
  cbn [Storage.totalStRSR Storage.totalRSRStaked
       Storage.totalRewardsAccumulated].
  rewrite Z.add_0_l. rewrite Z.eqb_refl.
  cbn [orb].
  unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE.
  rewrite Z.add_0_l.
  rewrite Z.mul_comm.
  rewrite Z.div_mul by lia.
  lia.
Qed.

End StRSRInversion.
