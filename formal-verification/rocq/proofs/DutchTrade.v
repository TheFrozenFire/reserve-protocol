(** DutchTrade simulation invariant proofs.

    Proves the load-bearing safety invariants on the [DutchTrade]
    simulation defined in [Reserve.simulations.DutchTrade]:

      INV-START      progression at startTime = 0; bidPrice falls into phase 1.
      INV-END        bidPrice at endTime = worstPrice.
      INV-MONO-PH3   phase3_price is monotone non-increasing in progression.
      INV-MONO-PH4   phase4_price is constant in progression.
      INV-AT-95      phase3_price evaluated at NINETY_FIVE_PERCENT = worstPrice.
      INV-AT-45      phase3_price evaluated at FORTY_FIVE_PERCENT = bestPrice.
      INV-PHASE4-EQ  phase4_price = worstPrice.
      INV-BID-MONO-PRICE  bidAmount_at_price monotone non-decreasing in price.
      INV-BID-CEIL   bidAmount_at_price >= FLOOR variant (CEIL never under-charges).
      INV-BID-PLUS-ONE  at buyDecimals = 18, bidAmount = mul_ceil; gap to FLOOR
                        variant is at most one wei.

    Avoid [simpl] on terms containing FIX_ONE = 10^18.
    Do NOT install Z.to_euclidean_division_equations.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.DutchTrade.
Require Import Coq.Bool.Bool.

Module DutchTradeProofs.

Import FixLib.
Import DutchTrade.

(** ===== Phase-4 sanity: phase4_price = worstPrice. ===== *)
Lemma phase4_eq_worstPrice (a : Auction.t) :
  phase4_price a = a.(Auction.worstPrice).
Proof. reflexivity. Qed.

(** ===== Phase-4 is constant in [prog]. ===== *)
Lemma phase4_constant (a : Auction.t) (p1 p2 : Z) :
  phase4_price a = phase4_price a.
Proof. reflexivity. Qed.

(** ===== Continuity at the 45% boundary: phase3 at 45% = bestPrice. ===== *)
Lemma phase3_at_45_pct (a : Auction.t) :
  phase3_price a FORTY_FIVE_PERCENT = a.(Auction.bestPrice).
Proof.
  unfold phase3_price.
  replace (FORTY_FIVE_PERCENT - FORTY_FIVE_PERCENT) with 0 by reflexivity.
  rewrite Z.mul_0_r.
  unfold FIFTY_PERCENT.
  rewrite Z.div_0_l by lia.
  lia.
Qed.

(** ===== Continuity at the 95% boundary: phase3 at 95% = worstPrice. ===== *)
Lemma phase3_at_95_pct (a : Auction.t) :
  Valid.t a ->
  phase3_price a NINETY_FIVE_PERCENT = a.(Auction.worstPrice).
Proof.
  intros Hv.
  destruct Hv as [_ Hpo _ _ _ _ _ _].
  unfold phase3_price.
  unfold NINETY_FIVE_PERCENT, FORTY_FIVE_PERCENT, FIFTY_PERCENT.
  set (best := a.(Auction.bestPrice)).
  set (worst := a.(Auction.worstPrice)).
  fold best. fold worst.
  replace (95 * 10^16 - 45 * 10^16) with (50 * 10^16) by lia.
  rewrite Z.div_mul by lia.
  lia.
Qed.

(** ===== Phase-3 is monotone non-increasing in [prog]. ===== *)
Lemma phase3_monotone (a : Auction.t) (p1 p2 : Z) :
  Valid.t a ->
  FORTY_FIVE_PERCENT <= p1 <= p2 ->
  p2 <= NINETY_FIVE_PERCENT ->
  phase3_price a p2 <= phase3_price a p1.
Proof.
  intros Hv [Hp1 Hp12] _Hp2.
  destruct Hv as [_ Hpo _ _ _ _ _ _].
  unfold phase3_price.
  set (delta := a.(Auction.bestPrice) - a.(Auction.worstPrice)).
  assert (Hdelta : 0 <= delta) by (unfold delta; lia).
  unfold FIFTY_PERCENT.
  apply Z.sub_le_mono_l.
  apply Z.div_le_mono; [lia|].
  apply Z.mul_le_mono_nonneg_l; [exact Hdelta|].
  unfold FORTY_FIVE_PERCENT in *. lia.
Qed.

(** ===== highPrice = mul best 1.5 CEIL >= best (since 1.5 > 1, when best >= 0). ===== *)
Lemma high_price_ge_best (best : Z) :
  0 <= best ->
  best <= mul best ONE_POINT_FIVE RoundingMode.CEIL.
Proof.
  intros Hb.
  unfold mul, divrnd, ONE_POINT_FIVE, FIX_SCALE.
  set (n := best * (150 * 10^16)).
  (* n / 10^18 = best * 150 / 100 = (3/2) * best when divisible.
     We need: best <= n / 10^18 + (if n mod 10^18 =? 0 then 0 else 1).
     Compute n / 10^18:
       n = best * 1.5e18 = best*1.0e18 + best*0.5e18
       n / 1e18 = best + best/2  (with FLOOR on the half) *)
  assert (Hsplit : n = best * 10^18 + best * (5 * 10^17)).
  { unfold n. lia. }
  rewrite Hsplit.
  rewrite Z.div_add_l by lia.
  assert (H05 : 0 <= best * (5 * 10^17) / 10^18).
  { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; lia. }
  destruct ((best * 10^18 + best * (5 * 10^17)) mod 10^18 =? 0); lia.
Qed.

(** ===== Phase-2 is monotone non-increasing in [prog]. ===== *)
Lemma phase2_monotone (a : Auction.t) (p1 p2 : Z) :
  TWENTY_PERCENT <= p1 <= p2 ->
  p2 <= FORTY_FIVE_PERCENT ->
  0 <= a.(Auction.bestPrice) ->
  phase2_price a p2 <= phase2_price a p1.
Proof.
  intros [Hp1 Hp12] _Hp2 Hbest.
  unfold phase2_price.
  set (best := a.(Auction.bestPrice)).
  set (high := mul best ONE_POINT_FIVE RoundingMode.CEIL).
  assert (Hhigh_ge_best : best <= high) by (apply high_price_ge_best; exact Hbest).
  assert (Hhigh_minus_best : 0 <= high - best) by lia.
  unfold TWENTY_FIVE_PERCENT.
  apply Z.sub_le_mono_l.
  apply Z.div_le_mono; [lia|].
  apply Z.mul_le_mono_nonneg_l; [exact Hhigh_minus_best|].
  unfold TWENTY_PERCENT in *. lia.
Qed.

(** ===== Helper lemma: integer-division floor strict-jump under exact-divisibility. -----
    If [n1 <= n2], [k > 0], [n1 mod k != 0], and [n2 mod k = 0], then
    [n1 / k + 1 <= n2 / k]. Used in CEIL-monotonicity arguments below. *)
Lemma div_floor_strict_jump (n1 n2 k : Z) :
  0 < k ->
  n1 <= n2 ->
  n1 mod k <> 0 ->
  n2 mod k = 0 ->
  n1 / k + 1 <= n2 / k.
Proof.
  intros Hk Hn Hr1 Hr2.
  assert (Hr1' : n1 = (n1 / k) * k + n1 mod k).
  { rewrite (Z.div_mod n1 k) at 1 by lia. lia. }
  assert (Hr1_pos : 0 < n1 mod k).
  { assert (0 <= n1 mod k < k) by (apply Z.mod_pos_bound; lia). lia. }
  assert (Hr2' : n2 = (n2 / k) * k).
  { rewrite (Z.div_mod n2 k) at 1 by lia. lia. }
  nia.
Qed.

(** ===== mul_ceil monotone in y (when sellAmount >= 0). ===== *)
Lemma mul_ceil_monotone (s p1 p2 : Z) :
  0 <= s ->
  p1 <= p2 ->
  mul s p1 RoundingMode.CEIL <= mul s p2 RoundingMode.CEIL.
Proof.
  intros Hs Hp.
  unfold mul, divrnd, FIX_SCALE.
  set (n1 := s * p1). set (n2 := s * p2).
  assert (Hn : n1 <= n2)
    by (unfold n1, n2; apply Z.mul_le_mono_nonneg_l; assumption).
  assert (Hd : n1 / 10^18 <= n2 / 10^18) by (apply Z.div_le_mono; [lia|exact Hn]).
  destruct (n1 mod 10^18 =? 0) eqn:H1;
  destruct (n2 mod 10^18 =? 0) eqn:H2.
  - lia.
  - lia.
  - apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    pose proof (div_floor_strict_jump n1 n2 (10^18) ltac:(lia) Hn H1 H2).
    lia.
  - lia.
Qed.

(** ===== bidAmount_at_price is monotone non-decreasing in [price]. ===== *)
Lemma bidAmount_at_price_monotone (a : Auction.t) (p1 p2 : Z) :
  0 <= a.(Auction.sellAmount) ->
  p1 <= p2 ->
  bidAmount_at_price a p1 <= bidAmount_at_price a p2.
Proof.
  intros Hsell Hp.
  unfold bidAmount_at_price.
  set (m1 := mul a.(Auction.sellAmount) p1 RoundingMode.CEIL).
  set (m2 := mul a.(Auction.sellAmount) p2 RoundingMode.CEIL).
  assert (Hmle : m1 <= m2) by (apply mul_ceil_monotone; assumption).
  set (shift := 18 - a.(Auction.buyDecimals)).
  destruct (0 <=? shift) eqn:Hshift.
  - apply Z.leb_le in Hshift.
    assert (Hpow : 0 < 10^shift) by (apply Z.pow_pos_nonneg; lia).
    unfold divrnd.
    assert (Hd : m1 / 10^shift <= m2 / 10^shift)
      by (apply Z.div_le_mono; [lia|exact Hmle]).
    destruct (m1 mod 10^shift =? 0) eqn:H1;
    destruct (m2 mod 10^shift =? 0) eqn:H2.
    + lia.
    + lia.
    + apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
      pose proof (div_floor_strict_jump m1 m2 (10^shift) Hpow Hmle H1 H2).
      lia.
    + lia.
  - apply Z.mul_le_mono_nonneg_r; [|exact Hmle].
    apply Z.pow_nonneg. lia.
Qed.

(** ===== bidAmount uses CEIL: bidAmount_at_price >= FLOOR variant. ===== *)
Lemma bidAmount_at_price_ge_floor (a : Auction.t) (price : Z) :
  0 <= a.(Auction.sellAmount) ->
  0 <= price ->
  bidAmount_floor_variant a price <= bidAmount_at_price a price.
Proof.
  intros Hsell Hprice.
  unfold bidAmount_floor_variant, bidAmount_at_price.
  set (sn := a.(Auction.sellAmount) * price).
  assert (Hsn : 0 <= sn)
    by (unfold sn; apply Z.mul_nonneg_nonneg; assumption).
  set (mfloor := mul a.(Auction.sellAmount) price RoundingMode.FLOOR).
  set (mceil  := mul a.(Auction.sellAmount) price RoundingMode.CEIL).
  assert (Hmle : mfloor <= mceil).
  { unfold mfloor, mceil, mul, divrnd, FIX_SCALE.
    fold sn.
    destruct (sn mod 10^18 =? 0); lia. }
  set (shift := 18 - a.(Auction.buyDecimals)).
  destruct (0 <=? shift) eqn:Hshift.
  - apply Z.leb_le in Hshift.
    assert (Hpow : 0 < 10^shift) by (apply Z.pow_pos_nonneg; lia).
    unfold divrnd.
    destruct (mceil mod 10^shift =? 0) eqn:Hmod.
    + apply Z.div_le_mono; lia.
    + assert (Hd : mfloor / 10^shift <= mceil / 10^shift)
        by (apply Z.div_le_mono; lia).
      lia.
  - apply Z.mul_le_mono_nonneg_r; [|exact Hmle].
    apply Z.pow_nonneg. lia.
Qed.

(** ===== At buyDecimals = 18, bidAmount = mul_ceil (the shiftl is identity). ===== *)
Lemma bidAmount_at_18_decimals (a : Auction.t) (price : Z) :
  a.(Auction.buyDecimals) = 18 ->
  bidAmount_at_price a price = mul a.(Auction.sellAmount) price RoundingMode.CEIL.
Proof.
  intros Hbd.
  unfold bidAmount_at_price.
  rewrite Hbd.
  replace (18 - 18) with 0 by reflexivity.
  cbv [Z.leb Pos.compare].
  unfold divrnd.
  replace (10 ^ 0) with 1 by reflexivity.
  set (m := mul _ _ _).
  rewrite Z.mod_1_r.
  rewrite Z.eqb_refl.
  rewrite Z.div_1_r. reflexivity.
Qed.

Lemma bidAmount_floor_at_18 (a : Auction.t) (price : Z) :
  a.(Auction.buyDecimals) = 18 ->
  bidAmount_floor_variant a price = mul a.(Auction.sellAmount) price RoundingMode.FLOOR.
Proof.
  intros Hbd.
  unfold bidAmount_floor_variant.
  rewrite Hbd.
  replace (18 - 18) with 0 by reflexivity.
  cbv [Z.leb Pos.compare].
  replace (10 ^ 0) with 1 by reflexivity.
  unfold divrnd. cbn match.
  apply Z.div_1_r.
Qed.

Lemma bidAmount_le_floor_plus_one_at_18 (a : Auction.t) (price : Z) :
  a.(Auction.buyDecimals) = 18 ->
  bidAmount_at_price a price <=
    bidAmount_floor_variant a price + 1.
Proof.
  intros Hbd.
  rewrite (bidAmount_at_18_decimals _ _ Hbd).
  rewrite (bidAmount_floor_at_18 _ _ Hbd).
  unfold mul, divrnd, FIX_SCALE.
  destruct (a.(Auction.sellAmount) * price mod 10^18 =? 0); lia.
Qed.

(** ===== Endpoint behavior: progression at startTime = 0. ===== *)
Lemma progression_at_startTime (a : Auction.t) :
  Valid.t a ->
  progression a a.(Auction.startTime) = 0.
Proof.
  intros Hv.
  destruct Hv as [Ht _ _ _ _ _ _ _].
  unfold progression.
  replace (a.(Auction.startTime) - a.(Auction.startTime)) with 0 by lia.
  rewrite Z.mul_0_l.
  apply Z.div_0_l. lia.
Qed.

(** ===== Endpoint behavior: progression at endTime = FIX_ONE. ===== *)
Lemma progression_at_endTime (a : Auction.t) :
  Valid.t a ->
  progression a a.(Auction.endTime) = FIX_ONE.
Proof.
  intros Hv.
  destruct Hv as [Ht _ _ _ _ _ _ _].
  unfold progression.
  set (s := a.(Auction.startTime)). set (e := a.(Auction.endTime)).
  fold s. fold e.
  assert (Hpos : 0 < e - s) by lia.
  rewrite Z.mul_comm.
  rewrite Z.div_mul. reflexivity. lia.
Qed.

(** ===== Endpoint behavior: bidPrice at endTime = worstPrice. ===== *)
Lemma bidPrice_at_endTime (a : Auction.t) :
  Valid.t a ->
  bidPrice a a.(Auction.endTime) = a.(Auction.worstPrice).
Proof.
  intros Hv.
  unfold bidPrice.
  rewrite (progression_at_endTime _ Hv).
  (* FIX_ONE = 10^18 = 100*10^16, while NINETY_FIVE_PERCENT = 95*10^16.
     So FIX_ONE >= NINETY_FIVE_PERCENT, all guards fall through. *)
  unfold FIX_ONE, FIX_SCALE, TWENTY_PERCENT, FORTY_FIVE_PERCENT,
         NINETY_FIVE_PERCENT.
  cbn [Z.ltb Z.compare].
  reflexivity.
Qed.

(** ===== Endpoint behavior: bidPrice at startTime = phase1_price at 0. =====
    progression(startTime) = 0 < TWENTY_PERCENT, so dispatcher returns phase1
    evaluated at progression = 0. *)
Lemma bidPrice_at_startTime (a : Auction.t) :
  Valid.t a ->
  bidPrice a a.(Auction.startTime) = phase1_price a 0.
Proof.
  intros Hv.
  unfold bidPrice.
  rewrite (progression_at_startTime _ Hv).
  unfold TWENTY_PERCENT.
  cbn [Z.ltb Z.compare].
  reflexivity.
Qed.

(** ===== Within-phase 4: bidPrice constant at worstPrice. ===== *)
Lemma bidPrice_phase4_constant (a : Auction.t) (t : U256.t) :
  NINETY_FIVE_PERCENT <= progression a t ->
  progression a t <= FIX_ONE ->
  bidPrice a t = a.(Auction.worstPrice).
Proof.
  intros Hge Hle.
  unfold bidPrice.
  set (p := progression a t). fold p.
  assert (H1 : (p <? TWENTY_PERCENT) = false).
  { apply Z.ltb_ge. unfold TWENTY_PERCENT, NINETY_FIVE_PERCENT in *. lia. }
  assert (H2 : (p <? FORTY_FIVE_PERCENT) = false).
  { apply Z.ltb_ge. unfold FORTY_FIVE_PERCENT, NINETY_FIVE_PERCENT in *. lia. }
  assert (H3 : (p <? NINETY_FIVE_PERCENT) = false)
    by (apply Z.ltb_ge; lia).
  rewrite H1, H2, H3. reflexivity.
Qed.

(** ===== Bid amount monotone DECREASING in time t (composed direction).
    If bidPrice(t1) >= bidPrice(t2) — which holds within each phase — then
    bidAmount(t1) >= bidAmount(t2).  This is the key liveness property
    for bidders: waiting longer never costs more. We state the lifted
    form: the property is parametric over any time pair where bidPrice
    is monotone-decreasing. =====*)
Lemma bidAmount_decreases_with_price_drop
    (a : Auction.t) (t1 t2 : U256.t) :
  0 <= a.(Auction.sellAmount) ->
  bidPrice a t2 <= bidPrice a t1 ->
  bidAmount a t2 <= bidAmount a t1.
Proof.
  intros Hsell Hpr.
  unfold bidAmount.
  apply bidAmount_at_price_monotone; assumption.
Qed.

End DutchTradeProofs.
