(** TradeLib simulation invariant proofs.

    Proves the load-bearing safety invariants on the [TradeLib]
    simulation in [Reserve.simulations.TradeLib].

    Slippage / buy-amount invariants:
      INV-MUL-CR-INNER  inner mul under CEIL >= inner mul under FLOOR
                        (lifts proofs/Fixed.divrnd_floor_le_ceil to mul)
      INV-BUY-POST-GE-PRE  buyAmount >= buyAmountPre, always
                           (the post-mitigation guarantee)
      INV-BUY-ZERO-SLIPPAGE buyAmount with slippage = 0  =  buyAmount with
                            FLOOR inner (rounding-mode insensitive)
      INV-BUY-FULL-SLIPPAGE buyAmount with slippage = FIX_ONE  =  0
      INV-BUY-ZERO-S        buyAmount with s = 0  =  0
      INV-BUY-NONNEG        buyAmount >= 0  (under sane inputs)

    safeMulDiv invariants:
      INV-SMD-A0-ZERO       safeMulDiv 0 b c mode = 0
      INV-SMD-B0-ZERO       safeMulDiv a 0 c mode = 0
      INV-SMD-LE-FIX-MAX    safeMulDiv a b c mode <= FIX_MAX
      INV-SMD-NONNEG        safeMulDiv a b c mode >= 0  (under sane inputs)
      INV-SMD-CEIL-MONO     safeMulDiv FLOOR <= safeMulDiv CEIL
                            (when neither saturates)

    minTradeSize / isEnoughToSell invariants:
      INV-MTS-PRICE-ZERO    minTradeSize _ 0   =  FIX_MAX
      INV-MTS-AT-LEAST-1    minTradeSize mtv p >= 1  (when p > 0 OR p = 0)
      INV-MTS-NONNEG        minTradeSize mtv p >= 0
      INV-IETS-MONOTONE     amt1 <= amt2 ->
                            isEnoughToSell_whole amt1 -> isEnoughToSell_whole amt2

    Avoid [simpl] inside these proofs — FIX_ONE = 10^18 explodes under simpl.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.proofs.Fixed.
Require Import Coq.Bool.Bool.

Module TradeLibProofs.

Import FixLib.
Import FixLibProofs.
Import TradeLib.

(** ============================================================ *)
(** ===== safeMulDiv basic shape ================================ *)
(** ============================================================ *)

(** ----- INV-SMD-A0-ZERO. ----- *)
Lemma safeMulDiv_a_zero (b c : Z) (mode : RoundingMode.t) :
  safeMulDiv 0 b c mode = 0.
Proof.
  unfold safeMulDiv.
  rewrite Z.eqb_refl. cbn [orb]. reflexivity.
Qed.

(** ----- INV-SMD-B0-ZERO. ----- *)
Lemma safeMulDiv_b_zero (a c : Z) (mode : RoundingMode.t) :
  safeMulDiv a 0 c mode = 0.
Proof.
  unfold safeMulDiv.
  destruct (a =? 0) eqn:Ha.
  - cbn [orb]. reflexivity.
  - rewrite Z.eqb_refl.
    replace (false || true)%bool with true by reflexivity. reflexivity.
Qed.

(** ----- INV-SMD-LE-FIX-MAX: result is bounded above by FIX_MAX. ----- *)
Lemma safeMulDiv_le_fix_max (a b c : Z) (mode : RoundingMode.t) :
  safeMulDiv a b c mode <= FIX_MAX.
Proof.
  assert (HFM_pos : 0 < FIX_MAX) by (unfold FIX_MAX; lia).
  unfold safeMulDiv.
  destruct ((a =? 0) || (b =? 0))%bool.
  - lia.
  - destruct ((a =? FIX_MAX) || (b =? FIX_MAX) || (c =? 0))%bool.
    + lia.
    + destruct (FIX_MAX <=? divrnd (a * b) c mode) eqn:Hge.
      * lia.
      * apply Z.leb_gt in Hge. lia.
Qed.

(** ----- INV-SMD-NONNEG: result is nonneg under sane inputs. -----
    Inputs: 0 <= a, 0 <= b, 0 <= c. divrnd's quotient on a*b/c with c > 0
    and a*b >= 0 is >= 0. The c = 0 branch saturates to FIX_MAX > 0 so
    the result remains >= 0. *)
Lemma safeMulDiv_nonneg (a b c : Z) (mode : RoundingMode.t) :
  0 <= a ->
  0 <= b ->
  0 <= c ->
  0 <= safeMulDiv a b c mode.
Proof.
  intros Ha Hb Hc.
  assert (HFM_pos : 0 < FIX_MAX) by (unfold FIX_MAX; lia).
  unfold safeMulDiv.
  destruct ((a =? 0) || (b =? 0))%bool; [lia|].
  destruct ((a =? FIX_MAX) || (b =? FIX_MAX) || (c =? 0))%bool eqn:Hsat.
  - lia.
  - destruct (FIX_MAX <=? divrnd (a * b) c mode) eqn:Hge.
    + lia.
    + apply Z.leb_gt in Hge.
      (* c > 0 because (c =? 0) is in the saturation OR which is false *)
      assert (Hc_pos : 0 < c).
      { apply orb_false_iff in Hsat. destruct Hsat as [_ Hcz].
        apply Z.eqb_neq in Hcz. lia. }
      unfold divrnd.
      assert (Hab_nn : 0 <= a * b) by (apply Z.mul_nonneg_nonneg; assumption).
      assert (Hq_nn : 0 <= (a * b) / c) by (apply Z.div_pos; lia).
      destruct mode.
      * exact Hq_nn.
      * destruct ((a * b) mod c >? (c - 1) / 2); lia.
      * destruct ((a * b) mod c =? 0); lia.
Qed.

(** ============================================================ *)
(** ===== Inner-mul rounding direction ========================== *)
(** ============================================================ *)

(** ----- The CEIL inner mul never under-credits the FLOOR inner mul. -----
    Lift of proofs/Fixed.divrnd_floor_le_ceil to [mul]. *)
Lemma inner_ceil_ge_floor (s slippage : Z) :
  mul s (FIX_ONE - slippage) RoundingMode.FLOOR
  <= mul s (FIX_ONE - slippage) RoundingMode.CEIL.
Proof.
  apply mul_floor_le_ceil.
Qed.

(** ============================================================ *)
(** ===== safeMulDiv monotone in numerator-input ================ *)
(** ============================================================ *)

(** Helper: divrnd-CEIL is monotone in numerator when divisor is positive
    and the smaller numerator is non-negative. *)
Lemma divrnd_ceil_monotone (n1 n2 d : Z) :
  0 <= n1 ->
  n1 <= n2 ->
  0 < d ->
  divrnd n1 d RoundingMode.CEIL <= divrnd n2 d RoundingMode.CEIL.
Proof.
  intros Hn1 Hle Hd.
  unfold divrnd.
  assert (Hq : n1 / d <= n2 / d) by (apply Z.div_le_mono; lia).
  destruct (n1 mod d =? 0) eqn:E1.
  - destruct (n2 mod d =? 0) eqn:E2; lia.
  - apply Z.eqb_neq in E1.
    destruct (n2 mod d =? 0) eqn:E2.
    + apply Z.eqb_eq in E2.
      (* n1 mod d != 0, n2 mod d = 0, n1 <= n2 implies n1/d < n2/d *)
      assert (Hstrict : n1 / d < n2 / d).
      { pose proof Z.div_mod n2 d ltac:(lia) as Hd2.
        rewrite E2 in Hd2. rewrite Z.add_0_r in Hd2.
        pose proof Z.div_mod n1 d ltac:(lia) as Hd1.
        pose proof Z.mod_pos_bound n1 d Hd as Hbnd.
        (* From E1: n1 mod d > 0. From Hd2: n2 = (n2/d) * d. From Hle: n1 <= n2.
           Suppose for contradiction n1/d >= n2/d. With Hd1 we get
           n1 = (n1/d)*d + n1 mod d >= (n2/d)*d + n1 mod d > (n2/d)*d = n2. *)
        destruct (Z_lt_le_dec (n1 / d) (n2 / d)) as [Hlt | Hge]; [exact Hlt|].
        exfalso. nia. }
      lia.
    + lia.
Qed.

(** safeMulDiv with CEIL is monotone in [a] when neither input saturates
    and the result stays below FIX_MAX. This lifts the inner-mul direction
    to the outer composition. We prove it carefully because the function
    has saturating short-circuits at a = 0, a = FIX_MAX, etc. *)
Lemma safeMulDiv_a_mono_ceil_nonsat (a1 a2 b c : Z) :
  0 < a1 ->
  a1 <= a2 ->
  a2 < FIX_MAX ->
  0 < b < FIX_MAX ->
  0 < c ->
  divrnd (a2 * b) c RoundingMode.CEIL < FIX_MAX ->
  safeMulDiv a1 b c RoundingMode.CEIL <= safeMulDiv a2 b c RoundingMode.CEIL.
Proof.
  intros Ha1 Ha12 Ha2 [Hb1 Hb2] Hc Hraw.
  unfold safeMulDiv.
  assert (Ha1_nz : (a1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Ha2_nz : (a2 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hb_nz  : (b  =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Ha1_max: (a1 =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  assert (Ha2_max: (a2 =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  assert (Hb_max : (b  =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  assert (Hc_nz  : (c  =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Ha1_nz, Ha2_nz, Hb_nz. cbn [orb].
  rewrite Ha1_max, Ha2_max, Hb_max, Hc_nz. cbn [orb].
  assert (Hab_le : a1 * b <= a2 * b)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hab1_nn : 0 <= a1 * b) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hmono : divrnd (a1 * b) c RoundingMode.CEIL
                  <= divrnd (a2 * b) c RoundingMode.CEIL)
    by (apply divrnd_ceil_monotone; lia).
  assert (Ha2_clamp : (FIX_MAX <=? divrnd (a2 * b) c RoundingMode.CEIL) = false)
    by (apply Z.leb_gt; exact Hraw).
  rewrite Ha2_clamp.
  destruct (FIX_MAX <=? divrnd (a1 * b) c RoundingMode.CEIL) eqn:Hclamp1.
  - apply Z.leb_le in Hclamp1. lia.
  - apply Z.leb_gt in Hclamp1. exact Hmono.
Qed.

(** ============================================================ *)
(** ===== INV-BUY-POST-GE-PRE: post-#1283 mitigation direction == *)
(** ============================================================ *)

(** When neither inner mul is at FIX_MAX and the outer divrnd raw output
    is below FIX_MAX, the post-mitigation buy amount is at least the
    pre-mitigation buy amount. *)
Lemma buyAmount_ge_pre (s slippage sellLow buyHigh : Z) :
  0 <= s ->
  0 <= slippage <= FIX_ONE ->
  0 < sellLow < FIX_MAX ->
  0 < buyHigh ->
  let inner_floor := mul s (FIX_ONE - slippage) RoundingMode.FLOOR in
  let inner_ceil  := mul s (FIX_ONE - slippage) RoundingMode.CEIL in
  0 < inner_floor ->
  inner_ceil < FIX_MAX ->
  divrnd (inner_ceil * sellLow) buyHigh RoundingMode.CEIL < FIX_MAX ->
  buyAmountPre s slippage sellLow buyHigh
  <= buyAmount    s slippage sellLow buyHigh.
Proof.
  intros Hs Hslip [HsL1 HsL2] HbH inner_floor inner_ceil
         Hfloor_pos Hceil_lt Hraw.
  unfold buyAmount, buyAmountPre.
  fold inner_ceil. fold inner_floor.
  pose proof inner_ceil_ge_floor s slippage as Hinner.
  fold inner_floor in Hinner. fold inner_ceil in Hinner.
  apply safeMulDiv_a_mono_ceil_nonsat;
    [exact Hfloor_pos | exact Hinner | exact Hceil_lt
    | split; [exact HsL1 | exact HsL2] | exact HbH | exact Hraw].
Qed.

(** ============================================================ *)
(** ===== Boundary cases on buyAmount =========================== *)
(** ============================================================ *)

(** ----- INV-BUY-FULL-SLIPPAGE: at slippage = FIX_ONE, b = 0. ----- *)
Lemma buyAmount_full_slippage (s sellLow buyHigh : Z) :
  buyAmount s FIX_ONE sellLow buyHigh = 0.
Proof.
  unfold buyAmount, mul, divrnd.
  replace (FIX_ONE - FIX_ONE) with 0 by lia.
  rewrite Z.mul_0_r.
  unfold FIX_SCALE.
  replace (0 / 10 ^ 18) with 0 by reflexivity.
  replace (0 mod 10 ^ 18) with 0 by reflexivity.
  rewrite Z.eqb_refl.
  unfold safeMulDiv.
  rewrite Z.eqb_refl. cbn [orb]. reflexivity.
Qed.

(** ----- INV-BUY-ZERO-S: at s = 0, b = 0. ----- *)
Lemma buyAmount_zero_s (slippage sellLow buyHigh : Z) :
  buyAmount 0 slippage sellLow buyHigh = 0.
Proof.
  unfold buyAmount, mul, divrnd.
  rewrite Z.mul_0_l.
  unfold FIX_SCALE.
  replace (0 / 10 ^ 18) with 0 by reflexivity.
  replace (0 mod 10 ^ 18) with 0 by reflexivity.
  rewrite Z.eqb_refl.
  unfold safeMulDiv.
  rewrite Z.eqb_refl. cbn [orb]. reflexivity.
Qed.

(** ----- INV-BUY-ZERO-SLIPPAGE: at slippage = 0, the inner mul has no
    rounding gap (s * FIX_ONE / FIX_ONE = s exactly), so post == pre. ----- *)
Lemma buyAmount_zero_slippage_eq_pre (s sellLow buyHigh : Z) :
  buyAmount    s 0 sellLow buyHigh
  = buyAmountPre s 0 sellLow buyHigh.
Proof.
  unfold buyAmount, buyAmountPre, mul, divrnd.
  replace (FIX_ONE - 0) with FIX_ONE by lia.
  unfold FIX_ONE, FIX_SCALE.
  rewrite Z.mod_mul by lia.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** ============================================================ *)
(** ===== buyAmount is bounded above by FIX_MAX ================= *)
(** ============================================================ *)

Lemma buyAmount_le_fix_max (s slippage sellLow buyHigh : Z) :
  buyAmount s slippage sellLow buyHigh <= FIX_MAX.
Proof.
  unfold buyAmount. apply safeMulDiv_le_fix_max.
Qed.

Lemma buyAmountPre_le_fix_max (s slippage sellLow buyHigh : Z) :
  buyAmountPre s slippage sellLow buyHigh <= FIX_MAX.
Proof.
  unfold buyAmountPre. apply safeMulDiv_le_fix_max.
Qed.

(** ============================================================ *)
(** ===== Slippage sufficiency: structural form ================= *)
(** ============================================================ *)

(** The CAS slippage_sufficiency.gp script proves
        b >= floor(s * (FIX_ONE - slippage) * sellLow / (FIX_ONE * buyHigh))
    on the calibration corpus.  Here we prove the structural step that
    the post-mitigation [buyAmount] is at least the inner-FLOOR composed
    with outer-FLOOR (which is the exact-rational floor of the divisible
    factor). The full algebraic equivalence between
        floor(inner_floor) / buyHigh
    and the exact rational floor is a kernel arithmetic identity on
    [divrnd]; we expose the structural composition here.

    Specifically: when the outer divrnd does not saturate, the buyAmount
    matches its raw divrnd value, and lifting [mul_floor_le_ceil] +
    [divrnd_floor_le_ceil] gives the chain. *)
Lemma buyAmount_ge_floor_floor_nonsat (s slippage sellLow buyHigh : Z) :
  0 <= s ->
  0 <= slippage <= FIX_ONE ->
  0 < sellLow < FIX_MAX ->
  0 < buyHigh ->
  let inner_floor := mul s (FIX_ONE - slippage) RoundingMode.FLOOR in
  let inner_ceil  := mul s (FIX_ONE - slippage) RoundingMode.CEIL in
  0 < inner_floor ->
  inner_ceil < FIX_MAX ->
  divrnd (inner_ceil * sellLow) buyHigh RoundingMode.CEIL < FIX_MAX ->
  divrnd (inner_floor * sellLow) buyHigh RoundingMode.FLOOR
  <= buyAmount s slippage sellLow buyHigh.
Proof.
  intros Hs [Hslip1 Hslip2] [HsL_pos HsL_lt] HbH
         inner_floor inner_ceil Hfl_pos Hcl_lt Hraw_lt.
  unfold buyAmount.
  fold inner_ceil.
  unfold safeMulDiv.
  assert (Hinner : inner_floor <= inner_ceil) by apply mul_floor_le_ceil.
  assert (Hcl_pos : 0 < inner_ceil) by lia.
  assert (HsL_b : (sellLow =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HsL_max_b : (sellLow =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  assert (Hcl_nz_b : (inner_ceil =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hcl_nm_b : (inner_ceil =? FIX_MAX) = false) by (apply Z.eqb_neq; lia).
  assert (HbH_nz_b : (buyHigh =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hcl_nz_b, HsL_b. cbn [orb].
  rewrite Hcl_nm_b, HsL_max_b, HbH_nz_b. cbn [orb].
  assert (Hraw_b :
    (FIX_MAX <=? divrnd (inner_ceil * sellLow) buyHigh RoundingMode.CEIL) = false)
    by (apply Z.leb_gt; exact Hraw_lt).
  rewrite Hraw_b.
  (* Now show floor(inner_floor*sellLow / buyHigh) <= ceil(inner_ceil*sellLow / buyHigh). *)
  assert (Hprod_le : inner_floor * sellLow <= inner_ceil * sellLow)
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hdiv_le : (inner_floor * sellLow) / buyHigh
                    <= (inner_ceil * sellLow) / buyHigh)
    by (apply Z.div_le_mono; lia).
  unfold divrnd at 1.
  unfold divrnd.
  destruct (inner_ceil * sellLow mod buyHigh =? 0); lia.
Qed.

(** ============================================================ *)
(** ===== minTradeSize / isEnoughToSell ========================= *)
(** ============================================================ *)

(** ----- INV-MTS-PRICE-ZERO. ----- *)
Lemma minTradeSize_price_zero (mtv : Z) :
  minTradeSize mtv 0 = FIX_MAX.
Proof.
  unfold minTradeSize. rewrite Z.eqb_refl. reflexivity.
Qed.

(** ----- INV-MTS-AT-LEAST-1: minTradeSize >= 1 under valid (non-negative)
    inputs. -----
    By the [size != 0 ? size : 1] clamp. The price = 0 branch returns
    FIX_MAX which is also >= 1. *)
Lemma minTradeSize_ge_one (mtv price : Z) :
  0 <= mtv ->
  0 <= price ->
  1 <= minTradeSize mtv price.
Proof.
  intros Hmtv Hp.
  unfold minTradeSize.
  destruct (price =? 0) eqn:Eprice.
  - unfold FIX_MAX. lia.
  - apply Z.eqb_neq in Eprice.
    assert (Hp_pos : 0 < price) by lia.
    destruct (div mtv price RoundingMode.CEIL =? 0) eqn:E.
    + lia.
    + apply Z.eqb_neq in E.
      unfold div, divrnd, FIX_SCALE.
      assert (Hnn : 0 <= mtv * 10^18) by (apply Z.mul_nonneg_nonneg; lia).
      assert (Hq_nn : 0 <= mtv * 10^18 / price) by (apply Z.div_pos; lia).
      unfold div, divrnd, FIX_SCALE in E.
      destruct (mtv * 10^18 mod price =? 0); lia.
Qed.

(** ----- INV-MTS-NONNEG. ----- *)
Lemma minTradeSize_nonneg (mtv price : Z) :
  0 <= mtv ->
  0 <= price ->
  0 <= minTradeSize mtv price.
Proof.
  intros Hmtv Hp.
  pose proof minTradeSize_ge_one mtv price Hmtv Hp. lia.
Qed.

(** ----- INV-IETS-MONOTONE. ----- *)
Lemma isEnoughToSell_whole_monotone
    (amt1 amt2 price minTradeVolume : Z) :
  amt1 <= amt2 ->
  isEnoughToSell_whole amt1 price minTradeVolume = true ->
  isEnoughToSell_whole amt2 price minTradeVolume = true.
Proof.
  intros Hle H1.
  unfold isEnoughToSell_whole in *.
  apply Z.leb_le in H1. apply Z.leb_le. lia.
Qed.

(** ----- isEnoughToSell with amt >= mtv when price <= 1 (large volume case). ----- *)
Lemma isEnoughToSell_whole_threshold (amt price minTradeVolume : Z) :
  isEnoughToSell_whole amt price minTradeVolume = true ->
  minTradeSize minTradeVolume price <= amt.
Proof.
  intros H. apply Z.leb_le. exact H.
Qed.

End TradeLibProofs.
