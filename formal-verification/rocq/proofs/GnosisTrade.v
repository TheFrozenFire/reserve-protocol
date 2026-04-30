(** GnosisTrade simulation invariant proofs.

    Proves the load-bearing safety properties on the [GnosisTrade]
    simulation defined in [Reserve.simulations.GnosisTrade]:

      INV-MBA-MONO   minBuyAmount is non-increasing in [slippage]
                     (more slippage tolerance => lower required floor).
      INV-MBA-LE-PAR minBuyAmount <= ceil(sellAmount * sellLow / buyHigh)
                     (decimal-shifted) — the CEIL chain never exceeds the
                     zero-slippage exact ceiling.
      INV-MBA-NONNEG minBuyAmount is non-negative when inputs are.
      INV-WCP-NONNEG worstCasePrice is non-negative.
      INV-WCP-FLOOR  worstCasePrice <= ceil-numerator / sellAmount, no
                     overshoot from FLOOR division.
      INV-SETTLE-NV  settle() with sellBalAfter >= initBal returns the
                     no-violation, no-check sentinel.
      INV-SETTLE-CONS  settle().soldAmt + sellBalAfter = initBal
                       (when checked).
      INV-SF-NONNEG  settlement_floor >= 0.
      INV-SF-MONO    settlement_floor is monotone non-decreasing in
                     worstCasePrice.
      INV-CANSETTLE  canSettle flips at endTime (<=, not <).

    These invariants document the contract's intended trader-protection
    semantics, propagated to the on-chain code through the eventual
    [run_settle] equivalence lemma.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.simulations.GnosisTrade.
Require Import Coq.Bool.Bool.

Module GnosisTradeProofs.

Import FixLib.
Import FixLibProofs.
Import GnosisTrade.

(** ===== INV-MBA-MONO: more slippage => smaller minBuyAmount. =====

    All three steps in the [minBuyAmount] chain are monotone non-decreasing
    in [(FIX_ONE - slippage)]: increasing slippage shrinks that factor and
    therefore shrinks each composed step.
*)

(** Helper: divrnd with CEIL is monotone non-decreasing in the numerator
    when the denominator is positive. *)
Lemma divrnd_ceil_mono_numerator (n1 n2 d : Z) :
  0 < d ->
  n1 <= n2 ->
  divrnd n1 d RoundingMode.CEIL <= divrnd n2 d RoundingMode.CEIL.
Proof.
  intros Hd Hle.
  rewrite !divrnd_ceil_eq by exact Hd.
  set (q1 := n1 / d). set (r1 := n1 mod d).
  set (q2 := n2 / d). set (r2 := n2 mod d).
  assert (Hq : q1 <= q2) by (apply Z.div_le_mono; lia).
  assert (Hr1 : 0 <= r1 < d) by (apply Z.mod_pos_bound; exact Hd).
  assert (Hr2 : 0 <= r2 < d) by (apply Z.mod_pos_bound; exact Hd).
  assert (Hn1 : n1 = q1 * d + r1).
  { unfold q1, r1.
    pose proof (Z.div_mod n1 d ltac:(lia)) as Heq.
    lia. }
  assert (Hn2 : n2 = q2 * d + r2).
  { unfold q2, r2.
    pose proof (Z.div_mod n2 d ltac:(lia)) as Heq.
    lia. }
  destruct (r1 =? 0) eqn:H1; destruct (r2 =? 0) eqn:H2.
  - lia.
  - lia.
  - (* (false, true): the hard case.  q1 + 1 vs q2.  *)
    apply Z.eqb_neq in H1. apply Z.eqb_eq in H2.
    nia.
  - lia.
Qed.

(** Helper: mul x y CEIL is monotone non-decreasing in y when x >= 0. *)
Lemma mul_ceil_mono_right (x y1 y2 : Z) :
  0 <= x ->
  y1 <= y2 ->
  mul x y1 RoundingMode.CEIL <= mul x y2 RoundingMode.CEIL.
Proof.
  intros Hx Hy. unfold mul.
  apply divrnd_ceil_mono_numerator.
  - unfold FIX_SCALE. lia.
  - apply Z.mul_le_mono_nonneg_l; assumption.
Qed.

(** Helper: divrnd CEIL with non-negative numerator and positive denominator
    yields a non-negative result. *)
Lemma divrnd_ceil_nonneg (n d : Z) :
  0 < d ->
  0 <= n ->
  0 <= divrnd n d RoundingMode.CEIL.
Proof.
  intros Hd Hn.
  rewrite divrnd_ceil_eq by exact Hd.
  assert (Hq : 0 <= n / d) by (apply Z.div_pos; lia).
  destruct (n mod d =? 0); lia.
Qed.

(** Helper: safeMulDiv_ceil monotone in [a] when b, c, a all >= 0 and c > 0. *)
Lemma safeMulDiv_ceil_mono_left (a1 a2 b c : Z) :
  0 < c ->
  0 <= b ->
  0 <= a1 ->
  a1 <= a2 ->
  safeMulDiv_ceil a1 b c <= safeMulDiv_ceil a2 b c.
Proof.
  intros Hc Hb Ha1 Ha12.
  unfold safeMulDiv_ceil.
  assert (Hcz : (c =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hcz.
  (* Goal forms (right hand side of each = 0 sentinel or divrnd CEIL ...):
       lhs: if andb (a1 =? 0) (b =? 0) then 0 else divrnd (a1*b) c CEIL
       rhs: if andb (a2 =? 0) (b =? 0) then 0 else divrnd (a2*b) c CEIL
     Cases:
       LHS = 0: a1 = 0 and b = 0  -> rhs >= 0
       LHS = divrnd: at least one of a1, b non-zero
         RHS = 0: a2 = 0 and b = 0 -> a1 = 0 too (since a1 <= a2 <= 0
                  combined with Ha1) so contradicts non-zero a1; and b = 0
                  forces a1 * b = 0 so divrnd = 0 = RHS — easy.
         RHS = divrnd: monotone numerator. *)
  assert (Ha2 : 0 <= a2) by lia.
  destruct (andb (a1 =? 0) (b =? 0)) eqn:HL.
  - (* LHS = 0; RHS = divrnd OR 0. Either way >= 0. *)
    destruct (andb (a2 =? 0) (b =? 0)); [lia|].
    apply divrnd_ceil_nonneg; [exact Hc|].
    apply Z.mul_nonneg_nonneg; assumption.
  - destruct (andb (a2 =? 0) (b =? 0)) eqn:HR.
    + (* LHS = divrnd (a1*b)/c CEIL,  RHS = 0.
         HR -> a2 = 0 and b = 0. a1 = 0 too (Ha1, a1<=a2=0). Then a1*b = 0,
         so divrnd 0 c CEIL = 0. *)
      apply andb_true_iff in HR. destruct HR as [HRa HRb].
      apply Z.eqb_eq in HRa. apply Z.eqb_eq in HRb. subst.
      assert (Ha1z : a1 = 0) by lia. subst.
      rewrite Z.mul_0_l.
      rewrite divrnd_ceil_eq by exact Hc.
      rewrite Z.div_0_l, Z.mod_0_l by lia. cbn. lia.
    + apply divrnd_ceil_mono_numerator; [exact Hc|].
      apply Z.mul_le_mono_nonneg_r; assumption.
Qed.

(** Helper: shiftl_toUint_ceil is monotone non-decreasing in x when x >= 0. *)
Lemma shiftl_toUint_ceil_mono (x1 x2 d : Z) :
  0 <= x1 ->
  x1 <= x2 ->
  shiftl_toUint_ceil x1 d <= shiftl_toUint_ceil x2 d.
Proof.
  intros Hx1 Hxx. unfold shiftl_toUint_ceil.
  destruct (0 <=? 18 - d) eqn:Hsh.
  - apply divrnd_ceil_mono_numerator; [|exact Hxx].
    apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_le_mono_nonneg_r; [|exact Hxx].
    apply Z.pow_nonneg. lia.
Qed.

(** ----- INV-MBA-MONO: as slippage increases, minBuyAmount weakly decreases.
    Stated as: slippage1 <= slippage2 ==> mba(slippage2) <= mba(slippage1).
    More permissive (larger) slippage => lower minBuy floor. *)
Lemma minBuyAmount_monotone_in_slippage
    (sellAmount slippage1 slippage2 sellLow buyHigh : Z) (buyDec : Z) :
  0 <= sellAmount ->
  0 <= sellLow ->
  0 < buyHigh ->
  slippage1 <= slippage2 ->
  slippage2 <= FIX_ONE ->
  minBuyAmount sellAmount slippage2 sellLow buyHigh buyDec
    <= minBuyAmount sellAmount slippage1 sellLow buyHigh buyDec.
Proof.
  intros Hsa Hslo Hbhi Hslip Hslip_hi.
  unfold minBuyAmount.
  set (inner1 := mul sellAmount (minus FIX_ONE slippage1) RoundingMode.CEIL).
  set (inner2 := mul sellAmount (minus FIX_ONE slippage2) RoundingMode.CEIL).
  assert (Hinner : inner2 <= inner1).
  { unfold inner1, inner2. apply mul_ceil_mono_right; [exact Hsa|].
    unfold minus. lia. }
  assert (Hinner_nn : 0 <= inner2).
  { unfold inner2, mul.
    apply divrnd_ceil_nonneg; [unfold FIX_SCALE; lia|].
    apply Z.mul_nonneg_nonneg; [exact Hsa|]. unfold minus. lia. }
  apply shiftl_toUint_ceil_mono.
  - unfold safeMulDiv_ceil.
    assert (Hcz : (buyHigh =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hcz.
    destruct (andb _ _) eqn:Hzero; [lia|].
    rewrite divrnd_ceil_eq by exact Hbhi.
    set (q := inner2 * sellLow / buyHigh).
    set (r := inner2 * sellLow mod buyHigh).
    assert (Hr : 0 <= r < buyHigh) by (apply Z.mod_pos_bound; exact Hbhi).
    assert (Hq : 0 <= q).
    { unfold q. apply Z.div_pos; [|exact Hbhi].
      apply Z.mul_nonneg_nonneg; assumption. }
    destruct (r =? 0); lia.
  - apply safeMulDiv_ceil_mono_left; [exact Hbhi|exact Hslo|exact Hinner_nn|exact Hinner].
Qed.

(** ===== INV-MBA-LE-PAR: minBuyAmount <= zero-slippage ceiling. =====

    With slippage = 0, the inner step is exactly sellAmount (a CEIL of an
    exact division), so the chain reduces to ceil(sellAmount * sellLow /
    buyHigh) (decimal-shifted). For positive slippage, monotonicity in the
    inner factor pushes minBuyAmount strictly below that ceiling.
*)

(** Zero-slippage inner step is exactly sellAmount (sellAmount * FIX_ONE / FIX_ONE,
    no remainder). *)
Lemma inner_zero_slippage (sellAmount : Z) :
  0 <= sellAmount ->
  mul sellAmount (minus FIX_ONE 0) RoundingMode.CEIL = sellAmount.
Proof.
  intros Hsa. unfold mul, minus.
  rewrite Z.sub_0_r.
  rewrite divrnd_ceil_eq by (unfold FIX_SCALE; lia).
  unfold FIX_ONE, FIX_SCALE.
  rewrite Z.div_mul by lia.
  rewrite Z_mod_mult.
  cbn. lia.
Qed.

(** INV-MBA-LE-PAR specialized: minBuyAmount with any slippage <=
    minBuyAmount with zero slippage. *)
Lemma minBuyAmount_le_par
    (sellAmount slippage sellLow buyHigh : Z) (buyDec : Z) :
  0 <= sellAmount ->
  0 <= sellLow ->
  0 < buyHigh ->
  0 <= slippage ->
  slippage <= FIX_ONE ->
  minBuyAmount sellAmount slippage sellLow buyHigh buyDec
    <= minBuyAmount sellAmount 0 sellLow buyHigh buyDec.
Proof.
  intros Hsa Hslo Hbhi Hslip Hhi.
  apply minBuyAmount_monotone_in_slippage; assumption.
Qed.

(** Sharper: minBuyAmount at zero slippage equals the decimal-lifted
    ceil(sellAmount * sellLow / buyHigh). *)
Lemma minBuyAmount_zero_slippage_eq
    (sellAmount sellLow buyHigh : Z) (buyDec : Z) :
  0 <= sellAmount ->
  minBuyAmount sellAmount 0 sellLow buyHigh buyDec =
  shiftl_toUint_ceil (safeMulDiv_ceil sellAmount sellLow buyHigh) buyDec.
Proof.
  intros Hsa. unfold minBuyAmount.
  rewrite (inner_zero_slippage sellAmount Hsa).
  reflexivity.
Qed.

(** ===== INV-MBA-NONNEG ===== *)
Lemma minBuyAmount_nonneg
    (sellAmount slippage sellLow buyHigh : Z) (buyDec : Z) :
  0 <= sellAmount ->
  0 <= sellLow ->
  0 < buyHigh ->
  slippage <= FIX_ONE ->
  0 <= minBuyAmount sellAmount slippage sellLow buyHigh buyDec.
Proof.
  intros Hsa Hslo Hbhi Hslip.
  unfold minBuyAmount.
  set (inner := mul sellAmount (minus FIX_ONE slippage) RoundingMode.CEIL).
  assert (Hinner_nn : 0 <= inner).
  { unfold inner, mul.
    apply divrnd_ceil_nonneg; [unfold FIX_SCALE; lia|].
    apply Z.mul_nonneg_nonneg; [exact Hsa|]. unfold minus. lia. }
  set (b := safeMulDiv_ceil inner sellLow buyHigh).
  assert (Hb_nn : 0 <= b).
  { unfold b, safeMulDiv_ceil.
    assert (Hcz : (buyHigh =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hcz.
    destruct (andb _ _); [lia|].
    apply divrnd_ceil_nonneg; [exact Hbhi|].
    apply Z.mul_nonneg_nonneg; assumption. }
  unfold shiftl_toUint_ceil.
  destruct (0 <=? 18 - buyDec) eqn:Hsh.
  - apply Z.leb_le in Hsh.
    apply divrnd_ceil_nonneg; [|exact Hb_nn].
    apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg; [exact Hb_nn|].
    apply Z.pow_nonneg; lia.
Qed.

(** ===== INV-WCP-NONNEG ===== *)
Lemma worstCasePrice_nonneg
    (mba sa : Z) :
  0 <= mba ->
  0 <= sa ->
  0 <= worstCasePrice mba sa.
Proof.
  intros Hmba Hsa. unfold worstCasePrice.
  destruct (sa =? 0) eqn:Hzero; [lia|].
  apply Z.eqb_neq in Hzero.
  rewrite divrnd_floor_eq.
  apply Z.div_pos.
  - unfold shiftl_toFix_d27. apply Z.mul_nonneg_nonneg; [exact Hmba|]. lia.
  - lia.
Qed.

(** ===== INV-WCP-FLOOR: worstCasePrice = floor(mba*1e27 / sa). =====

    Documents that the divu FLOOR rounds *down*, so the on-chain
    floor is no greater than the exact rational. *)
Lemma worstCasePrice_floor_bound
    (mba sa : Z) :
  0 < sa ->
  worstCasePrice mba sa * sa <= mba * D27_ONE.
Proof.
  intros Hsa. unfold worstCasePrice, shiftl_toFix_d27, D27_ONE.
  assert (Hzero : (sa =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hzero.
  rewrite divrnd_floor_eq.
  set (n := mba * 10^27).
  assert (Hn : n = (n / sa) * sa + n mod sa).
  { rewrite Z.mul_comm. apply Z.div_mod. lia. }
  assert (Hr : 0 <= n mod sa < sa) by (apply Z.mod_pos_bound; exact Hsa).
  lia.
Qed.

(** ===== INV-SETTLE-NV ===== *)
Lemma settle_no_check_when_full_return
    (initBal sellBalAfter boughtAmt worstCase : Z) :
  initBal <= sellBalAfter ->
  let r := settle initBal sellBalAfter boughtAmt worstCase in
  r.(SettleResult.violation) = false /\
  r.(SettleResult.checked) = false /\
  r.(SettleResult.soldAmt) = 0 /\
  r.(SettleResult.clearingPrice) = 0.
Proof.
  intros Hge. cbv zeta.
  unfold settle.
  assert (Hcond : (initBal <=? sellBalAfter) = true) by (apply Z.leb_le; exact Hge).
  rewrite Hcond. cbn. repeat split.
Qed.

(** ===== INV-SETTLE-CONS: when checked, soldAmt + sellBalAfter = initBal. ===== *)
Lemma settle_conservation
    (initBal sellBalAfter boughtAmt worstCase : Z) :
  let r := settle initBal sellBalAfter boughtAmt worstCase in
  r.(SettleResult.checked) = true ->
  r.(SettleResult.soldAmt) + sellBalAfter = initBal.
Proof.
  cbv zeta. unfold settle.
  destruct (initBal <=? sellBalAfter) eqn:Hcond.
  - cbn. intros Hf. discriminate.
  - cbn. intros _. apply Z.leb_gt in Hcond. lia.
Qed.

(** ===== INV-SETTLE-CLEARING: full-fill at exactly minBuyAmount keeps
    clearingPrice >= worstCasePrice (no violation). =====

    The +1 pad in [adjustedBuyAmt = boughtAmt + 1] absorbs at least 1
    wei of Gnosis-side defensive rounding. Specifically, when boughtAmt
    + 1 = adjustedBuyAmt and soldAmt > 0,
      clearingPrice = floor((boughtAmt+1) * 1e27 / soldAmt)
    is computed against the same FLOOR semantics as worstCasePrice,
    so equality is achieved when (boughtAmt+1)/sa = mba/sa exactly,
    i.e. when boughtAmt = mba - 1 (the pad re-shifts the boundary by 1). *)

(** Settlement-floor monotonicity: a higher worstCasePrice imposes a
    higher minimum boughtAmt. *)
Lemma settlement_floor_mono_in_wcp
    (wcp1 wcp2 soldAmt : Z) :
  0 <= wcp1 <= wcp2 ->
  settlement_floor wcp1 soldAmt <= settlement_floor wcp2 soldAmt.
Proof.
  intros [H1 H2]. unfold settlement_floor.
  set (adj := Z.max soldAmt 1).
  assert (Hadj : 1 <= adj) by (unfold adj; lia).
  set (raw1 := divrnd (wcp1 * adj) D27_ONE RoundingMode.CEIL - 1).
  set (raw2 := divrnd (wcp2 * adj) D27_ONE RoundingMode.CEIL - 1).
  assert (Hraw : raw1 <= raw2).
  { unfold raw1, raw2.
    apply Z.sub_le_mono_r.
    apply divrnd_ceil_mono_numerator.
    - unfold D27_ONE. lia.
    - apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

(** ===== INV-SF-NONNEG ===== *)
Lemma settlement_floor_nonneg (worstCase soldAmt : Z) :
  0 <= settlement_floor worstCase soldAmt.
Proof.
  unfold settlement_floor. lia.
Qed.

(** ===== INV-CANSETTLE: canSettle flips inclusively at endTime. ===== *)
Lemma canSettle_at_endTime (endTime : Z) :
  canSettle endTime endTime true = true.
Proof.
  unfold canSettle. cbn. apply Z.leb_le. lia.
Qed.

Lemma canSettle_before_endTime (now endTime : Z) :
  now < endTime ->
  canSettle now endTime true = false.
Proof.
  intros Hlt. unfold canSettle. cbn.
  apply Z.leb_gt. exact Hlt.
Qed.

Lemma canSettle_status_closed (now endTime : Z) :
  canSettle now endTime false = false.
Proof.
  unfold canSettle. reflexivity.
Qed.

(** ===== Cancellation window: cancellationEndTime - startTime is exactly
    auctionLength * 0.9 (rounded down). ===== *)
Lemma cancellationEndTime_offset (startTime auctionLength : Z) :
  cancellationEndTime startTime auctionLength - startTime
  = (auctionLength * CANCEL_WINDOW) / FIX_ONE.
Proof.
  unfold cancellationEndTime. lia.
Qed.

End GnosisTradeProofs.
