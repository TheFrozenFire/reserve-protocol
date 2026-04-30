(** BackingManager simulation invariant proofs.

    Proves the load-bearing safety invariants on [BackingManager]:

      INV-MINT-0     mintAmount = 0 and basketsNeeded unchanged when the
                     held floor basketsHeldBottom / (FIX_ONE+buf) <= basketsNeeded
      INV-MINT-DIFF  mintAmount = baskets - basketsNeeded when baskets > basketsNeeded
      INV-NEEDED-CEIL needed >= floor(basketsNeeded' * (FIX_ONE+buf) / FIX_ONE)
                       (CEIL never under-charges; the post-#1283 invariant)
      INV-NEEDED-CEIL-FLOOR_BOUND needed <= floor(...) + 1
                       (CEIL is at most 1 wei above FLOOR)
      INV-BUF-ZERO   needed = basketsNeeded' when backingBuffer = 0  (CEIL no-op)

    Surplus split (per-asset forward-revenue distribution):
      INV-SS-LE-NO-SPLIT    bal <= req  =>  all outputs are 0
      INV-SS-CONSERVATION   rsrAmount + rTokenAmount + dust = delta
      INV-SS-DUST-BOUND     0 <= dust <= delta
      INV-SS-TPS-ZERO       tokensPerShare = 0  =>  rsr = rTok = 0, dust = delta

    Avoid [simpl] inside these proofs — the FixLib operations contain large
    numeric literals (FIX_ONE = 10^18) that explode under [simpl].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Coq.Bool.Bool.

Module BackingManagerProofs.

Import FixLib.
Import BackingManager.

(** ----- INV-MINT-0a: mintAmount = 0 below threshold. ----- *)
Lemma mintAmount_zero_when_below_threshold
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  baskets <= basketsNeeded ->
  (computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
    .(BasketState.mintAmount) = 0.
Proof.
  intros baskets Hle.
  unfold computeNewBasketsAndNeeded, BasketState.mintAmount.
  fold baskets.
  destruct (basketsNeeded <? baskets) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

(** ----- INV-MINT-0b: basketsNeeded unchanged below threshold. ----- *)
Lemma basketsNeeded_unchanged_when_below_threshold
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  baskets <= basketsNeeded ->
  (computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
    .(BasketState.basketsNeeded) = basketsNeeded.
Proof.
  intros baskets Hle.
  unfold computeNewBasketsAndNeeded, BasketState.basketsNeeded.
  fold baskets.
  destruct (basketsNeeded <? baskets) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

(** ----- INV-MINT-DIFFa: mintAmount = baskets - basketsNeeded above threshold. ----- *)
Lemma mintAmount_eq_diff_when_above_threshold
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  basketsNeeded < baskets ->
  (computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
    .(BasketState.mintAmount) = baskets - basketsNeeded.
Proof.
  intros baskets Hgt.
  unfold computeNewBasketsAndNeeded, BasketState.mintAmount.
  fold baskets.
  assert (Hlt : (basketsNeeded <? baskets) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt. reflexivity.
Qed.

(** ----- INV-MINT-DIFFb: basketsNeeded = baskets above threshold. ----- *)
Lemma basketsNeeded_eq_baskets_when_above_threshold
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  basketsNeeded < baskets ->
  (computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
    .(BasketState.basketsNeeded) = baskets.
Proof.
  intros baskets Hgt.
  unfold computeNewBasketsAndNeeded, BasketState.basketsNeeded.
  fold baskets.
  assert (Hlt : (basketsNeeded <? baskets) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt. reflexivity.
Qed.

(** ----- Helper: needed = mul basketsNeeded' (FIX_ONE + buf) CEIL. ----- *)
Lemma needed_eq_mul_ceil
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  (computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
    .(BasketState.needed)
  = FixLib.mul
      ((computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded backingBuffer)
         .(BasketState.basketsNeeded))
      (FIX_ONE + backingBuffer) RoundingMode.CEIL.
Proof.
  unfold computeNewBasketsAndNeeded, BasketState.needed,
         BasketState.basketsNeeded.
  destruct (basketsNeeded <? _); reflexivity.
Qed.

(** ----- needed_uses_ceil_rounding: closed form. -----
    Proved via [needed_eq_mul_ceil] + the kernel definition of CEIL,
    sidestepping the field-name vs argument-name collision. *)
Lemma needed_uses_ceil_rounding
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let st := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded
                                       backingBuffer in
  let n  := st.(BasketState.basketsNeeded) * (FIX_ONE + backingBuffer) in
  st.(BasketState.needed) =
    n / FIX_SCALE + (if n mod FIX_SCALE =? 0 then 0 else 1).
Proof.
  intros st n.
  unfold st. rewrite needed_eq_mul_ceil.
  unfold mul, divrnd.
  unfold n, st.
  destruct (_ mod FIX_SCALE =? 0); lia.
Qed.

(** ----- INV-NEEDED-CEIL: needed >= floor of the exact rational. ----- *)
Lemma needed_ge_floor
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let st := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded
                                       backingBuffer in
  (st.(BasketState.basketsNeeded) * (FIX_ONE + backingBuffer)) / FIX_ONE
  <= st.(BasketState.needed).
Proof.
  intros st. unfold st.
  rewrite needed_eq_mul_ceil.
  unfold mul, divrnd.
  unfold FIX_ONE, FIX_SCALE.
  destruct (_ =? 0); lia.
Qed.

(** ----- INV-NEEDED-CEIL-BOUND: needed <= floor + 1. ----- *)
Lemma needed_le_floor_plus_one
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  let st := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded
                                       backingBuffer in
  st.(BasketState.needed)
  <= (st.(BasketState.basketsNeeded) * (FIX_ONE + backingBuffer)) / FIX_ONE + 1.
Proof.
  intros st. unfold st.
  rewrite needed_eq_mul_ceil.
  unfold mul, divrnd.
  unfold FIX_ONE, FIX_SCALE.
  destruct (_ =? 0); lia.
Qed.

(** ----- INV-BUF-ZERO: at backingBuffer = 0, needed = basketsNeeded'. ----- *)
Lemma needed_at_buffer_zero
    (basketsHeldBottom basketsNeeded : U256.t) :
  let st := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded 0 in
  st.(BasketState.needed) = st.(BasketState.basketsNeeded).
Proof.
  intros st. unfold st.
  rewrite needed_eq_mul_ceil.
  unfold mul, divrnd.
  replace (FIX_ONE + 0) with FIX_SCALE by reflexivity.
  rewrite Z.mod_mul by (unfold FIX_SCALE; lia).
  rewrite Z.eqb_refl.
  rewrite Z.div_mul by (unfold FIX_SCALE; lia).
  lia.
Qed.

(** ----- INV-SS-LE-NO-SPLIT: bal <= req  =>  all outputs are 0. ----- *)
Lemma surplusSplit_bal_le_req_no_split
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) :
  bal <= FixLib.mul needed quantity RoundingMode.CEIL ->
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 0;
    |}.
Proof.
  intros Hle.
  unfold computeSurplusSplit.
  destruct (bal <=? FixLib.mul needed quantity RoundingMode.CEIL) eqn:Hbal.
  - reflexivity.
  - apply Z.leb_gt in Hbal. lia.
Qed.

(** ----- INV-SS-CONSERVATION: shares + dust = delta. ----- *)
Lemma surplusSplit_conservation
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) (split : SurplusSplit.t) :
  let req   := FixLib.mul needed quantity RoundingMode.CEIL in
  let delta := shiftl_toUint (bal - req) decimals in
  let totalShares := rTokenTotal + rsrTotal in
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
    = Result.Success split ->
  req < bal ->
  0 < totalShares ->
  split.(SurplusSplit.rsrAmount)
  + split.(SurplusSplit.rTokenAmount)
  + split.(SurplusSplit.dust)
  = delta.
Proof.
  intros req delta totalShares Hsucc Hbal Htot.
  unfold computeSurplusSplit in Hsucc. fold req in Hsucc.
  assert (Hle : (bal <=? req) = false) by (apply Z.leb_gt; lia).
  rewrite Hle in Hsucc. fold delta in Hsucc. fold totalShares in Hsucc.
  assert (Htot' : (totalShares =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Htot' in Hsucc.
  destruct (delta / totalShares =? 0) eqn:Htps;
    inversion Hsucc; subst;
    unfold SurplusSplit.rsrAmount, SurplusSplit.rTokenAmount, SurplusSplit.dust;
    lia.
Qed.

(** ----- INV-SS-DUST-BOUND: 0 <= dust <= delta. ----- *)
Lemma surplusSplit_dust_bound
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) (split : SurplusSplit.t) :
  let req   := FixLib.mul needed quantity RoundingMode.CEIL in
  let delta := shiftl_toUint (bal - req) decimals in
  let totalShares := rTokenTotal + rsrTotal in
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
    = Result.Success split ->
  req < bal ->
  0 < totalShares ->
  0 <= delta ->
  0 <= split.(SurplusSplit.dust) <= delta.
Proof.
  intros req delta totalShares Hsucc Hbal Htot Hdelta.
  unfold computeSurplusSplit in Hsucc. fold req in Hsucc.
  assert (Hle : (bal <=? req) = false) by (apply Z.leb_gt; lia).
  rewrite Hle in Hsucc. fold delta in Hsucc. fold totalShares in Hsucc.
  assert (Htot' : (totalShares =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Htot' in Hsucc.
  set (tps := delta / totalShares) in Hsucc.
  destruct (tps =? 0) eqn:Htps.
  - inversion Hsucc; subst;
    unfold SurplusSplit.dust; lia.
  - inversion Hsucc; subst.
    unfold SurplusSplit.dust.
    assert (Htps_ge : 0 <= tps) by (unfold tps; apply Z.div_pos; lia).
    assert (Htps_mul : tps * totalShares <= delta).
    { unfold tps.
      rewrite Z.mul_comm.
      apply Z.mul_div_le. exact Htot. }
    assert (Hsum : tps * rsrTotal + tps * rTokenTotal = tps * totalShares).
    { unfold totalShares. ring. }
    split; lia.
Qed.

(** ----- INV-SS-TPS-ZERO: tokensPerShare = 0 path. ----- *)
Lemma surplusSplit_tps_zero_dust_eq_delta
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) (split : SurplusSplit.t) :
  let req   := FixLib.mul needed quantity RoundingMode.CEIL in
  let delta := shiftl_toUint (bal - req) decimals in
  let totalShares := rTokenTotal + rsrTotal in
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
    = Result.Success split ->
  req < bal ->
  0 < totalShares ->
  delta < totalShares ->
  0 <= delta ->
  split.(SurplusSplit.rsrAmount) = 0 /\
  split.(SurplusSplit.rTokenAmount) = 0 /\
  split.(SurplusSplit.dust) = delta.
Proof.
  intros req delta totalShares Hsucc Hbal Htot Hdelta_lt Hdelta_ge.
  unfold computeSurplusSplit in Hsucc. fold req in Hsucc.
  assert (Hle : (bal <=? req) = false) by (apply Z.leb_gt; lia).
  rewrite Hle in Hsucc. fold delta in Hsucc. fold totalShares in Hsucc.
  assert (Htot' : (totalShares =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Htot' in Hsucc.
  assert (Htps_zero : delta / totalShares = 0)
    by (apply Z.div_small; lia).
  rewrite Htps_zero in Hsucc.
  rewrite Z.eqb_refl in Hsucc.
  inversion Hsucc; subst.
  repeat split; reflexivity.
Qed.

(** ----- Revert path: totalShares = 0 reverts. ----- *)
Lemma surplusSplit_zero_totalShares_reverts
    (needed quantity bal : U256.t) (decimals : Z) :
  FixLib.mul needed quantity RoundingMode.CEIL < bal ->
  exists ps qs,
    computeSurplusSplit needed quantity bal decimals 0 0
    = Result.Revert ps qs.
Proof.
  intros Hbal.
  unfold computeSurplusSplit.
  assert (Hle : (bal <=? FixLib.mul needed quantity RoundingMode.CEIL) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hle.
  exists 0. exists 32. reflexivity.
Qed.

End BackingManagerProofs.
