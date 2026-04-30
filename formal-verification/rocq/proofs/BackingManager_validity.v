(** BackingManager output-bound (validity) lemmas.

    Two narrow output-bound invariants on the BackingManager simulation:

      1. [computeNewBasketsAndNeeded_outputs_nonneg] — given the standard
         input validity ([Valid.bufferInputs]), the [mintAmount] and
         [needed] output fields are non-negative.

         These are the "no negative mint, no negative liability" sanity
         bounds — without them, downstream callers (mint paths, basket
         accounting) could see nonsensical values.

      2. [computeSurplusSplit_outputs_nonneg] — given a non-negative
         [bal] and non-negative [decimals], every Success-branch output
         of [computeSurplusSplit] is non-negative.

         The [dust] non-negativity is the load-bearing one: it justifies
         that the BackingManager retains a real (uint256-representable)
         remainder rather than going underwater on rounding.

    Both proofs lean on the FixLib round-direction discipline: [divrnd]
    is non-negative whenever its numerator is non-negative and divisor
    is positive, which is the only round-direction fact needed.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Coq.Bool.Bool.

Module BackingManagerValidityProofs.

Import FixLib.
Import BackingManager.

(** Helper: [divrnd n d mode] is non-negative whenever the numerator is
    non-negative and the divisor is positive. *)
Lemma divrnd_nonneg (n d : Z) (mode : RoundingMode.t) :
  0 <= n -> 0 < d -> 0 <= divrnd n d mode.
Proof.
  intros Hn Hd.
  unfold divrnd.
  assert (Hq : 0 <= n / d) by (apply Z.div_pos; [exact Hn|exact Hd]).
  destruct mode.
  - exact Hq.
  - destruct (n mod d >? (d - 1) / 2); lia.
  - destruct (n mod d =? 0); lia.
Qed.

(** Output-bound lemma for [computeNewBasketsAndNeeded]:
    [mintAmount] and [needed] are both non-negative.

    Preconditions: standard [Valid.bufferInputs] — every input fits in
    uint192 (so >= 0), the buffer is at most [MAX_BACKING_BUFFER]. The
    last condition is not strictly needed for non-negativity but it is
    the natural bundling already used elsewhere. *)
Lemma computeNewBasketsAndNeeded_outputs_nonneg
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t) :
  Valid.bufferInputs basketsHeldBottom basketsNeeded backingBuffer ->
  let s' := computeNewBasketsAndNeeded basketsHeldBottom basketsNeeded
                                       backingBuffer in
  0 <= s'.(BasketState.mintAmount) /\ 0 <= s'.(BasketState.needed).
Proof.
  intros Hvalid s'.
  destruct Hvalid as [HbHB HbN Hbf _].
  destruct HbHB as [HbHB_lo HbHB_hi].
  destruct HbN as [HbN_lo HbN_hi].
  destruct Hbf as [Hbf_lo Hbf_hi].
  unfold s', computeNewBasketsAndNeeded,
         BasketState.mintAmount, BasketState.needed.
  (* FIX_ONE + backingBuffer is positive — needed for divrnd below. *)
  assert (Hone_pos : 0 < FIX_ONE) by (unfold FIX_ONE, FIX_SCALE; lia).
  assert (Hsum_pos : 0 < FIX_ONE + backingBuffer) by lia.
  assert (HFS_pos : 0 < FIX_SCALE) by (unfold FIX_SCALE; lia).
  set (baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                              RoundingMode.FLOOR).
  (* baskets is non-negative by divrnd_nonneg. *)
  assert (Hbk_nn : 0 <= baskets).
  { unfold baskets, FixLib.div.
    apply divrnd_nonneg; [|exact Hsum_pos].
    apply Z.mul_nonneg_nonneg; [exact HbHB_lo|unfold FIX_SCALE; lia]. }
  (* Choose basketsNeeded' depending on the comparison branch. *)
  set (bn' := if basketsNeeded <? baskets then baskets else basketsNeeded).
  assert (Hbn'_nn : 0 <= bn').
  { unfold bn'. destruct (basketsNeeded <? baskets); [exact Hbk_nn|exact HbN_lo]. }
  split.
  - (* mintAmount: either 0 or baskets - basketsNeeded (which is positive
       in that branch). *)
    destruct (basketsNeeded <? baskets) eqn:Hlt.
    + apply Z.ltb_lt in Hlt. lia.
    + lia.
  - (* needed = mul bn' (FIX_ONE + buf) CEIL = divrnd (bn' * (FIX_ONE+buf))
       FIX_SCALE CEIL. Non-negative since numerator >= 0 and FIX_SCALE > 0. *)
    unfold FixLib.mul.
    apply divrnd_nonneg; [|exact HFS_pos].
    apply Z.mul_nonneg_nonneg; [|lia].
    destruct (basketsNeeded <? baskets); [exact Hbk_nn|exact HbN_lo].
Qed.

(** Output-bound lemma for [computeSurplusSplit]:
    every Success-branch output is non-negative.

    Preconditions: [0 <= bal], [0 <= needed * quantity], [0 <= rTokenTotal],
    [0 <= rsrTotal], [0 <= decimals] (so [shiftl_toUint] multiplies rather
    than divides — keeping [delta] non-negative when [bal - req] is). *)
Lemma computeSurplusSplit_outputs_nonneg
    (needed quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) (split : SurplusSplit.t) :
  0 <= needed ->
  0 <= quantity ->
  0 <= bal ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  0 <= decimals ->
  computeSurplusSplit needed quantity bal decimals rTokenTotal rsrTotal
    = Result.Success split ->
  0 <= split.(SurplusSplit.rsrAmount) /\
  0 <= split.(SurplusSplit.rTokenAmount) /\
  0 <= split.(SurplusSplit.dust).
Proof.
  intros Hneeded Hquantity Hbal HrT HrS Hdec Hsucc.
  unfold computeSurplusSplit in Hsucc.
  set (req := FixLib.mul needed quantity RoundingMode.CEIL) in Hsucc.
  (* req is non-negative: req = divrnd (needed*quantity) FIX_SCALE CEIL. *)
  assert (Hreq_nn : 0 <= req).
  { unfold req, FixLib.mul.
    apply divrnd_nonneg.
    - apply Z.mul_nonneg_nonneg; [exact Hneeded|exact Hquantity].
    - unfold FIX_SCALE; lia. }
  destruct (bal <=? req) eqn:Hle.
  - (* bal <= req branch: all outputs are zero. *)
    inversion Hsucc; subst.
    unfold SurplusSplit.rsrAmount, SurplusSplit.rTokenAmount,
           SurplusSplit.dust.
    repeat split; lia.
  - (* bal > req branch. *)
    apply Z.leb_gt in Hle.
    set (delta := shiftl_toUint (bal - req) decimals) in Hsucc.
    (* delta is non-negative: bal - req >= 0 and decimals >= 0 so
       shiftl_toUint multiplies by 10^decimals (non-negative). *)
    assert (Hdelta_nn : 0 <= delta).
    { unfold delta, shiftl_toUint.
      assert (Hcond : (decimals <? 0) = false) by (apply Z.ltb_ge; exact Hdec).
      rewrite Hcond.
      apply Z.mul_nonneg_nonneg; [lia|].
      apply Z.pow_nonneg; lia. }
    set (totalShares := rTokenTotal + rsrTotal) in Hsucc.
    assert (HtS_nn : 0 <= totalShares) by (unfold totalShares; lia).
    destruct (totalShares =? 0) eqn:Hts_zero.
    + (* Revert branch: contradicts Hsucc. *)
      discriminate Hsucc.
    + apply Z.eqb_neq in Hts_zero.
      assert (Hts_pos : 0 < totalShares) by lia.
      set (tps := delta / totalShares) in Hsucc.
      assert (Htps_nn : 0 <= tps).
      { unfold tps. apply Z.div_pos; [exact Hdelta_nn|exact Hts_pos]. }
      destruct (tps =? 0) eqn:Htps.
      * inversion Hsucc; subst.
        unfold SurplusSplit.rsrAmount, SurplusSplit.rTokenAmount,
               SurplusSplit.dust.
        repeat split; lia.
      * inversion Hsucc; subst.
        unfold SurplusSplit.rsrAmount, SurplusSplit.rTokenAmount,
               SurplusSplit.dust.
        (* dust = delta - (tps*rsr + tps*rTok) = delta - tps*totalShares,
           which is >= 0 by Z.mul_div_le. *)
        assert (Htps_mul_le : tps * totalShares <= delta).
        { unfold tps. rewrite Z.mul_comm.
          apply Z.mul_div_le. exact Hts_pos. }
        assert (Hsum : tps * rsrTotal + tps * rTokenTotal
                       = tps * totalShares).
        { unfold totalShares. ring. }
        repeat split.
        -- apply Z.mul_nonneg_nonneg; [exact Htps_nn|exact HrS].
        -- apply Z.mul_nonneg_nonneg; [exact Htps_nn|exact HrT].
        -- lia.
Qed.

End BackingManagerValidityProofs.
