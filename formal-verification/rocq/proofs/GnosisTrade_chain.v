(** GnosisTrade composition lemmas.

    Two small composition results that close cleanly on top of the
    existing [GnosisTrade] / [GnosisTrade_validity] proofs:

      1. [worstCasePrice_zero_sa] — the dual zero-input identity to
         [GnosisTradeValidity.worstCasePrice_zero_mba]: when [sa = 0],
         [worstCasePrice] returns 0 directly via the divide-by-zero
         guard. Together with [worstCasePrice_zero_mba] this fully
         characterizes the zero-input boundary of the worst-case-price
         function.

      2. [settlement_floor_monotone_in_soldAmt] — companion to
         [settlement_floor_mono_in_wcp]: the settlement floor is
         weakly non-decreasing in [soldAmt] when [worstCase >= 0].
         Larger soldAmt scales the qBuyTok floor [boughtAmt] that
         must be cleared. Composes [Z.max] monotonicity with the
         CEIL-divrnd numerator monotonicity helper already proved in
         [GnosisTradeProofs].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.GnosisTrade.
Require Import Reserve.proofs.GnosisTrade.
Require Import Reserve.proofs.GnosisTrade_validity.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module GnosisTradeChain.

Import FixLib.
Import GnosisTrade.GnosisTrade.

(** ===== worstCasePrice_zero_sa: zero sellAmount maps to zero price. =====

    The [sa = 0] guard in [worstCasePrice] short-circuits to 0 — this
    is the divide-by-zero protection. Together with the companion
    [worstCasePrice_zero_mba] in [GnosisTradeValidity], the two zero
    boundaries are fully characterized: either zero input yields a
    zero output. *)
Lemma worstCasePrice_zero_sa (mba : Z) :
  worstCasePrice mba 0 = 0.
Proof.
  unfold worstCasePrice. cbn. reflexivity.
Qed.

(** Combined zero-boundary characterization: zero in either argument
    yields a zero worst-case price. *)
Lemma worstCasePrice_zero_either (mba sa : Z) :
  mba = 0 \/ sa = 0 ->
  worstCasePrice mba sa = 0.
Proof.
  intros [Hm | Hs].
  - subst. apply GnosisTradeValidity.worstCasePrice_zero_mba.
  - subst. apply worstCasePrice_zero_sa.
Qed.

(** ===== settlement_floor_monotone_in_soldAmt =====

    The settlement floor is weakly non-decreasing in [soldAmt] given
    [0 <= worstCase]. As soldAmt grows, the qBuyTok floor required of
    the bidder grows in tandem.

    Proof: [Z.max soldAmt 1] is monotone in soldAmt; multiplying by a
    non-negative [worstCase] preserves the ordering; [divrnd CEIL] is
    monotone in the numerator (already proved as
    [GnosisTradeProofs.divrnd_ceil_mono_numerator]); subtracting 1 and
    clipping at 0 with [Z.max] both preserve weak monotonicity. *)
Lemma settlement_floor_monotone_in_soldAmt
    (worstCase soldAmt1 soldAmt2 : Z) :
  0 <= worstCase ->
  soldAmt1 <= soldAmt2 ->
  settlement_floor worstCase soldAmt1
    <= settlement_floor worstCase soldAmt2.
Proof.
  intros Hwc Hsa.
  unfold settlement_floor.
  set (adj1 := Z.max soldAmt1 1).
  set (adj2 := Z.max soldAmt2 1).
  assert (Hadj : adj1 <= adj2) by (unfold adj1, adj2; lia).
  assert (Hadj1_pos : 1 <= adj1) by (unfold adj1; lia).
  set (raw1 := divrnd (worstCase * adj1) D27_ONE RoundingMode.CEIL - 1).
  set (raw2 := divrnd (worstCase * adj2) D27_ONE RoundingMode.CEIL - 1).
  assert (Hraw : raw1 <= raw2).
  { unfold raw1, raw2.
    apply Z.sub_le_mono_r.
    apply GnosisTradeProofs.divrnd_ceil_mono_numerator.
    - unfold D27_ONE. lia.
    - apply Z.mul_le_mono_nonneg_l; [exact Hwc | exact Hadj]. }
  lia.
Qed.

End GnosisTradeChain.
