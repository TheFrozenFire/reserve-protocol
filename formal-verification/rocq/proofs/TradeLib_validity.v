(** TradeLib output-bound (validity) lemmas.

    Narrow output-bound invariants on the [TradeLib] simulation operations:

      1. [buyAmount_nonneg] — under [Valid.buyInputs], [buyAmount] is >= 0.
         Combined with the existing [buyAmount_le_fix_max] this gives the
         full uint192 fit.

      2. [buyAmount_uint192_valid] — packages the two bounds into the
         [uint192_valid] predicate downstream callers expect.

      3. [buyAmountPre_nonneg] — same shape for the pre-mitigation variant,
         used by the rounding-direction witness corpus.

      4. [coverDeficitSellAmount_nonneg] — the [prepareTradeToCoverDeficit]
         kernel returns a non-negative slipped sell amount whenever the
         caller's [require]s hold (sellLow > 0, slippage < FIX_ONE,
         non-negative deficit).

    All proofs lean on the FixLib round-direction discipline: [divrnd] is
    non-negative whenever its numerator is non-negative and divisor is
    positive (mirroring [divrnd_nonneg] in BackingManager_validity).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.proofs.TradeLib.
Require Import Coq.Bool.Bool.

Module TradeLibValidityProofs.

Import FixLib.
Import FixLibProofs.
Import Reserve.simulations.TradeLib.TradeLib.
Import Reserve.proofs.TradeLib.TradeLibProofs.

(** Local helper: [divrnd] is non-negative on non-negative numerator
    and positive divisor. Same shape as the BackingManager_validity
    helper; kept local to avoid a cross-file import. *)
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

(** [mul x y mode] is non-negative whenever both inputs are non-negative.
    Reduces to [divrnd_nonneg] over the FIX_SCALE divisor. *)
Lemma mul_nonneg (x y : Z) (mode : RoundingMode.t) :
  0 <= x -> 0 <= y -> 0 <= mul x y mode.
Proof.
  intros Hx Hy.
  unfold mul.
  apply divrnd_nonneg.
  - apply Z.mul_nonneg_nonneg; assumption.
  - unfold FIX_SCALE. lia.
Qed.

(** [div x y mode] is non-negative whenever x is non-negative and y is
    positive. *)
Lemma div_nonneg (x y : Z) (mode : RoundingMode.t) :
  0 <= x -> 0 < y -> 0 <= div x y mode.
Proof.
  intros Hx Hy.
  unfold div.
  apply divrnd_nonneg.
  - apply Z.mul_nonneg_nonneg; [assumption | unfold FIX_SCALE; lia].
  - exact Hy.
Qed.

(** ============================================================ *)
(** ===== buyAmount output-bounds =============================== *)
(** ============================================================ *)

(** [buyAmount] is non-negative under [Valid.buyInputs].

    Both inner muls (CEIL and FLOOR) preserve non-negativity since
    s >= 0 and (FIX_ONE - slippage) >= 0 (slippage <= FIX_ONE). The
    outer [safeMulDiv] then fires its non-negativity lemma, which
    needs only that all of inner, sellLow, buyHigh are non-negative. *)
Lemma buyAmount_nonneg (s slippage sellLow buyHigh : Z) :
  Valid.buyInputs s slippage sellLow buyHigh ->
  0 <= buyAmount s slippage sellLow buyHigh.
Proof.
  intros Hv.
  destruct Hv as [Hs Hslip HsL HbH Hslip_lim HbH_pos].
  destruct Hs as [Hs_lo _].
  destruct HsL as [HsL_lo _].
  destruct HbH as [HbH_lo _].
  unfold buyAmount.
  apply safeMulDiv_nonneg; [| exact HsL_lo | exact HbH_lo].
  apply mul_nonneg; [exact Hs_lo | unfold FIX_ONE, FIX_SCALE in *; lia].
Qed.

(** [buyAmount] fits in uint192 under [Valid.buyInputs]: combines the
    above non-negativity with the existing [buyAmount_le_fix_max]. *)
Lemma buyAmount_uint192_valid (s slippage sellLow buyHigh : Z) :
  Valid.buyInputs s slippage sellLow buyHigh ->
  uint192_valid (buyAmount s slippage sellLow buyHigh).
Proof.
  intros Hv.
  unfold uint192_valid.
  split.
  - apply buyAmount_nonneg; exact Hv.
  - apply buyAmount_le_fix_max.
Qed.

(** [buyAmountPre] is non-negative under [Valid.buyInputs]. Same shape
    as [buyAmount_nonneg] — the inner mul rounds FLOOR rather than CEIL,
    but [mul_nonneg] is rounding-mode insensitive. *)
Lemma buyAmountPre_nonneg (s slippage sellLow buyHigh : Z) :
  Valid.buyInputs s slippage sellLow buyHigh ->
  0 <= buyAmountPre s slippage sellLow buyHigh.
Proof.
  intros Hv.
  destruct Hv as [Hs Hslip HsL HbH Hslip_lim HbH_pos].
  destruct Hs as [Hs_lo _].
  destruct HsL as [HsL_lo _].
  destruct HbH as [HbH_lo _].
  unfold buyAmountPre.
  apply safeMulDiv_nonneg; [| exact HsL_lo | exact HbH_lo].
  apply mul_nonneg; [exact Hs_lo | unfold FIX_ONE, FIX_SCALE in *; lia].
Qed.

(** [buyAmountPre] fits in uint192 under [Valid.buyInputs]. *)
Lemma buyAmountPre_uint192_valid (s slippage sellLow buyHigh : Z) :
  Valid.buyInputs s slippage sellLow buyHigh ->
  uint192_valid (buyAmountPre s slippage sellLow buyHigh).
Proof.
  intros Hv.
  unfold uint192_valid.
  split.
  - apply buyAmountPre_nonneg; exact Hv.
  - apply buyAmountPre_le_fix_max.
Qed.

(** ============================================================ *)
(** ===== coverDeficitSellAmount output-bound =================== *)
(** ============================================================ *)

(** [coverDeficitSellAmount] is non-negative under the caller's
    [require]s: 0 <= b, 0 < sellLow, 0 <= slippage < FIX_ONE.

    The kernel composes:
        exactSell    = divrnd (b * buyHigh) sellLow CEIL    -- needs sellLow > 0
        slippedSell  = div exactSell (FIX_ONE - slippage) CEIL
                                                            -- needs FIX_ONE - slippage > 0
    Both rounding modes preserve non-negativity, by [divrnd_nonneg]. *)
Lemma coverDeficitSellAmount_nonneg (b slippage sellLow buyHigh : Z) :
  0 <= b ->
  0 <= slippage < FIX_ONE ->
  0 < sellLow ->
  0 <= buyHigh ->
  0 <= coverDeficitSellAmount b slippage sellLow buyHigh.
Proof.
  intros Hb [Hslip_lo Hslip_hi] HsL HbH.
  unfold coverDeficitSellAmount.
  set (exactSell := divrnd (b * buyHigh) sellLow RoundingMode.CEIL).
  assert (HexactSell_nn : 0 <= exactSell).
  { unfold exactSell. apply divrnd_nonneg.
    - apply Z.mul_nonneg_nonneg; assumption.
    - exact HsL. }
  apply div_nonneg; [exact HexactSell_nn | lia].
Qed.

End TradeLibValidityProofs.
