(** TradeLib composition lemmas.

    Small chain proofs over the [TradeLib] kernel that bolt together
    pieces already proved in [proofs/TradeLib.v]:

      1. [buyAmount_zero_when_sellAmt_zero] — when the sell amount fed
         into the kernel is zero, the buy amount is zero. Direct
         re-export of [buyAmount_zero_s] under the canonical
         [sellAmt = 0] name used by callers in TradeLib.sol.

      2. [buyAmount_monotone_in_sellAmount_nonsat] — under non-saturation,
         increasing the sell-amount input weakly increases the buy
         amount. Composes [divrnd_ceil_monotone] (lifted to [mul] over
         FIX_SCALE) with [safeMulDiv_a_mono_ceil_nonsat]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.proofs.TradeLib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module TradeLibChain.

Import FixLib.
Import Reserve.simulations.TradeLib.TradeLib.
Import Reserve.proofs.TradeLib.TradeLibProofs.

Local Open Scope Z_scope.

(** ============================================================ *)
(** ===== buyAmount_zero_when_sellAmt_zero ===================== *)
(** ============================================================ *)

(** When the sell amount fed into the kernel is zero, the buy amount is
    zero, regardless of slippage and prices. Direct re-export of
    [buyAmount_zero_s] under the canonical Solidity argument name. *)
Lemma buyAmount_zero_when_sellAmt_zero
    (slippage sellLow buyHigh : Z) :
  buyAmount 0 slippage sellLow buyHigh = 0.
Proof.
  apply buyAmount_zero_s.
Qed.

(** ============================================================ *)
(** ===== buyAmount_monotone_in_sellAmount_nonsat ============== *)
(** ============================================================ *)

(** [mul] under CEIL is monotone in its first argument when both inputs
    are non-negative. Lifts [divrnd_ceil_monotone] over [FIX_SCALE]. *)
Local Lemma mul_ceil_monotone_in_x (x1 x2 y : Z) :
  0 <= x1 ->
  x1 <= x2 ->
  0 <= y ->
  mul x1 y RoundingMode.CEIL <= mul x2 y RoundingMode.CEIL.
Proof.
  intros Hx1 Hle Hy.
  unfold mul.
  apply divrnd_ceil_monotone.
  - apply Z.mul_nonneg_nonneg; assumption.
  - apply Z.mul_le_mono_nonneg_r; lia.
  - unfold FIX_SCALE. lia.
Qed.

(** Increasing [sellAmt] weakly increases [buyAmount] under fixed
    prices/slippage and non-saturation hypotheses.

    The hypotheses match those of [safeMulDiv_a_mono_ceil_nonsat] lifted
    over the inner [mul]: both inner muls must be strictly between 0
    and FIX_MAX (positive so the [safeMulDiv] non-zero-input branch
    triggers; sub-FIX_MAX so the saturation branch does not), and the
    raw outer divrnd at the larger input must stay below FIX_MAX. *)
Lemma buyAmount_monotone_in_sellAmount_nonsat
    (s1 s2 slippage sellLow buyHigh : Z) :
  0 <= s1 ->
  s1 <= s2 ->
  0 <= slippage <= FIX_ONE ->
  0 < sellLow < FIX_MAX ->
  0 < buyHigh ->
  let inner1 := mul s1 (FIX_ONE - slippage) RoundingMode.CEIL in
  let inner2 := mul s2 (FIX_ONE - slippage) RoundingMode.CEIL in
  0 < inner1 ->
  inner2 < FIX_MAX ->
  divrnd (inner2 * sellLow) buyHigh RoundingMode.CEIL < FIX_MAX ->
  buyAmount s1 slippage sellLow buyHigh
  <= buyAmount s2 slippage sellLow buyHigh.
Proof.
  intros Hs1 Hs12 [Hslip_lo Hslip_hi] [HsL_lo HsL_hi] HbH
         inner1 inner2 Hin1_pos Hin2_lt Hraw_lt.
  unfold buyAmount.
  fold inner1. fold inner2.
  assert (Hslip_diff_nn : 0 <= FIX_ONE - slippage) by lia.
  assert (Hinner_le : inner1 <= inner2).
  { unfold inner1, inner2. apply mul_ceil_monotone_in_x; lia. }
  apply safeMulDiv_a_mono_ceil_nonsat;
    [ exact Hin1_pos
    | exact Hinner_le
    | exact Hin2_lt
    | split; [exact HsL_lo | exact HsL_hi]
    | exact HbH
    | exact Hraw_lt ].
Qed.

End TradeLibChain.
