(** Fixed_certora_mitigation.v

    Formalizes the gap between the pre- and post-mitigation Reserve
    FixLib semantics introduced by the Certora audit (PR #1283).

    The simulation in [simulations/Fixed.v] models only the post-#1283
    surface — there is no concrete pre-mitigation [mul]/[safeMulDiv].
    However, the [TradeLib] simulation deliberately exposes both
    rounding orientations of the inner [mul] inside [buyAmount]:
      - [buyAmount]    uses [mul ... CEIL] (post-mitigation).
      - [buyAmountPre] uses [mul ... FLOOR] (pre-mitigation default).
    Both compose with the same outer [safeMulDiv ... CEIL] kernel,
    so [buyAmount] vs [buyAmountPre] is the cleanest pre-vs-post
    pair that the simulation makes available.

    This file proves two things at the FixLib / TradeLib boundary:

      1. [certora_mitigation_diverges_at_witness] — there exist
         concrete inputs at which the post-mitigation [buyAmount]
         strictly exceeds the pre-mitigation [buyAmountPre]. This
         shows the mitigation is non-trivial: it changes observable
         output on at least one input.

      2. [post_mitigation_inner_ge_pre] — the FixLib-level pre/post
         characterization on the *inner* [mul]: for every input,
         [mul x y CEIL >= mul x y FLOOR]. This is the algebraic
         identity that propagates into [buyAmount_ge_pre] in
         [proofs/TradeLib.v].

    The CAS witness corpus in
      cas/fixlib/safe_muldiv_certora_witness.gp
    enumerates 4753 (a, b, c) triples on the FIX_MAX overflow boundary;
    the simulation's [safeMulDiv] models the saturating return path
    (producing FIX_MAX) on all of them, so the saturation contribution
    to the gap collapses. The remaining, *non-saturating* gap between
    pre- and post-mitigation comes from the inner [mul] rounding flip,
    which is precisely what these lemmas characterize. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.proofs.TradeLib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module FixedCertoraMitigation.

Import FixLib.
Import Reserve.simulations.TradeLib.TradeLib.
Import Reserve.proofs.TradeLib.TradeLibProofs.

Local Open Scope Z_scope.

(** ============================================================ *)
(** ===== Lemma 1: concrete divergence witness ================== *)
(** ============================================================ *)

(** Concrete witness exhibiting strict divergence between the
    post-mitigation [buyAmount] and the pre-mitigation [buyAmountPre].

    Inputs:
      s        = 1
      slippage = 1
      sellLow  = 1
      buyHigh  = 1

    Inner mul:
      pre  (FLOOR): (1 * (FIX_ONE - 1)) / FIX_ONE = (10^18 - 1) / 10^18 = 0
      post (CEIL):  (1 * (FIX_ONE - 1)) / FIX_ONE = 0 + 1 (remainder != 0) = 1

    Outer safeMulDiv inner 1 1 CEIL:
      pre  : safeMulDiv 0 1 1 CEIL = 0       (a = 0 short-circuit)
      post : safeMulDiv 1 1 1 CEIL = 1       (raw = 1, below FIX_MAX)

    Hence buyAmount = 1 > 0 = buyAmountPre. *)
Lemma certora_mitigation_diverges_at_witness :
  exists s slippage sellLow buyHigh,
    buyAmount    s slippage sellLow buyHigh
    > buyAmountPre s slippage sellLow buyHigh.
Proof.
  exists 1, 1, 1, 1.
  vm_compute. reflexivity.
Qed.

(** ============================================================ *)
(** ===== Lemma 2: pre/post on the inner FixLib mul ============= *)
(** ============================================================ *)

(** FixLib-level characterization theorem. The post-mitigation
    inner [mul] (CEIL) never under-credits the pre-mitigation inner
    [mul] (FLOOR). This is the algebraic root of [buyAmount_ge_pre]:
    once it's lifted through the (monotone) outer [safeMulDiv] CEIL
    kernel, the chain-level guarantee follows. *)
Theorem post_mitigation_inner_ge_pre (x y : Z) :
  mul x y RoundingMode.FLOOR <= mul x y RoundingMode.CEIL.
Proof.
  apply FixLibProofs.mul_floor_le_ceil.
Qed.

(** ============================================================ *)
(** ===== Lemma 3: re-export of TradeLib's chain-level result === *)
(** ============================================================ *)

(** The full pre/post chain-level guarantee, surfaced under a name
    that points back at the Certora mitigation rather than the
    TradeLib internals. This is the universally-quantified
    counterpart to [certora_mitigation_diverges_at_witness]: under
    the non-saturation hypotheses spelled out in [buyAmount_ge_pre],
    the post-mitigation result is *always* at least the pre value. *)
Theorem post_mitigation_buyAmount_ge_pre
    (s slippage sellLow buyHigh : Z) :
  0 <= s ->
  0 <= slippage <= FIX_ONE ->
  0 < sellLow < FIX_MAX ->
  0 < buyHigh ->
  let inner_floor := mul s (FIX_ONE - slippage) RoundingMode.FLOOR in
  let inner_ceil  := mul s (FIX_ONE - slippage) RoundingMode.CEIL  in
  0 < inner_floor ->
  inner_ceil < FIX_MAX ->
  divrnd (inner_ceil * sellLow) buyHigh RoundingMode.CEIL < FIX_MAX ->
  buyAmountPre s slippage sellLow buyHigh
  <= buyAmount    s slippage sellLow buyHigh.
Proof.
  apply buyAmount_ge_pre.
Qed.

End FixedCertoraMitigation.
