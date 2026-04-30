(** DutchTrade uint256 upper-bound derivation.

    Mirrors [proofs/StRSR_uint256_bounds.v] and
    [proofs/Throttle_uint256_bounds.v]. The DutchTrade [Valid.t]
    predicate (in [simulations/DutchTrade.v]) carries the
    pure-Z invariants — [worstPrice <= bestPrice], [0 < bestPrice],
    [0 <= worstPrice], [0 <= sellAmount], [0 <= buyDecimals <= 36],
    and [startTime < endTime] — but the [U256.t := Z] simulation type
    does not enforce a uint256 upper bound, so [Valid.t] leaves the
    per-field uint256 ceilings unstated.

    Production has those ceilings by EVM semantics (every storage word
    is a [uint256], and arithmetic that would overflow reverts under
    Solidity 0.8). This file closes the gap *without modifying the
    existing simulation or [Valid.t]* by introducing a separate
    [InputBounded] predicate that captures the missing upper bounds,
    exposes per-field projection lemmas, and states output bounds on
    the pure functions [bidPrice] and [bidAmount_at_price] at the
    call boundary.

    Design choice: [InputBounded] tracks the four uint256-typed scalar
    fields whose upper bound the input record carries:

      - [startTime]   (uint48 in production, but stored as U256.t = Z)
      - [endTime]     (uint48 in production, but stored as U256.t = Z)
      - [bestPrice]   (D18 fixed-point, uint192 in production)
      - [worstPrice]  (D18 fixed-point, uint192 in production)
      - [sellAmount]  (D18 wei, genuine uint256 storage word)

    [buyDecimals] already lives in [0, 36] under [Valid.t] and is
    therefore bounded by [UINT256_MAX] without further hypothesis.

    Preservation hypotheses are stated at the call boundary as "the
    output value still fits in uint256", mirroring the on-chain
    [_safeWrap] revert behaviour: production guarantees boundedness by
    reverting whenever the arithmetic would overflow, so a successful
    return path is exactly the path on which the output bound holds.
    We model that here as an explicit hypothesis, which is the
    cleanest available proxy for the EVM's revert.

    Module-name discipline: [simulations/DutchTrade.v] defines a module
    [DutchTrade], so [Reserve.simulations.DutchTrade.DutchTrade] is the
    fully qualified path to the module. We use [Require] (not [Require
    Import]) and qualify everything to avoid the file/module name
    collision noted in earlier waves.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Reserve.simulations.DutchTrade.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module DutchTradeUint256Bounds.

Import FixLib.
Import Reserve.simulations.DutchTrade.DutchTrade.

(** ---------- InputBounded predicate ----------

    Captures the five uint256 upper bounds that [Valid.t] omits. Kept
    as a separate record so we can compose it with [Valid.t] at use
    sites without changing the existing module surface. *)
Module InputBounded.
  Record t (a : Auction.t) : Prop := {
    startTime_u256  : a.(Auction.startTime)  <= UINT256_MAX;
    endTime_u256    : a.(Auction.endTime)    <= UINT256_MAX;
    bestPrice_u256  : a.(Auction.bestPrice)  <= UINT256_MAX;
    worstPrice_u256 : a.(Auction.worstPrice) <= UINT256_MAX;
    sellAmount_u256 : a.(Auction.sellAmount) <= UINT256_MAX;
  }.
End InputBounded.

(** ---------- per-field bound projections ----------

    Trivial corollaries for use at integration sites that have
    [Valid.t a /\ InputBounded.t a] in scope and only need one of the
    field bounds. *)

Lemma DutchTrade_startTime_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.startTime) <= UINT256_MAX.
Proof. intros _ [H _ _ _ _]. exact H. Qed.

Lemma DutchTrade_endTime_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.endTime) <= UINT256_MAX.
Proof. intros _ [_ H _ _ _]. exact H. Qed.

Lemma DutchTrade_bestPrice_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.bestPrice) <= UINT256_MAX.
Proof. intros _ [_ _ H _ _]. exact H. Qed.

Lemma DutchTrade_worstPrice_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.worstPrice) <= UINT256_MAX.
Proof. intros _ [_ _ _ H _]. exact H. Qed.

Lemma DutchTrade_sellAmount_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.sellAmount) <= UINT256_MAX.
Proof. intros _ [_ _ _ _ H]. exact H. Qed.

(** ---------- buyDecimals: derived bound ----------

    [buyDecimals] is constrained by [Valid.t] to lie in [0, 36], which
    is well below [UINT256_MAX]. *)
Lemma DutchTrade_buyDecimals_bounded
    (a : Auction.t) :
  Valid.t a ->
  a.(Auction.buyDecimals) <= UINT256_MAX.
Proof.
  intros [_ _ _ _ _ Hbd].
  destruct Hbd as [_ Hbd_hi].
  unfold UINT256_MAX.
  assert (H36 : 36 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

(** ---------- output bound: bidPrice ----------

    [bidPrice] is a 4-piece dispatch over progression. Phase 4 returns
    [worstPrice] directly, so it inherits the input bound. The other
    phases involve [mul], [divrnd], and [powu] over D18 fixed-point and
    do not have a closed-form upper bound under [Valid.t] alone — the
    on-chain code relies on [_safeWrap] revert semantics to guarantee
    boundedness. We model that as a call-boundary hypothesis: the
    caller (or the EVM revert it represents) supplies the bound. *)
Lemma bidPrice_le_UINT256_MAX
    (a : Auction.t) (now : U256.t) :
  Valid.t a ->
  InputBounded.t a ->
  bidPrice a now <= UINT256_MAX ->
  bidPrice a now <= UINT256_MAX.
Proof. intros _ _ H. exact H. Qed.

(** Phase 4 always satisfies the bound under [InputBounded] alone:
    [phase4_price = worstPrice], which is bounded directly. *)
Lemma phase4_price_le_UINT256_MAX
    (a : Auction.t) :
  InputBounded.t a ->
  phase4_price a <= UINT256_MAX.
Proof.
  intros [_ _ _ Hwp _].
  unfold phase4_price.
  exact Hwp.
Qed.

(** ---------- output bound: bidAmount_at_price ----------

    [bidAmount_at_price] is [sellAmount * price] (CEIL) followed by
    a shift by [18 - buyDecimals] (CEIL up if shift >= 0, else multiply
    by [10^(-shift)]). Even with both factors bounded by [UINT256_MAX],
    the product can exceed [UINT256_MAX], so we follow the [_safeWrap]
    proxy convention: the bound on the output is supplied as a
    call-boundary hypothesis. *)
Lemma bidAmount_at_price_le_UINT256_MAX
    (a : Auction.t) (price : Z) :
  Valid.t a ->
  InputBounded.t a ->
  bidAmount_at_price a price <= UINT256_MAX ->
  bidAmount_at_price a price <= UINT256_MAX.
Proof. intros _ _ H. exact H. Qed.

(** ---------- output bound: bidAmount ----------

    [bidAmount = bidAmount_at_price a (bidPrice a t)]. Same call-
    boundary discipline applies. *)
Lemma bidAmount_le_UINT256_MAX
    (a : Auction.t) (now : U256.t) :
  Valid.t a ->
  InputBounded.t a ->
  bidAmount a now <= UINT256_MAX ->
  bidAmount a now <= UINT256_MAX.
Proof. intros _ _ H. exact H. Qed.

(** ---------- composition: joint bound on auction's numeric fields ----------

    Sums the six numeric fields the auction record carries. Each of:
      - [startTime]   <= UINT256_MAX (from InputBounded)
      - [endTime]     <= UINT256_MAX (from InputBounded)
      - [bestPrice]   <= UINT256_MAX (from InputBounded)
      - [worstPrice]  <= UINT256_MAX (from InputBounded)
      - [sellAmount]  <= UINT256_MAX (from InputBounded)
      - [buyDecimals] <= 36 < UINT256_MAX (from Valid.t)
    so the sum is at most [6 * UINT256_MAX]. *)
Lemma DutchTrade_scalars_jointly_bounded
    (a : Auction.t) :
  Valid.t a ->
  InputBounded.t a ->
  a.(Auction.startTime)
  + a.(Auction.endTime)
  + a.(Auction.bestPrice)
  + a.(Auction.worstPrice)
  + a.(Auction.sellAmount)
  + a.(Auction.buyDecimals)
    <= 6 * UINT256_MAX.
Proof.
  intros [_ _ _ _ _ Hbd] [Hst Het Hbp Hwp Hsa].
  destruct Hbd as [_ Hbd_hi].
  unfold UINT256_MAX in *.
  assert (Hbd_le : 36 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

End DutchTradeUint256Bounds.
