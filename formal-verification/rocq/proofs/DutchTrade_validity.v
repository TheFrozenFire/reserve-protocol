(** DutchTrade validity-preservation lemmas.

    Small bound lemmas on the DutchTrade price curve, given the [Valid.t]
    invariants. Builds on the monotonicity / endpoint lemmas in
    [proofs/DutchTrade.v].

    Lemmas:
      - [phase4_price_nonneg]      : phase4_price >= 0 (= worstPrice).
      - [phase4_price_le_bestPrice]: phase4_price <= bestPrice.
      - [phase3_price_le_bestPrice]: in [45%, 95%], phase3_price <= bestPrice.
      - [phase3_price_nonneg]      : in [45%, 95%], phase3_price >= 0.
      - [bidPrice_phase4_nonneg]   : bidPrice in the phase-4 range is non-negative.

    Proof note: keep [Opaque] on the FixLib operations not directly unfolded
    (they would otherwise blow up under [simpl] / [lia]).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Reserve.simulations.DutchTrade.
Require Reserve.proofs.DutchTrade.

Module DutchTradeValidity.

Import FixLib.
Import Reserve.simulations.DutchTrade.DutchTrade.
Import Reserve.proofs.DutchTrade.DutchTradeProofs.

Opaque FixLib.mul FixLib.divrnd FixLib.powu.

(** ===== phase4_price >= 0. =====

    Trivial unfolding: phase4_price = worstPrice, which is non-negative
    by [Valid.t.worstPrice_nonneg]. *)
Lemma phase4_price_nonneg (a : Auction.t) :
  Valid.t a ->
  0 <= phase4_price a.
Proof.
  intros Hv.
  destruct Hv as [_ _ _ Hwn _ _].
  unfold phase4_price.
  exact Hwn.
Qed.

(** ===== phase4_price <= bestPrice. =====

    phase4_price = worstPrice <= bestPrice by [Valid.t.prices_ordered]. *)
Lemma phase4_price_le_bestPrice (a : Auction.t) :
  Valid.t a ->
  phase4_price a <= a.(Auction.bestPrice).
Proof.
  intros Hv.
  destruct Hv as [_ Hpo _ _ _ _].
  unfold phase4_price.
  exact Hpo.
Qed.

(** ===== phase3_price <= bestPrice in [45%, 95%]. =====

    phase3_price = best - drop where drop >= 0 (best >= worst, prog >= 45%).
    Therefore phase3_price <= best. *)
Lemma phase3_price_le_bestPrice (a : Auction.t) (prog : Z) :
  Valid.t a ->
  FORTY_FIVE_PERCENT <= prog ->
  phase3_price a prog <= a.(Auction.bestPrice).
Proof.
  intros Hv Hge.
  destruct Hv as [_ Hpo _ _ _ _].
  unfold phase3_price.
  set (delta := a.(Auction.bestPrice) - a.(Auction.worstPrice)).
  assert (Hdelta : 0 <= delta) by (unfold delta; lia).
  assert (Hprog : 0 <= prog - FORTY_FIVE_PERCENT)
    by (unfold FORTY_FIVE_PERCENT in *; lia).
  assert (Hnum : 0 <= delta * (prog - FORTY_FIVE_PERCENT))
    by (apply Z.mul_nonneg_nonneg; assumption).
  assert (Hdrop : 0 <= delta * (prog - FORTY_FIVE_PERCENT) / FIFTY_PERCENT).
  { apply Z.div_pos; [exact Hnum|]. unfold FIFTY_PERCENT. lia. }
  lia.
Qed.

(** ===== phase3_price >= 0 (in fact >= worstPrice) when prog in [45%, 95%]. =====

    Inside the phase-3 range:
      drop = (best - worst) * (prog - 45%) / 50%
    With prog <= 95%, [prog - 45% <= 50%], so the division by 50% bounds
    [drop] above by [best - worst]. Hence [best - drop >= worst >= 0]. *)
Lemma phase3_price_nonneg (a : Auction.t) (prog : Z) :
  Valid.t a ->
  FORTY_FIVE_PERCENT <= prog ->
  prog <= NINETY_FIVE_PERCENT ->
  0 <= phase3_price a prog.
Proof.
  intros Hv Hge Hle.
  destruct Hv as [_ Hpo _ Hwn _ _].
  unfold phase3_price.
  set (best := a.(Auction.bestPrice)).
  set (worst := a.(Auction.worstPrice)).
  fold best. fold worst.
  set (delta := best - worst).
  assert (Hdelta : 0 <= delta) by (unfold delta, best, worst; lia).
  set (range := prog - FORTY_FIVE_PERCENT).
  assert (Hrange_lo : 0 <= range)
    by (unfold range, FORTY_FIVE_PERCENT in *; lia).
  assert (Hrange_hi : range <= FIFTY_PERCENT).
  { unfold range, FORTY_FIVE_PERCENT, FIFTY_PERCENT, NINETY_FIVE_PERCENT in *.
    lia. }
  (* drop = (delta * range) / FIFTY_PERCENT, with FLOOR. *)
  assert (Hnum_nn : 0 <= delta * range)
    by (apply Z.mul_nonneg_nonneg; assumption).
  assert (Hnum_le : delta * range <= delta * FIFTY_PERCENT).
  { apply Z.mul_le_mono_nonneg_l; assumption. }
  assert (Hfp_pos : 0 < FIFTY_PERCENT) by (unfold FIFTY_PERCENT; lia).
  (* (delta * range) / FIFTY_PERCENT <= delta. *)
  assert (Hdrop_le : delta * range / FIFTY_PERCENT <= delta).
  { apply Z.div_le_upper_bound; [exact Hfp_pos|].
    rewrite (Z.mul_comm FIFTY_PERCENT delta).
    rewrite (Z.mul_comm delta FIFTY_PERCENT) in Hnum_le.
    rewrite (Z.mul_comm delta range) in Hnum_le.
    (* Now Hnum_le : range * delta <= FIFTY_PERCENT * delta *)
    (* Goal: delta * range <= delta * FIFTY_PERCENT *)
    rewrite (Z.mul_comm delta range), (Z.mul_comm delta FIFTY_PERCENT).
    exact Hnum_le. }
  (* So best - drop >= best - delta = worst >= 0. *)
  unfold delta in *. unfold best, worst in *. lia.
Qed.

(** ===== Phase-4 range: bidPrice >= 0. =====

    Combines [bidPrice_phase4_constant] with [worstPrice_nonneg]. *)
Lemma bidPrice_phase4_nonneg (a : Auction.t) (t : U256.t) :
  Valid.t a ->
  NINETY_FIVE_PERCENT <= progression a t ->
  progression a t <= FIX_ONE ->
  0 <= bidPrice a t.
Proof.
  intros Hv Hge Hle.
  rewrite (bidPrice_phase4_constant a t Hge Hle).
  destruct Hv as [_ _ _ Hwn _ _].
  exact Hwn.
Qed.

End DutchTradeValidity.
