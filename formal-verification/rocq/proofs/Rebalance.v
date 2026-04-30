(** Rebalance simulation invariant proofs.

    Proves the load-bearing structural and noise invariants on the
    [RebalanceLib] simulation defined in [Reserve.simulations.Rebalance]:

      INV-LH    basketRange.low <= basketRange.high
      INV-LB    basketRange.low <= basketsHeldBottom
      INV-TH    basketsHeldTop  <= basketRange.high     (under capping)
      INV-TS    basketRange.high <= supplyTotal         (top is clipped)
      INV-NF    noise_loose / noise_tight finite & bounded under valid inputs
      INV-TL    noise_tight <= noise_loose             (for bl >= 5)
      INV-PA    "per-asset noise contribution <= 2 * priceError * weight"
                (CAS algebraic claim from cas/rebalance/noise_bound_tightness.gp)

    The high-level safety statement is

      basketRange.high - basketRange.low <= noise + 2 * priceErrorBound

    which appears in cas/rebalance/basket_range_noise.gp as the invariant
    the trade-selection harness checks. We prove a structural form of it
    here: the gap is bounded by [lowSlack + highSlack], and any caller-
    supplied bound on the slacks lifts to a bound on the gap.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Rebalance.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module RebalanceProofs.

Import RebalanceLib.

(** ============================================================ *)
(** ===== Structural invariants on basketRange ================== *)
(** ============================================================ *)

(** INV-LH: low <= high, by construction (the final clipping step). *)
Lemma basket_range_low_le_high (i : RangeInputs.t) :
  (basketRange i).(BasketRange.low) <= (basketRange i).(BasketRange.high).
Proof.
  unfold basketRange. cbn.
  apply Z.le_min_r.
Qed.

(** INV-LB: low <= basketsHeldBottom. The pessimistic floor cannot
    exceed the balance we already hold, regardless of how slack is
    distributed — slack subtracts from the bottom. *)
Lemma basket_range_low_le_held_bottom (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.low)
    <= i.(RangeInputs.basketsHeldBottom).
Proof.
  intros V.
  destruct V as [_ _ _ _ _ Hls _ _].
  unfold basketRange. cbn.
  (* low = min(raw_low, high1) <= raw_low = bhBottom - lowSlack <= bhBottom *)
  eapply Z.le_trans; [apply Z.le_min_l|].
  lia.
Qed.

(** INV-TH: basketsHeldTop <= high. The optimistic ceiling cannot fall
    below what we hold; slack adds to the top. The clip at supplyTotal
    is benign because [bhTop_le_supply] is part of the validity preds. *)
Lemma basket_range_held_top_le_high (i : RangeInputs.t) :
  Valid.inputs i ->
  i.(RangeInputs.basketsHeldTop) <= (basketRange i).(BasketRange.high).
Proof.
  intros V.
  destruct V as [_ _ _ _ Hsup _ Hhs _].
  unfold basketRange. cbn.
  apply Z.min_glb; [lia|exact Hsup].
Qed.

(** INV-TS: high <= supplyTotal. The clip step makes this immediate. *)
Lemma basket_range_high_le_supply (i : RangeInputs.t) :
  (basketRange i).(BasketRange.high) <= i.(RangeInputs.supplyTotal).
Proof.
  unfold basketRange. cbn.
  apply Z.le_min_r.
Qed.

(** ============================================================ *)
(** ===== Noise / headroom bounds =============================== *)
(** ============================================================ *)

(** Helper: dustNoiseBU is non-negative under non-negative inputs and
    a positive divisor. *)
Lemma dustNoiseBU_nonneg (mtv buPriceHigh : Z) :
  0 <= mtv ->
  0 < buPriceHigh ->
  0 <= dustNoiseBU mtv buPriceHigh.
Proof.
  intros Hmtv Hbup.
  unfold dustNoiseBU, ceil_div.
  destruct ((mtv * FIX_ONE) mod buPriceHigh =? 0).
  - apply Z.div_pos; [|lia].
    apply Z.mul_nonneg_nonneg; [exact Hmtv|unfold FIX_ONE; lia].
  - assert (0 <= (mtv * FIX_ONE) / buPriceHigh).
    { apply Z.div_pos; [|lia].
      apply Z.mul_nonneg_nonneg; [exact Hmtv|unfold FIX_ONE; lia]. }
    lia.
Qed.

(** INV-NF (a): noise_tight is non-negative on sane inputs. *)
Lemma noise_tight_nonneg (bl mtv buPriceHigh : Z) :
  0 <= bl ->
  0 <= mtv ->
  0 < buPriceHigh ->
  0 <= noise_tight bl mtv buPriceHigh.
Proof.
  intros Hbl Hmtv Hbup.
  unfold noise_tight.
  pose proof dustNoiseBU_nonneg mtv buPriceHigh Hmtv Hbup as Hdust.
  assert (0 <= bl * dustNoiseBU mtv buPriceHigh)
    by (apply Z.mul_nonneg_nonneg; assumption).
  lia.
Qed.

(** INV-NF (b): noise_loose is non-negative on sane inputs. *)
Lemma noise_loose_nonneg (bl mtv buPriceHigh : Z) :
  0 <= bl ->
  0 <= mtv ->
  0 < buPriceHigh ->
  0 <= noise_loose bl mtv buPriceHigh.
Proof.
  intros Hbl Hmtv Hbup.
  unfold noise_loose.
  pose proof dustNoiseBU_nonneg mtv buPriceHigh Hmtv Hbup as Hdust.
  assert (0 <= bl * dustNoiseBU mtv buPriceHigh)
    by (apply Z.mul_nonneg_nonneg; assumption).
  assert (0 <= bl * bl) by (apply Z.mul_nonneg_nonneg; lia).
  lia.
Qed.

(** INV-TL: tight bound is no looser than the production bound,
    for [bl >= 5]. This is the algebraic claim driving
    cas/rebalance/noise_bound_tightness.gp. *)
Lemma noise_tight_le_loose (bl mtv buPriceHigh : Z) :
  5 <= bl ->
  noise_tight bl mtv buPriceHigh <= noise_loose bl mtv buPriceHigh.
Proof.
  intros Hbl.
  unfold noise_tight, noise_loose.
  (* reduces to 4*bl + 4 <= bl*bl + 2, i.e. 4*bl + 2 <= bl^2 *)
  assert (4 * bl + 2 <= bl * bl) by nia.
  lia.
Qed.

(** ============================================================ *)
(** ===== Range-gap bound (the central tightness claim) ========= *)
(** ============================================================ *)

(** Structural form of the central claim:
      high - low  <=  (basketsHeldTop - basketsHeldBottom)
                       + lowSlack + highSlack.
    The (bhTop - bhBottom) term comes from the price-low/high spread
    on the held basket; the slacks are the per-asset noise budgets
    accumulated by the production loop. *)
Lemma basket_range_gap_le_slacks (i : RangeInputs.t) :
  Valid.inputs i ->
  (basketRange i).(BasketRange.high) - (basketRange i).(BasketRange.low)
    <= (i.(RangeInputs.basketsHeldTop) - i.(RangeInputs.basketsHeldBottom))
       + i.(RangeInputs.lowSlack) + i.(RangeInputs.highSlack).
Proof.
  intros V.
  destruct V as [_ _ _ Hbb Hbt Hls Hhs _].
  unfold basketRange. cbn.
  remember (i.(RangeInputs.basketsHeldTop) + i.(RangeInputs.highSlack))
    as raw_high eqn:Eraw_high.
  remember (i.(RangeInputs.basketsHeldBottom) - i.(RangeInputs.lowSlack))
    as raw_low eqn:Eraw_low.
  remember (Z.min raw_high i.(RangeInputs.supplyTotal))
    as high1 eqn:Ehigh1.
  (* Now the goal contains [Z.min raw_low high1] explicitly. *)
  destruct (Z.min_spec raw_low high1) as [Hcase | Hcase].
  - destruct Hcase as [Hle Heq]. rewrite Heq.
    assert (Hh : high1 <= raw_high)
      by (subst high1; apply Z.le_min_l).
    subst raw_high raw_low. lia.
  - destruct Hcase as [Hlt Heq]. rewrite Heq. lia.
Qed.

(** INV-NF: under a noise_tight slack budget *and* a bound on the
    basketsHeldTop / basketsHeldBottom spread, the (high - low) gap
    is finite. This is the propagated form of the
    "gap bounded by noise + price-error" claim from the CAS scripts.

    The [bhSpreadBound] arg captures the production
    [(basketsHeldTop - basketsHeldBottom) <= 2 * priceErrorBound]
    relationship: the same balances priced high vs low cannot differ
    by more than twice the per-asset price-error envelope. *)
Lemma noise_bound_finite (i : RangeInputs.t)
    (bl mtv buPriceHigh priceErrorBound : Z) :
  Valid.inputs i ->
  i.(RangeInputs.basketsHeldTop) - i.(RangeInputs.basketsHeldBottom)
    <= 2 * priceErrorBound ->
  i.(RangeInputs.lowSlack)  <= noise_tight bl mtv buPriceHigh ->
  i.(RangeInputs.highSlack) <= noise_tight bl mtv buPriceHigh ->
  (basketRange i).(BasketRange.high) - (basketRange i).(BasketRange.low)
    <= 2 * noise_tight bl mtv buPriceHigh + 2 * priceErrorBound.
Proof.
  intros V Hsprd Hlo Hhi.
  pose proof basket_range_gap_le_slacks i V.
  lia.
Qed.

(** ============================================================ *)
(** ===== CAS algebraic claim (per-asset contribution) ========== *)
(** ============================================================ *)

(** The CAS scripts factor the noise into per-asset contributions
      [contribution_i = 2 * priceError_i * weight_i]
    and claim the sum is bounded by [2 * priceErrorBound * sum(weight_i)].
    We prove the per-asset bound here.

    [priceError] is the per-asset spread (high - low) bound; [weight]
    is the per-asset balance contribution. The factor 2 comes from the
    bound applying symmetrically to top and bottom legs. *)
Lemma per_asset_noise_le (priceError priceErrorBound weight : Z) :
  0 <= priceError <= priceErrorBound ->
  0 <= weight ->
  2 * priceError * weight <= 2 * priceErrorBound * weight.
Proof.
  intros [Hpe1 Hpe2] Hw.
  apply Z.mul_le_mono_nonneg_r; [exact Hw|].
  lia.
Qed.

(** Aggregate form: summing two per-asset contributions.  The full sum
    is induced by induction on a list of weights; we prove the binary
    case here as the key step (the inductive lift is standard). *)
Lemma per_asset_noise_sum_le
    (pe1 pe2 priceErrorBound w1 w2 : Z) :
  0 <= pe1 <= priceErrorBound ->
  0 <= pe2 <= priceErrorBound ->
  0 <= w1 ->
  0 <= w2 ->
  2 * pe1 * w1 + 2 * pe2 * w2
    <= 2 * priceErrorBound * (w1 + w2).
Proof.
  intros Hpe1 Hpe2 Hw1 Hw2.
  pose proof per_asset_noise_le pe1 priceErrorBound w1 Hpe1 Hw1.
  pose proof per_asset_noise_le pe2 priceErrorBound w2 Hpe2 Hw2.
  nia.
Qed.

(** ============================================================ *)
(** ===== Numerical sanity at small bl =========================== *)
(** ============================================================ *)

(** At [bl = 5] the loose / tight gap is exactly 3 (4*5+2 = 22 vs 5^2 = 25),
    matching cas/rebalance/noise_bound_tightness.gp section (a). *)
Lemma noise_gap_at_bl_5 :
  noise_loose 5 0 1 - noise_tight 5 0 1 = 3.
Proof. vm_compute. reflexivity. Qed.

(** At [bl = 10] the gap is 58. *)
Lemma noise_gap_at_bl_10 :
  noise_loose 10 0 1 - noise_tight 10 0 1 = 58.
Proof. vm_compute. reflexivity. Qed.

(** Saturation: zero basket-length collapses both bounds to a constant. *)
Lemma noise_zero_bl :
  noise_tight 0 0 1 = 4 /\ noise_loose 0 0 1 = 2.
Proof. split; vm_compute; reflexivity. Qed.

End RebalanceProofs.
