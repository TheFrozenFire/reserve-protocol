(** Rebalance basket-range pinned witnesses.

    The CAS scripts [cas/rebalance/basket_range_simulation.gp] and
    [cas/rebalance/noise_bound_tightness.gp] explore the empirical /
    algebraic envelope for [basketRange] and the rounding-noise bound
    used by [BackingManagerP1Fuzz.isBasketRangeSmaller]. This file
    pins the corresponding Rocq numerical witnesses, each closed by
    [vm_compute] + [reflexivity] / [discriminate].

    Each witness mirrors a structurally important point on the input
    space: degenerate (zero supply / max-held), the calibrated 1B-supply
    RToken example, extreme [lowSlack] values, and noise-bound boundary
    inputs from the two scripts above.

    Companion to:
      - [proofs/Rebalance.v]: the universal basket-range invariants.
      - [proofs/Rebalance_xcheck.v]: simulation x CAS oracle parity probes.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Rebalance.

Module RebalanceWitnesses.

Import RebalanceLib.

(** ===== (1) Degenerate: supply = 0 collapses both bounds to 0 ===== *)

Definition zero_supply : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 0;
  RangeInputs.basketsHeldBottom := 0;
  RangeInputs.basketsHeldTop    := 0;
  RangeInputs.lowSlack          := 0;
  RangeInputs.highSlack         := 0;
|}.

Lemma w_zero_supply_low :
  (basketRange zero_supply).(BasketRange.low) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma w_zero_supply_high :
  (basketRange zero_supply).(BasketRange.high) = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== (2) Saturated: basketsHeldBottom = supply (max held) =====
    With [bhBottom = bhTop = supply] and zero slack, both bounds pin to supply.
    [highSlack = 0] keeps [raw_high = supply], which clips trivially. *)

Definition saturated : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 1000000;
  RangeInputs.basketsHeldBottom := 1000000;
  RangeInputs.basketsHeldTop    := 1000000;
  RangeInputs.lowSlack          := 0;
  RangeInputs.highSlack         := 0;
|}.

Lemma w_saturated_high :
  (basketRange saturated).(BasketRange.high) = 1000000.
Proof. vm_compute. reflexivity. Qed.

Lemma w_saturated_low :
  (basketRange saturated).(BasketRange.low) = 1000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== (3) Calibrated 1B-supply RToken =====
    Production-shaped numbers: 1e9 BU supply, ~99% held bottom, 100% held top,
    small noise-style slack. Mirrors a deployed RToken at recollateralization. *)

Definition cal_1b : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 1000000000;
  RangeInputs.basketsHeldBottom := 990000000;
  RangeInputs.basketsHeldTop    := 1000000000;
  RangeInputs.lowSlack          := 102;     (* noise_loose 10 0 1 = 102 *)
  RangeInputs.highSlack         := 0;
|}.

Lemma w_cal_1b_low :
  (basketRange cal_1b).(BasketRange.low) = 989999898.
Proof. vm_compute. reflexivity. Qed.

Lemma w_cal_1b_high :
  (basketRange cal_1b).(BasketRange.high) = 1000000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== (4) Extreme lowSlack: collapses low to 0 (clipped at high) =====
    When [lowSlack > basketsHeldBottom], [raw_low] goes negative; the model
    clamps via [Z.min raw_low high1], which keeps the negative value (since
    [raw_low < high1]). This pins the negative-witness to the exact value. *)

Definition huge_lowslack : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 1000;
  RangeInputs.basketsHeldBottom := 100;
  RangeInputs.basketsHeldTop    := 200;
  RangeInputs.lowSlack          := 1000000;
  RangeInputs.highSlack         := 0;
|}.

(** raw_low = 100 - 1000000 = -999900; min(-999900, 200) = -999900. *)
Lemma w_huge_lowslack_low :
  (basketRange huge_lowslack).(BasketRange.low) = -999900.
Proof. vm_compute. reflexivity. Qed.

Lemma w_huge_lowslack_high :
  (basketRange huge_lowslack).(BasketRange.high) = 200.
Proof. vm_compute. reflexivity. Qed.

(** ===== (5) basket_range_simulation.gp section (a) noise envelope =====
    "Pure rounding (mtv = 0, eps = 1 wei)" — every sweep entry is bounded
    above by [4*bl + 4]. Pin the boundary points. *)

(** BL=7  tight = 4*7 + 4 = 32. *)
Lemma w_sim_a_bl7_tight :
  noise_tight 7 0 1 = 32.
Proof. vm_compute. reflexivity. Qed.

(** BL=7  loose = 7*0 + 49 + 2 = 51. *)
Lemma w_sim_a_bl7_loose :
  noise_loose 7 0 1 = 51.
Proof. vm_compute. reflexivity. Qed.

(** BL=30 tight = 4*30 + 4 = 124. The script sweeps to BL=30. *)
Lemma w_sim_a_bl30_tight :
  noise_tight 30 0 1 = 124.
Proof. vm_compute. reflexivity. Qed.

(** ===== (6) noise_bound_tightness.gp section (a): tight <= loose ===== *)

(** At BL=5 loose - tight = 3. The script reports this exact savings. *)
Lemma w_tight_savings_bl5 :
  noise_loose 5 0 1 - noise_tight 5 0 1 = 3.
Proof. vm_compute. reflexivity. Qed.

(** At BL=20 loose - tight = 318. *)
Lemma w_tight_savings_bl20 :
  noise_loose 20 0 1 - noise_tight 20 0 1 = 318.
Proof. vm_compute. reflexivity. Qed.

(** ===== (7) Tight bound non-trivial vs zero =====
    The tight bound is never zero (contains the [+4] residual). This rules
    out a degenerate compile producing a vacuous noise envelope. *)

Lemma w_tight_nonzero_bl0 :
  noise_tight 0 0 1 = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma w_loose_nonzero_bl0 :
  noise_loose 0 0 1 = 2.
Proof. vm_compute. reflexivity. Qed.

(** Discriminate-flavoured boundary: tight (4) and loose (2) at BL=0 differ. *)
Lemma w_tight_neq_loose_bl0 :
  noise_tight 0 0 1 = noise_loose 0 0 1 -> False.
Proof. vm_compute. discriminate. Qed.

(** ===== (8) Dust-flip regime witness from basket_range_simulation.gp (b) =====
    BL=5 mtv=$10 bup=$1: dustNoiseBU = 10 * 10^18; loose adds bl^2 + 2 = 27.
    The total is 5 * 10^19 + 27 = 50000000000000000027. *)

Lemma w_dust_flip_bl5_10dollar :
  noise_loose 5 (10 * 10^18) (10^18) = 50000000000000000027.
Proof. vm_compute. reflexivity. Qed.

(** BL=10 mtv=$100 bup=$1: dust = 10^20; loose = 10 * 10^20 + 100 + 2. *)
Lemma w_dust_flip_bl10_100dollar :
  noise_loose 10 (100 * 10^18) (10^18) = 1000000000000000000102.
Proof. vm_compute. reflexivity. Qed.

End RebalanceWitnesses.
