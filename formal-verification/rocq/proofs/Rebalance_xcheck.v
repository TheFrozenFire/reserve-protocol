(** Rebalance simulation x CAS witness cross-check.

    Evaluates the [RebalanceLib] simulation on the same numerical
    witnesses produced by the three CAS scripts in cas/rebalance/, and
    asserts identical outputs. Any drift between the Rocq simulation
    and the CAS witness corpus fails the build.

    Witness sources:
      cas/rebalance/basket_range_noise.gp        (loose-bound calibrations)
      cas/rebalance/noise_bound_tightness.gp     (loose vs tight gap)
      cas/rebalance/basket_range_simulation.gp   (empirical sweep grid)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Rebalance.

Module RebalanceXCheck.

Import RebalanceLib.

(** ===== noise_bound_tightness.gp section (a) =====
    "with mtv = 0, only the rounding term remains; this isolates
     the bl^2 vs 4*bl + 2 difference."

    CAS report (verbatim):
      BL= 5:  loose = 27   tight = 24   savings = 3
      BL=10:  loose = 102  tight = 44   savings = 58
      BL=20:  loose = 402  tight = 84   savings = 318
      BL=50:  loose = 2502 tight = 204  savings = 2298
*)

Lemma xcheck_noise_loose_bl5_mtv0 :
  noise_loose 5 0 1 = 27.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_tight_bl5_mtv0 :
  noise_tight 5 0 1 = 24.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_loose_bl10_mtv0 :
  noise_loose 10 0 1 = 102.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_tight_bl10_mtv0 :
  noise_tight 10 0 1 = 44.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_loose_bl20_mtv0 :
  noise_loose 20 0 1 = 402.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_tight_bl50_mtv0 :
  noise_tight 50 0 1 = 204.
Proof. vm_compute. reflexivity. Qed.

(** Section-(a) gap witnesses from the same script. *)
Lemma xcheck_savings_at_bl_10 :
  noise_loose 10 0 1 - noise_tight 10 0 1 = 58.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_savings_at_bl_50 :
  noise_loose 50 0 1 - noise_tight 50 0 1 = 2298.
Proof. vm_compute. reflexivity. Qed.

(** ===== basket_range_noise.gp section (b) =====
    Calibrated on (basketLength, minTradeVolume, buPriceHigh):

      BL= 5  mtv=$10    bup=$1   noise = 50000000000000000027 BU
      BL=20  mtv=$1000  bup=$1   noise = 20000000000000000000402 BU
      BL= 7  mtv=$100   bup=$3k  noise = 233333333333333389 BU

    The CAS script uses FIX_ONE = 10^18 throughout. *)

(** $10 = 10 * 10^18; bup = 10^18. *)
Lemma xcheck_noise_loose_bl5_mtv10_dollar :
  noise_loose 5 (10 * 10^18) (10^18) = 50000000000000000027.
Proof. vm_compute. reflexivity. Qed.

(** $1000 = 1000 * 10^18; bup = 10^18. *)
Lemma xcheck_noise_loose_bl20_mtv1000_dollar :
  noise_loose 20 (1000 * 10^18) (10^18) = 20000000000000000000402.
Proof. vm_compute. reflexivity. Qed.

(** $100 = 100 * 10^18; bup = 3000 * 10^18 (an "ETH+" basket unit).
    dustNoiseBU = ceil(100 * 10^36 / 3000 * 10^18)
                = ceil(10^20 / 3) = 33333333333333334
    then 7 * 33333333333333334 + 49 + 2 = 233333333333333389.
    CAS prints exactly this number. *)
Lemma xcheck_noise_loose_bl7_mtv100_eth :
  noise_loose 7 (100 * 10^18) (3000 * 10^18) = 233333333333333389.
Proof. vm_compute. reflexivity. Qed.

(** Same calibration, tight bound. Gap 49 - 32 = 17 lower. *)
Lemma xcheck_noise_tight_bl7_mtv100_eth :
  noise_tight 7 (100 * 10^18) (3000 * 10^18) = 233333333333333370.
Proof. vm_compute. reflexivity. Qed.

(** ===== basket_range_simulation.gp section (a) =====
    Expected tight bounds match section (a) of the simulation script.

      BL= 7   tight=32  loose=51
      BL=15   tight=64  loose=227
      BL=30   tight=124 loose=902
*)

Lemma xcheck_noise_loose_bl15_mtv0 :
  noise_loose 15 0 1 = 227.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_noise_tight_bl30_mtv0 :
  noise_tight 30 0 1 = 124.
Proof. vm_compute. reflexivity. Qed.

(** ===== Sanity: dustNoiseBU computes the expected ceil ===== *)

(** $0 dust = 0 BU regardless of bup. *)
Lemma xcheck_dust_zero :
  dustNoiseBU 0 (10^18) = 0.
Proof. vm_compute. reflexivity. Qed.

(** Exact division: $1 dust at bup=$1 gives 10^18 BU. *)
Lemma xcheck_dust_unit :
  dustNoiseBU (10^18) (10^18) = 10^18.
Proof. vm_compute. reflexivity. Qed.

(** Inexact division (the +1 ceil branch): 100 / 3000 rounds up.
    100 * 10^36 / (3000 * 10^18) = 33333333333333333.33...
    -> ceiling = 33333333333333334. *)
Lemma xcheck_dust_ceil_branch :
  dustNoiseBU (100 * 10^18) (3000 * 10^18) = 33333333333333334.
Proof. vm_compute. reflexivity. Qed.

(** ===== basketRange structural witnesses =====
    Sample inputs that exercise the clipping path. *)

Definition cal_inputs : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 1000;
  RangeInputs.basketsHeldBottom := 90;
  RangeInputs.basketsHeldTop    := 100;
  RangeInputs.lowSlack          := 5;
  RangeInputs.highSlack         := 7;
|}.

(** With these inputs:
      raw_high = 100 + 7 = 107 ; min(107, 1000) = 107
      raw_low  = 90  - 5 = 85  ; min(85, 107)   = 85
    so the unclipped (low, high) = (85, 107). *)
Lemma xcheck_basketRange_low :
  (basketRange cal_inputs).(BasketRange.low) = 85.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_basketRange_high :
  (basketRange cal_inputs).(BasketRange.high) = 107.
Proof. vm_compute. reflexivity. Qed.

(** Clipped form: when supplyTotal forces high down. *)
Definition cal_inputs_clipped : RangeInputs.t := {|
  RangeInputs.supplyTotal       := 100;
  RangeInputs.basketsHeldBottom := 90;
  RangeInputs.basketsHeldTop    := 100;
  RangeInputs.lowSlack          := 0;
  RangeInputs.highSlack         := 50;
|}.

(** raw_high = 150 ; clipped to supply = 100.
    raw_low  = 90  ; min(90, 100) = 90.
    Result: (90, 100). *)
Lemma xcheck_basketRange_clipped :
  basketRange cal_inputs_clipped
  = {| BasketRange.low := 90; BasketRange.high := 100 |}.
Proof. vm_compute. reflexivity. Qed.

End RebalanceXCheck.
