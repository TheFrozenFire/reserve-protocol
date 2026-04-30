(** TradeLib numerical witnesses — pinned closed-form values.

    Companion to [TradeLib_xcheck.v] but focused on pinning specific
    numerical outputs of [buyAmount], [buyAmountPre], and
    [coverDeficitSellAmount] at canonical inputs (slippage 0%, 1%, 5%,
    full; saturation at FIX_MAX; ceil-rounding witness from PR #1283).

    Each lemma is a closed-form integer equality discharged by
    [vm_compute. reflexivity.] (or [discriminate.]). Drift in the
    simulation kernel — or in the [Fixed] dependency — fails the build
    here before it can propagate.

    Witness sources:
      cas/trade_lib/slippage_sufficiency.gp (sections 1, 2, 3)
      cas/trade_lib/ceil_rounding_witness.gp (sections A, B, C, D)

    Calibration (matching both CAS scripts):
      sellLow  = 99 * 10^16    ($0.99 in D18)
      buyHigh  = 101 * 10^16   ($1.01 in D18)
      sellAmt  = 10^6 * FIX_ONE  ($1M of sell token)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.TradeLib.

Module TradeLibWitnesses.

Import FixLib.
Import TradeLib.

(** Calibration constants. *)
Definition cal_sellLow  : Z := 99 * 10^16.
Definition cal_buyHigh  : Z := 101 * 10^16.
Definition cal_sellAmt  : Z := 10^6 * FIX_ONE.

(** ============================================================== *)
(** ===== buyAmount at canonical slippage values ================= *)
(** ============================================================== *)

(** ----- (1a) Slippage = 0%: b = ceil(s * sellLow / buyHigh).

    s = 10^24, sellLow = 99e16, buyHigh = 101e16.
    99 * 10^24 / 101 = 980198019801980198019801 remainder 99.
    ceil = 980198019801980198019802. ----- *)
Lemma witness_buyAmount_slippage_0pct :
  buyAmount cal_sellAmt 0 cal_sellLow cal_buyHigh
  = 980198019801980198019802.
Proof. vm_compute. reflexivity. Qed.

(** ----- (1b) Slippage = 1% (10^16 in D18).

    inner_ceil = ceil(10^24 * 99e16 / 10^18) = 99 * 10^22.
    buy = ceil(99 * 10^22 * 99e16 / 101e16)
        = ceil(99^2 * 10^22 / 101)
        = 970396039603960396039604. ----- *)
Lemma witness_buyAmount_slippage_1pct :
  buyAmount cal_sellAmt (10^16) cal_sellLow cal_buyHigh
  = 970396039603960396039604.
Proof. vm_compute. reflexivity. Qed.

(** ----- (1c) Slippage = 5% (5 * 10^16 in D18).
    Closed-form value via vm_compute. ----- *)
Lemma witness_buyAmount_slippage_5pct :
  buyAmount cal_sellAmt (5 * 10^16) cal_sellLow cal_buyHigh
  = 931188118811881188118812.
Proof. vm_compute. reflexivity. Qed.

(** ----- (1d) Slippage = 0.5% (the production calibration).
    Already pinned by xcheck; mirrored here for completeness. ----- *)
Lemma witness_buyAmount_slippage_0p5pct :
  buyAmount cal_sellAmt (5 * 10^15) cal_sellLow cal_buyHigh
  = 975297029702970297029703.
Proof. vm_compute. reflexivity. Qed.

(** ----- (1e) Slippage = FIX_ONE: full-slippage boundary is zero
    with no underflow. ----- *)
Lemma witness_buyAmount_full_slippage_zero :
  buyAmount cal_sellAmt FIX_ONE cal_sellLow cal_buyHigh = 0.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================== *)
(** ===== Certora #1283 ceil-rounding witness ==================== *)
(** ============================================================== *)

(** ----- (2a) At s = sellAmt + 1 with the production 0.5% slippage,
    the post-mitigation buyAmount is strictly greater than the pre-
    mitigation buyAmountPre. The CEIL inner rounding bumps the inner
    mul up by 1, which the outer safeMulDiv-CEIL then propagates.

    Pre  = 975297029702970297029703.
    Post = 975297029702970297029704.
    Delta = +1 wei. ----- *)
Lemma witness_ceil_rounding_post_strictly_greater_at_off1 :
  buyAmountPre (cal_sellAmt + 1) (5 * 10^15) cal_sellLow cal_buyHigh
  <  buyAmount   (cal_sellAmt + 1) (5 * 10^15) cal_sellLow cal_buyHigh.
Proof. vm_compute. reflexivity. Qed.

(** ----- (2b) Pin the exact pre-fix value at s = sellAmt + 1. ----- *)
Lemma witness_ceil_rounding_pre_value_at_off1 :
  buyAmountPre (cal_sellAmt + 1) (5 * 10^15) cal_sellLow cal_buyHigh
  = 975297029702970297029703.
Proof. vm_compute. reflexivity. Qed.

(** ----- (2c) Pin the exact post-fix value at s = sellAmt + 1.
    Together with (2b) this proves the +1 wei delta is real. ----- *)
Lemma witness_ceil_rounding_post_value_at_off1 :
  buyAmount (cal_sellAmt + 1) (5 * 10^15) cal_sellLow cal_buyHigh
  = 975297029702970297029704.
Proof. vm_compute. reflexivity. Qed.

(** ----- (2d) Section (C) sanity: at an exact-multiple input
    (s = 200 * FIX_ONE, where s * (FIX_ONE - 0.5%) divides FIX_ONE),
    pre and post agree on the same value. ----- *)
Lemma witness_ceil_rounding_exact_multiple_value :
  buyAmount (200 * FIX_ONE) (5 * 10^15) cal_sellLow cal_buyHigh
  = 195059405940594059406.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================== *)
(** ===== coverDeficitSellAmount boundary witnesses ============== *)
(** ============================================================== *)

(** ----- (3a) Zero deficit -> zero sell amount. ----- *)
Lemma witness_coverDeficit_zero_deficit :
  coverDeficitSellAmount 0 (5 * 10^15) cal_sellLow cal_buyHigh = 0.
Proof. vm_compute. reflexivity. Qed.

(** ----- (3b) At slippage = 0 and b = FIX_ONE (one whole token of
    deficit), the sell amount is exactly ceil(FIX_ONE * buyHigh / sellLow):
       ceil(10^18 * 101e16 / 99e16)
     = ceil(101 * 10^18 / 99)
     = 1020202020202020203 (101 * 10^18 = 99 * 1020202020202020202 + 2,
       so the CEIL bumps to 1020202020202020203). ----- *)
Lemma witness_coverDeficit_zero_slippage_unit :
  coverDeficitSellAmount FIX_ONE 0 cal_sellLow cal_buyHigh
  = 1020202020202020203.
Proof. vm_compute. reflexivity. Qed.

(** ----- (3c) coverDeficit at b = 10^21 with the production 0.5%
    slippage. Pinned numerical value. ----- *)
Lemma witness_coverDeficit_calibration :
  coverDeficitSellAmount (10^21) (5 * 10^15) cal_sellLow cal_buyHigh
  = 1025328663519618293489.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================== *)
(** ===== Saturation witnesses at FIX_MAX inputs ================= *)
(** ============================================================== *)

(** ----- (4a) buyHigh = 0 saturates safeMulDiv to FIX_MAX
    (matches the production safeMulDiv c = 0 branch). ----- *)
Lemma witness_buyAmount_buyHigh_zero_saturates :
  buyAmount cal_sellAmt (5 * 10^15) cal_sellLow 0 = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ----- (4b) sellLow = FIX_MAX triggers safeMulDiv saturation
    (the [b = FIX_MAX] branch). ----- *)
Lemma witness_buyAmount_sellLow_FIX_MAX_saturates :
  buyAmount cal_sellAmt (5 * 10^15) FIX_MAX cal_buyHigh = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** ----- (4c) sellLow = 0 with nonzero buyHigh forces inner * 0 = 0
    in safeMulDiv, which short-circuits to 0 (no saturation,
    no FIX_MAX). This is the [b = 0] short-circuit. ----- *)
Lemma witness_buyAmount_sellLow_zero_returns_zero :
  buyAmount cal_sellAmt (5 * 10^15) 0 cal_buyHigh = 0.
Proof. vm_compute. reflexivity. Qed.

End TradeLibWitnesses.
