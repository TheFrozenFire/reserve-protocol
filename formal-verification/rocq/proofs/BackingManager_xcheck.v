(** BackingManager simulation × CAS witness cross-check.

    Evaluates the [BackingManager] simulation on the same inputs used
    by the two CAS witness scripts and asserts identical outputs. Any
    drift between the Rocq simulation and the CAS witness corpora fails
    the build.

    Witness sources:
      cas/backing_manager/forward_revenue_conservation.gp
      cas/backing_manager/backing_buffer_ceil_witness.gp

    Calibration (matching both scripts):
      basketsNeeded     = 10^6 * FIX_ONE          (= 10^24)
      backingBuffer     = 10^16                   (= 1% in D18)
      MAX_BACKING_BUFFER = FIX_ONE                (= 10^18, 100%)
      Distributor totals = (rTokenTotal=4000, rsrTotal=6000)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.

Module BackingManagerXCheck.

Import FixLib.
Import BackingManager.

(** Calibration constants from the CAS scripts. *)
Definition cal_basketsNeeded : U256.t := 10^6 * FIX_ONE.
Definition cal_backingBuffer : U256.t := 10^16.
Definition cal_rTokenTotal   : U256.t := 4000.
Definition cal_rsrTotal      : U256.t := 6000.

(** ===== forward_revenue_conservation.gp witnesses ===== *)

(** INV-1: at the calibrated round-number input, needed_post = needed_pre
    = 1.01 * 10^24 (exact-rational ceil). CAS reports
    [needed_post (CEIL) = 1010000000000000000000000]. *)
Lemma xcheck_needed_at_calibration :
  let st := computeNewBasketsAndNeeded cal_basketsNeeded cal_basketsNeeded
                                        cal_backingBuffer in
  st.(BasketState.needed) = 1010000000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** Held-bottom = basketsNeeded * (1+buf), full collateralization +
    no excess: mintAmount = 0. *)
Lemma xcheck_mintAmount_at_calibration_no_excess :
  let st := computeNewBasketsAndNeeded
              (cal_basketsNeeded * (FIX_ONE + cal_backingBuffer) / FIX_ONE)
              cal_basketsNeeded cal_backingBuffer in
  st.(BasketState.mintAmount) = 0.
Proof. vm_compute. reflexivity. Qed.

(** INV-3: held = bn * (1+buf) * 1.005. CAS reports baskets = 1005000...0
    (1.005M BU), basketsNeeded_old = 10^6 * FIX_ONE, mint = 5000 * FIX_ONE. *)
Lemma xcheck_mint_inv3 :
  let bn   := cal_basketsNeeded in
  let buf  := cal_backingBuffer in
  let held := bn * (FIX_ONE + buf) * 1005 / (FIX_ONE * 1000) in
  let st   := computeNewBasketsAndNeeded held bn buf in
  st.(BasketState.mintAmount) = 5000 * FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** INV-4: at backingBuffer = 0, needed = basketsNeeded. *)
Lemma xcheck_needed_buffer_zero :
  let st := computeNewBasketsAndNeeded cal_basketsNeeded cal_basketsNeeded 0 in
  st.(BasketState.needed) = cal_basketsNeeded.
Proof. vm_compute. reflexivity. Qed.

(** INV-5: at buf = MAX_BACKING_BUFFER (= FIX_ONE), needed = 2 * basketsNeeded. *)
Lemma xcheck_needed_at_buffer_max :
  let st := computeNewBasketsAndNeeded cal_basketsNeeded cal_basketsNeeded
                                        MAX_BACKING_BUFFER in
  st.(BasketState.needed) = 2 * cal_basketsNeeded.
Proof. vm_compute. reflexivity. Qed.

(** INV-2: surplus split conservation at delta = 1M (rTok=4000, rsr=6000).
    CAS reports tps=100, rsrShare=600000, rTokShare=400000, dust=0.
    Set needed=0, quantity=0, bal=10^6 so req=0 and delta = bal - req = 10^6
    (with decimals=0 so shiftl_toUint is identity). *)
Lemma xcheck_surplus_split_1M :
  computeSurplusSplit 0 0 (10^6) 0 cal_rTokenTotal cal_rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 600000;
      SurplusSplit.rTokenAmount := 400000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** INV-2: at delta = 1k (= 1000) below totalShares = 10000:
    tps=0, all dust = delta. CAS reports
    [delta=1000 tps=0 rsrShare=0 rTokShare=0 dust=1000]. *)
Lemma xcheck_surplus_split_1k_below_total :
  computeSurplusSplit 0 0 1000 0 cal_rTokenTotal cal_rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 1000;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** INV-2: at delta = 10000 (= totalShares): tps=1, dust=0.
    CAS reports [delta=10000 tps=1 rsrShare=6000 rTokShare=4000 dust=0]. *)
Lemma xcheck_surplus_split_at_total :
  computeSurplusSplit 0 0 10000 0 cal_rTokenTotal cal_rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 6000;
      SurplusSplit.rTokenAmount := 4000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** ===== backing_buffer_ceil_witness.gp witnesses ===== *)

(** (B) Smallest divergence at buf = 1%: at bn = 10^24 + 1, post = 10^24 + 101 + 100 + 1 = ...
    From the CAS output the pattern is needed_post = needed_pre + 1 wei. *)
Lemma xcheck_witness_b_off_1 :
  let st := computeNewBasketsAndNeeded
              (cal_basketsNeeded + 1) (cal_basketsNeeded + 1)
              cal_backingBuffer in
  st.(BasketState.needed) = 1010000000000000000000002.
Proof. vm_compute. reflexivity. Qed.

(** (B) Continuing the witness corpus: at off = 199, needed_post = 1010...0201
    (per CAS report). *)
Lemma xcheck_witness_b_off_199 :
  let st := computeNewBasketsAndNeeded
              (cal_basketsNeeded + 199) (cal_basketsNeeded + 199)
              cal_backingBuffer in
  st.(BasketState.needed) = 1010000000000000000000201.
Proof. vm_compute. reflexivity. Qed.

(** (D) buf = 0: at bn = cal_basketsNeeded, needed = bn. *)
Lemma xcheck_witness_d_buf_zero :
  let st := computeNewBasketsAndNeeded cal_basketsNeeded cal_basketsNeeded 0 in
  st.(BasketState.needed) = cal_basketsNeeded.
Proof. vm_compute. reflexivity. Qed.

(** (E) High-buffer regime: at bn = 1, buf = MAX_BACKING_BUFFER - 1,
    CAS reports post = 2 (= ceil((1*(2*FIX_ONE - 1))/FIX_ONE) = 2). *)
Lemma xcheck_witness_e_high_buf :
  let st := computeNewBasketsAndNeeded 1 1 (MAX_BACKING_BUFFER - 1) in
  st.(BasketState.needed) = 2.
Proof. vm_compute. reflexivity. Qed.

(** (F) buf = MAX_BACKING_BUFFER: needed = 2 * bn (sweep all 100). *)
Lemma xcheck_witness_f_max_buf_at_off_50 :
  let bn := cal_basketsNeeded + 50 in
  let st := computeNewBasketsAndNeeded bn bn MAX_BACKING_BUFFER in
  st.(BasketState.needed) = 2 * bn.
Proof. vm_compute. reflexivity. Qed.

End BackingManagerXCheck.
