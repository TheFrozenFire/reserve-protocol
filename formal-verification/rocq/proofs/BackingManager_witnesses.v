(** BackingManager pinned numerical witnesses.

    The CAS scripts [cas/backing_manager/forward_revenue_conservation.gp]
    and [cas/backing_manager/backing_buffer_ceil_witness.gp] enumerate
    concrete [(basketsHeldBottom, basketsNeeded, backingBuffer)] and
    [(needed, quantity, bal, decimals, rTokenTotal, rsrTotal)] inputs
    that exercise:

      - The post-#1283 CEIL rounding mitigation on
        [needed = basketsNeeded.mul(FIX_ONE + backingBuffer, CEIL)] —
        the Certora-audited buffer-ceil witness.
      - Forward-revenue conservation across the surplus split:
        rTokenAmount + rsrAmount + dust = delta.
      - The [bal <= req] short-circuit: every output is zero.
      - Boundary algebra at [backingBuffer = 0] (CEIL no-op) and at
        [backingBuffer = MAX_BACKING_BUFFER] (needed doubles exactly).

    Each lemma below pins one CAS witness as a Rocq theorem closed by
    [vm_compute; reflexivity] (or [vm_compute; discriminate] for shape
    discrimination). No admits.

    Companion to:
      - [proofs/BackingManager.v]: universal accounting lemmas.
      - [proofs/BackingManager_xcheck.v]: simulation × CAS oracle parity.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.

Module BackingManagerWitnesses.

Import FixLib.
Import BackingManager.

(** Distributor totals as in the calibration corpus. *)
Definition rTokenTotal : U256.t := 4000.
Definition rsrTotal    : U256.t := 6000.

(** ============================================================
    A. computeNewBasketsAndNeeded — Certora-audited CEIL witness
    ============================================================ *)

(** A1. Canonical input from the task brief: 1B BU at the 0.01% buffer
    (10^14 in D18). The product (1B*FIX_ONE)*(FIX_ONE + 10^14) is an
    exact multiple of FIX_ONE, so CEIL = FLOOR and
    needed = 10^27 + 10^23 = 1000100000000000000000000000. *)
Lemma witness_needed_1B_buf_0p01 :
  let bn := 10^9 * FIX_ONE in
  let st := computeNewBasketsAndNeeded bn bn (10^14) in
  st.(BasketState.needed) = 1000100000000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** A2. Same calibration, mintAmount = 0 because basketsHeldBottom equals
    basketsNeeded (no surplus baskets, so no RToken to mint). *)
Lemma witness_mintAmount_1B_no_surplus :
  let bn := 10^9 * FIX_ONE in
  let st := computeNewBasketsAndNeeded bn bn (10^14) in
  st.(BasketState.mintAmount) = 0.
Proof. vm_compute. reflexivity. Qed.

(** A3. Same calibration, basketsNeeded' = bn (no upward bump). *)
Lemma witness_basketsNeeded_1B_unchanged :
  let bn := 10^9 * FIX_ONE in
  let st := computeNewBasketsAndNeeded bn bn (10^14) in
  st.(BasketState.basketsNeeded) = bn.
Proof. vm_compute. reflexivity. Qed.

(** A4. Smallest-witness corpus from backing_buffer_ceil_witness.gp:
    at bn = 1, buf = MAX - 1 (= FIX_ONE - 1), CEIL gives 2 but FLOOR
    would give 1. We assert the post-mitigation value = 2. *)
Lemma witness_high_buf_smallest_ceil_bump :
  let buf := MAX_BACKING_BUFFER - 1 in
  let st := computeNewBasketsAndNeeded 1 1 buf in
  st.(BasketState.needed) = 2.
Proof. vm_compute. reflexivity. Qed.

(** A5. Discriminator: at bn = 1, buf = MAX - 1, CEIL strictly exceeds
    FLOOR, so needed != 1. Pinned via [discriminate]. *)
Lemma witness_high_buf_needed_not_floor :
  let buf := MAX_BACKING_BUFFER - 1 in
  let st := computeNewBasketsAndNeeded 1 1 buf in
  st.(BasketState.needed) = 1 -> False.
Proof. vm_compute. discriminate. Qed.

(** A6. (F)-witness from backing_buffer_ceil_witness.gp: at
    buf = MAX_BACKING_BUFFER (100%), needed = 2 * bn exactly across the
    bn corpus. Pin off = 99 (last of the 100-element sweep). *)
Lemma witness_buf_max_doubles_at_off_99 :
  let bn := 10^6 * FIX_ONE + 99 in
  let st := computeNewBasketsAndNeeded bn bn MAX_BACKING_BUFFER in
  st.(BasketState.needed) = 2 * bn.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    B. computeSurplusSplit — forward-revenue conservation
    ============================================================ *)

(** B1. report_split("excess = 1M qTok") from forward_revenue_conservation.gp.
    delta = 10^6, totalShares = 10000, tps = 100, rsrShare = 600000,
    rTokShare = 400000, dust = 0. *)
Lemma witness_split_1M :
  computeSurplusSplit 0 0 (10^6) 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 600000;
      SurplusSplit.rTokenAmount := 400000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B2. report_split("excess = 10^18 qTok") from forward_revenue_conservation.gp.
    delta = 10^18, totalShares = 10000, tps = 10^14,
    rsrShare = 6 * 10^17, rTokShare = 4 * 10^17, dust = 0. *)
Lemma witness_split_1e18 :
  computeSurplusSplit 0 0 (10^18) 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 600000000000000000;
      SurplusSplit.rTokenAmount := 400000000000000000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B3. report_split("excess = 10^25 qTok"): delta = 10^25, tps = 10^21,
    rsrShare = 6 * 10^24, rTokShare = 4 * 10^24, dust = 0. *)
Lemma witness_split_1e25 :
  computeSurplusSplit 0 0 (10^25) 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 6000000000000000000000000;
      SurplusSplit.rTokenAmount := 4000000000000000000000000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B4. report_split("excess = 1 qTok (worst)"): delta = 1, tps = 0,
    rsrShare = rTokShare = 0, dust = 1 (entirely retained). *)
Lemma witness_split_1_qtok_all_dust :
  computeSurplusSplit 0 0 1 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 1;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B5. report_split("excess = 9999 (totalShares-1)"): delta = 9999,
    tps = 0, all dust = delta. *)
Lemma witness_split_9999_below_total :
  computeSurplusSplit 0 0 9999 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 9999;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B6. Conservation at delta = 12345 (off-multiple): tps = 1,
    rsrShare = 6000, rTokShare = 4000, dust = 12345 - 10000 = 2345.
    Verifies rsrAmount + rTokenAmount + dust = delta. *)
Lemma witness_split_conservation_12345 :
  computeSurplusSplit 0 0 12345 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 6000;
      SurplusSplit.rTokenAmount := 4000;
      SurplusSplit.dust         := 2345;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B7. Boundary: bal <= req — every output is zero. Sets needed = 1,
    quantity = FIX_ONE, so req = ceil(1 * FIX_ONE / FIX_ONE) = 1. With
    bal = 1, bal <= req triggers and the result is (0, 0, 0). *)
Lemma witness_split_bal_le_req_zero :
  computeSurplusSplit 1 FIX_ONE 1 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B8. Boundary at the strict equality bal = req: still (0, 0, 0)
    because the production guard is bal <= req (not <). *)
Lemma witness_split_bal_eq_req_zero :
  computeSurplusSplit FIX_ONE FIX_ONE FIX_ONE 0 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

(** B9. shiftl_toUint with positive decimals: with bal - req = 1 and
    decimals = 6, delta = 10^6, tps = 100, conservation holds with
    dust = 0. Exercises the asset-decimals leg of the harness. *)
Lemma witness_split_shiftl_decimals_6 :
  computeSurplusSplit 0 0 1 6 rTokenTotal rsrTotal
  = Result.Success {|
      SurplusSplit.rsrAmount    := 600000;
      SurplusSplit.rTokenAmount := 400000;
      SurplusSplit.dust         := 0;
    |}.
Proof. vm_compute. reflexivity. Qed.

End BackingManagerWitnesses.
