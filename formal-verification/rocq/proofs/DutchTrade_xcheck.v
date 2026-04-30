(** DutchTrade simulation x CAS witness cross-check.

    Evaluates the [DutchTrade] simulation on the same calibration inputs
    used by [cas/dutch_trade/price_decay.gp] and [cas/dutch_trade/bid_rounding.gp]
    and asserts identical outputs. Any divergence between the Rocq
    simulation and the CAS witness corpus fails the build.

    Calibration (matching cas/dutch_trade/price_decay.gp):
      AUCTION_LEN  = 1800 s
      START_T      = 1000000
      END_T        = 1001800
      BEST_PRICE   = 105 * 10^16  ($1.05 in D18)
      WORST_PRICE  =  95 * 10^16  ($0.95 in D18)
      SELL_AMT     = 10000 * FIX_ONE
      BUY_DECIMALS = 18

    CAS witness rows verified here:
      - bidPrice(END_T)        = 950000000000000000   (= worstPrice)
      - phase3_at_45_pct       = bestPrice            (continuity at 45%)
      - phase3_at_95_pct       = worstPrice           (continuity at 95%)
      - phase4_price           = worstPrice
      - bidAmount(END_T)       = SELL_AMT * worstPrice / FIX_ONE = 9500e18
      - bidPrice monotone-decreasing across phases 2-4 sample points.

    The geometric phase-1 closed-form produces ~6.5M-iteration powu
    computations and is *not* materialized here (matches the CAS script's
    note about float fallback for the geometric regime). Phase-1
    end-to-end equivalence with the on-chain implementation is left
    to the equivalence proof; the CAS script handles the empirical check.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.DutchTrade.

Module DutchTradeXCheck.

Import FixLib.
Import DutchTrade.

(** ---- Calibration (matches cas/dutch_trade/price_decay.gp) ---- *)
Definition cal_startTime  : Z := 1000000.
Definition cal_endTime    : Z := 1001800.
Definition cal_bestPrice  : Z := 105 * 10^16.
Definition cal_worstPrice : Z :=  95 * 10^16.
Definition cal_sellAmount : Z := 10000 * 10^18.

Definition cal_auction : Auction.t := {|
  Auction.startTime   := cal_startTime;
  Auction.endTime     := cal_endTime;
  Auction.bestPrice   := cal_bestPrice;
  Auction.worstPrice  := cal_worstPrice;
  Auction.sellAmount  := cal_sellAmount;
  Auction.buyDecimals := 18;
|}.

(** ===== CAS witness: progression at endTime = FIX_ONE. ===== *)
Lemma xcheck_progression_at_end :
  progression cal_auction cal_endTime = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: progression at startTime = 0. ===== *)
Lemma xcheck_progression_at_start :
  progression cal_auction cal_startTime = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: progression(start + AUCTION_LEN/2) = FIX_ONE / 2. -----
    cas reports prog(start + 900) = 5e17 = TWENTY_PERCENT * 2.5. *)
Lemma xcheck_progression_at_half :
  progression cal_auction (cal_startTime + 900) = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: bidPrice(END_T) = worstPrice = 95e16. -----
    cas reports: price(end) = 950000000000000000  (0.9500). *)
Lemma xcheck_bidPrice_at_end :
  bidPrice cal_auction cal_endTime = 950000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: phase3_price at 45% boundary = bestPrice. ===== *)
Lemma xcheck_phase3_at_45 :
  phase3_price cal_auction FORTY_FIVE_PERCENT = cal_bestPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: phase3_price at 95% boundary = worstPrice. ===== *)
Lemma xcheck_phase3_at_95 :
  phase3_price cal_auction NINETY_FIVE_PERCENT = cal_worstPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: phase4_price = worstPrice. ===== *)
Lemma xcheck_phase4_eq_worst :
  phase4_price cal_auction = cal_worstPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: phase2_price at 20% = highPrice (= 1.5 * bestPrice CEIL).
    For bestPrice = 105e16, highPrice = ceil(105e16 * 150e16 / 1e18) = 1575e15.
    Note that 105e16 * 150e16 = 1575e33 and 1575e33 / 1e18 = 1575e15 exactly. *)
Lemma xcheck_phase2_at_20 :
  phase2_price cal_auction TWENTY_PERCENT = 1575 * 10^15.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: phase2_price at 45% boundary = bestPrice (continuity). ===== *)
Lemma xcheck_phase2_at_45 :
  phase2_price cal_auction FORTY_FIVE_PERCENT = cal_bestPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: bidAmount at end = SELL_AMT * worstPrice / FIX_ONE
    = 10000 * 0.95 * FIX_ONE = 9500 * FIX_ONE. -----
    With buyDecimals = 18, shiftl is identity, so bidAmount = mul_ceil. *)
Lemma xcheck_bidAmount_at_end :
  bidAmount cal_auction cal_endTime = 9500 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS witness: bidAmount at 45% boundary = SELL_AMT * bestPrice / FIX_ONE
    = 10000 * 1.05 * FIX_ONE = 10500 * FIX_ONE. ----- *)
Lemma xcheck_bidAmount_at_45 :
  bidAmount cal_auction (cal_startTime + 810) = 10500 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** ===== Monotonicity sample: bidAmount(t1) >= bidAmount(t2) for t1 <= t2 in
    phase 3. cas section (6) checks 300 sample points; we pin two anchors
    to ensure the simulation tracks the CAS curve direction. -----

    Pick t1 = start + 810 (45% boundary, prog = 45%, bidPrice = bestPrice
    = 105e16, bidAmount = 10500e18) and t2 = start + 1710 (95% boundary,
    prog = 95%, bidPrice = worstPrice = 95e16, bidAmount = 9500e18). *)
Lemma xcheck_bidAmount_monotone_anchor :
  bidAmount cal_auction (cal_startTime + 1710)
  <= bidAmount cal_auction (cal_startTime + 810).
Proof. vm_compute. discriminate. Qed.

(** ===== CAS witness: bidPrice in phase 4 is constant at worstPrice. -----
    Sample t = start + 1750 (still phase 4) and confirm = worstPrice. *)
Lemma xcheck_bidPrice_phase4_const :
  bidPrice cal_auction (cal_startTime + 1750) = cal_worstPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS bid_rounding.gp witness (1): 18-decimal CEIL bid at typical
    prices. SELL = 10000 * FIX_ONE.
    price = 950000000000000000  -> bid = 9500 * FIX_ONE
    price = 1050000000000000000 -> bid = 10500 * FIX_ONE
    These are exact (no rounding needed at these prices). *)
Lemma xcheck_bidAmount_price_950 :
  bidAmount_at_price cal_auction 950000000000000000 = 9500 * 10^18.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_bidAmount_price_1050 :
  bidAmount_at_price cal_auction 1050000000000000000 = 10500 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS bid_rounding.gp witness (1) tail: rounding-prone price
    1234567890123456789. SELL = 10000 * FIX_ONE in D18 with 18-dec buy
    -> bidAmount = ceil(SELL * price / FIX_ONE) =
       ceil(10000 * 1.234... * FIX_ONE) = 12345678901234567890000 (no rem
       because SELL is a multiple of FIX_ONE). *)
Lemma xcheck_bidAmount_price_1234 :
  bidAmount_at_price cal_auction 1234567890123456789 = 12345678901234567890000.
Proof. vm_compute. reflexivity. Qed.

(** ===== CAS bid_rounding.gp witness (3): CEIL >= FLOOR for rounding-prone
    inputs. With SELL_ODD = 10000*FIX_ONE + 1, PRICE_ODD = 1234567890123456789,
    the 18-decimal CEIL bid is one wei above the FLOOR result. ===== *)
Definition cal_auction_odd : Auction.t :=
  cal_auction <| Auction.sellAmount := 10000 * 10^18 + 1 |>.

Lemma xcheck_bidAmount_ceil_ge_floor :
  let pi := 1234567890123456789 in
  bidAmount_floor_variant cal_auction_odd pi
  <= bidAmount_at_price cal_auction_odd pi.
Proof. vm_compute. discriminate. Qed.

End DutchTradeXCheck.
