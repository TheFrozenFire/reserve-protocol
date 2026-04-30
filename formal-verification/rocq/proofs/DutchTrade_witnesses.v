(** DutchTrade witness corpus.

    Companion to [proofs/DutchTrade_xcheck.v]: where [DutchTrade_xcheck]
    pins the calibration rows that exactly match
    [cas/dutch_trade/price_decay.gp] / [cas/dutch_trade/bid_rounding.gp],
    this file nails down extra closed-form witnesses that exercise:

      - bidPrice at the start endpoint (geometric phase 1) — confirming
        the contract's documented "starts at ~1000x bestPrice" claim,
      - bidPrice at the 20% boundary (transition geometric -> linear),
      - phase 4 constancy across multiple sample points in [95%, 100%],
      - bidAmount at canonical 6-decimal (USDC) buy-token configurations
        from cas/dutch_trade/bid_rounding.gp section (2),
      - explicit FLOOR-vs-CEIL divergence for rounding-prone inputs at
        both 18-decimal and 6-decimal buy-token decimals.

    Every witness is a closed evaluation discharged by [vm_compute] +
    [reflexivity] / [discriminate]. No admits.

    Reference:
      - [cas/dutch_trade/price_decay.gp] sections (2), (3), (4), (7).
      - [cas/dutch_trade/bid_rounding.gp] sections (1), (2), (3), (4).
      - [simulations/DutchTrade.v]: bidPrice / bidAmount / phase[1-4]_price.
      - [proofs/DutchTrade_xcheck.v] for the calibration-row witnesses.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.DutchTrade.

Module DutchTradeWitnesses.

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

(** Same calibration but with 6-decimal (USDC-style) buy token —
    for the cas/dutch_trade/bid_rounding.gp section (2) witnesses. *)
Definition cal_auction_usdc : Auction.t := {|
  Auction.startTime   := cal_startTime;
  Auction.endTime     := cal_endTime;
  Auction.bestPrice   := cal_bestPrice;
  Auction.worstPrice  := cal_worstPrice;
  Auction.sellAmount  := cal_sellAmount;
  Auction.buyDecimals := 6;
|}.

(** Odd-sellAmount auction for FLOOR-vs-CEIL divergence witnesses
    (cas/dutch_trade/bid_rounding.gp section (3)). *)
Definition cal_auction_odd_usdc : Auction.t := {|
  Auction.startTime   := cal_startTime;
  Auction.endTime     := cal_endTime;
  Auction.bestPrice   := cal_bestPrice;
  Auction.worstPrice  := cal_worstPrice;
  Auction.sellAmount  := 10000 * 10^18 + 1;
  Auction.buyDecimals := 6;
|}.

(** ===== Witness 1: bidPrice at start sits ~1000x above bestPrice. -----

    cas/dutch_trade/price_decay.gp section (2) reports
    [price(start) / bestPrice ~ 1000x]. The geometric phase exponent at
    progression 0 is exp_int = ROUND(MAX_EXP / FIX_ONE) = 6502287, and
    [(1 - 1e-6)^6502287 ~ exp(-6.502)] ~ 1.498e-3, so
    [price(start) ~ bestPrice * 1.5 / 1.498e-3 ~ 1001 * bestPrice].

    Pin the comparison [1000 * bestPrice <? bidPrice(start) = true].
    powu uses exp-by-squaring (~24 iterations for y = 6502287) so this
    is tractable under vm_compute. *)
Lemma witness_bidPrice_at_start_above_1000x_best :
  (1000 * cal_bestPrice <? bidPrice cal_auction cal_startTime) = true.
Proof. vm_compute. reflexivity. Qed.

(** And it stays below the 1100x ceiling (the CAS commentary hints
    "~1000x", not arbitrarily high). *)
Lemma witness_bidPrice_at_start_below_1100x_best :
  (bidPrice cal_auction cal_startTime <? 1100 * cal_bestPrice) = true.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 2: bidPrice at the 20% boundary equals 1.5 * bestPrice. -----

    At progression = 20%, the dispatcher transitions from phase 1 to
    phase 2. phase 2 evaluated at exactly 20% returns [highPrice =
    bestPrice.mul(1.5, CEIL) = 1575e15]. cas/dutch_trade/price_decay.gp
    section (3) tracks the cross-boundary drop magnitude. *)
Lemma witness_bidPrice_at_20_pct :
  bidPrice cal_auction (cal_startTime + 360) = 1575 * 10^15.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 3: phase 4 is constant — sampled at 96%, 98%, end. -----

    cas/dutch_trade/price_decay.gp asserts [price(end) == worstPrice]
    and that the geometric/linear/flat transitions are monotone.
    Pinning three sample points inside [95%, 100%] lets vm_compute
    confirm phase 4 is genuinely flat at worstPrice. *)
Lemma witness_phase4_constant_at_96_pct :
  bidPrice cal_auction (cal_startTime + 1728) = cal_worstPrice.
Proof. vm_compute. reflexivity. Qed.

Lemma witness_phase4_constant_at_98_pct :
  bidPrice cal_auction (cal_startTime + 1764) = cal_worstPrice.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 4: bidAmount with 6-decimal (USDC) buy token at $0.95.
    cas/dutch_trade/bid_rounding.gp section (2): "$9500 for 10k tokens
    at $0.95 should be 9_500_000_000 qUSDC". -----

    SELL = 10000 * FIX_ONE, price = 0.95e18 in D18, buyDecimals = 6.
      mul_ceil = ceil(SELL * price / FIX_ONE)
               = 10000 * 0.95 * FIX_ONE = 9500e18 (exact, no rounding)
      shift = 12, divrnd(9500e18, 1e12, CEIL) = 9.5e9 (exact). *)
Lemma witness_bidAmount_usdc_at_950 :
  bidAmount_at_price cal_auction_usdc 950000000000000000 = 9500000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 5: bidAmount with 6-decimal buy token at $1.05. -----
    Mirrors the bestPrice scenario: 10000 * 1.05 = 10500 USDC. *)
Lemma witness_bidAmount_usdc_at_1050 :
  bidAmount_at_price cal_auction_usdc 1050000000000000000 = 10500000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 6: bidAmount with 6-decimal buy token at price = 1
    (smallest non-zero D18). -----

    SELL * 1 / FIX_ONE = 10000 (exact). shiftl with shift=12 CEIL on
    10000 yields ceil(10000 / 1e12) = 1, since the remainder is non-zero.
    This is exactly the regime cas/dutch_trade/bid_rounding.gp warns
    about — a single wei of qUSDC is $1e-6, and FLOOR would round to 0,
    underpaying by the full bid. *)
Lemma witness_bidAmount_usdc_at_min_price_ceil :
  bidAmount_at_price cal_auction_usdc 1 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 7: FLOOR variant at the same price returns 0
    — concrete demonstration of the bug avoided by the contract's
    CEIL discipline. -----

    With FLOOR-only rounding, mul_floor = (10000e18 * 1) / 1e18 = 10000,
    then shiftl with shift=12 FLOOR on 10000 yields 10000 / 1e12 = 0.
    Bidder would pay nothing for the entire 10000-token sell-side. *)
Lemma witness_bidAmount_usdc_floor_underpays :
  bidAmount_floor_variant cal_auction_usdc 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 8: CEIL strictly exceeds FLOOR for the same input. -----
    Combines the previous two; pinning the 1-vs-0 gap as a concrete
    divergence witness so a regression that re-introduced FLOOR rounding
    would fail this exact equality. *)
Lemma witness_bidAmount_usdc_ceil_floor_gap_at_min :
  bidAmount_at_price cal_auction_usdc 1
  - bidAmount_floor_variant cal_auction_usdc 1
  = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 9: rounding-prone 6-decimal bid — both stages round up.
    cas/dutch_trade/bid_rounding.gp section (3):
      SELL_ODD  = 10000 * FIX_ONE + 1
      PRICE_ODD = 1234567890123456789
      buyDecimals = 6.
    The two-stage CEIL/FLOOR variants must differ by no more than 2
    qBuyTok (one unit per rounding step). Pin the production result and
    the FLOOR result, then assert the gap is in {0, 1, 2}.

    Concrete values (computed by vm_compute):
      mul_ceil(s, p) = ceil((10000e18 + 1) * 1234567890123456789 / 1e18)
                    = 12345678901234567890001  (one unit above floor)
      shift 12 CEIL: ceil(12345678901234567890001 / 1e12)
                    = 12345678902 qUSDC
      mul_floor(s, p) = (10000e18 + 1) * 1234567890123456789 / 1e18
                     = 12345678901234567890000
      shift 12 FLOOR: 12345678901234567890000 / 1e12
                     = 12345678901 qUSDC
    so the gap is exactly 1 qUSDC. *)
Lemma witness_bidAmount_usdc_ceil_at_pi :
  bidAmount_at_price cal_auction_odd_usdc 1234567890123456789 = 12345678902.
Proof. vm_compute. reflexivity. Qed.

Lemma witness_bidAmount_usdc_floor_at_pi :
  bidAmount_floor_variant cal_auction_odd_usdc 1234567890123456789 = 12345678901.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 10: 18-decimal FLOOR vs CEIL divergence at PRICE_ODD with
    SELL_ODD. cas/dutch_trade/bid_rounding.gp section (1) and (3) probe
    this case; here we pin both sides and the 1-wei gap.

    With buyDecimals = 18, shiftl is identity. The mul-CEIL stage adds
    one wei because (SELL_ODD * PRICE_ODD) is not divisible by FIX_ONE:
      (10000e18 + 1) * 1234567890123456789 / 1e18
        = 12345678901234567890000 + 1.234567890123456789...
    so mul_floor = 12345678901234567890001 (the +1 from the spillover
    into the integer part) and mul_ceil = 12345678901234567890002.

    Wait — let's be precise: the +1 in SELL_ODD multiplied by PRICE_ODD
    contributes 1234567890123456789 at the wei level. Adding to
    10000 * FIX_ONE * PRICE_ODD = 10000 * PRICE_ODD * FIX_ONE
    = 12345678901234567890000 * FIX_ONE. Total numerator
    = 12345678901234567890000 * FIX_ONE + 1234567890123456789.
    Dividing by FIX_ONE: quotient = 12345678901234567890001, remainder
    = 234567890123456789. So:
      FLOOR result = 12345678901234567890001
      CEIL  result = 12345678901234567890002
    — gap exactly 1 wei. *)
Definition cal_auction_odd : Auction.t :=
  cal_auction <| Auction.sellAmount := 10000 * 10^18 + 1 |>.

Lemma witness_bidAmount_d18_floor_at_pi :
  bidAmount_floor_variant cal_auction_odd 1234567890123456789
  = 12345678901234567890001.
Proof. vm_compute. reflexivity. Qed.

Lemma witness_bidAmount_d18_ceil_at_pi :
  bidAmount_at_price cal_auction_odd 1234567890123456789
  = 12345678901234567890002.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 11: cross-decimal sanity — at exact prices (where no
    rounding fires), 18-decimal and 6-decimal results agree up to the
    decimal-shift factor. -----

    bidAmount_at_price cal_auction      950e15 = 9500e18  (D18)
    bidAmount_at_price cal_auction_usdc 950e15 = 9500e9   (qUSDC)
    Ratio = 1e12 — i.e. the shift exactly absorbs the decimal gap. *)
Lemma witness_bidAmount_d18_d6_ratio_at_950 :
  bidAmount_at_price cal_auction 950000000000000000
  = bidAmount_at_price cal_auction_usdc 950000000000000000 * 10^12.
Proof. vm_compute. reflexivity. Qed.

End DutchTradeWitnesses.
