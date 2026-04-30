(** GnosisTrade simulation × CAS witness cross-check.

    Evaluates the [GnosisTrade] simulation on the same calibration inputs
    used by [cas/gnosis_trade/min_buy_amount.gp] and
    [cas/gnosis_trade/settlement_floor.gp] and asserts identical outputs.
    Any divergence between the Rocq simulation and the CAS witness corpus
    fails the build.

    Calibration (per task brief, R005, mirroring both CAS scripts):
      sellAmount       = 10000 sellTok (D18) = 10^22 qSellTok at 18 decimals
      sellPrice (Low)  = $0.99            -> 99e16 in D18
      buyPrice (High)  = $1.01            -> 101e16 in D18
      maxTradeSlippage = 1%               -> 1e16 in D18
      buyDecimals in {6, 18}; sellDecimals = 18

    CAS-reported numerical witnesses:
      18-dec minBuyAmount = 9703960396039603960397 qBuyTok
       6-dec minBuyAmount = 9703960397            qBuyTok
      18-dec worstCasePrice = 970396039603960396039700000  D27{qBuy/qSell}
       6-dec worstCasePrice =          970396039700000      D27{qUSDC/qSell}

    Settlement-side witnesses (settlement_floor.gp):
      Full fill at minBuyAmount: clearingPrice = 970396039603960396039800000,
        violation = 0  (the +1 pad pushes clearing 1 D27-wei above wcp).
      Full fill at minBuyAmount - 1: violation = 0 (pad still absorbs).
      Full fill at minBuyAmount - 2: violation = 1 (pad exhausted).
      cancellationEndTime offset at length=1800s: +1620s.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.GnosisTrade.

Module GnosisTradeXCheck.

Import FixLib.
Import GnosisTrade.

(** ===== Calibration ===== *)
Definition cal_sellAmount : Z := 10000 * FIX_ONE.       (** 10^22 D18 wei *)
Definition cal_sellLow    : Z := 99  * 10^16.           (** $0.99 in D18 *)
Definition cal_buyHigh    : Z := 101 * 10^16.           (** $1.01 in D18 *)
Definition cal_slippage   : Z := 10^16.                 (** 1% in D18 *)
Definition cal_initBal    : Z := 10000 * FIX_ONE.       (** 18-dec sell tok *)
Definition cal_auctionLen : Z := 1800.

(** ===== Section (1)/(7) of min_buy_amount.gp: 18-dec minBuyAmount ===== *)
Lemma xcheck_minBuyAmount_18 :
  minBuyAmount cal_sellAmount cal_slippage cal_sellLow cal_buyHigh 18
  = 9703960396039603960397.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (4): 6-dec minBuyAmount (USDC) ===== *)
Lemma xcheck_minBuyAmount_6 :
  minBuyAmount cal_sellAmount cal_slippage cal_sellLow cal_buyHigh 6
  = 9703960397.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (3)/(7): 18-dec worstCasePrice ===== *)
Lemma xcheck_worstCasePrice_18 :
  worstCasePrice 9703960396039603960397 cal_sellAmount
  = 970396039603960396039700000.
Proof. vm_compute. reflexivity. Qed.

(** ===== 6-dec worstCasePrice (D27{qUSDC/qSellTok}) ===== *)
Lemma xcheck_worstCasePrice_6 :
  worstCasePrice 9703960397 cal_sellAmount
  = 970396039700000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (5): residual exactness — divu FLOOR exact when 1e27
    cleanly divides minBuyAmount * 1e27 by sellAmount.  Test the formula
    directly. ===== *)
Lemma xcheck_worstCasePrice_residual :
  let mba := 9703960396039603960397 in
  let wcp := 970396039603960396039700000 in
  mba * 10^27 - wcp * cal_sellAmount = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (2): zero-slippage equivalence — the inner step is
    exactly sellAmount, so minBuyAmount = ceil(sellAmount * sellLow / buyHigh)
    decimal-shifted. ===== *)
Lemma xcheck_minBuyAmount_zero_slippage_18 :
  minBuyAmount cal_sellAmount 0 cal_sellLow cal_buyHigh 18
  = 9801980198019801980199.
Proof. vm_compute. reflexivity. Qed.

(** ===== Settlement, section (2) of settlement_floor.gp:
    full fill at minBuyAmount produces clearingPrice 1 D27-wei above wcp
    (because of the +1 pad). ===== *)
Lemma xcheck_settle_full_fill :
  let r := settle cal_initBal 0 9703960396039603960397
                  970396039603960396039700000 in
  r.(SettleResult.clearingPrice) = 970396039603960396039800000 /\
  r.(SettleResult.violation) = false /\
  r.(SettleResult.checked) = true.
Proof. vm_compute. repeat split. Qed.

(** ===== Section (2): bought = minBuyAmount - 1 still passes (pad absorbs). ===== *)
Lemma xcheck_settle_underpay_one :
  let r := settle cal_initBal 0 9703960396039603960396
                  970396039603960396039700000 in
  r.(SettleResult.violation) = false.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (2): bought = minBuyAmount - 2 violates (pad exhausted). ===== *)
Lemma xcheck_settle_underpay_two :
  let r := settle cal_initBal 0 9703960396039603960395
                  970396039603960396039700000 in
  r.(SettleResult.violation) = true.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (4): zero-fill skips check (sellBalAfter = initBal). ===== *)
Lemma xcheck_settle_zero_fill :
  let r := settle cal_initBal cal_initBal 0 970396039603960396039700000 in
  r.(SettleResult.checked) = false /\
  r.(SettleResult.violation) = false /\
  r.(SettleResult.soldAmt) = 0.
Proof. vm_compute. repeat split. Qed.

(** ===== Section (1) conservation at 50% fill.  CAS reports
    sold = 5e21, leftover = 5e21, clearing = 970396039603960396039800000. ===== *)
Lemma xcheck_settle_partial_fill_50 :
  let r := settle cal_initBal (cal_initBal / 2) 4851980198019801980198
                  970396039603960396039700000 in
  r.(SettleResult.soldAmt) = 5000000000000000000000 /\
  r.(SettleResult.clearingPrice) = 970396039603960396039800000 /\
  r.(SettleResult.violation) = false.
Proof. vm_compute. repeat split. Qed.

(** ===== Section (7): cancellationEndTime offset at length=1800s is +1620s. ===== *)
Lemma xcheck_cancellationEndTime_offset_1800 :
  cancellationEndTime 1000000 cal_auctionLen - 1000000 = 1620.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (6): canSettle flips inclusively at endTime. ===== *)
Lemma xcheck_canSettle_before :
  canSettle 1799 1800 true = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_canSettle_at :
  canSettle 1800 1800 true = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_canSettle_after :
  canSettle 1801 1800 true = true.
Proof. vm_compute. reflexivity. Qed.

(** ===== settle_floor consistency at the calibration:
    settlement_floor of worstCasePrice (D27 wcp, full sold = initBal) is
    exactly minBuyAmount - 1, since clearingPrice = (boughtAmt+1)*1e27/initBal
    crosses worstCasePrice at boughtAmt = minBuyAmount - 1 (where the +1 pad
    produces clearing = wcp). ===== *)
Lemma xcheck_settlement_floor :
  settlement_floor 970396039603960396039700000 cal_initBal
  = 9703960396039603960396.
Proof. vm_compute. reflexivity. Qed.

End GnosisTradeXCheck.
