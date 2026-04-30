(** GnosisTrade pinned numerical witnesses.

    Companion file to [GnosisTrade_xcheck.v]: where the xcheck file pins
    the canonical-calibration parity checks against
    [cas/gnosis_trade/min_buy_amount.gp] and
    [cas/gnosis_trade/settlement_floor.gp], this file pins additional
    boundary witnesses on [worstCasePrice] and [settlement_floor] —
    saturation under extreme inputs, mitigation divergence, exact
    settlement amounts the auctioneer must enforce, and the boundary
    [soldAmt] values (0, 1, max) of the [settle] arithmetic.

    Every witness is closed by [vm_compute. reflexivity.] (or
    [vm_compute. discriminate.] for inequality witnesses). No admits,
    no symbolic reasoning — these are concrete numerical checks the
    auctioneer relies on at run time.

    Calibration (matches both CAS scripts and [GnosisTrade_xcheck.v]):
      sellAmount        = 10000 * FIX_ONE = 10^22 qSellTok (D18)
      sellLow           = 99 * 10^16  ($0.99)
      buyHigh           = 101 * 10^16 ($1.01)
      slippage          = 10^16       (1%)
      18-dec minBuyAmount   = 9703960396039603960397 qBuyTok
      18-dec worstCasePrice = 970396039603960396039700000 D27{qBuy/qSell}
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.GnosisTrade.

Module GnosisTradeWitnesses.

Import FixLib.
Import GnosisTrade.

(** ===== Calibration constants ===== *)
Definition cal_sellAmount : Z := 10000 * FIX_ONE.
Definition cal_sellLow    : Z := 99  * 10^16.
Definition cal_buyHigh    : Z := 101 * 10^16.
Definition cal_slippage   : Z := 10^16.
Definition cal_initBal    : Z := 10000 * FIX_ONE.

(** Pinned 18-dec floor values (cross-checked in [GnosisTrade_xcheck.v]). *)
Definition cal_minBuy_18  : Z := 9703960396039603960397.
Definition cal_wcp_18     : Z := 970396039603960396039700000.

(** ===== Witness 1: worstCasePrice at 1M qBuyTok / 100 qSellTok =====

    Canonical task-suggested probe. With minBuyAmount = 1_000_000 qBuyTok
    and sellAmount = 100 qSellTok, the lifted numerator is 10^33 D27 wei
    and the divu FLOOR returns exactly 10^31 — a clean, unrounded
    quotient. *)
Lemma worstCasePrice_1M_over_100 :
  worstCasePrice 1000000 100 = 10^31.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 2: worstCasePrice scales linearly in mba at fixed sa =====

    Doubling [minBuyAmount] doubles [worstCasePrice] when the divisor is
    held fixed and the numerator stays exactly divisible. *)
Lemma worstCasePrice_2M_over_100 :
  worstCasePrice 2000000 100 = 2 * 10^31.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 3: worstCasePrice with extreme small sellAmount =====

    sellAmount = 1 qSellTok with minBuyAmount = 10^9 qBuyTok produces
    exactly 10^36 D27 wei. Pins the [max(soldAmt, 1)] companion path —
    no overflow saturation in the simulation (Z is unbounded; the
    Solidity wrapper reverts on uint256 overflow, which is out of model). *)
Lemma worstCasePrice_extreme_small_sa :
  worstCasePrice (10^9) 1 = 10^36.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 4: worstCasePrice zero-out via mba = 0 =====

    [boughtAmt = 0] yields zero clearing-floor. Confirms the lifted
    numerator [shiftl_toFix_d27 0 = 0] hits the trivial divu identity. *)
Lemma worstCasePrice_zero_mba_witness :
  worstCasePrice 0 cal_sellAmount = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 5: worstCasePrice returns 0 when sa = 0 =====

    The divide-by-zero guard in the simulation short-circuits to 0. *)
Lemma worstCasePrice_zero_sa_witness :
  worstCasePrice cal_minBuy_18 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 6: settlement_floor at soldAmt = 0 =====

    With [soldAmt = 0], the contract clamps to [adj = max(0, 1) = 1] and
    the required boughtAmt is [ceil(wcp / 1e27) - 1]. For
    [wcp = cal_wcp_18 = 970396039603960396039700000], we have
    [wcp / 1e27 = 0.97...], so [ceil = 1] and the floor clips to 0. *)
Lemma settlement_floor_soldAmt_zero :
  settlement_floor cal_wcp_18 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 7: settlement_floor at soldAmt = 1 =====

    With [soldAmt = 1], adj stays 1 and the floor still clips to 0
    (since [cal_wcp_18 < 10^27]). *)
Lemma settlement_floor_soldAmt_one :
  settlement_floor cal_wcp_18 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 8: settlement_floor at soldAmt = initBal =====

    The full-fill case: settlement_floor of cal_wcp_18 against the
    full initBal is exactly minBuyAmount - 1 (the +1 pad in
    [adjustedBuyAmt] absorbs the last wei). Auctioneers must clear at
    or above this. *)
Lemma settlement_floor_full_initBal :
  settlement_floor cal_wcp_18 cal_initBal = cal_minBuy_18 - 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 9: settlement_floor scales with soldAmt =====

    At half initBal, the required boughtAmt floor is roughly
    [(minBuyAmount - 1) / 2]. The exact computed value pins the
    arithmetic for partial fills — auctioneers must enforce this. *)
Lemma settlement_floor_half_initBal :
  settlement_floor cal_wcp_18 (cal_initBal / 2) = 4851980198019801980198.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 10: settlement_floor at extreme soldAmt =====

    With soldAmt = 10^30 (well above any realistic 18-dec balance), the
    floor is [ceil(wcp * 10^30 / 10^27) - 1]
    = [ceil(cal_wcp_18 * 1000) - 1]. Pin the exact value to lock in
    the contract's high-soldAmt arithmetic against future regression. *)
Lemma settlement_floor_extreme_soldAmt :
  settlement_floor cal_wcp_18 (10^30)
  = 970396039603960396039700000 * 1000 - 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 11: pre-mitigation vs post-mitigation divergence =====

    Pre-mitigation (no slippage): minBuyAmount =
    ceil(sellAmount * sellLow / buyHigh) = 9801980198019801980199 qBuyTok
    (per [GnosisTrade_xcheck.xcheck_minBuyAmount_zero_slippage_18]).

    Post-mitigation (1% slippage): minBuyAmount =
    cal_minBuy_18 = 9703960396039603960397 qBuyTok.

    The divergence is the strict, monotone effect of the slippage
    parameter — pre-mitigation is strictly larger. We pin both endpoints
    here to lock in the comparison. *)
Lemma pre_post_mitigation_diverge :
  Z.ltb (minBuyAmount cal_sellAmount cal_slippage cal_sellLow cal_buyHigh 18)
        (minBuyAmount cal_sellAmount 0           cal_sellLow cal_buyHigh 18)
  = true.
Proof. vm_compute. reflexivity. Qed.

(** Pre-mitigation (zero slippage) numeric witness, pinned. *)
Lemma minBuyAmount_pre_mitigation_pinned :
  minBuyAmount cal_sellAmount 0 cal_sellLow cal_buyHigh 18
  = 9801980198019801980199.
Proof. vm_compute. reflexivity. Qed.

(** ===== Witness 12: settle returns exactly minBuyAmount-1 violation
    boundary at full fill =====

    The auctioneer must produce >= minBuyAmount - 1 buy tokens at full
    fill (the +1 pad absorbs one wei). Pin the boundary directly:
    bought = minBuyAmount - 1 -> violation = false; minBuyAmount - 2 ->
    violation = true. Pinning the *transition* from ok to violation
    locks the exact numerical settlement amount the auctioneer enforces. *)
Lemma settle_boundary_pad_absorbs_one :
  (settle cal_initBal 0 (cal_minBuy_18 - 1) cal_wcp_18).(SettleResult.violation)
  = false.
Proof. vm_compute. reflexivity. Qed.

Lemma settle_boundary_pad_exhausted_at_two :
  (settle cal_initBal 0 (cal_minBuy_18 - 2) cal_wcp_18).(SettleResult.violation)
  = true.
Proof. vm_compute. reflexivity. Qed.

(** Same boundary, expressed structurally: minBuyAmount - 1 != 0
    (sanity discriminate witness so the file exercises both
    [reflexivity] and [discriminate] tactics). *)
Lemma minBuyAmount_minus_one_nonzero :
  cal_minBuy_18 - 1 <> 0.
Proof. vm_compute. discriminate. Qed.

End GnosisTradeWitnesses.
