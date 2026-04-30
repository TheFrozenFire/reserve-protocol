(** Additional CAS witnesses not yet pinned elsewhere.

    Source: a sweep of the 27 CAS scripts under [formal-verification/cas/]
    for "interesting witnesses" missing from the pinned-witness corpus
    ([_witnesses.v] / [_xcheck.v]). One unaddressed area surfaced:

      cas/gnosis_trade/min_buy_amount.gp section (6) — the auction-fee
      adjustment relationship. EasyAuction reduces the [_sellAmount]
      forwarded to the auction by [FEE_DENOMINATOR / (FEE_DENOMINATOR +
      feeNumerator)], yet [worstCasePrice] is computed against the
      *unfee'd* [req.sellAmount]. The CAS script verifies, over
      [feeNumerator in {0, 5, 10}], that the effective auction-clearing
      ratio against the fee'd [_sellAmount] is >= [worstCasePrice] —
      i.e. the auction's internal floor is at least as strict as the
      [reportViolation()] floor, so a fee'd auction that meets the
      auction floor automatically meets the [reportViolation()] floor.

    Why this matters:
      Currently [feeNumerator = 0] on the deployed EasyAuction, but
      governance can raise it. A divergence here would mean an auction
      could clear satisfying the on-Gnosis floor yet still trigger
      [reportViolation()] on the protocol side — a spurious-violation
      hazard. The CAS sweep reports OK; this file pins the canonical
      [feeNumerator in {0, 5, 10}] witnesses as Rocq theorems closed by
      [vm_compute] + [reflexivity] / [discriminate].

    The simulation file [simulations/GnosisTrade.v] does not yet model
    [FEE_DENOMINATOR] in the auction pipeline (it only exposes the
    constant). We mirror the CAS section-(6) helpers locally and pin
    the numerical witnesses against the same calibration constants
    already used by [proofs/GnosisTrade_xcheck.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.GnosisTrade.

Module CASAdditionalFindings.

Import FixLib.
Import GnosisTrade.

(** ===== Calibration (mirrors GnosisTrade_xcheck.v) ===== *)
Definition cal_sellAmount : Z := 10000 * FIX_ONE.       (** 10^22 D18 wei *)
Definition cal_sellLow    : Z := 99  * 10^16.           (** $0.99 in D18 *)
Definition cal_buyHigh    : Z := 101 * 10^16.           (** $1.01 in D18 *)
Definition cal_slippage   : Z := 10^16.                 (** 1% in D18 *)

(** CAS-reported 18-dec witnesses, pinned in [GnosisTrade_xcheck.v]. *)
Definition cal_minBuy_18      : Z := 9703960396039603960397.
Definition cal_worstCase_18   : Z := 970396039603960396039700000.

(** Mirror of CAS section (6)'s [fee_adjust]:
    EasyAuction reduces [_sellAmount] by [FEE_DENOMINATOR /
    (FEE_DENOMINATOR + feeNumerator)], FLOOR-rounded. *)
Definition fee_adjust (sa_qsell feeNumerator : Z) : Z :=
  (sa_qsell * FEE_DENOMINATOR) / (FEE_DENOMINATOR + feeNumerator).

(** Effective clearing ratio (D27 wei) against the fee-reduced
    [_sellAmount]: this is what the auction internally enforces. *)
Definition ratio_against_fee_adjusted
    (minBuyAmount_qBuy sa_qsell feeNumerator : Z) : Z :=
  let sa_eff := fee_adjust sa_qsell feeNumerator in
  if sa_eff =? 0 then 0
  else divrnd (shiftl_toFix_d27 minBuyAmount_qBuy)
              sa_eff
              RoundingMode.FLOOR.

(** ===== feeNumerator = 0 — current EasyAuction ===== *)

(** [_sellAmount = sa * 1000 / 1000 = sa]. *)
Lemma w_fee0_sa_eff :
  fee_adjust cal_sellAmount 0 = cal_sellAmount.
Proof. vm_compute. reflexivity. Qed.

(** Effective ratio = worstCasePrice exactly: no fee, no gap. *)
Lemma w_fee0_ratio_eq_wcp :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 0
    = cal_worstCase_18.
Proof. vm_compute. reflexivity. Qed.

(** ===== feeNumerator = 5 (0.5%) ===== *)

(** [_sellAmount = floor(10^22 * 1000 / 1005) = 9950248756218905472636]. *)
Lemma w_fee5_sa_eff :
  fee_adjust cal_sellAmount 5 = 9950248756218905472636.
Proof. vm_compute. reflexivity. Qed.

(** Effective ratio is *strictly greater* than [worstCasePrice]:
    975248019801980198019978470 vs 970396039603960396039700000. *)
Lemma w_fee5_ratio_value :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
    = 975248019801980198019978470.
Proof. vm_compute. reflexivity. Qed.

Lemma w_fee5_ratio_ge_wcp :
  cal_worstCase_18
    <=? ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
  = true.
Proof. vm_compute. reflexivity. Qed.

(** Strict inequality: at fee > 0 the auction floor is *strictly* tighter. *)
Lemma w_fee5_ratio_strictly_greater :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
    =? cal_worstCase_18
  = false.
Proof. vm_compute. reflexivity. Qed.

(** Pin the exact gap (D27 wei): 4851980198019801980278470. *)
Lemma w_fee5_gap :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
    - cal_worstCase_18
  = 4851980198019801980278470.
Proof. vm_compute. reflexivity. Qed.

(** ===== feeNumerator = 10 (1%) ===== *)

(** [_sellAmount = floor(10^22 * 1000 / 1010) = 9900990099009900990099]. *)
Lemma w_fee10_sa_eff :
  fee_adjust cal_sellAmount 10 = 9900990099009900990099.
Proof. vm_compute. reflexivity. Qed.

Lemma w_fee10_ratio_value :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 10
    = 980100000000000000000097980.
Proof. vm_compute. reflexivity. Qed.

Lemma w_fee10_ratio_ge_wcp :
  cal_worstCase_18
    <=? ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 10
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w_fee10_gap :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 10
    - cal_worstCase_18
  = 9703960396039603960397980.
Proof. vm_compute. reflexivity. Qed.

(** ===== Monotonicity in feeNumerator =====
    Higher fees mean a smaller [_sellAmount], so the ratio against the
    fee'd amount grows. Pin: ratio(0) < ratio(5) < ratio(10). *)

Lemma w_ratio_monotone_0_5 :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 0
    <=? ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w_ratio_monotone_5_10 :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 5
    <=? ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 10
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w_ratio_strict_increase_0_to_10 :
  ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 0
    =? ratio_against_fee_adjusted cal_minBuy_18 cal_sellAmount 10
  = false.
Proof. vm_compute. reflexivity. Qed.

End CASAdditionalFindings.
