(** BasketHandler quote pinned numerical witnesses.

    The CAS scripts
      cas/basket_handler/quote_rounding_direction.gp
      cas/basket_handler/quote_round_trip.gp
    sweep concrete (refAmt, baskets, mode) inputs that exercise the
    rounding-direction (INV-Q1/Q2) and round-trip (INV-RT1..RT5) properties
    of [BasketHandlerP1.quote()]. This file pins the corresponding
    numerical witnesses as Rocq theorems, each closed by [vm_compute].

    The Rocq simulation [BasketHandler.quote_one] only models the
    algebraic core
        qTok = refAmt * baskets / FIX_ONE  (rounded by mode)
    so we restrict witnesses to the calibration shape that collapses the
    full on-chain chain to that core: refPerTok = FIX_ONE, no premium,
    18 decimals. The numerics then match the CAS script's "USDC at 18d,
    no premium" / "DAI at 18d, no premium" rows exactly.

    Companion to:
      - [proofs/BasketHandler.v]:        algebraic CEIL/FLOOR lemmas.
      - [proofs/BasketHandler_xcheck.v]: simulation x CAS parity probes.

    Witness map:
      W1  Single-collateral basket at FIX_ONE refAmt, 1 BU -> FIX_ONE qTok.
      W2  Clean refAmt = FIX_ONE/5 at 1 BU FLOOR -> 2e17.
      W3  Clean refAmt at 7 BU FLOOR scales linearly -> 14e17.
      W4  Messy refAmt = FIX_ONE/7 at 7 wei: FLOOR vs CEIL divergence
          (CAS gap_max witness, INV-Q1 1-wei step).
      W5  Messy refAmt at 13 wei: FLOOR = 1, CEIL = 2 (mid-range diverge).
      W6  CEIL >= FLOOR at the divergence point (W4).
      W7  Round-trip clean: redeem(quote(2e17, FIX_ONE, FLOOR)) = FIX_ONE.
      W8  Round-trip lossy non-extraction: redeem(quote(messy, 7 wei,
          FLOOR)) = 0 <= 7 wei (INV-RT2 conservative direction).
      W9  Linearity at k = 100 (INV-RT4 sweep): quote(messy, 100 BU,
          FLOOR) = 100 * quote(messy, 1 BU, FLOOR).
      W10 Empty basket -> empty quote (INV-Q3 empty case).
      W11 Full 3-token basket quoteQuantities at 1 BU FLOOR.
      W12 [redeem_one] zero-refAmt sentinel: redeem_one(0, qTok) = 0.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Coq.Lists.List.
Import ListNotations.

Module BasketHandlerWitnesses.

Import FixLib.
Import BasketHandler.

(** Calibration constants (mirroring the CAS scripts). *)
Definition refAmt_clean : U256.t := FIX_ONE / 5.   (* 2e17 *)
Definition refAmt_messy : U256.t := FIX_ONE / 7.   (* 142857142857142857 *)

Definition asset_USDC : U256.t := 1.
Definition asset_DAI  : U256.t := 2.
Definition asset_FRAX : U256.t := 3.

Definition entry_USDC : BasketEntry.t := {|
  BasketEntry.asset  := asset_USDC;
  BasketEntry.refAmt := refAmt_clean;
|}.

Definition entry_DAI : BasketEntry.t := {|
  BasketEntry.asset  := asset_DAI;
  BasketEntry.refAmt := refAmt_clean;
|}.

Definition entry_FRAX : BasketEntry.t := {|
  BasketEntry.asset  := asset_FRAX;
  BasketEntry.refAmt := refAmt_messy;
|}.

Definition cal_basket : Storage :=
  [entry_USDC; entry_DAI; entry_FRAX].

(** ===== W1: single-collateral basket at FIX_ONE refAmt. =====
    refAmt = FIX_ONE, baskets = FIX_ONE.
    quote_one = FIX_ONE * FIX_ONE / FIX_ONE = FIX_ONE.
    This is the "1.0 ref/BU, 1 BU issued -> 1.0 token" identity: the
    cleanest possible quote and the canonical sanity probe. *)
Lemma W1_single_collateral_FIX_ONE :
  quote_one FIX_ONE FIX_ONE RoundingMode.FLOOR = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== W2: clean refAmt at 1 BU, FLOOR -> 2e17. =====
    Mirrors quote_rounding_direction.gp INV-Q1 USDC/DAI/USDT at amount=1 BU,
    no-premium, 18d. The full on-chain chain collapses to refAmt itself
    when refPerTok = FIX_ONE and amount = 1 BU. *)
Lemma W2_clean_one_BU_FLOOR :
  quote_one refAmt_clean FIX_ONE RoundingMode.FLOOR = 2 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ===== W3: clean refAmt linearity at 7 BU, FLOOR. =====
    Mirrors INV-RT1 linearity probe: quote(7 BU) = 7 * quote(1 BU)
    exactly when the ratio is clean. *)
Lemma W3_clean_seven_BU_FLOOR :
  quote_one refAmt_clean (7 * FIX_ONE) RoundingMode.FLOOR
  = 7 * (2 * 10^17).
Proof. vm_compute. reflexivity. Qed.

(** ===== W4: messy refAmt at 7 wei, FLOOR vs CEIL divergence. =====
    Pins the CAS INV-Q1 "gap_max = 1 wei" witness on a non-exact-divide
    input.
      refAmt = FIX_ONE/7 = 142857142857142857
      baskets = 7 wei
      product = 142857142857142857 * 7 = 999999999999999999
      999999999999999999 / 10^18 = 0   (FLOOR)
      ceil_div(999999999999999999, 10^18) = 1   (CEIL)
    This is the canonical "1 wei short of FIX_ONE" rounding witness. *)
Lemma W4_messy_seven_wei_FLOOR :
  quote_one refAmt_messy 7 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma W4_messy_seven_wei_CEIL :
  quote_one refAmt_messy 7 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

(** ===== W5: messy refAmt at 13 wei, FLOOR = 1 / CEIL = 2. =====
    Mid-range non-exact-divide witness:
      product = 142857142857142857 * 13 = 1857142857142857141
      / 10^18 -> FLOOR = 1, CEIL = 2.
    Confirms the rounding-direction divergence isn't a one-off
    boundary artefact. *)
Lemma W5_messy_thirteen_wei_FLOOR :
  quote_one refAmt_messy 13 RoundingMode.FLOOR = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma W5_messy_thirteen_wei_CEIL :
  quote_one refAmt_messy 13 RoundingMode.CEIL = 2.
Proof. vm_compute. reflexivity. Qed.

(** ===== W6: CEIL >= FLOOR at the divergence point (INV-Q1). =====
    The strict 0 < 1 case from W4, pinned as an inequality witness. *)
Lemma W6_CEIL_gt_FLOOR_witness :
  quote_one refAmt_messy 7 RoundingMode.FLOOR
  <  quote_one refAmt_messy 7 RoundingMode.CEIL.
Proof. vm_compute. reflexivity. Qed.

(** ===== W7: round-trip clean -> recovers FIX_ONE exactly. =====
    quote_one(2e17, FIX_ONE, FLOOR) = 2e17.
    redeem_one(2e17, 2e17) = 2e17 * 10^18 / 2e17 = 10^18 = FIX_ONE.
    This is the "issue 1 BU then redeem the resulting tokens recovers
    1 BU exactly" identity for clean ratios. *)
Lemma W7_round_trip_clean :
  redeem_one refAmt_clean
    (quote_one refAmt_clean FIX_ONE RoundingMode.FLOOR)
  = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== W8: round-trip lossy non-extraction (INV-RT2). =====
    quote_one(messy, 7 wei, FLOOR) = 0 from W4.
    redeem_one(messy, 0) = 0 * 10^18 / messy = 0.
    The redeemed BU (0) is <= the issued BU (7 wei): no value extracted
    by the round-trip, even on the lossy direction. *)
Lemma W8_round_trip_no_extraction :
  redeem_one refAmt_messy
    (quote_one refAmt_messy 7 RoundingMode.FLOOR)
  = 0.
Proof. vm_compute. reflexivity. Qed.

(** ===== W9: linearity at k = 100 (INV-RT4 sweep). =====
    quote_one(messy, 100 BU, FLOOR) = 100 * quote_one(messy, 1 BU, FLOOR)
    exactly when refPerTok = FIX_ONE (linear in the second argument with
    integer divisor), so the gap-per-BU is 0 -- the CAS-side INV-RT4
    "worst gap-per-BU << 1 wei" claim, pinned at one concrete scale. *)
Lemma W9_linearity_messy_100BU :
  quote_one refAmt_messy (100 * FIX_ONE) RoundingMode.FLOOR
  = 100 * 142857142857142857.
Proof. vm_compute. reflexivity. Qed.

(** ===== W10: empty basket -> empty quoteQuantities (INV-Q3). =====
    The for-loop over an empty basket runs zero times; the result is
    the empty list. Pinned for both FLOOR and CEIL. *)
Lemma W10_empty_basket_FLOOR :
  quoteQuantities nil FIX_ONE RoundingMode.FLOOR = nil.
Proof. vm_compute. reflexivity. Qed.

Lemma W10_empty_basket_CEIL :
  quoteQuantities nil FIX_ONE RoundingMode.CEIL = nil.
Proof. vm_compute. reflexivity. Qed.

(** ===== W11: full 3-token basket quoteQuantities at 1 BU FLOOR. =====
    Storage order is preserved; clean entries give 2e17 each, messy
    entry gives 142857142857142857. Cross-checks the dropping of the
    asset id by [quoteQuantities] vs the paired form. *)
Lemma W11_full_basket_quoteQuantities :
  quoteQuantities cal_basket FIX_ONE RoundingMode.FLOOR
  = [2 * 10^17; 2 * 10^17; 142857142857142857].
Proof. vm_compute. reflexivity. Qed.

(** ===== W12: redeem_one zero-refAmt sentinel. =====
    The redemption-side inverse short-circuits when refAmt = 0 to avoid
    division by zero; it returns 0 regardless of the qTok argument. The
    CAS scripts treat this as the "degenerate basket weight" boundary. *)
Lemma W12_redeem_zero_refAmt :
  redeem_one 0 (10^18) = 0.
Proof. vm_compute. reflexivity. Qed.

End BasketHandlerWitnesses.
