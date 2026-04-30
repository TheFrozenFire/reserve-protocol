(** BasketHandler simulation × CAS witness cross-check.

    Evaluates the [BasketHandler] simulation on the same calibration inputs
    used by [cas/basket_handler/quote_rounding_direction.gp] and
    [cas/basket_handler/quote_round_trip.gp], and asserts identical
    outputs. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build.

    Simulation scope vs CAS scope:
      The CAS scripts model the FULL [quote()] chain on-chain (per-token
      _quantity / safeMul / shiftl_toUint with decimals + premium); the
      Rocq simulation models only the algebraic core
      [refAmt * baskets / FIX_ONE]. We pin the algebraic core by keeping
      [refPerTok = FIX_ONE], 18 decimals, no premium — this collapses
      the full chain to the simulation's [quote_one]. The CAS-side
      "USDC at 18 decimals, no premium" rows produce the same numerics.

    Calibration mirrors the CAS scripts:
      refAmt_clean = FIX_ONE / 5 = 2 * 10^17        (clean ratio)
      refAmt_messy = FIX_ONE / 7 = 142857142857142857 (1-wei gap producer)

    Probes:
      1. Clean per-token quote: quote_one(2e17, FIX_ONE, FLOOR) = 2e17.
      2. Clean per-token quote: quote_one(2e17, FIX_ONE, CEIL)  = 2e17.
      3. Messy ratio gap: quote_one(messy, 1 wei, FLOOR) = 0;
                          quote_one(messy, 1 wei, CEIL)  = 1.
      4. Messy ratio at 1 BU: 142857142857142857 (FLOOR == CEIL).
      5. Round-trip clean: redeem(quote(2e17, FIX_ONE, FLOOR)) = FIX_ONE.
      6. Round-trip messy: redeem(quote(messy, FIX_ONE, FLOOR)) = FIX_ONE.
      7. Empty basket: quote([], _, _) = [].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Coq.Lists.List.
Import ListNotations.

Module BasketHandlerXCheck.

Import FixLib.
Import BasketHandler.

(** ----- Calibration constants (mirroring the CAS scripts). ----- *)
Definition cal_refAmt_clean : U256.t := FIX_ONE / 5.   (* 2e17 *)
Definition cal_refAmt_messy : U256.t := FIX_ONE / 7.   (* 142857142857142857 *)

(** Asset ids — opaque, just need to be distinct. *)
Definition asset_USDC : U256.t := 1.
Definition asset_DAI  : U256.t := 2.
Definition asset_FRAX : U256.t := 3.

Definition entry_USDC : BasketEntry.t := {|
  BasketEntry.asset  := asset_USDC;
  BasketEntry.refAmt := cal_refAmt_clean;
|}.

Definition entry_DAI : BasketEntry.t := {|
  BasketEntry.asset  := asset_DAI;
  BasketEntry.refAmt := cal_refAmt_clean;
|}.

Definition entry_FRAX : BasketEntry.t := {|
  BasketEntry.asset  := asset_FRAX;
  BasketEntry.refAmt := cal_refAmt_messy;
|}.

Definition cal_basket : Storage :=
  [entry_USDC; entry_DAI; entry_FRAX].

(** ----- Probe 1: clean quote at 1 BU, FLOOR. -----
    refAmt = 2e17, baskets = FIX_ONE = 10^18.
    refAmt * baskets / FIX_SCALE = 2e17 * 10^18 / 10^18 = 2e17. *)
Lemma xcheck_clean_one_bu_floor :
  quote_one cal_refAmt_clean FIX_ONE RoundingMode.FLOOR = 2 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 2: clean quote at 1 BU, CEIL — same exact result. ----- *)
Lemma xcheck_clean_one_bu_ceil :
  quote_one cal_refAmt_clean FIX_ONE RoundingMode.CEIL = 2 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 3: messy ratio FLOOR vs CEIL gap at 1 wei of BU. -----
    refAmt = 142857142857142857, baskets = 1 wei.
    refAmt * baskets / 10^18 = 142857142857142857 / 10^18 = 0 (FLOOR).
    Same numerator with CEIL = 0 + 1 = 1.
    This is the canonical 1-wei rounding-direction witness. *)
Lemma xcheck_messy_1wei_floor :
  quote_one cal_refAmt_messy 1 RoundingMode.FLOOR = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_messy_1wei_ceil :
  quote_one cal_refAmt_messy 1 RoundingMode.CEIL = 1.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 4: messy ratio at 1 BU — FLOOR == CEIL since
    142857142857142857 * 10^18 / 10^18 = 142857142857142857 exactly. ----- *)
Lemma xcheck_messy_one_bu_floor :
  quote_one cal_refAmt_messy FIX_ONE RoundingMode.FLOOR
  = 142857142857142857.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_messy_one_bu_ceil :
  quote_one cal_refAmt_messy FIX_ONE RoundingMode.CEIL
  = 142857142857142857.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 5: round-trip clean. ----- *)
Lemma xcheck_round_trip_clean :
  redeem_one cal_refAmt_clean
    (quote_one cal_refAmt_clean FIX_ONE RoundingMode.FLOOR)
  = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 6: round-trip messy at 1 BU. -----
    quote_one(messy, FIX_ONE, FLOOR) = 142857142857142857.
    redeem_one(messy, 142857142857142857) = 142857142857142857 * 10^18
       / 142857142857142857 = 10^18 = FIX_ONE. ----- *)
Lemma xcheck_round_trip_messy :
  redeem_one cal_refAmt_messy
    (quote_one cal_refAmt_messy FIX_ONE RoundingMode.FLOOR)
  = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 7: round-trip lossy direction is conservative. -----
    quote_one(messy, 7 wei, FLOOR) = 7 * 142857142857142857 / 10^18
       = 999999999999999999 / 10^18 = 0.
    redeem_one(messy, 0) = 0; 0 <= 7. Conservative direction. ----- *)
Lemma xcheck_round_trip_lossy :
  redeem_one cal_refAmt_messy
    (quote_one cal_refAmt_messy 7 RoundingMode.FLOOR) <= 7.
Proof. vm_compute. discriminate. Qed.

(** ----- Probe 8: empty basket. ----- *)
Lemma xcheck_empty_basket_floor :
  quote nil FIX_ONE RoundingMode.FLOOR = nil.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_empty_basket_ceil :
  quote nil FIX_ONE RoundingMode.CEIL = nil.
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 9: full basket quote at 1 BU, FLOOR.
    USDC and DAI are clean (2e17 each); FRAX is messy (142857142857142857).
    The result preserves the storage order and pairs each asset id with
    its per-asset {qTok}. ----- *)
Lemma xcheck_full_basket_floor :
  quote cal_basket FIX_ONE RoundingMode.FLOOR
  = [(asset_USDC, 2 * 10^17);
     (asset_DAI,  2 * 10^17);
     (asset_FRAX, 142857142857142857)].
Proof. vm_compute. reflexivity. Qed.

(** ----- Probe 10: per-asset CEIL >= FLOOR on the messy entry at 1 wei. ----- *)
Lemma xcheck_floor_le_ceil_witness :
  quote_one cal_refAmt_messy 1 RoundingMode.FLOOR
  <= quote_one cal_refAmt_messy 1 RoundingMode.CEIL.
Proof. vm_compute. discriminate. Qed.

End BasketHandlerXCheck.
