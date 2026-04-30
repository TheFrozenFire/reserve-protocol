(** IssuancePremium additional witness corpus.

    Companion to [proofs/IssuancePremium_xcheck.v]: the xcheck file pins
    the canonical 5-token stablecoin calibration rows from
    [cas/issuance_premium/premium_curve.gp]. This file extends that
    coverage with concrete witnesses that exercise:

      - Boundary points adjacent to the [pegPrice >= targetPerRef] guard
        ([FIX_ONE - 1] just under, [FIX_ONE + 1] just at-or-above).
      - Intermediate monotonicity rows between the published curve
        ([0.999], [0.85], [0.80], [0.75], [0.50], [0.10]) so the
        non-increasing slope is pinned at extra grid points.
      - Multi-targetPerRef witnesses ([2.0], [1.5]) covering RTokens
        whose target is not the stablecoin [FIX_ONE].
      - Combined toggle witnesses ([enable=false, lastSave=false],
        [pegPrice = FIX_MAX]).
      - Far-from-peg saturation through the safeDiv path
        ([target = FIX_MAX - 1], pegPrice = 1) — the post-mitigation
        Certora #2 mitigation triggered through [issuancePremium] itself
        rather than the bare [safeDiv_ceil].

    Every witness is a closed evaluation discharged by [vm_compute] +
    [reflexivity]. No admits.

    Reference:
      - [cas/issuance_premium/premium_curve.gp].
      - [simulations/IssuancePremium.v]: [issuancePremium], [safeDiv_ceil].
      - [proofs/IssuancePremium_xcheck.v] for the calibration witnesses
        ([USDC]/[USDT]/[DAI]/[FRAX]/[LUSD] rows + the [0.99]/[0.98]/[0.95]/[0.90]
        published curve points).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.

Module IssuancePremiumWitnesses.

Import FixLib.
Import IssuancePremium.

(** ===== Boundary witnesses around the [pegPrice >= targetPerRef] guard. ===== *)

(** pegPrice = FIX_ONE + 1: the [<=?] guard fires on equality OR strictly
    above peg, so any peg above [FIX_ONE] returns [FIX_ONE]. The xcheck
    pins [+10^15]; this nails the 1-wei boundary. *)
Lemma witness_just_above_peg_one_wei :
  issuancePremium true true (FIX_ONE + 1) FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = FIX_ONE - 1: 1 wei below peg, the smallest non-trivial
    under-peg input. safeDiv ceil(10^36 / (10^18 - 1)) = FIX_ONE + 2. *)
Lemma witness_just_below_peg_one_wei :
  issuancePremium true true (FIX_ONE - 1) FIX_ONE
  = 1000000000000000002.
Proof. vm_compute. reflexivity. Qed.

(** ===== Intermediate-grid monotonicity witnesses. =====
    Fills gaps between the xcheck rows at [0.99 / 0.98 / 0.95 / 0.90]. *)

(** pegPrice = 0.999: the closest-to-peg published row in the CAS sweep. *)
Lemma witness_curve_999 :
  issuancePremium true true (FIX_ONE * 999 / 1000) FIX_ONE
  = 1001001001001001002.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 0.85: between the [0.90] and [0.80] curve rows. *)
Lemma witness_curve_85 :
  issuancePremium true true (FIX_ONE * 85 / 100) FIX_ONE
  = 1176470588235294118.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 0.80. *)
Lemma witness_curve_80 :
  issuancePremium true true (FIX_ONE * 80 / 100) FIX_ONE
  = 1250000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 0.75. *)
Lemma witness_curve_75 :
  issuancePremium true true (FIX_ONE * 75 / 100) FIX_ONE
  = 1333333333333333334.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 0.50: half-peg. *)
Lemma witness_curve_50 :
  issuancePremium true true (FIX_ONE / 2) FIX_ONE
  = 2000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 0.10: deep-discount stress, not yet at safeDiv saturation. *)
Lemma witness_curve_10 :
  issuancePremium true true (FIX_ONE / 10) FIX_ONE
  = 10000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** Multi-step monotonicity chain across the new grid. *)
Lemma witness_chain_monotone_999_85_80_75 :
  let p999 := issuancePremium true true (FIX_ONE * 999 / 1000) FIX_ONE in
  let p85  := issuancePremium true true (FIX_ONE * 85 / 100)   FIX_ONE in
  let p80  := issuancePremium true true (FIX_ONE * 80 / 100)   FIX_ONE in
  let p75  := issuancePremium true true (FIX_ONE * 75 / 100)   FIX_ONE in
  (p999 <? p85) && (p85 <? p80) && (p80 <? p75) = true.
Proof. vm_compute. reflexivity. Qed.

(** ===== Multi-targetPerRef witnesses. =====
    RTokens whose ref unit is priced in something other than 1.0
    (e.g. an LST-based RToken where target unit is 2x ref). *)

(** target = 2.0, peg = 1.0: under-peg gives premium = 2.0 = ceil(2e36/1e18). *)
Lemma witness_target_2x_peg_at_one :
  issuancePremium true true FIX_ONE (2 * FIX_ONE)
  = 2000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** target = 2.0, peg = 1.5: under-peg, premium = ceil(2e36/1.5e18). *)
Lemma witness_target_2x_peg_at_1p5 :
  issuancePremium true true (FIX_ONE * 3 / 2) (2 * FIX_ONE)
  = 1333333333333333334.
Proof. vm_compute. reflexivity. Qed.

(** target = 1.5, peg = 1.0: premium = ceil(1.5e36/1e18) = 1.5. *)
Lemma witness_target_1p5x_peg_at_one :
  issuancePremium true true FIX_ONE (FIX_ONE * 3 / 2)
  = 1500000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Combined-toggle witnesses. =====
    Both feature flags off simultaneously — both branches short-circuit;
    [enable=false] takes priority over [lastSaveIsNow=false]. *)
Lemma witness_disabled_and_stale :
  issuancePremium false false (FIX_ONE / 2) FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== Extreme far-from-peg witnesses. ===== *)

(** pegPrice = FIX_MAX, target = FIX_ONE: pegPrice >= target, returns FIX_ONE
    (no saturation through this branch — the >= guard fires first). *)
Lemma witness_peg_at_fix_max :
  issuancePremium true true FIX_MAX FIX_ONE = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** Saturation through [issuancePremium] itself with a huge target and
    pegPrice = 1 wei. target = FIX_MAX - 1 dodges the [a =? FIX_MAX]
    short-circuit in [safeDiv_ceil] and forces the [raw >= FIX_MAX]
    saturation branch via the multiplied numerator. Post-mitigation
    behaviour: returns [FIX_MAX] rather than wrapping to 0. *)
Lemma witness_saturation_through_issuance :
  issuancePremium true true 1 (FIX_MAX - 1) = FIX_MAX.
Proof. vm_compute. reflexivity. Qed.

(** pegPrice = 1 wei, target = FIX_ONE: extreme under-peg with no
    saturation — premium = ceil(10^36 / 1) = 10^36, well below FIX_MAX. *)
Lemma witness_extreme_under_peg :
  issuancePremium true true 1 FIX_ONE
  = 1000000000000000000000000000000000000.
Proof. vm_compute. reflexivity. Qed.

End IssuancePremiumWitnesses.
