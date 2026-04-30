(** Furnace simulation × CAS witness cross-check.

    Evaluates the [Furnace] simulation on the same calibration inputs
    used by [cas/furnace/melt_curve.gp] and asserts identical outputs.
    Any divergence between the Rocq simulation and the CAS witness corpus
    fails the build.

    Witness rows from cas/furnace/melt_curve.gp section (1):
      N=1        ratio=MAX_RATIO  payoutRatio = 100000000000000
      N=60       ratio=MAX_RATIO  payoutRatio = 5982334171291066
      N=3600     ratio=MAX_RATIO  payoutRatio = 302336232827074651
      N=86400    ratio=MAX_RATIO  payoutRatio = 999823189501488433
      N=604800   ratio=MAX_RATIO  payoutRatio = 1000000000000000000

    Witness from section (3):
      ratio=1e10, bal=100M*FIX_ONE, N=86400 (1 day):
        Closed-form melt: 86362686378847900000000

    The simulation reproduces these values bit-for-bit through the
    halfDiv-based [powu] kernel.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.

Module FurnaceXCheck.

Import FixLib.
Import Furnace.

(** Helper: closed-form payoutRatio for (ratio, N).
    Mirrors the inner expression in [Furnace.melt]. *)
Definition payoutRatio (ratio_ N : Z) : Z :=
  FixLib.minus FixLib.FIX_ONE
    (FixLib.powu (FixLib.minus FixLib.FIX_ONE ratio_) N).

(** ===== Section (1): payoutRatio at MAX_RATIO across N. ===== *)

(** N=1, ratio=MAX_RATIO: payoutRatio = MAX_RATIO itself
    (since 1 - (1 - r) = r). *)
Lemma xcheck_payout_max_n1 :
  payoutRatio MAX_RATIO 1 = 100000000000000.
Proof. vm_compute. reflexivity. Qed.

(** N=60 (one minute) at MAX_RATIO. *)
Lemma xcheck_payout_max_n60 :
  payoutRatio MAX_RATIO 60 = 5982334171291066.
Proof. vm_compute. reflexivity. Qed.

(** N=3600 (one hour) at MAX_RATIO: ~30.23%. *)
Lemma xcheck_payout_max_n3600 :
  payoutRatio MAX_RATIO 3600 = 302336232827074651.
Proof. vm_compute. reflexivity. Qed.

(** N=86400 (one day) at MAX_RATIO: ~99.98%. *)
Lemma xcheck_payout_max_n86400 :
  payoutRatio MAX_RATIO 86400 = 999823189501488433.
Proof. vm_compute. reflexivity. Qed.

(** N=604800 (one week) at MAX_RATIO: saturates to FIX_ONE. *)
Lemma xcheck_payout_max_n604800 :
  payoutRatio MAX_RATIO 604800 = 1000000000000000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (3) closed-form witness: typical ratio, 1-day melt. =====
    ratio=1e10, balance=10^8 * FIX_ONE, N=86400.
    CAS reports payoutRatio * bal / FIX_ONE = 86362686378847900000000. *)

Definition typ_storage : Storage.t := {|
  Storage.ratio         := 10^10;
  Storage.lastPayout    := 0;
  Storage.lastPayoutBal := 10^8 * FIX_ONE;
|}.

Lemma xcheck_payout_typ_n86400 :
  payoutRatio (10^10) 86400 = 863626863788479.
Proof. vm_compute. reflexivity. Qed.

(** Full melt() witness on the typical setup: amount = 86362686378847900000000.
    The new lastPayout advances to [now=86400]; lastPayoutBal becomes
    currentBalance - amount. *)
Lemma xcheck_melt_typical_amount :
  snd (melt typ_storage 86400 (10^8 * FIX_ONE)) = 86362686378847900000000.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_melt_typical_lastPayout :
  (fst (melt typ_storage 86400 (10^8 * FIX_ONE))).(Storage.lastPayout) = 86400.
Proof. vm_compute. reflexivity. Qed.

(** ===== Early-return witness: now = lastPayout, no melt happens. ===== *)
Lemma xcheck_melt_early_return :
  melt typ_storage 0 (10^8 * FIX_ONE) = (typ_storage, 0).
Proof. vm_compute. reflexivity. Qed.

(** ===== Section (2) cap witness: payoutRatio <= FIX_ONE for the
    saturated row (N=604800 already hit FIX_ONE; any larger N stays
    at FIX_ONE since [powu (FIX_ONE - MAX_RATIO) k] floors to 0). ===== *)
Lemma xcheck_payout_max_le_fix_one_n86400 :
  payoutRatio MAX_RATIO 86400 <= FIX_ONE.
Proof. vm_compute. discriminate. Qed.

Lemma xcheck_payout_max_le_fix_one_n604800 :
  payoutRatio MAX_RATIO 604800 <= FIX_ONE.
Proof. vm_compute. discriminate. Qed.

(** ===== setRatio witnesses: boundary at MAX_RATIO. ===== *)

Definition fresh_storage : Storage.t := {|
  Storage.ratio         := 0;
  Storage.lastPayout    := 0;
  Storage.lastPayoutBal := 0;
|}.

Lemma xcheck_setRatio_at_max :
  exists s', setRatio fresh_storage MAX_RATIO = Some s'.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_setRatio_above_max :
  setRatio fresh_storage (MAX_RATIO + 1) = None.
Proof. vm_compute. reflexivity. Qed.

End FurnaceXCheck.
