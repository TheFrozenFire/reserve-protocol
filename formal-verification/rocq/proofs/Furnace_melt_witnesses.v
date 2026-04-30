(** Furnace.melt witness corpus.

    Companion to [proofs/Furnace_xcheck.v]: where [Furnace_xcheck] pins the
    five canonical CAS rows from [cas/furnace/melt_curve.gp], this file
    nails down extra closed-form witnesses that exercise:

      - branches of [melt] that the xcheck file does not target
        (early-return on [now < lastPayout + 1]; [ratio = 0] no-op;
         [setRatio] round-trip then [melt] with the freshly-set ratio),
      - intermediate [N] rows between the calibration grid (N=10, N=100,
        N=1000), which the CAS script asserts monotonicity over but does
        not print,
      - dollar-denominated melt amounts at canonical balances (1M qRTok)
        for typical (ratio = 1e10) and saturating (ratio = MAX_RATIO)
        configurations.

    Every witness is a closed evaluation discharged by [vm_compute] +
    [reflexivity] / [discriminate]. No admits.

    Reference:
      - [cas/furnace/melt_curve.gp] sections (1)–(4).
      - [simulations/Furnace.v]: [melt], [setRatio], [Storage], [MAX_RATIO].
      - [proofs/Furnace_xcheck.v] for the calibration-row witnesses.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.

Module FurnaceMeltWitnesses.

Import FixLib.
Import Furnace.

(** Helper mirroring the inner [payoutRatio] expression in [melt]. *)
Definition payoutRatio (ratio_ N : Z) : Z :=
  FixLib.minus FixLib.FIX_ONE
    (FixLib.powu (FixLib.minus FixLib.FIX_ONE ratio_) N).

(** Canonical fixtures. *)
Definition one_million_qRTok : Z := 10^6 * FIX_ONE.

Definition s_typical : Storage.t := {|
  Storage.ratio         := 10^10;          (* ~27%/yr *)
  Storage.lastPayout    := 0;
  Storage.lastPayoutBal := one_million_qRTok;
|}.

Definition s_max : Storage.t := {|
  Storage.ratio         := MAX_RATIO;
  Storage.lastPayout    := 0;
  Storage.lastPayoutBal := one_million_qRTok;
|}.

Definition s_zero_ratio : Storage.t := {|
  Storage.ratio         := 0;
  Storage.lastPayout    := 0;
  Storage.lastPayoutBal := one_million_qRTok;
|}.

(** ===== (W1) ratio = 0 is a no-op — amount = 0 =====

    [payoutRatio 0 N = FIX_ONE - powu (FIX_ONE - 0) N = FIX_ONE - FIX_ONE = 0],
    so [amount = mulu_toUint 0 bal FLOOR = 0] regardless of [N] or [bal].
    The on-chain consequence is that a Furnace with [ratio = 0] never
    burns RToken even after arbitrarily long elapsed periods. *)
Lemma melt_zero_ratio_amount_is_zero :
  snd (melt s_zero_ratio 86400 one_million_qRTok) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma melt_zero_ratio_balance_unchanged :
  (fst (melt s_zero_ratio 86400 one_million_qRTok)).(Storage.lastPayoutBal)
    = one_million_qRTok.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W2) numPeriods = 0 (now = lastPayout) early-return =====

    The [now <? lastPayout + 1] guard fires when [now = lastPayout],
    so [melt] returns the storage *unchanged* and amount = 0. This is
    distinct from the [ratio = 0] case: here the storage is bit-equal,
    not just amount-zero. *)
Lemma melt_early_return_now_equals_lastPayout :
  melt s_typical 0 one_million_qRTok = (s_typical, 0).
Proof. vm_compute. reflexivity. Qed.

(** ===== (W3) MAX_RATIO at N=10 — intermediate row not in xcheck ===== *)
Lemma payout_max_n10 :
  payoutRatio MAX_RATIO 10 = 999550119979003.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W4) MAX_RATIO at N=100 — intermediate row =====
    Lies strictly between the [N=60] and [N=3600] xcheck rows; together
    they pin the monotonicity claim from [melt_curve.gp] section (1) at
    a finer grid. *)
Lemma payout_max_n100 :
  payoutRatio MAX_RATIO 100 = 9950661308629185.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W5) MAX_RATIO at N=1000 — between hour and minute rows ===== *)
Lemma payout_max_n1000 :
  payoutRatio MAX_RATIO 1000 = 95167106441453745.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W6) MAX_RATIO monotonicity across consecutive xcheck rows =====
    Pinning the inequalities directly so a future regression in [powu]
    that breaks monotonicity fails this file even if individual rows
    happen to match. *)
Lemma payout_max_monotone_n10_n100 :
  payoutRatio MAX_RATIO 10 <? payoutRatio MAX_RATIO 100 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma payout_max_monotone_n100_n1000 :
  payoutRatio MAX_RATIO 100 <? payoutRatio MAX_RATIO 1000 = true.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W7) Full melt() amount on 1M qRTok at MAX_RATIO over 1 hour =====
    payoutRatio(MAX_RATIO, 3600) = 302336232827074651 (xcheck pin), so
    amount = floor(payoutRatio * 10^6 * FIX_ONE / FIX_ONE)
           = 302336232827074651 * 10^6
           = 302336232827074651000000. *)
Lemma melt_max_1M_n3600_amount :
  snd (melt s_max 3600 one_million_qRTok) = 302336232827074651000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W8) Full melt() amount on 1M qRTok at typical ratio over 1 day =====
    payoutRatio(1e10, 86400) = 863626863788479, so
    amount = 863626863788479 * 10^6 = 863626863788479000000. *)
Lemma melt_typ_1M_n86400_amount :
  snd (melt s_typical 86400 one_million_qRTok) = 863626863788479000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W9) setRatio round-trip then melt — fresh ratio takes effect =====
    Start at [ratio = 0] (which would yield amount = 0 forever), call
    [setRatio MAX_RATIO], then [melt] for one period. The result must
    match the [N=1] MAX_RATIO row applied to the cached balance. *)
Definition s_after_setRatio : option Storage.t :=
  setRatio s_zero_ratio MAX_RATIO.

Lemma setRatio_then_melt_n1_amount :
  match s_after_setRatio with
  | Some s' => snd (melt s' 1 one_million_qRTok)
  | None    => -1
  end = 100000000000000 * 10^6.
Proof. vm_compute. reflexivity. Qed.

(** ===== (W10) lastPayout advances by exactly numPeriods =====
    [melt s_typical 86400 _] should advance lastPayout from 0 to 86400.
    Pinning this jointly with the amount lemma (W8) closes the bookkeeping
    side of the melt() postcondition. *)
Lemma melt_typ_lastPayout_advances :
  (fst (melt s_typical 86400 one_million_qRTok)).(Storage.lastPayout) = 86400.
Proof. vm_compute. reflexivity. Qed.

End FurnaceMeltWitnesses.
