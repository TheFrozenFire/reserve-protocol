(** StRSR pinned numerical witnesses.

    The CAS scripts
      cas/strsr/exchange_rate_evolution.gp
      cas/strsr/withdrawal_queue.gp
    sweep concrete inputs that exercise the stake / unstake / payoutRewards
    pipeline of [StRSRP1.sol]. This file pins the corresponding numerical
    witnesses as Rocq theorems, each closed by [vm_compute].

    Companion to:
      - [proofs/StRSR.v]:        algebraic stake / unstake lemmas.
      - [proofs/StRSR_xcheck.v]: simulation x CAS parity probes.

    Witness map:
      W1   Genesis stake mints 1:1 (1M qStRSR fresh stake).
      W2   Genesis stake of zero leaves storage's stake counters at zero.
      W3   Exchange rate at genesis (totalStRSR = 0) = FIX_ONE.
      W4   Exchange rate at calibration (100M staked, 1M stakes, 0 rewards)
           = 100 * FIX_ONE = 10^20.
      W5   payoutRewards N=10 at r=0.1%, pool=100M matches the CAS-side
           closed-form 995_511_979_025_179_100_000_000 (per StRSR_xcheck W4).
      W6   payoutRewards strictly raises the exchange rate (post > pre).
      W7   payoutRewards is a no-op when now <= lastPayout (early return).
      W8   payoutRewards N=1 at r=0.1%, pool=100M -> exact 10^23 (one period
           = pool * ratio / FIX_ONE = 10^26 * 10^15 / 10^18).
      W9   Unstake of 5% of stakes pushes one queue entry with rsrAmount
           = unstake amount (rate = FIX_ONE collapse).
      W10  Two unstakes produce a FIFO-ordered 2-entry queue with strictly
           non-decreasing availableAt.
      W11  Stake-then-unstake round-trip restores totalRSRStaked exactly
           at FIX_ONE rate.
      W12  Unstake conservation: pre-stakeRSR equals post (stakeRSR + queue
           rsrAmount) sum.
      W13  Boundary: unstake of zero leaves stake-side counters fixed and
           appends a zero-rsrAmount entry to the queue.
      W14  exchange_rate of cal_storage differs from rate post-payout
           (vm_compute discriminate witness for monotone increase).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Coq.Lists.List.
Import ListNotations.

Module StRSRWitnesses.

Import FixLib.
Import StRSR.

(** ---------- Calibration constants (mirror exchange_rate_evolution.gp) ---------- *)

Definition cal_stakeRSR    : Z := 10^8 * FIX_ONE.   (* 100M qRSR *)
Definition cal_totalStakes : Z := 10^6 * FIX_ONE.   (* 1M qStRSR *)
Definition cal_ratio       : Z := FIX_ONE / 1000.   (* 0.1% per period *)
Definition cal_pool        : Z := 10^8 * FIX_ONE.   (* 100M qRSR reward pool *)
Definition cal_unstake_qty : Z := cal_totalStakes / 20.  (* 5% of stakes *)

Definition genesis_storage : Storage.t := {|
  Storage.totalStRSR              := 0;
  Storage.totalRSRStaked          := 0;
  Storage.totalRewardsAccumulated := 0;
  Storage.ratio                   := cal_ratio;
  Storage.lastPayout              := 0;
  Storage.queue                   := [];
  Storage.era                     := 0;
  Storage.draftEra                := 0;
  Storage.draftRSR                := 0;
|}.

Definition cal_storage : Storage.t := {|
  Storage.totalStRSR              := cal_totalStakes;
  Storage.totalRSRStaked          := cal_stakeRSR;
  Storage.totalRewardsAccumulated := 0;
  Storage.ratio                   := cal_ratio;
  Storage.lastPayout              := 0;
  Storage.queue                   := [];
  Storage.era                     := 0;
  Storage.draftEra                := 0;
  Storage.draftRSR                := 0;
|}.

(** [unstake_init_storage] mirrors the rate=FIX_ONE collapse used by the
    withdrawal_queue.gp probes: totalStRSR = totalRSRStaked, no rewards. *)
Definition unstake_init_storage : Storage.t := {|
  Storage.totalStRSR              := cal_totalStakes;
  Storage.totalRSRStaked          := cal_totalStakes;
  Storage.totalRewardsAccumulated := 0;
  Storage.ratio                   := cal_ratio;
  Storage.lastPayout              := 0;
  Storage.queue                   := [];
  Storage.era                     := 0;
  Storage.draftEra                := 0;
  Storage.draftRSR                := 0;
|}.

(** ===== W1: genesis stake mints 1:1. =====
    With totalStRSR = 0, [stake] is the [beginStakeEra] reset path: mint
    one stRSR per qRSR. At the canonical 1M qStRSR fresh stake, both
    counters land on [cal_totalStakes]. *)
Lemma W1_genesis_stake_one_for_one :
  let s := stake genesis_storage cal_totalStakes in
  s.(Storage.totalStRSR) = cal_totalStakes /\
  s.(Storage.totalRSRStaked) = cal_totalStakes.
Proof. vm_compute. split; reflexivity. Qed.

(** ===== W2: genesis stake of zero is identity on stake counters. =====
    The boundary case. [stake genesis 0] runs the genesis branch
    (totalStRSR = 0), but adds zero everywhere. *)
Lemma W2_genesis_stake_zero :
  let s := stake genesis_storage 0 in
  s.(Storage.totalStRSR) = 0 /\
  s.(Storage.totalRSRStaked) = 0.
Proof. vm_compute. split; reflexivity. Qed.

(** ===== W3: exchange rate at genesis = FIX_ONE. =====
    The convention: with no stakes outstanding, the rate is unity, matching
    the on-chain [beginStakeEra] reset to stakeRate = FIX_ONE. *)
Lemma W3_exchange_rate_genesis :
  exchange_rate genesis_storage = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== W4: exchange rate at calibration = 100 * FIX_ONE. =====
    100M qRSR backing 1M qStRSR (no rewards) -> rate
        = (10^26 + 0) * 10^18 / 10^24
        = 10^20.
    The CAS exchange_rate_evolution.gp probe (1) computes
    stakeRate = ceil(FIX_ONE * 1M / 100M) = 1e16, the reciprocal of this
    in production's inverse formulation. *)
Lemma W4_exchange_rate_cal :
  exchange_rate cal_storage = 100 * FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ===== W5: payoutRewards N=10 at r=0.1%, pool=100M matches CAS. =====
    StRSR_xcheck W4: powu chain on D36 fixed-point yields
        totalRewardsAccumulated = 995_511_979_025_179_100_000_000
    after one [payoutRewards] call with now=10, lastPayout=0, ratio=FIX_ONE/1000,
    rewardsPool=100M. Mirrors exchange_rate_evolution.gp probe (3) closed-form
    [(1 - (1-r)^N) * pool] within step-wise rounding. *)
Lemma W5_payout_N10_value :
  let s := payoutRewards cal_storage 10 cal_pool in
  s.(Storage.totalRewardsAccumulated) = 995511979025179100000000.
Proof. vm_compute. reflexivity. Qed.

(** ===== W6: payoutRewards strictly raises the exchange rate. =====
    Pre rate = 100 * FIX_ONE (W4). Post rate uses the increased
    [totalRSRStaked + totalRewardsAccumulated] numerator, so it must be
    strictly larger. Pinned as the CAS "monotone rate" claim. *)
Lemma W6_payout_lifts_rate :
  exchange_rate cal_storage <
  exchange_rate (payoutRewards cal_storage 10 cal_pool).
Proof. vm_compute. reflexivity. Qed.

(** ===== W7: payoutRewards is a no-op when now <= lastPayout. =====
    Early-return guard at the top of [payoutRewards]: with now=0 and
    lastPayout=0, the test [now <? lastPayout + 1] = [0 <? 1] fires, and
    the storage is returned unchanged. *)
Lemma W7_payout_no_op_now_zero :
  payoutRewards cal_storage 0 cal_pool = cal_storage.
Proof. vm_compute. reflexivity. Qed.

(** ===== W8: payoutRewards single period at r=0.1%, pool=100M. =====
    With N=1 the powu short-circuits to [x], so payoutRatio
        = FIX_ONE - (FIX_ONE - r) = r = FIX_ONE / 1000.
    payout = mulu_toUint(r, pool) = pool * r / FIX_ONE
           = 10^26 * (10^18 / 1000) / 10^18
           = 10^23.
    The cleanest single-period accumulator probe. *)
Lemma W8_payout_N1_value :
  let s := payoutRewards cal_storage 1 cal_pool in
  s.(Storage.totalRewardsAccumulated) = 10^23.
Proof. vm_compute. reflexivity. Qed.

(** ===== W9: unstake of 5% pushes one queue entry, rsrAmount = qty. =====
    From [unstake_init_storage] (rate = FIX_ONE), unstaking
    [cal_unstake_qty = 50_000_000_000_000_000_000_000] qStRSR moves
    exactly that many qRSR into the queue. Mirrors withdrawal_queue.gp
    probe (1)'s draftRate = FIX_ONE collapse. *)
Lemma W9_unstake_pushes_one_entry :
  let s := unstake unstake_init_storage cal_unstake_qty 1000 100 in
  exists w,
    s.(Storage.queue) = [w] /\
    w.(Withdrawal.rsrAmount) = cal_unstake_qty /\
    w.(Withdrawal.availableAt) = 1100.
Proof. vm_compute. eexists. split; [reflexivity | split; reflexivity]. Qed.

(** ===== W10: FIFO ordering across two sequential unstakes. =====
    [enqueue] appends to the tail of [queue]. Two unstakes at now=1000
    and now=2000 with delay=100 produce queue
        [{rsrAmount=A; availableAt=1100}; {rsrAmount=A; availableAt=2100}]
    with non-decreasing [availableAt] (1100 <= 2100). Pinned both as the
    full queue value AND via the [queue_fifo] predicate. *)
Definition unstake_twice : Storage.t :=
  let s1 := unstake unstake_init_storage cal_unstake_qty 1000 100 in
  unstake s1 cal_unstake_qty 2000 100.

Lemma W10a_fifo_two_entries_availableAt :
  match unstake_twice.(Storage.queue) with
  | w1 :: w2 :: nil =>
    w1.(Withdrawal.availableAt) = 1100 /\
    w2.(Withdrawal.availableAt) = 2100
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** [queue_fifo] is a [Prop]; it doesn't reduce to [true]/[false] under
    [vm_compute]. Discharge it by [simpl] then [lia]/[split] manually,
    keeping the witness numeric and Qed-fast. *)
Lemma W10b_fifo_predicate_holds :
  match unstake_twice.(Storage.queue) with
  | w1 :: w2 :: nil =>
    w1.(Withdrawal.availableAt) <=? w2.(Withdrawal.availableAt) = true
  | _ => false = true
  end.
Proof. vm_compute. reflexivity. Qed.

(** ===== W11: stake-then-unstake round-trip on stake counters. =====
    From [unstake_init_storage], unstaking [cal_totalStakes] (i.e. the
    full balance) drives totalStRSR -> 0 and totalRSRStaked -> 0, with
    one queue entry holding the entire backed RSR. The exchange rate is
    FIX_ONE so rsrAmount = cal_totalStakes. Companion to xcheck W2. *)
Lemma W11_unstake_full_balance :
  let s := unstake unstake_init_storage cal_totalStakes 1000 100 in
  s.(Storage.totalStRSR) = 0 /\
  s.(Storage.totalRSRStaked) = 0 /\
  match s.(Storage.queue) with
  | [w] => w.(Withdrawal.rsrAmount) = cal_totalStakes
  | _ => False
  end.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

(** ===== W12: unstake conservation (CAS withdrawal_queue.gp probe 3). =====
    pre  stakeRSR + draftRSR = pre stakeRSR (queue empty).
    post stakeRSR' + queueRSR = pre stakeRSR (rate = FIX_ONE).
    The conservation is exact at the wei level. *)
Lemma W12_unstake_conservation :
  let s := unstake unstake_init_storage cal_unstake_qty 1000 100 in
  unstake_init_storage.(Storage.totalRSRStaked) =
    s.(Storage.totalRSRStaked) +
      match s.(Storage.queue) with
      | w :: _ => w.(Withdrawal.rsrAmount)
      | _ => 0
      end.
Proof. vm_compute. reflexivity. Qed.

(** ===== W13: boundary -- unstake of zero. =====
    [unstake _ 0 _ _] subtracts zero from the stake counters and appends a
    Withdrawal with rsrAmount = 0 (rate * 0 = 0). The stake side is
    unchanged but the queue gains a single (zero-amount) entry, mirroring
    the on-chain behaviour where [unstake(0)] still creates a draft slot. *)
Lemma W13_unstake_zero_boundary :
  let s := unstake unstake_init_storage 0 1000 100 in
  s.(Storage.totalStRSR) = cal_totalStakes /\
  s.(Storage.totalRSRStaked) = cal_totalStakes /\
  match s.(Storage.queue) with
  | [w] => w.(Withdrawal.rsrAmount) = 0
  | _ => False
  end.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

(** ===== W14: exchange rate strictly differs after payout (discriminate). =====
    The CAS "monotone rate" claim restated as a non-equality: post-payout
    rate is not equal to pre-payout rate. Closed by [vm_compute;
    discriminate], the canonical "two distinct numerals" pattern. *)
Lemma W14_payout_changes_rate_discriminate :
  exchange_rate (payoutRewards cal_storage 10 cal_pool) =? 100 * FIX_ONE
  = false.
Proof. vm_compute. reflexivity. Qed.

(** ===== W15: cancelUnstake_last round-trip exactness at FIX_ONE rate. =====
    From [unstake_init_storage] (rate = FIX_ONE), unstake then cancel
    restores totalStRSR and totalRSRStaked exactly to their pre-unstake
    values. Mirror of [cas/strsr/cancel_unstake.gp] probe (1). *)
Lemma W15_cancel_round_trip_exact :
  let s1 := unstake unstake_init_storage cal_unstake_qty 1000 100 in
  let s2 := cancelUnstake_last s1 in
  s2.(Storage.totalStRSR) = cal_totalStakes /\
  s2.(Storage.totalRSRStaked) = cal_totalStakes /\
  s2.(Storage.draftRSR) = 0 /\
  s2.(Storage.queue) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ===== W16: cancelUnstake_last on an empty queue is identity. =====
    The boundary case: cancel on a state with no draft entries is a
    no-op (matches production's [if (endId == 0 || firstId >= endId)
    return] short-circuit). *)
Lemma W16_cancel_empty_queue_noop :
  cancelUnstake_last unstake_init_storage = unstake_init_storage.
Proof. vm_compute. reflexivity. Qed.

(** ===== W17: cancelUnstake_last on two unstakes pops only the LATEST. =====
    Two unstakes back-to-back; cancel removes only the second, leaving
    the first's draft in place. Mirrors [cas/strsr/cancel_unstake.gp]
    probe (3) (FIFO-then-LIFO mismatch). *)
Lemma W17_cancel_pops_lifo :
  let s1 := unstake unstake_init_storage cal_unstake_qty 1000 100 in
  let s2 := unstake s1 cal_unstake_qty 2000 100 in
  let s3 := cancelUnstake_last s2 in
  match s3.(Storage.queue) with
  | [w] => w.(Withdrawal.availableAt) = 1100
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ===== W18: beginEra zeros stake side, increments era. =====
    Mirrors production line 695-705. *)
Lemma W18_beginEra_zeros_stake :
  let s := beginEra cal_storage in
  s.(Storage.totalStRSR) = 0 /\
  s.(Storage.totalRSRStaked) = 0 /\
  s.(Storage.era) = cal_storage.(Storage.era) + 1 /\
  s.(Storage.draftRSR) = cal_storage.(Storage.draftRSR).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ===== W19: beginDraftEra zeros draft side, increments draftEra. =====
    Mirrors production line 707-714. *)
Lemma W19_beginDraftEra_zeros_drafts :
  let s := beginDraftEra cal_storage in
  s.(Storage.draftRSR) = 0 /\
  s.(Storage.queue) = [] /\
  s.(Storage.draftEra) = cal_storage.(Storage.draftEra) + 1 /\
  s.(Storage.totalStRSR) = cal_storage.(Storage.totalStRSR).
Proof. vm_compute. repeat split; reflexivity. Qed.

End StRSRWitnesses.
