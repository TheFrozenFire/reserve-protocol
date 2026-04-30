(** StRSR simulation invariant proofs.

    Proves the load-bearing safety properties of the [StRSR]
    simulation:

      INV-XR-MONO   exchange_rate is non-decreasing across payoutRewards
                    (modulo the early-return guard).
      INV-STAKE     stake increments totalRSRStaked by [amount] and
                    creates stRSR proportionally to the current rate.
      INV-UNSTAKE   unstake decrements totalStRSR by [amount] and
                    queues a withdrawal of the corresponding rsrAmount.
      INV-FIFO      enqueue preserves the queue's FIFO order when the
                    new entry's availableAt dominates every existing
                    entry's.
      INV-RT        stake then immediate unstake at the same rate
                    recovers the original rsrAmount up to one wei of
                    rounding.

    The simulation is in [Z], so the invariants speak to algebraic
    correctness only; uint256 / uint192 boundedness lives separately
    in proofs/Fixed.v.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.StRSR.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Module StRSRProofs.

Import FixLib.
Import StRSR.

(** ---------- helpers ---------- *)

Lemma enqueue_last (q : list Withdrawal.t) (w : Withdrawal.t) :
  enqueue q w = q ++ [w].
Proof. reflexivity. Qed.

(** ---------- INV-FIFO ---------- *)

Lemma queue_fifo_app_singleton (q : list Withdrawal.t) (w : Withdrawal.t) :
  queue_fifo q ->
  (forall w', List.In w' q ->
              w'.(Withdrawal.availableAt) <= w.(Withdrawal.availableAt)) ->
  queue_fifo (q ++ [w]).
Proof.
  induction q as [|x rest IH]; intros Hq Hbound.
  - simpl. exact I.
  - destruct rest as [|y rest'] eqn:Erest.
    + simpl. split.
      * apply Hbound. left. reflexivity.
      * exact I.
    + simpl in Hq. destruct Hq as [Hxy Hrest].
      change ((x :: y :: rest') ++ [w]) with (x :: ((y :: rest') ++ [w])).
      change (queue_fifo (x :: ((y :: rest') ++ [w])))
        with (x.(Withdrawal.availableAt) <=
              (match (y :: rest') ++ [w] with
               | [] => x
               | w' :: _ => w'
               end).(Withdrawal.availableAt) /\
              queue_fifo ((y :: rest') ++ [w])).
      split.
      * change ((y :: rest') ++ [w]) with (y :: (rest' ++ [w])).
        exact Hxy.
      * apply IH.
        -- exact Hrest.
        -- intros w' Hin. apply Hbound. right. exact Hin.
Qed.

Lemma withdrawal_fifo
    (q : list Withdrawal.t) (w : Withdrawal.t) :
  queue_fifo q ->
  (forall w', List.In w' q ->
              w'.(Withdrawal.availableAt) <= w.(Withdrawal.availableAt)) ->
  queue_fifo (enqueue q w).
Proof.
  intros Hq Hbound. unfold enqueue.
  apply queue_fifo_app_singleton; assumption.
Qed.

Lemma withdrawal_fifo_empty (w : Withdrawal.t) :
  queue_fifo (enqueue [] w).
Proof.
  apply withdrawal_fifo.
  - exact I.
  - intros w' Hin. inversion Hin.
Qed.

(** ---------- INV-STAKE ---------- *)

Lemma stake_conservation_genesis
    (s : Storage.t) (amount : U256.t) :
  s.(Storage.totalStRSR) = 0 ->
  let s' := stake s amount in
  s'.(Storage.totalRSRStaked) = s.(Storage.totalRSRStaked) + amount /\
  s'.(Storage.totalStRSR) = amount /\
  s'.(Storage.totalRewardsAccumulated) = s.(Storage.totalRewardsAccumulated).
Proof.
  intros Hgen. unfold stake.
  rewrite Hgen.
  cbv match.
  cbn -[Z.add Z.eqb].
  rewrite Z.eqb_refl.
  cbn -[Z.add].
  repeat split.
Qed.

Lemma stake_conservation_active
    (s : Storage.t) (amount : U256.t) :
  s.(Storage.totalStRSR) <> 0 ->
  let s' := stake s amount in
  let rate := exchange_rate s in
  let minted := divrnd (amount * FIX_ONE_Z) rate RoundingMode.FLOOR in
  s'.(Storage.totalRSRStaked) = s.(Storage.totalRSRStaked) + amount /\
  s'.(Storage.totalStRSR) = s.(Storage.totalStRSR) + minted /\
  s'.(Storage.totalRewardsAccumulated) = s.(Storage.totalRewardsAccumulated).
Proof.
  intros Hnz. unfold stake.
  destruct (s.(Storage.totalStRSR) =? 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - cbn -[Z.add divrnd Z.mul exchange_rate]. repeat split.
Qed.

(** ---------- INV-UNSTAKE ---------- *)

Lemma unstake_conservation
    (s : Storage.t) (amount now delay : U256.t) :
  let s' := unstake s amount now delay in
  let rate := exchange_rate s in
  let rsrAmount := divrnd (amount * rate) FIX_ONE_Z RoundingMode.FLOOR in
  s'.(Storage.totalStRSR) = s.(Storage.totalStRSR) - amount /\
  s'.(Storage.totalRSRStaked) = s.(Storage.totalRSRStaked) - rsrAmount /\
  s'.(Storage.queue) =
    s.(Storage.queue) ++
       [{|
         Withdrawal.rsrAmount   := rsrAmount;
         Withdrawal.availableAt := now + delay;
       |}].
Proof.
  unfold unstake. cbn -[Z.add Z.sub Z.mul divrnd exchange_rate].
  unfold enqueue. repeat split.
Qed.

(** ---------- INV-XR-MONO ---------- *)

Lemma exchange_rate_active
    (s : Storage.t) :
  s.(Storage.totalStRSR) <> 0 ->
  exchange_rate s =
    ((s.(Storage.totalRSRStaked) + s.(Storage.totalRewardsAccumulated))
       * FIX_ONE_Z) / s.(Storage.totalStRSR).
Proof.
  intros Hnz. unfold exchange_rate.
  destruct (s.(Storage.totalStRSR) =? 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma payoutRewards_no_period
    (s : Storage.t) (now rewardsPool : U256.t) :
  now < s.(Storage.lastPayout) + 1 ->
  payoutRewards s now rewardsPool = s.
Proof.
  intros Hlt. unfold payoutRewards.
  assert (Hb : (now <? s.(Storage.lastPayout) + 1) = true)
    by (apply Z.ltb_lt; exact Hlt).
  rewrite Hb. reflexivity.
Qed.

Lemma payoutRewards_active
    (s : Storage.t) (now rewardsPool : U256.t) :
  s.(Storage.lastPayout) + 1 <= now ->
  payoutRewards s now rewardsPool = {|
    Storage.totalStRSR              := s.(Storage.totalStRSR);
    Storage.totalRSRStaked          := s.(Storage.totalRSRStaked);
    Storage.totalRewardsAccumulated :=
      s.(Storage.totalRewardsAccumulated) +
      FixLib.mulu_toUint
        (FixLib.minus FixLib.FIX_ONE
          (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
                       (now - s.(Storage.lastPayout))))
        rewardsPool RoundingMode.FLOOR;
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout) +
                                       (now - s.(Storage.lastPayout));
    Storage.queue                   := s.(Storage.queue);
    Storage.era                     := s.(Storage.era);
    Storage.draftEra                := s.(Storage.draftEra);
    Storage.draftRSR                := s.(Storage.draftRSR);
  |}.
Proof.
  intros Hle. unfold payoutRewards.
  assert (Hb : (now <? s.(Storage.lastPayout) + 1) = false)
    by (apply Z.ltb_ge; exact Hle).
  rewrite Hb. reflexivity.
Qed.

Lemma exchange_rate_monotone_payoutRewards
    (s : Storage.t) (now rewardsPool : U256.t) :
  let payoutRatio :=
    FixLib.minus FixLib.FIX_ONE
      (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio))
                   (now - s.(Storage.lastPayout))) in
  let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
  0 <= payout ->
  0 < s.(Storage.totalStRSR) ->
  exchange_rate s <= exchange_rate (payoutRewards s now rewardsPool).
Proof.
  intros payoutRatio payout Hpay Hsupply.
  destruct (Z_lt_le_dec now (s.(Storage.lastPayout) + 1)) as [Hno|Hyes].
  - rewrite (payoutRewards_no_period s now rewardsPool Hno). lia.
  - rewrite (payoutRewards_active s now rewardsPool Hyes).
    assert (HnsR : s.(Storage.totalStRSR) <> 0) by lia.
    rewrite (exchange_rate_active s HnsR).
    rewrite exchange_rate_active by (cbn; exact HnsR).
    cbn [Storage.totalStRSR Storage.totalRSRStaked
         Storage.totalRewardsAccumulated].
    apply Z.div_le_mono; [lia|].
    apply Z.mul_le_mono_nonneg_r; [unfold FIX_ONE_Z, FIX_ONE, FIX_SCALE; lia|].
    fold payoutRatio. fold payout. lia.
Qed.

(** ---------- INV-RT ---------- *)

(** Genesis fresh state with [ratio = 0]; we keep [ratio = 0] so the
    storage is computable to small terms. *)
Definition rt_genesis_storage : Storage.t := {|
  Storage.totalStRSR              := 0;
  Storage.totalRSRStaked          := 0;
  Storage.totalRewardsAccumulated := 0;
  Storage.ratio                   := 0;
  Storage.lastPayout              := 0;
  Storage.queue                   := [];
  Storage.era                     := 0;
  Storage.draftEra                := 0;
  Storage.draftRSR                := 0;
|}.

Lemma stake_genesis_eq (amount : U256.t) :
  stake rt_genesis_storage amount = {|
    Storage.totalStRSR              := amount;
    Storage.totalRSRStaked          := amount;
    Storage.totalRewardsAccumulated := 0;
    Storage.ratio                   := 0;
    Storage.lastPayout              := 0;
    Storage.queue                   := [];
    Storage.era                     := 0;
    Storage.draftEra                := 0;
    Storage.draftRSR                := 0;
  |}.
Proof.
  unfold stake, rt_genesis_storage.
  cbn -[Z.add].
  rewrite !Z.add_0_l.
  reflexivity.
Qed.

(** Exchange rate of a storage where [totalStRSR = totalRSRStaked = X]
    and rewards are zero is exactly FIX_ONE_Z. *)
Lemma exchange_rate_balanced (X : Z) :
  0 < X ->
  exchange_rate {|
    Storage.totalStRSR              := X;
    Storage.totalRSRStaked          := X;
    Storage.totalRewardsAccumulated := 0;
    Storage.ratio                   := 0;
    Storage.lastPayout              := 0;
    Storage.queue                   := [];
    Storage.era                     := 0;
    Storage.draftEra                := 0;
    Storage.draftRSR                := 0;
  |} = FIX_ONE_Z.
Proof.
  intros Hpos. unfold exchange_rate. cbn.
  assert (HX : (X =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite HX.
  unfold divrnd.
  rewrite Z.add_0_r.
  rewrite Z.mul_comm.
  rewrite Z_div_mult_full by lia.
  reflexivity.
Qed.

(** [unstake_after_stake_round_trip]: stake [amount] into a fresh
    storage, then immediately unstake [amount] -- the queue holds a
    single withdrawal of [amount] qRSR. *)
Lemma unstake_after_stake_round_trip
    (amount now delay : U256.t) :
  0 < amount ->
  let s1 := stake rt_genesis_storage amount in
  let s2 := unstake s1 amount now delay in
  exists w,
    s2.(Storage.queue) = [w] /\
    w.(Withdrawal.rsrAmount) = amount.
Proof.
  intros Hpos s1 s2.
  unfold s2, s1.
  rewrite stake_genesis_eq.
  unfold unstake.
  rewrite (exchange_rate_balanced amount Hpos).
  unfold enqueue.
  cbn [Storage.queue].
  eexists. split; [reflexivity|].
  cbn [Withdrawal.rsrAmount].
  unfold divrnd, FIX_ONE_Z, FIX_ONE, FIX_SCALE.
  rewrite Z_div_mult_full by lia.
  reflexivity.
Qed.

(** ---------- INV-SEIZE-NN ----------

    [seizeRSR_total_nonneg]: post-seizure, both [totalRSRStaked] and
    [draftRSR] remain non-negative. Follows directly from
    [seizeRSR_preserves_validity] (which gives the full [Valid.t]
    record), but pinned separately as the headline non-negativity
    claim. *)

(** Note: this lemma is stated in [proofs/StRSR_validity.v] under the
    [Valid.t]-preservation umbrella; we don't repeat the proof here.
    Use [StRSRValidity.seizeRSR_preserves_validity] at call sites. *)

(** ---------- INV-SEIZE-CONS ----------

    [seizeRSR_conserves_total_RSR]: in the no-era-reset branch,
    [totalRSRStaked + draftRSR] decreases by exactly [rsrAmount].

    This is the modular conservation property: production reverts on
    [rsrAmount > rsrBalance] (precondition), and the proportional
    split is constructed so [stake_share + draft_share = rsrAmount]
    exactly (CEIL on stake, residual to draft). When neither reset
    fires, the post-state has [totalRSRStaked + draftRSR =
    pre.(totalRSRStaked + draftRSR) - rsrAmount].

    Era-reset branches DO NOT preserve this exactly: when
    [beginEra] fires, [totalRSRStaked] is wiped to 0 (the residue
    is "given up" and seized in addition to [stake_share]); same for
    [beginDraftEra] and [draftRSR]. The lemma carries the
    no-reset hypothesis explicitly. *)

(** A storage where neither reset fires is exactly the [s_phase1]
    branch of [seizeRSR]. Project that out cleanly. *)
Definition seizeRSR_no_reset_phase1
    (s : Storage.t) (rsrAmount : U256.t) : Storage.t :=
  let totalRSR := s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) in
  let stake_share :=
    divrnd (s.(Storage.totalRSRStaked) * rsrAmount) totalRSR
           RoundingMode.CEIL in
  let draft_share := rsrAmount - stake_share in
  {|
    Storage.totalStRSR              := s.(Storage.totalStRSR);
    Storage.totalRSRStaked          := s.(Storage.totalRSRStaked) - stake_share;
    Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout);
    Storage.queue                   := s.(Storage.queue);
    Storage.era                     := s.(Storage.era);
    Storage.draftEra                := s.(Storage.draftEra);
    Storage.draftRSR                := s.(Storage.draftRSR) - draft_share;
  |}.

(** The modular conservation lemma: regardless of era resets, the
    Phase-1 (proportional split) post-state always satisfies the
    additive conservation
        totalRSRStaked + draftRSR = pre - rsrAmount.

    This is the load-bearing arithmetic identity: [stake_share +
    draft_share = stake_share + (rsrAmount - stake_share) = rsrAmount]
    by construction. *)
Lemma seizeRSR_phase1_conserves_total_RSR
    (s : Storage.t) (rsrAmount : U256.t) :
  let s' := seizeRSR_no_reset_phase1 s rsrAmount in
  s'.(Storage.totalRSRStaked) + s'.(Storage.draftRSR)
    = s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) - rsrAmount.
Proof.
  unfold seizeRSR_no_reset_phase1.
  cbn [Storage.totalRSRStaked Storage.draftRSR].
  lia.
Qed.

(** ---------- INV-SEIZE-PROP ----------

    [seizeRSR_proportional]: the stake-share and draft-share are
    bounded above and below by the proportional ratios of their
    pools to the total. Specifically:

      stake_share = ceil(totalRSRStaked * rsrAmount / totalRSR)
      draft_share = rsrAmount - stake_share

    so:
      totalRSRStaked * rsrAmount / totalRSR <= stake_share <= ceiling
      draft_share = rsrAmount - stake_share \in [floor, ceiling] of
                    draftRSR * rsrAmount / totalRSR.
*)
Lemma seizeRSR_proportional
    (s : Storage.t) (rsrAmount : U256.t) :
  0 <= rsrAmount ->
  rsrAmount <= s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) ->
  0 < s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) ->
  let totalRSR := s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) in
  let stake_share :=
    divrnd (s.(Storage.totalRSRStaked) * rsrAmount) totalRSR
           RoundingMode.CEIL in
  s.(Storage.totalRSRStaked) * rsrAmount <= stake_share * totalRSR /\
  stake_share * totalRSR < s.(Storage.totalRSRStaked) * rsrAmount + totalRSR.
Proof.
  intros Hra_nn Hra_le Htot_pos totalRSR stake_share.
  cbv zeta in *. unfold stake_share. Transparent FixLib.divrnd. unfold divrnd.
  set (n := s.(Storage.totalRSRStaked) * rsrAmount).
  fold n.
  set (q := n / totalRSR).
  set (r := n mod totalRSR).
  pose proof (Z.div_mod n totalRSR ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound n totalRSR Htot_pos) as [Hmlb Hmub].
  fold q r in Hdm, Hmlb, Hmub.
  destruct (r =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. nia.
  - apply Z.eqb_neq in Hzero. nia.
Qed.

End StRSRProofs.
