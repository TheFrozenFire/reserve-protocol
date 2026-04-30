(** StRSR simulation.

    Mirrors the core math of protocol/contracts/p1/StRSRP1.sol — the
    staking module that mints stRSR for staked RSR, locks RSR for
    unstaking via a FIFO withdrawal queue, and ratchets the exchange
    rate up over time as rewards are emitted.

    Modelling choices:

    - Exchange rate is expressed as a ratio
        rate = (rsrBacking + rewardsAccumulated) / stakeRSR
      following the simpler formulation in the task spec rather than
      the inverse [stakeRate = totalStakes / stakeRSR] used on chain.
      The two are equivalent up to inversion; the production form is
      preferred on chain because it lets [stakeRate] saturate to a
      maximum value safely on extreme seizures.

    - [stake amount] mints [stRSR_minted = amount * FIX_ONE / rate],
      i.e. proportionally to the current exchange rate. With the
      genesis condition [stakeRSR = 0], we mint [amount] one-for-one,
      matching production's [beginStakeEra] reset behaviour.

    - [unstake amount] burns [amount] stRSR, computes the locked
      [rsrAmount] at the current rate, and pushes a [withdrawal]
      onto the queue. The queue is a list ordered (by construction)
      by the [availableAt] timestamps, FIFO.

    - [payoutRewards] applies the per-period [ratio] over [numPeriods]
      via the closed form [1 - (1 - ratio)^N], adding the resulting
      reward amount into [totalRewardsAccumulated]. This monotonically
      raises the exchange rate. The on-chain code computes a payout
      out of an external [rsrRewards()] balance; here we use a
      simplified integral representation parameterised on the
      [rsrRewardsAtLastPayout] snapshot.

    All arithmetic is in [Z]; uint256/uint192 boundedness is left as a
    separate concern (the production code reverts on overflow via
    [FixLib._safeWrap]; the simulation's invariant lemmas state the
    pure-Z properties).

    Coverage scope: this simulation models aggregate stake/unstake math,
    compound payout, the [withdraw] / [cancelUnstake_last] / [seizeRSR]
    operations, and the seizure-driven era / draft-era reset model. It
    omits per-account balances, the ERC20 surface, the withdrawal-leak
    mechanism, governance-setter auth, and the basket-handler
    [isReady] / [fullyCollateralized] gates. See
    [../../notes/simulation_fidelity_audit.md] for the full divergence
    list and the proof-transferability implications.

    Revert coverage:
      Modeled:  [payoutRewards] early-return when [now < lastPayout + 1]
                (matches production's [_payoutRewards] check). No
                explicit revert paths.
      Deferred: [unstake]'s [amount <= totalStRSR] precondition is
                carried by integration lemmas as a hypothesis; the
                simulation does not check it. [Valid.t] holds the
                non-negativity, ratio-band, and conservation
                invariants. [seizeRSR]'s [rsrAmount <= totalRSRStaked
                + draftRSR] precondition (production's
                [SeizeExceedsBalance] revert) is similarly deferred to
                an explicit hypothesis.
      Not modeled: the [withdraw] / [cancelUnstake_last]
                [basketHandler.isReady() && fullyCollateralized()]
                gate, withdrawal-leak refresh requirements, ERC20
                transfer reverts, governance setter authentication.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Coq.Lists.List.
Import ListNotations.

Module StRSR.

Import FixLib.

Definition FIX_ONE_Z : Z := FIX_ONE.

(** Production governance cap on [ratio] per StRSR.sol#L42:
    [MAX_REWARD_RATIO = 1e14] (0.01% per period). Enforced by
    [setRewardRatio]; the simulation doesn't model the setter but
    carries the bound in [Valid.t] so all proofs operate within the
    governance-enforced range. *)
Definition MAX_REWARD_RATIO : Z := 10^14.

(** Production-side hard cap on the (inverted) stakeRate, per
    StRSR.sol#L68:
        MAX_STAKE_RATE = 1e9 * FIX_ONE  ({qStRSR/qRSR} D18)
    Crossing this cap during [seizeRSR] triggers a stake-side era
    reset ([beginEra]). The simulation does not separately track
    [stakeRate] (we collapse to a single [exchange_rate] derived
    from totals); the cap surfaces here purely as the proportional-
    seizure trigger that empties the stake pool when the seized
    fraction would otherwise leave a near-zero residue. *)
Definition MAX_STAKE_RATE : Z := 10^9 * FIX_ONE.

(** Production-side hard cap on [draftRate], per StRSR.sol#L90:
        MAX_DRAFT_RATE = 1e9 * FIX_ONE  ({qDrafts/qRSR} D18)
    Crossing this cap during [seizeRSR] triggers a draft-side era
    reset ([beginDraftEra]). *)
Definition MAX_DRAFT_RATE : Z := 10^9 * FIX_ONE.

(** A single withdrawal entry in the queue. [rsrAmount] is the locked
    RSR principal computed at the unstake-time rate; [availableAt] is
    the unix timestamp at which the entry vests. *)
Module Withdrawal.
  Record t : Set := {
    rsrAmount   : U256.t;   (** {qRSR} *)
    availableAt : U256.t;   (** {seconds} *)
  }.
End Withdrawal.

Module Storage.
  Record t : Set := {
    totalStRSR              : U256.t;   (** {qStRSR} *)
    totalRSRStaked          : U256.t;   (** {qRSR} — RSR backing stakes *)
    totalRewardsAccumulated : U256.t;   (** {qRSR} — accumulated rewards atop stakes *)
    ratio                   : U256.t;   (** {1}, D18 — per-period payout ratio *)
    lastPayout              : U256.t;   (** {seconds} *)
    queue                   : list Withdrawal.t;
    era                     : U256.t;   (** monotonically incremented by [beginEra] *)
    draftEra                : U256.t;   (** monotonically incremented by [beginDraftEra] *)
    draftRSR                : U256.t;   (** {qRSR} — RSR locked in the withdrawal queue *)
  }.
End Storage.

(** ---------- Exchange rate ----------

    rate = (rsrBacking + rewardsAccumulated) / stakeRSR

    where [stakeRSR = totalRSRStaked]. We return the rate as a D18
    fixed-point quantity. With [totalStRSR = 0] the rate is by
    convention [FIX_ONE] (one stRSR per RSR), matching production's
    genesis era. *)
Definition exchange_rate (s : Storage.t) : Z :=
  if s.(Storage.totalStRSR) =? 0 then FIX_ONE_Z
  else
    divrnd
      ((s.(Storage.totalRSRStaked) + s.(Storage.totalRewardsAccumulated))
         * FIX_ONE_Z)
      s.(Storage.totalStRSR)
      RoundingMode.FLOOR.

(** ---------- stake ----------

    Mints stRSR proportional to [amount] at the current exchange rate.
    With [totalStRSR = 0] (genesis era) the rate is unity by
    convention; we mint [amount] one-for-one and grow [totalRSRStaked]
    by [amount].

    On a non-genesis call:
        rate         = currentRate
        stRSR_minted = amount * FIX_ONE / rate     (FLOOR)
        totalRSRStaked' = totalRSRStaked + amount
        totalStRSR'  = totalStRSR + stRSR_minted

    Returns the updated storage. *)
Definition stake (s : Storage.t) (amount : U256.t) : Storage.t :=
  if s.(Storage.totalStRSR) =? 0 then
    {|
      Storage.totalStRSR              := s.(Storage.totalStRSR) + amount;
      Storage.totalRSRStaked          := s.(Storage.totalRSRStaked) + amount;
      Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
      Storage.ratio                   := s.(Storage.ratio);
      Storage.lastPayout              := s.(Storage.lastPayout);
      Storage.queue                   := s.(Storage.queue);
      Storage.era                     := s.(Storage.era);
      Storage.draftEra                := s.(Storage.draftEra);
      Storage.draftRSR                := s.(Storage.draftRSR);
    |}
  else
    let rate := exchange_rate s in
    let minted := divrnd (amount * FIX_ONE_Z) rate RoundingMode.FLOOR in
    {|
      Storage.totalStRSR              := s.(Storage.totalStRSR) + minted;
      Storage.totalRSRStaked          := s.(Storage.totalRSRStaked) + amount;
      Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
      Storage.ratio                   := s.(Storage.ratio);
      Storage.lastPayout              := s.(Storage.lastPayout);
      Storage.queue                   := s.(Storage.queue);
      Storage.era                     := s.(Storage.era);
      Storage.draftEra                := s.(Storage.draftEra);
      Storage.draftRSR                := s.(Storage.draftRSR);
    |}.

(** ---------- enqueue ----------

    Append a [Withdrawal] onto the queue. We expose this as a separate
    constructor so the FIFO invariant — non-decreasing [availableAt] —
    can be stated as a precondition on the new entry's timestamp. *)
Definition enqueue (q : list Withdrawal.t) (w : Withdrawal.t) : list Withdrawal.t :=
  q ++ [w].

(** Predicate: queue entries are in non-decreasing order of [availableAt]. *)
Fixpoint queue_fifo (q : list Withdrawal.t) : Prop :=
  match q with
  | [] => True
  | w :: rest =>
    match rest with
    | [] => True
    | w' :: _ =>
      w.(Withdrawal.availableAt) <= w'.(Withdrawal.availableAt) /\
      queue_fifo rest
    end
  end.

(** ---------- unstake ----------

    Burns [amount] stRSR, computes the corresponding RSR principal at
    the current rate, moves that RSR from the active stake pool
    [totalRSRStaked] into the draft pool [draftRSR], and pushes a
    withdrawal entry recording the amount and the unlock timestamp.

    Pre: [amount <= totalStRSR]. We do not enforce this here; the
    [unstake_conservation] lemma takes it as an explicit hypothesis.

        rate         = currentRate
        rsrAmount    = amount * rate / FIX_ONE   (FLOOR)
        totalStRSR'  = totalStRSR - amount
        totalRSRStaked' = totalRSRStaked - rsrAmount
        draftRSR'    = draftRSR + rsrAmount
        queue'       = queue ++ [{rsrAmount; now + delay}]

    The simulation conflates the per-account [draftQueues[draftEra]
    [account]] mapping with a single global [queue]; production
    tracks per-account cumulative-draft running totals while we
    record each entry's individual [rsrAmount]. The conservation
    invariant carried by [Valid.t] ([sum(queue.rsrAmount) <= draftRSR])
    is the simulation analog of production's [total-drafts /
    [draft-rate]] invariant block. *)
Definition unstake
    (s : Storage.t) (amount : U256.t) (now : U256.t) (delay : U256.t)
    : Storage.t :=
  let rate := exchange_rate s in
  let rsrAmount := divrnd (amount * rate) FIX_ONE_Z RoundingMode.FLOOR in
  let w := {|
    Withdrawal.rsrAmount   := rsrAmount;
    Withdrawal.availableAt := now + delay;
  |} in
  {|
    Storage.totalStRSR              := s.(Storage.totalStRSR) - amount;
    Storage.totalRSRStaked          := s.(Storage.totalRSRStaked) - rsrAmount;
    Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout);
    Storage.queue                   := enqueue s.(Storage.queue) w;
    Storage.era                     := s.(Storage.era);
    Storage.draftEra                := s.(Storage.draftEra);
    Storage.draftRSR                := s.(Storage.draftRSR) + rsrAmount;
  |}.

(** ---------- withdraw ----------

    Pop the front entry of the queue if it has matured ([availableAt <= now])
    and return the [rsrAmount] paid out to the staker. If the front is not
    yet ready, the queue is unchanged and 0 is returned.

    On a successful pop the [draftRSR] pool is decremented by exactly
    the popped entry's [rsrAmount] (production line 341), preserving
    the conservation invariant
        sum(queue.rsrAmount) <= draftRSR.
    [totalRSRStaked] is untouched (it tracks the active backing pool
    only; [unstake] already moved this quantity out when the entry was
    enqueued).

    Production's [withdraw] takes an [endId] specifying how many entries
    to claim in a batch. We model the simpler one-step pop here; batch
    withdrawal is the iterated composition. The vesting check is
    head-of-queue only because the FIFO invariant ([queue_fifo]) ensures
    the head's [availableAt] is the smallest in the queue — so if the
    head is not ready, none are.

    Pre: [queue_fifo s.(queue)] (carried by [Valid.t]).

    Diverges from production:
      - Per-account state not modeled (sim aggregates everything).
      - The [basketHandler.isReady() && fullyCollateralized()] gate is
        not modeled — production reverts with [RTokenNotReady] if either
        condition fails.
      - The withdrawal-leak refresh is not modeled — production calls
        [leakyRefresh(rsrAmount)] inline.
*)
Definition withdraw (s : Storage.t) (now : U256.t) : Storage.t * U256.t :=
  match s.(Storage.queue) with
  | [] => (s, 0)
  | w :: rest =>
    if w.(Withdrawal.availableAt) <=? now then
      ({|
        Storage.totalStRSR              := s.(Storage.totalStRSR);
        Storage.totalRSRStaked          := s.(Storage.totalRSRStaked);
        Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
        Storage.ratio                   := s.(Storage.ratio);
        Storage.lastPayout              := s.(Storage.lastPayout);
        Storage.queue                   := rest;
        Storage.era                     := s.(Storage.era);
        Storage.draftEra                := s.(Storage.draftEra);
        Storage.draftRSR                := s.(Storage.draftRSR) - w.(Withdrawal.rsrAmount);
      |}, w.(Withdrawal.rsrAmount))
    else (s, 0)
  end.

(** ---------- payoutRewards ----------

    Computes the compound payout ratio
        payoutRatio = FIX_ONE - (FIX_ONE - ratio)^N
    over [N = now - lastPayout] periods, applies it to a [rewardsPool]
    snapshot, and adds the resulting payout to
    [totalRewardsAccumulated]. The exchange rate increases (or stays
    constant) as a result.

    Following production's [_payoutRewards], we early-return if
    [now < lastPayout + 1] (no whole period elapsed). *)
Definition payoutRewards
    (s : Storage.t) (now : U256.t) (rewardsPool : U256.t)
    : Storage.t :=
  if now <? s.(Storage.lastPayout) + 1 then s
  else
    let numPeriods := now - s.(Storage.lastPayout) in
    let payoutRatio :=
      FixLib.minus FixLib.FIX_ONE
        (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio)) numPeriods) in
    let payout := FixLib.mulu_toUint payoutRatio rewardsPool RoundingMode.FLOOR in
    {|
      Storage.totalStRSR              := s.(Storage.totalStRSR);
      Storage.totalRSRStaked          := s.(Storage.totalRSRStaked);
      Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated) + payout;
      Storage.ratio                   := s.(Storage.ratio);
      Storage.lastPayout              := s.(Storage.lastPayout) + numPeriods;
      Storage.queue                   := s.(Storage.queue);
      Storage.era                     := s.(Storage.era);
      Storage.draftEra                := s.(Storage.draftEra);
      Storage.draftRSR                := s.(Storage.draftRSR);
    |}.

(** ---------- beginEra / beginDraftEra ----------

    Production lines 695-705 / 707-714: the era-reset primitives. They
    are called internally from [seizeRSR] (when a stake or draft pool is
    fully consumed) and from [resetStakes] (governance-triggered when
    one of the rates exits its safe band).

    [beginEra] zeros the active stake side ([totalStRSR],
    [totalRSRStaked]) and increments [era]. Production additionally
    resets [stakeRate] to [FIX_ONE]; the simulation derives the rate
    from totals so the convention falls out of [exchange_rate]
    returning [FIX_ONE_Z] when [totalStRSR = 0].

    [beginDraftEra] zeros the draft side ([draftRSR], [queue]) and
    increments [draftEra]. *)
Definition beginEra (s : Storage.t) : Storage.t :=
  {|
    Storage.totalStRSR              := 0;
    Storage.totalRSRStaked          := 0;
    Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout);
    Storage.queue                   := s.(Storage.queue);
    Storage.era                     := s.(Storage.era) + 1;
    Storage.draftEra                := s.(Storage.draftEra);
    Storage.draftRSR                := s.(Storage.draftRSR);
  |}.

Definition beginDraftEra (s : Storage.t) : Storage.t :=
  {|
    Storage.totalStRSR              := s.(Storage.totalStRSR);
    Storage.totalRSRStaked          := s.(Storage.totalRSRStaked);
    Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
    Storage.ratio                   := s.(Storage.ratio);
    Storage.lastPayout              := s.(Storage.lastPayout);
    Storage.queue                   := [];
    Storage.era                     := s.(Storage.era);
    Storage.draftEra                := s.(Storage.draftEra) + 1;
    Storage.draftRSR                := 0;
  |}.

(** ---------- cancelUnstake_last ----------

    Pop the *back* (most recently enqueued) entry of the queue and
    re-stake its [rsrAmount] at the *current* exchange rate. Mirrors
    production's [cancelUnstake] (StRSR.sol#356) for a single tail
    entry: production iterates over a contiguous suffix of the
    per-account queue indexed by [endId]; the simulation models the
    one-step LIFO pop, which composes by iteration. The rate used to
    convert RSR back to stRSR is the *current* [exchange_rate], not the
    rate at unstake time, matching production's [mintStakes] call.

    The total RSR sum [totalRSRStaked + draftRSR] is preserved by this
    operation (RSR moves from [draftRSR] back into [totalRSRStaked]).
    The stRSR side is lossy: [unstake] did
        rsrAmount = floor(amount * rate1 / FIX_ONE)
    and [cancelUnstake_last] mints
        amount' = floor(rsrAmount * FIX_ONE / rate2).
    With [rate1 = rate2 = FIX_ONE] the round-trip is exact; otherwise
    the two FLOOR steps each may shave one wei.

    Pre: [s.(queue) <> []]. We use the [match]-on-tail idiom to make
    the empty case a no-op (matching production's
    [if (endId == 0 || firstId >= endId) return]).

    Diverges from production:
      - Per-account [firstRemainingDraft]/[draftQueues] not modeled —
        the simulation has a single global queue.
      - [endId] is fixed to the queue's tail; production allows any
        [endId] in a contiguous suffix.
      - Production's [_payoutRewards] is called inline; the simulation
        callers compose [payoutRewards] explicitly when they need the
        accrual. *)
Definition cancelUnstake_last (s : Storage.t) : Storage.t :=
  match List.rev s.(Storage.queue) with
  | [] => s
  | w :: rest_rev =>
    let qFront := List.rev rest_rev in
    let rsrAmount := w.(Withdrawal.rsrAmount) in
    (* Convert RSR back to stRSR at the current rate. With totalStRSR =
       0 we use the genesis FIX_ONE convention: mint one-for-one. *)
    let minted :=
      if s.(Storage.totalStRSR) =? 0 then
        rsrAmount
      else
        let rate := exchange_rate s in
        divrnd (rsrAmount * FIX_ONE_Z) rate RoundingMode.FLOOR
    in
    {|
      Storage.totalStRSR              := s.(Storage.totalStRSR) + minted;
      Storage.totalRSRStaked          := s.(Storage.totalRSRStaked) + rsrAmount;
      Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
      Storage.ratio                   := s.(Storage.ratio);
      Storage.lastPayout              := s.(Storage.lastPayout);
      Storage.queue                   := qFront;
      Storage.era                     := s.(Storage.era);
      Storage.draftEra                := s.(Storage.draftEra);
      Storage.draftRSR                := s.(Storage.draftRSR) - rsrAmount;
    |}
  end.

(** ---------- sum_rsr_amounts ----------

    Sum of [rsrAmount] across the queue. Used by the conservation
    invariant in [Valid.t] and by the [seizeRSR] proportional-split
    proofs. Defined here (rather than in the [Integration_unstake_lifecycle]
    file where it originated) so that the simulation's own [Valid.t]
    invariants can refer to it. *)
Fixpoint sum_rsr_amounts (q : list Withdrawal.t) : Z :=
  match q with
  | [] => 0
  | w :: rest => w.(Withdrawal.rsrAmount) + sum_rsr_amounts rest
  end.

(** ---------- seizeRSR ----------

    Production-faithful seizure: backing-manager-triggered removal of
    [rsrAmount] qRSR from the StRSR contract, split proportionally
    between the stake and draft pools. If either pool is fully
    consumed (or its derived rate would saturate the [MAX_STAKE_RATE]
    / [MAX_DRAFT_RATE] cap), the corresponding era is reset.

    Production line 436-507. The simulation's collapsed-rate model
    means we don't separately maintain [stakeRate] / [draftRate]
    fields, so the [stakeRate > MAX_STAKE_RATE] saturation trigger
    can't be checked by direct comparison. We approximate it via the
    product
        totalStRSR' * FIX_ONE > stakeRSR_post * MAX_STAKE_RATE
    which is the "rate would round above the cap" condition.

    Mathematical kernel (production line 457-484):
        total_RSR    = totalRSRStaked + draftRSR
        keep_ratio   = 1 - rsrAmount / total_RSR
        stake_share  = ceil(totalRSRStaked * rsrAmount / total_RSR)
        draft_share  = ceil(draftRSR       * rsrAmount / total_RSR)
        seizedRSR    = stake_share + draft_share + (era-reset residues)

    Production uses [rsrBalance = stakeRSR + draftRSR + rewards] as
    the divisor; the simulation's [rsrAmount] is constrained to
    [<= totalRSRStaked + draftRSR] (no separate rewards balance). The
    proportional-split numerator stays the same, the divisor differs
    only by the [rewards] term that we abstract away.

    Pre: [rsrAmount <= totalRSRStaked + draftRSR] (production's
    [SeizeExceedsBalance] revert; we discharge it in the validity
    preservation lemma rather than enforce it inline).

    Diverges from production:
      - Single combined seizure step rather than the production's
        two-phase computation (Phase 1 updates rates, Phase 2 fires
        era resets). The two phases have the same net effect when
        [Valid.t] holds; the simulation collapses them.
      - The [rewards * rsrAmount / rsrBalance] residue piece is not
        modeled separately (production tracks [rsrRewardsAtLastPayout]
        which is updated as part of the seizure).
      - [exchangeRate()] event emission and ERC20 transfer side-effects
        not modeled (irrelevant to the storage-state invariants). *)
Definition seizeRSR (s : Storage.t) (rsrAmount : U256.t) : Storage.t :=
  let totalRSR := s.(Storage.totalRSRStaked) + s.(Storage.draftRSR) in
  if totalRSR =? 0 then
    (* Degenerate: nothing to seize. Production reverts on
       [SeizeExceedsBalance] when [rsrAmount > 0]; with [rsrAmount = 0]
       production's [_notZero] guard reverts first. The simulation
       returns [s] unchanged for both cases (no-op semantics for the
       non-Valid input). *)
    s
  else
    (* CEIL division for stake_share, residual to draft_share so that
       the two add to [rsrAmount] exactly (production splits this way
       to avoid leaving dust in either pool). *)
    let stake_share :=
      divrnd (s.(Storage.totalRSRStaked) * rsrAmount) totalRSR RoundingMode.CEIL in
    let draft_share := rsrAmount - stake_share in
    let stakeRSR_post := s.(Storage.totalRSRStaked) - stake_share in
    let draftRSR_post := s.(Storage.draftRSR) - draft_share in
    (* Stake-side era reset trigger:
       1. [stakeRSR_post = 0]: trivially needs reset (production line 466).
       2. [totalStRSR > 0] and the derived rate would exceed
          [MAX_STAKE_RATE]: production line 466 checks [stakeRate >
          MAX_STAKE_RATE]; we model the derived-rate test as
          [totalStRSR * FIX_ONE > stakeRSR_post * MAX_STAKE_RATE]. *)
    let stake_reset :=
      (stakeRSR_post =? 0) ||
      ((0 <? s.(Storage.totalStRSR)) &&
       (s.(Storage.totalStRSR) * FIX_ONE_Z >? stakeRSR_post * MAX_STAKE_RATE)) in
    (* Draft-side era reset trigger:
       1. [draftRSR_post = 0]: trivially (production line 481).
       2. The conservation invariant
            sum_rsr_amounts queue <= draftRSR_post
          would break. This is the simulation's tighter analog of
          production's [draftRate > MAX_DRAFT_RATE] check; the
          simulation maintains [draftRate = FIX_ONE] (no separate
          draftRate field), so it era-resets at the FIX_ONE boundary
          rather than the MAX_DRAFT_RATE boundary. The simulation's
          reachable-state set is therefore a strict subset of
          production's, but every reachable state satisfies the
          [Valid.t] invariants. *)
    let draft_reset :=
      (draftRSR_post =? 0) ||
      (sum_rsr_amounts s.(Storage.queue) >? draftRSR_post) in
    (* Build the post-seizure storage by applying the proportional
       deltas, then conditionally apply [beginEra] / [beginDraftEra]. *)
    let s_phase1 := {|
      Storage.totalStRSR              := s.(Storage.totalStRSR);
      Storage.totalRSRStaked          := stakeRSR_post;
      Storage.totalRewardsAccumulated := s.(Storage.totalRewardsAccumulated);
      Storage.ratio                   := s.(Storage.ratio);
      Storage.lastPayout              := s.(Storage.lastPayout);
      Storage.queue                   := s.(Storage.queue);
      Storage.era                     := s.(Storage.era);
      Storage.draftEra                := s.(Storage.draftEra);
      Storage.draftRSR                := draftRSR_post;
    |} in
    let s_after_stake := if stake_reset then beginEra s_phase1 else s_phase1 in
    if draft_reset then beginDraftEra s_after_stake else s_after_stake.

(** Validity predicate — the pure-Z invariants the model maintains.

    [queue_entries_nonneg] is the per-entry counterpart of the
    aggregate [queue_drafts_le_draftRSR]: every queue entry's
    [rsrAmount] is non-negative. Required by [withdraw] (decrementing
    [draftRSR] by a non-negative amount keeps it non-negative) and by
    the queue-manipulation lemmas in [seizeRSR] / [cancelUnstake_last].
    Operations that push entries (just [unstake]) push an [rsrAmount]
    computed by [divrnd] of a non-negative numerator by a positive
    denominator, which is always non-negative; the validity preservation
    lemmas discharge this.

    [queue_drafts_le_draftRSR] models production's [draft-rate]
    invariant block (StRSR.sol#L120):
        [draft-rate]: draftRSR * draftRate >= totalDrafts * 1e18
    The simulation's analog is [sum_rsr_amounts queue <= draftRSR]
    (which corresponds to [draftRate = FIX_ONE]; production allows
    [draftRate > FIX_ONE] up to [MAX_DRAFT_RATE]). The simulation
    chooses the tighter [draftRate = FIX_ONE] invariant because it
    does not separately track [draftRate]; operations that would
    push the implied rate above [FIX_ONE] (i.e. seizures that shrink
    [draftRSR] below the queue's draft sum) trigger an era reset
    via [beginDraftEra], wiping the queue and restoring the invariant.

    This is strictly tighter than production but consistent with it —
    every production state where [draftRate > FIX_ONE] but
    [draftRate <= MAX_DRAFT_RATE] is unreachable in the simulation
    (the simulation pre-emptively era-resets earlier). The proofs
    are still safety-conservative: any safety property proved in the
    simulation also holds in production (the simulation's reachable
    states are a subset). *)
Module Valid.
  Record t (s : Storage.t) : Prop := {
    totalStRSR_nonneg     : 0 <= s.(Storage.totalStRSR);
    totalRSRStaked_nonneg : 0 <= s.(Storage.totalRSRStaked);
    rewards_nonneg        : 0 <= s.(Storage.totalRewardsAccumulated);
    ratio_in_range        : 0 <= s.(Storage.ratio) <= MAX_REWARD_RATIO;
    queue_ordered         : queue_fifo s.(Storage.queue);
    draftRSR_nonneg       : 0 <= s.(Storage.draftRSR);
    queue_drafts_le_draftRSR :
      sum_rsr_amounts s.(Storage.queue) <= s.(Storage.draftRSR);
    queue_entries_nonneg  :
      forall w, List.In w s.(Storage.queue) ->
                0 <= w.(Withdrawal.rsrAmount);
  }.
End Valid.

End StRSR.
