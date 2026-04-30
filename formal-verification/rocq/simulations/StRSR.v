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

    Coverage scope: this simulation models aggregate stake/unstake math
    and compound payout. It omits per-account balances, the era /
    seizure / draft-rate model, the [withdraw] / [cancelUnstake] /
    [seizeRSR] operations, the ERC20 surface, and the withdrawal-leak
    mechanism. See [../../notes/simulation_fidelity_audit.md] for the
    full divergence list and the proof-transferability implications.

    Revert coverage:
      Modeled:  [payoutRewards] early-return when [now < lastPayout + 1]
                (matches production's [_payoutRewards] check). No
                explicit revert paths.
      Deferred: [unstake]'s [amount <= totalStRSR] precondition is
                carried by integration lemmas as a hypothesis; the
                simulation does not check it. [Valid.t] holds the
                non-negativity and ratio-band invariants.
      Not modeled: the [withdraw]/[cancelUnstake] vesting-completion
                paths (which check [availableAt <= now] and
                [basketHandler.isReady() && fullyCollateralized()]),
                era-reset triggers via [seizeRSR], withdrawal-leak
                refresh requirements, ERC20 transfer reverts, governance
                setter authentication.
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
    the current rate, and pushes a withdrawal onto the queue with
    [availableAt = now + delay].

    Pre: [amount <= totalStRSR]. We do not enforce this here; the
    [unstake_conservation] lemma takes it as an explicit hypothesis.

        rate         = currentRate
        rsrAmount    = amount * rate / FIX_ONE   (FLOOR)
        totalStRSR'  = totalStRSR - amount
        totalRSRStaked' = totalRSRStaked - rsrAmount
        queue'       = queue ++ [{rsrAmount; now + delay}]
*)
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
  |}.

(** ---------- withdraw ----------

    Pop the front entry of the queue if it has matured ([availableAt <= now])
    and return the [rsrAmount] paid out to the staker. If the front is not
    yet ready, the queue is unchanged and 0 is returned.

    Note: the [totalRSRStaked] field is NOT decremented here — [unstake]
    already moved that quantity out of the active stake pool when the
    entry was enqueued. In the simulation's collapsed accounting,
    [totalRSRStaked] tracks the active backing pool only; the queue
    entries themselves represent the locked draft RSR. A user redemption
    via [withdraw] just transfers the entry's [rsrAmount] from the
    locked-in-queue pool to the staker's balance.

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
    |}.

(** Validity predicate — the pure-Z invariants the model maintains. *)
Module Valid.
  Record t (s : Storage.t) : Prop := {
    totalStRSR_nonneg     : 0 <= s.(Storage.totalStRSR);
    totalRSRStaked_nonneg : 0 <= s.(Storage.totalRSRStaked);
    rewards_nonneg        : 0 <= s.(Storage.totalRewardsAccumulated);
    ratio_in_range        : 0 <= s.(Storage.ratio) <= MAX_REWARD_RATIO;
    queue_ordered         : queue_fifo s.(Storage.queue);
  }.
End Valid.

End StRSR.
