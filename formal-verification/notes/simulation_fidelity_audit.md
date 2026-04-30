# Simulation fidelity audit

The `simulations/<Domain>.v` files are hand-written Gallina models of
the production contracts. The proof tree's invariants are stated and
proved against these models, not against the Solidity directly. Any
divergence between simulation and production is a gap the proofs do
not cover.

This file records known divergences. It is currently incomplete — only
StRSR has been audited line-by-line. Other domains should be audited
with the same shape before the proof tree is taken as comprehensive
coverage.

## StRSR (`simulations/StRSR.v` vs `contracts/p1/StRSR.sol`)

The simulation captures the **revenue accrual and aggregate exchange
rate math**. It omits substantial structural state and operations that
the production contract maintains. The proofs against this model are
correct for the model; they do not transfer to the production contract
without first verifying the omitted structure does not interact with
the proved invariants.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `era`, `draftEra` | Seizure-driven balance reset (entire stake/draft pool wiped, era incremented) | None. The simulation has no notion of seizure. |
| `stakes[era][account]` | Per-account stake balance (the actual ERC20 balances) | None. Simulation aggregates to `totalStRSR` only. |
| `draftQueues[draftEra][account]` | Per-account draft queue, indexed by era | Single global `queue : list Withdrawal.t`. |
| `firstRemainingDraft[era][account]` | Index past which drafts have been claimed | None. Simulation has no claim/dequeue operation. |
| `CumulativeDraft.drafts` (uint176, *running total*) | Lets `withdraw` compute claimed amount as `queue[end-1].drafts - queue[first-1].drafts` in O(1) regardless of cancellations | `Withdrawal.rsrAmount` (the individual amount). Different data structure with different complexity properties. |
| `stakeRate`, `draftRate` (D18, separately tracked) | Independent exchange rates for stakes vs drafts; both can saturate at MAX_STAKE_RATE / MAX_DRAFT_RATE | Single derived `exchange_rate` from totals. No saturation modeled. |
| `stakeRSR`, `draftRSR` (separate RSR pools) | Drafts are paid from a distinct pool that doesn't earn rewards; seizure hits both proportionally | Conflated as `totalRSRStaked`. |
| `totalDrafts`, `totalStakes` separately | Sum of all drafts vs sum of all stakes | Only `totalStRSR`. |
| `_allowances`, `_nonces`, `_delegationNonces`, ERC20 name/symbol | ERC20 surface | None. The simulation isn't an ERC20. |
| `leaked`, `lastWithdrawRefresh`, `withdrawalLeak` | 3.0.0 withdrawal-leak mechanism: refresh required if cumulative leak exceeds `MAX_WITHDRAWAL_LEAK = 30%` | None. |
| `unstakingDelay`, `rewardRatio`, `withdrawalLeak` (governance setters) | Mutable governance parameters | `delay` is a function argument; `ratio` is in storage but with no setter. |
| `assetRegistry`, `backingManager`, `basketHandler`, `rsr` | Component pointers — `basketHandler.isReady()` and `fullyCollateralized()` gate `withdraw` | None. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `withdraw(account, endId)` | The actual RSR claim — pops drafts from the queue once `availableAt` has passed and transfers RSR to the account. Required for the unstake lifecycle to complete. | **No.** Simulation only models the queue-push half (`unstake`). |
| `cancelUnstake(endId)` | Rolls back queued drafts, returning them to active stake | **No.** |
| `seizeRSR(rsrAmount)` | Backing-manager-triggered seizure of RSR from both stake and draft pools, possibly triggering era reset if the pool is fully consumed | **No.** This is a major omission — the entire seizure-driven era model is unrepresented. |
| `resetStakes()` | Governance-triggered era reset when stakeRate / draftRate exits the safe band (`MAX_SAFE_STAKE_RATE` / `MIN_SAFE_STAKE_RATE`) | **No.** |
| `transfer`, `approve`, `transferFrom`, `permit`, `delegate`, `delegateBySig` | ERC20 + ERC20Permit + delegation surface | **No.** |
| `beginEra`, `beginDraftEra` | Internal era-reset primitives | **No.** |
| `init` | Initialization (sets payoutLastPaid, rsrRewardsAtLastPayout, governance params) | **No.** Simulation operates on an arbitrary `Storage.t`. |
| `setUnstakingDelay`, `setRewardRatio`, `setWithdrawalLeak` | Governance setters | **No.** |
| `payoutRewards()` (public) vs `_payoutRewards()` (internal) | The public form has no arguments and reads `rsrRewards()` from RSR balance; simulation takes `rewardsPool` as an explicit argument | **Partial.** The integral form is correct; the snapshot-vs-balance distinction is acknowledged in the simulation header. |
| Saturation behavior on extreme seizures | `stakeRate = MAX_STAKE_RATE` triggers era reset; `payoutRewards` skips when `rsrRewards == 0`; etc. | **No.** Simulation uses the inverse exchange-rate form precisely to avoid modeling saturation, per the simulation's header comment. |

### What the simulation *does* faithfully model

- **Aggregate revenue accrual**: `totalRewardsAccumulated` increases via the closed-form compound payout `1 - (1 - ratio)^N`. CAS xchecks pin specific values.
- **Aggregate exchange rate**: `(totalRSRStaked + totalRewardsAccumulated) / totalStRSR` — equivalent to production's `1 / stakeRate` up to inversion.
- **Stake math at the aggregate level**: `stake` mints `amount * FIX_ONE / rate` stRSR; `unstake` burns and queues an RSR principal at the current rate.
- **FIFO queue ordering**: `queue_fifo` predicate; `unstake` extends with monotone `availableAt`.
- **Genesis behavior**: `totalStRSR == 0 ⇒ rate = FIX_ONE` matches production's post-`beginEra` state.

### Implications for proof transferability

The proofs against this simulation establish:

- The closed-form payout matches the geometric pool decay (cross-checked by CAS).
- Aggregate `totalStRSR * rate ≥ totalRSRStaked * FIX_ONE` (the inverted form of production's `[stake-rate]` invariant).
- Aggregate stake/unstake conservation at fixed rate (`Integration_revenue_path.v`, `Integration_supply_decay.v`).

They do **not** establish:

- Per-account balance correctness.
- Withdraw lifecycle correctness (the simulation has no `withdraw`).
- Seizure/era-reset correctness — the entire path that handles RSR
  loss is unmodeled.
- ERC20 transfer/allowance/permit correctness.
- Withdrawal-leak refresh correctness (3.0.0 mechanism).
- Governance-parameter mutation effects.
- Cross-component interactions with `basketHandler.isReady()` /
  `fullyCollateralized()` gating.

The audit-relevant claim "StRSR exchange-rate accounting is verified"
should therefore be read narrowly as "the aggregate compound-payout
identity and the aggregate stake invariant hold under a model that
omits seizure, drafts-as-cumulative, per-account balances, and the
ERC20 surface."

### Recommended next steps if this gap matters

In approximate effort order:

1. Add a `withdraw` operation modeling the queue-pop / RSR-claim path.
   Required for the unstake lifecycle to be closeable. This is the
   smallest material extension.
2. Split `totalRSRStaked` into `stakeRSR` / `draftRSR` and model
   `seizeRSR` proportionally hitting both. Without this, the
   simulation cannot reason about under-collateralization recovery.
3. Add the `era` / `beginEra` / `beginDraftEra` model and a `seizeRSR`
   operation that triggers era reset on full pool consumption. Once
   present, the era-invariant ("each era's balances are consistent
   among themselves") becomes provable.
4. Lift to per-account balances. Substantially more work; gates
   per-account ERC20 / delegation reasoning.

## Other domains: not audited

The following simulations have not been compared line-by-line against
their production sources. The same audit shape should be applied
before the coverage claims can be taken as comprehensive:

- `simulations/Throttle.v` vs `contracts/libraries/Throttle.sol`
- `simulations/Furnace.v` vs `contracts/p1/Furnace.sol`
- `simulations/Distributor.v` vs `contracts/p1/Distributor.sol`
- `simulations/BackingManager.v` vs `contracts/p1/BackingManager.sol`
- `simulations/Rebalance.v` vs `contracts/libraries/RebalancingLib.sol`
- `simulations/TradeLib.v` vs `contracts/p1/mixins/TradeLib.sol`
- `simulations/BasketHandler.v` vs `contracts/p1/BasketHandler.sol`
- `simulations/DutchTrade.v` vs `contracts/plugins/trading/DutchTrade.sol`
- `simulations/GnosisTrade.v` vs `contracts/plugins/trading/GnosisTrade.sol`
- `simulations/Collateral.v` vs the asset/collateral plugins under
  `contracts/plugins/assets/`
- `simulations/IssuancePremium.v` vs the relevant code in
  `contracts/p1/BasketHandler.sol` and friends
