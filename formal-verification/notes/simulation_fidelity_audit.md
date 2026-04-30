# Simulation fidelity audit

The `simulations/<Domain>.v` files are hand-written Gallina models of the
production contracts. The proof tree's invariants are stated and proved
against these models, not against the Solidity directly. Any divergence
between simulation and production is a gap the proofs do not cover.

This file documents all known divergences across the proof tree. It is
organized as cross-cutting findings (patterns that recur across several
simulations) followed by per-simulation summaries.

---

# Part 1 — Cross-cutting findings

## 1. Edge-case guards

For each simulation, the question is: does the simulation handle all the
input edge cases that the production contract handles, and does it do
so with the same semantics (return value, revert, no-op)?

### Findings

| Simulation | Zero-input handling | Empty-collection | Terminal-state | Observations |
|---|---|---|---|---|
| **Throttle** | `amount = 0` → no-op; `amtRate = pctRate = 0` → return as-is | n/a | n/a | Faithful match. The "untestable" branches in production are explicit branches in the sim. |
| **Furnace** | `now < lastPayout + 1` → no-op `(s, 0)`; `amount = 0` → balance update only | n/a | n/a | Faithful. |
| **Distributor** | `totalShares = 0` → `(nil, amount)` returned | Empty destination list → `nil` returned | n/a | **Divergence**: production reverts with `"nothing to distribute"` when `tokensPerShare = 0`. The sim returns dust = amount. The header documents this explicitly. |
| **BasketHandler** | `refAmt = 0` in `redeem_one` → 0 returned (avoids div-by-zero) | Empty basket → `nil` quote | n/a | Faithful, but the production `quote` reverts on basket-not-set; sim doesn't model the lifecycle. |
| **BackingManager** | `bal <= req` → zero split; `totalShares = 0` → `Result.Revert` | n/a | n/a | Faithful for the math kernel. |
| **Rebalance** | n/a (algebraic skeleton) | n/a | n/a | Header explicitly scopes out per-asset oracle / FIX_MAX-overflow reverts. |
| **StRSR** | `totalStRSR = 0` → genesis rate `FIX_ONE`; `seizeRSR` totalRSR = 0 → no-op | Empty queue handled; `cancelUnstake_last` on empty queue is a no-op | Era-reset (via `beginEra` / `beginDraftEra`) is the closest analog: wipes the affected pool and bumps the era counter. | Phase A-D expansion: era model, seizeRSR, cancelUnstake_last all modeled. Per-account state and the ERC20 surface remain out of scope. |
| **TradeLib** | `a = 0 ∨ b = 0` → 0; `c = 0 ∨ FIX_MAX-input` → saturate | n/a | n/a | Faithful match against `safeMulDiv` production semantics. |
| **DutchTrade** | `progression < 20%` etc. dispatched cleanly; out-of-range t handled by clamping (instead of revert) | n/a | Phase 4 is the terminal price clip | **Divergence**: production reverts when called outside `[startTime, endTime]`; sim returns nearest endpoint as a total function. Header documents this. |
| **GnosisTrade** | `sellAmount = 0` → `worstCasePrice = 0`; `initBal <= sellBalAfter` → no-violation early return | n/a | `canSettle` checks `status_open` flag | Faithful for the math; auth/lifecycle gating not modeled. |
| **Collateral** | `wd <= now` → no-op (terminal DISABLED); soft-default decision handles `low = 0` | n/a | DISABLED is correctly terminal (production line 175) | Faithful match. The state machine's terminality is preserved. |
| **IssuancePremium** | `enable = false` → `FIX_ONE`; `lastSaveIsNow = false` → `FIX_ONE`; `pegPrice = 0` → `FIX_ONE`; `targetPerRef <= pegPrice` → `FIX_ONE`; `safeDiv_ceil` saturates on `b = 0` | n/a | n/a | Faithful match. |
| **Fixed** | `_safeWrap` returns `None` on overflow (matches revert); `mul` and friends have `_opt` variants | n/a | n/a | Models the production revert as `option`-returning. |

### Real findings worth chasing

- **Distributor**: `totalShares = 0` returns `(nil, amount)` in the sim but reverts in production. The proofs about `distribute` are therefore vacuous on the corner case where governance has zeroed all shares for one of (rsr, rToken). The header acknowledges this; downgrade the coverage claim accordingly or model the revert explicitly.
- **DutchTrade**: out-of-range `t` returns the nearest endpoint instead of reverting. Means lemmas about `bidPrice` are stronger than the production function — they cover inputs production rejects. Acceptable as long as integration sites carry the in-range hypothesis, but it should be stated as a `Valid` predicate, not implicit.

## 2. Live-state vs deployment-time arguments

The question: when production stores a parameter (so governance can mutate
it mid-flight), does the simulation either store it (allowing mutation) or
take it as a function arg (making it a frozen snapshot)? Mismatches mean
proofs apply to a frozen-snapshot model that the production contract
never sees.

### Findings

| Simulation | Storage params | Frozen-arg params | Mutation operations modeled? |
|---|---|---|---|
| **Throttle** | `params { amtRate, pctRate }` ✓ matches production | `now` (block.timestamp) ✓, `supply` ✓ | No — governance setters not modeled, but `params` is in storage so the model would accept a mutated struct between calls. |
| **Furnace** | `ratio` ✓ matches production | `now`, `currentBalance` ✓ | `setRatio` modeled. **Divergence**: production calls `melt()` *before* updating `ratio` (line 85); sim's `setRatio` does not. Composing `setRatio` after rewards have accrued at the old ratio gives different results. |
| **Distributor** | `Storage = list (addr, share)` ✓ | `amount`, `isRSR` | No — `setDistribution` not modeled. Governance mutations to the share table happen entirely outside the proof scope. |
| **BasketHandler** | `Storage = list (asset, refAmt)` ✓ | `baskets`, `mode` | No — `setPrimeBasket`, `refreshBasket`, etc. not modeled. The basket is treated as static. |
| **BackingManager** | None (pure math kernel) | `basketsHeldBottom`, `basketsNeeded`, `backingBuffer`, `quantity`, `bal`, `decimals`, `rTokenTotal`, `rsrTotal` | No state. **All governance params are frozen-snapshot here**, including `backingBuffer` which production stores. A reviewer should confirm the math is invariant under arbitrary `backingBuffer` (true within `Valid.bufferInputs`) and that callers pass the live storage value, not a stale copy. |
| **Rebalance** | None (algebraic) | All inputs are `RangeInputs` arg fields | n/a — abstract over any `RangeInputs`, so live-vs-frozen is at the caller. |
| **StRSR** | Documented in StRSR section. Era / draftEra / draftRSR / queue all in storage post-Phase-A. | `now`, `delay`, `rewardsPool`, `amount`, `rsrAmount` (seizeRSR) | **Remaining divergences**: `unstakingDelay` is a function arg in the sim but a storage field in production. `rewardRatio` is in `Storage.ratio` but no `setRewardRatio` is modeled. The simulation's tighter `draftRate = FIX_ONE` invariant (vs production's [FIX_ONE, MAX_DRAFT_RATE] band) means some production-reachable states are unreachable in the simulation. |
| **TradeLib** | None | All inputs are args | Pure kernel; live-vs-frozen is at the caller. |
| **DutchTrade** | `Auction { startTime, endTime, bestPrice, worstPrice, sellAmount, buyDecimals }` ✓ matches | `t` (now) | No — auction lifecycle (init, bid, settle) not modeled at the state-transition level. |
| **GnosisTrade** | None (pure math kernel) | All inputs are args | Same shape as BackingManager — pure kernel. |
| **Collateral** | `State { whenDefault, exposedReferencePrice, delayUntilDefault, revenueShowing, pegBottom, pegTop }` | `underlying`, `pegPrice`, `low`, `now` | `delayUntilDefault`, `revenueShowing`, `pegBottom`, `pegTop` are in storage and marked "immutable" in the sim's comments. **Production has setters** for `revenueHiding` (which `revenueShowing = FIX_ONE - revenueHiding` would derive from) and `delayUntilDefault` is `immutable` in the constructor — sim is faithful for `delayUntilDefault`, less so for `revenueHiding`. Worth checking. |
| **IssuancePremium** | None | `enable`, `lastSaveIsNow`, `pegPrice`, `targetPerRef` | Pure function. `enable` is `enableIssuancePremium` — a governance flag in production. Sim takes it as arg, which is fine for a single-call computation but means proofs don't cover the toggling sequence. |
| **Fixed** | None | All inputs are args | Pure kernel — no live state. |

### Real findings worth chasing

- **Furnace `setRatio` does not call `melt()` first.** Production: `setRatio` → `melt()` → write `ratio`. Sim: write `ratio` directly. A composition lemma `setRatio_then_melt` proved in the sim does not match production — production's `melt` runs at the *old* ratio, then the new ratio takes effect for the next period. Verify whether any composition proof depends on this ordering. If it does, the proof is wrong.
- **StRSR `unstakingDelay` is an arg, not storage.** Means the validity preservation of unstake-then-cancel scenarios is proved against any `delay`, not the governance-mutable storage value. This is honest but incomplete — production's `setUnstakingDelay` could change `delay` between operations and the sim wouldn't notice.

## 3. Storage layout vs `_uint256_bounds.v`

Production storage uses packed integer types (`uint48`, `uint176`, `uint192`)
chosen for slot-packing efficiency. The simulations carry `Valid.t`
predicates that bound storage values, but those predicates are sometimes
loose — they say `<= UINT256_MAX` where the production type would say
`<= UINT48_MAX` or `<= FIX_MAX`. The `_uint256_bounds.v` files inherit
the looser bound.

### Findings

| Field (production type) | Production limit | Simulation `Valid.t` bound | `_uint256_bounds.v` bound |
|---|---|---|---|
| `Throttle.lastTimestamp` (uint48) | `2^48 − 1` | `<= UINT48_MAX` ✓ | (no `_uint256_bounds.v` for Throttle) |
| `Furnace.lastPayout` (uint48) | `2^48 − 1` | **`<= UINT256_MAX`** (loose) | `<= UINT256_MAX` (inherits the loose bound; the field name `lastPayout_uint48` is misleading) |
| `Furnace.ratio` (uint192) | `<= MAX_RATIO = 1e14` (gov-bounded) | `<= MAX_RATIO` ✓ | `<= UINT256_MAX` |
| `Furnace.lastPayoutBal` (uint256) | `<= UINT256_MAX` | `<= UINT256_MAX` ✓ | `<= UINT256_MAX` ✓ |
| `StRSR.lastPayout` (uint48) | `2^48 − 1` | (modeled as `U256.t`; no uint48 bound) | `<= UINT256_MAX` (loose) |
| `StRSR.ratio` (uint192, gov ≤ 1e14) | `<= MAX_REWARD_RATIO = 1e14` | `0 <= ratio <= FIX_ONE_Z` (loose; production caps at MAX_REWARD_RATIO ≪ FIX_ONE) | — |
| `Collateral.whenDefault` (uint48) | `2^48 − 1` | `<= UINT48_MAX` ✓ | (sim Valid.t carries the tight bound) |
| `Collateral.exposedReferencePrice` (uint192) | `<= FIX_MAX` | `<= FIX_MAX` ✓ | ✓ |
| `Collateral.delayUntilDefault` (uint48) | `<= 1209600` (2 weeks) | `0 <= delayUntilDefault <= 1209600` ✓ | ✓ |
| `BackingManager` storage | (no storage in sim — pure kernel) | n/a | `_uint256_bounds.v` reasons about call-boundary inputs, not storage | 
| **Other domains** | — | Mostly tight where the bound is well-defined; loose where production storage is uint48 but the sim treats the field as `U256.t` | — |

### Real findings worth chasing

- **Furnace `lastPayout` claim mismatch.** The simulation's `Valid.t` field is named `lastPayout_uint48` but bounds the value at `UINT256_MAX`. Either rename the field to `lastPayout_u256` (truth-in-naming) or strengthen the bound to `UINT48_MAX` (truth-in-content). Same probably applies to similar-shape fields in StRSR, BasketHandler, GnosisTrade, DutchTrade where uint48 timestamps are stored as `U256.t` without a tight bound.
- **StRSR `ratio` looseness.** The simulation bounds `ratio` at `FIX_ONE` but production governance enforces `ratio <= MAX_REWARD_RATIO = 1e14`, four orders of magnitude tighter. The compound-payout proofs may be sound under any ratio in `[0, FIX_ONE]`, but the saturation behavior (era reset, etc.) is calibrated to the tighter bound, which the sim doesn't see.
- **Pattern**: storage-type bounds should be encoded in the simulation's `Valid.t` predicate, not deferred to the `_uint256_bounds.v` file. The bounds files were originally intended to derive ceilings on *intermediate arithmetic* (where the sim works in `Z`), not to restate what the storage type already enforces.

## 4. assert vs require encoding

The question: when production reverts on bad input, how does the
simulation express that?

### Patterns observed

| Encoding | Used in | Notes |
|---|---|---|
| **`Result.Success / Result.Revert`** (two-constructor inductive) | Throttle, BackingManager | Mirrors the upstream rocq-of-solidity ERC20 simulation. Lets `run_<fn>` equivalence lemmas pin Yul revert offsets. |
| **`option`** (Some/None) | Furnace `setRatio`, Fixed `safeWrap` | Plain `option Z` when there's no extra information at the boundary. |
| **Total function with implicit precondition** | StRSR `unstake` (precondition `amount <= totalStRSR` not enforced), TradeLib (preconditions on `slippage <= FIX_ONE`, `buyHigh > 0`), DutchTrade (out-of-range `t` returns endpoint), Distributor (`tokensPerShare = 0` returns dust) | Preconditions live in `Valid` records, threaded via hypothesis. The proofs assume the call site has discharged them. |
| **Saturation** (clamp at FIX_MAX rather than revert) | TradeLib `safeMulDiv`, IssuancePremium `safeDiv_ceil` | Faithful — production's `_safeWrap` reverts, but several FixLib ops have explicit saturation paths instead. The sim distinguishes the two. |

### Findings

- **No simulation expresses the *full* set of production reverts.** Each sim picks a subset to model. This is a deliberate scoping choice but the consequence is that "validity preservation" is established against the modeled subset — an unmodeled production revert path corresponds to a region where the sim's behavior is unconstrained, not to a proven safety property.
- **Three different encodings for the same pattern** (`Result.t`, `option`, total-function-with-Valid-hypothesis). The choice is mostly historical — Throttle and BackingManager were written when Yul-equivalence was still an active goal and needed offset-bearing reverts. Furnace's `option` is fine for a one-shot governance call. Total functions with `Valid`-hypothesis are honest as long as the hypothesis is discharged at integration sites. None of these encodings is wrong; the inconsistency just costs cognitive overhead when reading across the tree.
- **No simulation enumerates the production revert messages.** A reviewer cross-referencing production's `require(..., "supply change throttled")` against the sim's `revert_throttled` cannot tell that the sim is matching the right revert without reading the proof's accompanying comments.

### Recommendations

- Adopt `Result.t` consistently if Yul-equivalence is ever revived (the parked workstream). Until then, the mix is acceptable.
- Document in each simulation's header which production reverts are modeled and which are deferred to `Valid`-hypothesis.

---

# Part 2 — Per-simulation summaries

## StRSR

The simulation now captures **the full aggregate state-transition
math**: revenue accrual, exchange-rate evolution, the FIFO
withdrawal-queue lifecycle (`unstake` -> `withdraw`), the LIFO cancel
operation (`cancelUnstake_last`), and the production-faithful
seizure machinery (`seizeRSR` with proportional split and era resets
via `beginEra` / `beginDraftEra`).

What remains omitted are **per-account state** (the production
`stakes[era][account]` and `draftQueues[draftEra][account]` mappings
collapse to a single global queue in the simulation) and **the ERC20
+ governance + integration surface** (transfer/approve/permit, the
withdrawal-leak mechanism, governance setters, and the
`basketHandler.isReady()` / `fullyCollateralized()` gates).

### State (post-Phase-A expansion)

| Production state | Purpose | Simulation analog |
|---|---|---|
| `era`, `draftEra` | Seizure-driven balance reset markers | **`era`, `draftEra` ✓** (Phase A). Bumped by `beginEra` / `beginDraftEra`. |
| `stakes[era][account]` | Per-account stake balance (the actual ERC20 balances) | None. Simulation aggregates to `totalStRSR`. |
| `draftQueues[draftEra][account]` | Per-account draft queue, indexed by era | Single global `queue : list Withdrawal.t`. |
| `firstRemainingDraft[era][account]` | Index past which drafts have been claimed | Implicit: `withdraw` pops the front of the queue, `cancelUnstake_last` pops the back. |
| `CumulativeDraft.drafts` (uint176, *running total*) | Lets `withdraw` compute claimed amount as `queue[end-1].drafts - queue[first-1].drafts` in O(1) regardless of cancellations | `Withdrawal.rsrAmount` (the individual amount). Different data structure with different complexity properties. |
| `stakeRate`, `draftRate` (D18, separately tracked) | Independent exchange rates for stakes vs drafts; both can saturate at MAX_STAKE_RATE / MAX_DRAFT_RATE | Single derived `exchange_rate` from totals. **The simulation maintains the tighter `draftRate = FIX_ONE` invariant** (vs production's [FIX_ONE, MAX_DRAFT_RATE] band): seizures that would push the implied rate above FIX_ONE trigger an early `beginDraftEra`. The reachable-state set is therefore a strict subset of production's, but every reachable state satisfies the [Valid.t] invariants. |
| `stakeRSR`, `draftRSR` (separate RSR pools) | Drafts are paid from a distinct pool that doesn't earn rewards; seizure hits both proportionally | **`totalRSRStaked`, `draftRSR` ✓** (Phase A). `unstake` moves rsrAmount from `totalRSRStaked` into `draftRSR`. |
| `totalDrafts`, `totalStakes` separately | Sum of all drafts vs sum of all stakes | `totalStRSR` (stakes) and `sum_rsr_amounts queue` (drafts). |
| `_allowances`, `_nonces`, `_delegationNonces`, ERC20 name/symbol | ERC20 surface | None. The simulation isn't an ERC20. |
| `leaked`, `lastWithdrawRefresh`, `withdrawalLeak` | 3.0.0 withdrawal-leak mechanism: refresh required if cumulative leak exceeds `MAX_WITHDRAWAL_LEAK = 30%` | None. |
| `unstakingDelay`, `rewardRatio`, `withdrawalLeak` (governance setters) | Mutable governance parameters | `delay` is a function argument; `ratio` is in storage but with no setter. |
| `assetRegistry`, `backingManager`, `basketHandler`, `rsr` | Component pointers — `basketHandler.isReady()` and `fullyCollateralized()` gate `withdraw` | None. |

### Operations (post-Phase-C expansion)

| Production function | Effect | Modeled? |
|---|---|---|
| `withdraw(account, endId)` | Pops drafts from the queue once `availableAt` has passed and transfers RSR to the account | **`withdraw` ✓** (one-step pop; batch withdrawal is iterated composition). |
| `cancelUnstake(endId)` | Rolls back queued drafts, returning them to active stake | **`cancelUnstake_last` ✓** (Phase B). One-step LIFO pop with re-stake at the current rate. |
| `seizeRSR(rsrAmount)` | Backing-manager-triggered seizure of RSR from both stake and draft pools, possibly triggering era reset if the pool is fully consumed | **`seizeRSR` ✓** (Phase C). Production-faithful proportional split (CEIL on stake side) with era-reset triggers. The simulation's reset trigger on the draft side is tighter than production's (FIX_ONE vs MAX_DRAFT_RATE boundary). |
| `resetStakes()` | Governance-triggered era reset when stakeRate / draftRate exits the safe band | Not modeled as a standalone operation, but the underlying primitives `beginEra` and `beginDraftEra` are available; a caller can compose them. |
| `transfer`, `approve`, `transferFrom`, `permit`, `delegate`, `delegateBySig` | ERC20 + ERC20Permit + delegation surface | **No.** |
| `beginEra`, `beginDraftEra` | Internal era-reset primitives | **`beginEra`, `beginDraftEra` ✓** (Phase A). |
| `init` | Initialization (sets payoutLastPaid, rsrRewardsAtLastPayout, governance params) | **No.** Simulation operates on an arbitrary `Storage.t`. |
| `setUnstakingDelay`, `setRewardRatio`, `setWithdrawalLeak` | Governance setters | **No.** |
| `payoutRewards()` (public) vs `_payoutRewards()` (internal) | The public form has no arguments and reads `rsrRewards()` from RSR balance; simulation takes `rewardsPool` as an explicit argument | **Partial.** The integral form is correct; the snapshot-vs-balance distinction is acknowledged in the simulation header. |

### Phase-C invariants

The expansion adds these load-bearing theorems (all in `proofs/`):
- `seizeRSR_preserves_validity` (StRSR_validity.v)
- `seizeRSR_phase1_conserves_total_RSR`, `seizeRSR_proportional` (StRSR.v)
- `cancelUnstake_last_preserves_validity` (StRSR_validity.v)
- `unstake_then_cancelUnstake_lossy_recovery` (StRSR_chain.v)
- `payoutRewards_then_seizeRSR_preserves_validity` (StRSR_chain.v)
- `unstake_then_seizeRSR_then_withdraw_preserves_validity` (StRSR_chain.v)
- `beginEra_preserves_validity`, `beginDraftEra_preserves_validity` (StRSR_validity.v)
- `unstake_preserves_pools_sum` (Integration_unstake_lifecycle.v): `totalRSRStaked + draftRSR = const`.

CAS witness coverage:
- `cas/strsr/exchange_rate_evolution.gp` (existing)
- `cas/strsr/withdrawal_queue.gp` (existing)
- `cas/strsr/cancel_unstake.gp` (Phase B)
- `cas/strsr/seize_rsr.gp` (Phase C)

## Throttle

**Faithful match.** All three production functions modeled (`hourlyLimit`,
`currentlyAvailable`, `useAvailable`). Storage shape and edge-case
behavior match production exactly. `Valid.t` carries tight bounds (uint48
on lastTimestamp, uint192 on pctRate). Two-constructor `Result.t` for
revert-bearing returns. Governance setters not modeled — params are in
storage so a mutated struct can be passed between calls, but no
`setParams` operation exists in the sim.

**Gaps**: governance setter operations, the integration with `RTokenP1`
(which does the actual storage write).

## Fixed

**The math kernel.** Models `RoundingMode`, `_divrnd`, `mul`, `div`,
`mulu`, `plus`, `minus`, comparisons, `powu`, `shiftl`. Both unchecked
(Z-only) and `_opt` (`safeWrap`-checked) variants. `_safeWrap` returns
`None` on overflow, matching production's `_safeWrap` revert.

**Out of scope (per simulation header)**: `sqrt`, `divFix`, `divuu`, the
full chained-operation surface (e.g. `mulu_toUint` is partial, `mulDiv256`
not modeled). Most CAS xchecks pin specific values, so faithfulness is
sampled even when not formally proved.

## Furnace

**Mostly faithful.** `melt`, `setRatio`, MAX_RATIO. The integral form
`payoutRatio = 1 - (1-ratio)^N` matches the documented
`[furnace-payout-formula]` block in production. CAS xchecks pin specific
values.

**Gaps**:
- `setRatio` does not call `melt` first (production line 85 does).
  Composition `setRatio_then_*` may not match production semantics. See
  cross-cutting finding 2.
- `Valid.t` bound on `lastPayout` is loose (claims uint48 by name, holds
  uint256). See cross-cutting finding 3.
- `init` not modeled; `__gap` storage gap not represented.
- The actual `rToken.melt(amount)` call at the end of production's `melt`
  is not modeled (sim just decrements `lastPayoutBal`).

## Distributor

**Math-kernel scoped.** Models `totals`, `tokensPerShare`,
`distributeAmounts` over a flat list of `(addr, RevenueShare)` pairs.

**Gaps**:
- `distribute`, `setDistribution`, `setDistributions`, `init` not modeled
  (acknowledged in header).
- DAOFeeRegistry leg explicitly omitted (acknowledged). The CAS finding
  about governance-conditional auction fees (`CAS_additional_findings.v`)
  covers a related accounting gap; the simulation doesn't reach it.
- Reward accounting calls (`stRSR.payoutRewards()`, `furnace.melt()` at
  production lines 195-198) not modeled.
- Auth checks (`require(caller == rsrTrader || rTokenTrader)`,
  `require(erc20 == rsr || erc20 == rToken)`) not modeled.
- `EnumerableSet` representation replaced with a plain list. Equivalent
  for the math but means proofs don't see the order-stability guarantee
  EnumerableSet provides.

## BackingManager

**Two pure functions only.** `computeNewBasketsAndNeeded`,
`computeSurplusSplit`. The full `BackingManager` contract has many other
state-mutating functions: `manageTokens`, `forwardRevenue` (full),
`compromiseBasketsNeeded`, `setBackingBuffer`, etc. **None modeled.**

The file/module name "BackingManager" oversells what's modeled —
`BackingManagerForwardRevenueMath` would be more accurate.

**Gaps**: the entire trade-trigger lifecycle, the basket-needs lifecycle,
the recollateralization flow.

## Rebalance / RecollateralizationLib

**Algebraic skeleton.** Models the noise-bound primitives
(`dustNoiseBU`, `noise_loose`, `noise_tight`) and an abstract
`basketRange` over `RangeInputs`.

The header explicitly scopes out the per-asset oracle loop, asset
registry indirection, and FIX_MAX-overflow reverts. Acceptable framing
but means lemmas about the noise envelope are statements about the
abstract function `basketRange`, not the production implementation.

**Gaps**: production `basketRange` is far more complex; the sim is
faithful only to the algebraic relation between aggregate inputs and
the (low, high) output, not to the oracle-driven derivation.

## TradeLib

**Buy-amount kernel.** Models `safeMulDiv`, `buyAmount`,
`buyAmountPre` (pre-#1283 mitigation), `coverDeficitSellAmount`,
`minTradeSize`, `isEnoughToSell_whole`. Saturation behavior matches
production for `safeMulDiv`.

**Gaps** (acknowledged in header):
- `prepareTradeSell`/`prepareTradeToCoverDeficit` full functions —
  only the kernel pieces.
- Asset-registry indirection (`sell.maxTradeVolume`, etc.).
- The `shiftl_toUint(amt, decimals) > 1` quanta-rounding side of
  `isEnoughToSell` (decimals-dependent).

## BasketHandler

**Quote math only.** Models `quote_one`, `quote`, `quoteQuantities`,
`redeem_one`. Storage = list of `(asset, refAmt)`.

**Gaps**: the entire basket-management lifecycle (`setPrimeBasket`,
`refreshBasket`, governance toggles, `nonce` for basket changes), the
issuance-premium application (which is modeled separately in
`IssuancePremium.v`), oracle integration, the `revenueHiding` decay,
multi-collateral `quote` complications.

The simulation header is explicit: "the asset-registry / oracle /
decimals layer is intentionally OUT of scope here."

## DutchTrade

**Price-decay curve.** Models all four phases of `_price`,
`bidAmount_at_price`, `bidAmount`, `bidAmount_floor_variant` (for
rounding-direction comparisons). Storage = `Auction { startTime, endTime,
bestPrice, worstPrice, sellAmount, buyDecimals }`.

**Gaps**:
- Out-of-range `t` returns the nearest endpoint instead of reverting
  (header acknowledges; treats the function as total).
- The auction lifecycle (init, bid, settle, claim) is not modeled at
  the state-transition level. Only the price/amount math.
- `bid()`'s side effects (token transfer, status update) not modeled.

## GnosisTrade

**Settlement-floor math.** Models `minBuyAmount`, `worstCasePrice`,
`settle`, `settlement_floor`, `canSettle`, `cancellationEndTime`.

**Gaps**:
- Init / lifecycle not modeled at the state level; `settle` is a pure
  function over inputs.
- The actual interaction with Gnosis EasyAuction (auction creation,
  bid registration, defensive +1 padding origins) not modeled.
- `FEE_DENOMINATOR` constant carried but the auction-fee gap finding
  (`CAS_additional_findings.v`) covers the case where `feeNumerator > 0`
  diverges from `worstCasePrice` — the sim's `worstCasePrice` doesn't
  account for the fee numerator. (This is the formalized bug; the
  simulation captures the post-fee-aware computation.)

## Collateral

**State machine.** Models `Status` (SOUND/IFFY/DISABLED), `statusOf`,
`markStatus`, `softDefaultStatus`, `updateExposed`, `refresh`. Storage
captures `whenDefault`, `exposedReferencePrice`, `delayUntilDefault`,
`revenueShowing`, `pegBottom`, `pegTop`.

**Faithful match** for the documented state transitions. DISABLED is
correctly terminal.

**Gaps**:
- `revenueShowing` is treated as immutable in the simulation but
  `revenueHiding` may be governance-mutable in some collateral
  variants — worth checking per-plugin.
- The plugin layer (FiatCollateral, AppreciatingFiatCollateral,
  CTokenFiatCollateral, etc.) has subclass-specific overrides not
  modeled — the simulation captures the base abstraction only.
- Oracle layer omitted; `pegPrice` and `low` are passed as inputs.

## IssuancePremium

**Pure function.** Models the production `issuancePremium` formula and
the underlying `safeDiv_ceil`. All edge cases handled.

**Faithful match.** This is the smallest and most thoroughly modeled
simulation in the tree.

---

# Recommended next steps — status

The recommendations from the original audit have been worked through.
Status as of the audit-driven follow-up commits:

1. **Truth-in-naming for storage bounds. ✓ DONE.**
   - Furnace `lastPayout_uint48` → `lastPayout_u256` (the bound is
     UINT256_MAX, not UINT48_MAX; rename matches content).
   - StRSR `ratio_in_range` tightened from `<= FIX_ONE` to
     `<= MAX_REWARD_RATIO = 1e14` (production governance cap).
   - All other type-named fields verified to match their actual bounds
     (Throttle `lastTs_uint48`, Collateral `wd_uint48` /
     `delay_uint48`, etc. are all honest).
   - Dependent proofs in EndToEnd and StRSR_uint256_bounds updated to
     use the new tighter MAX_REWARD_RATIO bound.

2. **Document each simulation's revert coverage. ✓ DONE.**
   Each of the 13 simulations now has a "Revert coverage" paragraph
   in its file header listing reverts modeled, deferred to
   `Valid`-hypothesis, and not modeled at all.

3. **Furnace `setRatio` ordering. ✓ DONE.**
   - No existing proof relies on the production melt-before-set
     ordering; the divergence is dormant in the current proof tree.
   - Added `setRatio_with_melt` as a production-faithful operation
     that calls `melt` first (with the OLD ratio, capturing accrual)
     before writing the new ratio. Available for future proofs that
     care about ordering.
   - Existing `setRatio` retained for proofs and witnesses where the
     ordering is irrelevant; the docstring now flags the divergence
     prominently.

4. **Add `withdraw` to StRSR. ✓ DONE.**
   - New `withdraw` operation pops the front of the FIFO queue if
     `availableAt <= now`, returning the rsrAmount paid out. Storage
     scalars unchanged (consistent with the simulation's collapsed
     accounting where the queue itself represents draft RSR).
   - `withdraw_preserves_validity` lemma added to
     `proofs/StRSR_validity.v`. Proof relies on a new helper
     `queue_fifo_tail` (popping the head preserves FIFO).
   - Production divergences explicitly documented in the operation's
     comment: per-account state, `RTokenNotReady` gate, withdrawal-
     leak refresh — all deferred.

5. **Audit `_uint256_bounds.v` files for tightness. ✓ PARTIAL.**
   Same finding as item 1. The current pass tightened the StRSR
   `ratio` bound (which propagates through `StRSR_uint256_bounds.v`).
   A full sweep of all `_uint256_bounds.v` files for further
   tightening opportunities is a follow-up; the loose bounds that
   remain (e.g. uint48 timestamps stored as `U256.t` without uint48
   bound) are structural and need either a tighter `Valid.t` or a
   model of production's uint48 truncation arithmetic — both larger
   changes than fit this pass.

6. **Per-domain operation surface expansion. PARTIAL: StRSR DONE; others DEFERRED.**

   - StRSR `seizeRSR` and `cancelUnstake`. **DONE.** Phases A-D
     landed:
     - Phase A: era / draftEra / draftRSR storage scaffolding,
       `beginEra` / `beginDraftEra` primitives, strengthened
       `Valid.t` (draftRSR_nonneg, queue_drafts_le_draftRSR,
       queue_entries_nonneg). Existing operations (stake, unstake,
       withdraw, payoutRewards) updated; unstake now correctly
       moves rsrAmount into draftRSR.
     - Phase B: `cancelUnstake_last` (LIFO pop-the-back with
       re-stake at the current rate); validity preservation;
       round-trip lemma; CAS witness `cas/strsr/cancel_unstake.gp`.
     - Phase C: `seizeRSR` (proportional split with era-reset
       triggers, production-faithful CEIL on stake side, residual
       to draft); validity preservation across all four reset
       branches; conservation and proportionality theorems; CAS
       witness `cas/strsr/seize_rsr.gp`.
     - Phase D: composition lemmas
       (`payoutRewards_then_seizeRSR_preserves_validity`,
       `unstake_then_seizeRSR_then_withdraw_preserves_validity`),
       xcheck reflexivity for the new witness values, audit
       notations in `Audit.v` Section 8.

     Documented divergence: the simulation's `Valid.t` carries the
     tighter invariant `sum_rsr_amounts queue <= draftRSR`
     (effective `draftRate = FIX_ONE`) where production allows up
     to `MAX_DRAFT_RATE`. Seizures that would push the implied rate
     above FIX_ONE trigger an early `beginDraftEra` in the sim;
     production allows the rate to drift up to its cap before
     era-resetting. The reachable-state set in the simulation is a
     strict subset of production's; safety properties proved on
     the simulation transfer to production unconditionally.

   - BackingManager's full `forwardRevenue` and `manageTokens`. The
     simulation today is `BackingManagerForwardRevenueMath` — only
     the math kernel from lines 218-262. The full operation surface
     covers asset-registry interaction, trade triggering, and
     basket-needs lifecycle; each of those needs its own simulation
     module before the full `forwardRevenue` can be assembled.

   - BasketHandler's `setPrimeBasket` / `refreshBasket`. Same shape
     — the simulation today is `BasketHandlerQuoteMath`, covering
     only `quote` semantics. The lifecycle operations require
     governance state (basket nonce, prime/reference distinction),
     `swapRegistered` semantics, and the asset-registry interaction.

   The two remaining surfaces (BackingManager, BasketHandler) are
   tracked as future work.

7. **DAO-fee leg in Distributor. ✓ DONE.**
   - Added `distributeAmounts_with_dao_fee` alongside the existing
     `distributeAmounts`. Models the production `totals()` inflation
     (DAO fee only inflates rsrTotal) and the per-leg fee transfer
     (`tps * (totalShares' - paidOutShares)` to the DAO recipient).
   - New `DistResult.t` record bundles per-destination amounts, the
     DAO-fee amount, and the residual dust. The conservation
     invariant `sum(amts) + daoFee + dust = amount` is now expressible
     across the DAO-fee path.
   - Helper `feeShareInflation` mirrors production line 219-225 with
     defensive zero-returns when the configuration is invalid (matches
     production's revert via Solidity checked subtraction).
   - `paidOutShares` helper sums the inner-loop share count for the
     leg being distributed.
