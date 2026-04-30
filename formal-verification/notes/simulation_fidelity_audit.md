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

## Throttle (gold-standard audit)

The simulation captures **the full math kernel and storage shape of
the throttle library — `hourlyLimit`, `currentlyAvailable`,
`useAvailable` — including the revert-bearing `useAvailable` path
when usage exceeds available**. It omits **the integration surface
with `RTokenP1` (which holds the actual storage and provides
governance-mutated params via constructor / `setIssuanceThrottleParams`
/ `setRedemptionThrottleParams`)**. The proofs against this model are
correct for the model; because the library is purely a state-mutator
on a struct passed by reference, transferability hinges on the caller
(`RTokenP1`) treating the throttle struct atomically — the simulation
cannot witness any caller-side races between `hourlyLimit` reads and
`useAvailable` writes.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `Throttle.params.amtRate` (uint256) | Hourly token-amount cap | **`Throttle.params.amtRate` ✓** (carried as `U256.t`). |
| `Throttle.params.pctRate` (uint192) | Hourly fraction-of-supply cap | **`Throttle.params.pctRate` ✓** with explicit uint192 bound in `Valid.params`. |
| `Throttle.lastTimestamp` (uint48) | Cache: timestamp of last successful update | **`Throttle.lastTimestamp` ✓** with `Valid.throttle.lastTs_uint48`. |
| `Throttle.lastAvailable` (uint256) | Cache: amount available at `lastTimestamp` | **`Throttle.lastAvailable` ✓**. |
| Caller's `block.timestamp` | EVM-supplied "now" | Passed in as explicit `now : U256.t` argument. Not stored. |
| Caller's `supply` | Total RToken supply at the call | Passed in as explicit `supply : U256.t` argument. Not stored. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `useAvailable(throttle, supply, amount)` | Storage-mutating consume / restore with revert when over the cap | **`useAvailable` ✓** — total function returning `Result.t Throttle.t`. |
| `currentlyAvailable(throttle, limit)` | View: clipped lazily-accrued available | **`currentlyAvailable` ✓** — pure on `(t, limit, now)`. |
| `hourlyLimit(throttle, supply)` | View: `max(amtRate, supply * pctRate / FIX_ONE)` | **`hourlyLimit` ✓** — pure on `(t, supply)`. |
| Caller-side `setIssuanceThrottleParams(Params)` / `setRedemptionThrottleParams(Params)` (lives in `RTokenP1`, not in the library) | Governance write of `params`; production calls `useAvailable(0)` first to settle accrual | **No.** The library has no setter — `params` is treated as storage that may be updated externally, but no operation models the settle-then-write composition. |

### What the simulation *does* faithfully model

- The full `useAvailable` control flow including the early-exit when both rate caps are zero (production line 43; sim line 94).
- The timestamp-update predicate (`available != lastAvailable || available == limit`) — the LHS of the bookkeeping decision at production line 52.
- The signed-`amount` semantics: `amount > 0` consume (revert iff over cap), `amount < 0` restore (uncapped, lazy clip on next call), `amount = 0` no-op — header documents the convention.
- The clip-at-limit invariant inside `currentlyAvailable` (the `Z.min limit raw` at sim line 87 mirrors the production `if (available > limit) available = limit` at line 76).
- Two-constructor `Result.t` so a future Yul-equivalence proof can pin revert offsets at the boundary.
- Tight `Valid.t` bounds on `lastTimestamp` (uint48), `pctRate` (uint192).

### Implications for proof transferability

1. Lemmas about `useAvailable` (e.g. `useAvailable_preserves_validity`) carry to the production library directly, modulo two preservation-of-context assumptions: (i) the caller always serializes `hourlyLimit` and `useAvailable` within the same transaction (true in `RTokenP1::issue` / `redeem`) and (ii) governance does not race a `setParams` between the `hourlyLimit` read and the `useAvailable` write within a single transaction.
2. Because the simulation has no `setParams`, the proof tree cannot witness a "settle accrued usage at the old rate before applying the new rate" composition theorem analogous to Furnace's `setRatio_with_melt`. If the production caller violates that pattern, the simulation cannot detect it.
3. The "untestable" branch at production line 43 (both rates zero) is an *explicit* branch in the sim, not a no-op-by-vacuity — proofs that case-split on it remain valid even when governance hard-codes positive rates.
4. Coverage claims on Throttle should read "library-internal math + struct invariants", not "throttle subsystem end-to-end".

## Fixed (gold-standard audit)

The simulation captures **the rounding-aware integer-division kernel
(`divrnd`), the core arithmetic surface (`mul`, `div`, `mulu`, `plus`,
`minus`, comparisons), `powu` exponentiation-by-squaring, and base-10
`shiftl`** — both as unchecked Z-arithmetic and as `_opt`-suffixed
variants returning `option Z` on uint192 overflow. It omits **the
"safe" overflow-guarding family (`safeMul`, `safeDiv`, `safeMulDiv`),
the precision-preserving 256-bit multiplication (`mulDiv256`,
`fullMul`), the convenience surface (`toUint`, `toFix`, `near`,
`fixMin`/`fixMax`), and the rare-use kernels (`sqrt`, `sqrt256`,
`divFix`, `divuu`)**. Proofs against this kernel are correct for the
modeled subset; lemmas about products that flow through `safeMulDiv`
or `mulDiv256` in production must be re-derived from the unchecked
`mul`/`div` (over Z) plus a separate boundedness-preservation
argument — the simulation does not give them for free.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| (none — Fixed.sol is a stateless library) | n/a | n/a |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `_safeWrap(uint256) -> uint192` (file-level helper, line 73) | Reverts if `x > FIX_MAX`, else identity | **Modeled as `safeWrap : Z -> option Z`** returning `None` on overflow. |
| `_divrnd(numerator, divisor, rounding) -> uint256` (line 155) | Rounding-mode-aware integer div | **`divrnd` ✓**. |
| `toFix(uint256) -> uint192` (line 81) | Multiply by `FIX_SCALE`, revert on overflow | **No.** |
| `shiftl_toFix(uint256, int8) -> uint192` (line 89; FLOOR-default and rounding overloads, lines 89/95) | Decimal-shift ints to fix | **No** — `shiftl_toUint` is also not modeled (the inverse direction at line 380/387 is not modeled either; only `shiftl` for fix-to-fix is). |
| `divFix(uint256, uint192) -> uint192` (line 117) | Divide a uint by a fix, return fix | **No** (header explicitly defers this). |
| `divuu(uint256, uint256) -> uint192` (line 130) | uint/uint to fix; used inside DutchTrade `_price`'s `progression` | **No** (header defers; DutchTrade simulation reimplements the formula directly). |
| `fixMin`, `fixMax` (lines 136, 142) | Min/max of two uint192 | **No.** Callers use `Z.min` / `Z.max` ad hoc. |
| `abs(int256) -> uint256` (line 148) | Absolute value | **No.** |
| `FixLib.toUint(uint192) -> uint136` (line 183, 190 with rounding) | Strip fixed-point scale, return integer | **No.** |
| `FixLib.shiftl(uint192, int8) -> uint192` (line 198) | FLOOR-default decimal shift | **No** — only the rounding-mode variant at line 206 is modeled (sim's `shiftl`). |
| `FixLib.shiftl(uint192, int8, RoundingMode) -> uint192` (line 206) | Decimal shift with rounding mode | **`shiftl` ✓**. Includes the `decimals <= -59` saturation at sim line 174 and `decimals >= 58` revert (returns `None`) at sim line 176. |
| `FixLib.plus`, `plusu`, `minus`, `minusu` (lines 223, 230, 237, 244) | uint192 add/sub with overflow revert | **`plus`, `plus_opt`, `minus`, `minus_opt` ✓** (no `plusu`/`minusu` — sim works in Z and uses `*_opt` to surface uint192 boundary). |
| `FixLib.mul(uint192, uint192) -> uint192` and rounding variant (lines 252, 259) | uint192 mul with rounding | **`mul`, `mul_opt` ✓** (CEIL/ROUND/FLOOR via `RoundingMode`). |
| `FixLib.mulu(uint192, uint256) -> uint192` (line 270) | mix-precision multiply | **`mulu`, `mulu_opt` ✓**. |
| `FixLib.div(uint192, uint192) -> uint192` and rounding variant (lines 277, 284) | uint192 div with rounding | **`div`, `div_opt` ✓**. |
| `FixLib.divu(uint192, uint256) -> uint192` and rounding variant (lines 296, 303) | mix-precision divide | **No.** Used inside Throttle's `currentlyAvailable` and DutchTrade indirectly; both reimplement the formula. |
| `FixLib.powu(uint192, uint48) -> uint192` (line 317) | Exp-by-squaring on D18 | **`powu` ✓**. The conditional ordering is rearranged from production for `simpl` reducibility (sim line 152 comment); production-equivalence relies on `powu_safe`-style lemmas in `proofs/Fixed_safety.v`. |
| `FixLib.sqrt(uint192) -> uint192` (line 332) | Newton-iteration sqrt on D18 | **No.** |
| `FixLib.lt`, `lte`, `gt`, `gte`, `eq`, `neq` (lines 337–357) | Comparisons | **`lt`, `lte`, `gt`, `gte`, `eq`, `neq` ✓**. |
| `FixLib.near(uint192, uint192, uint192) -> bool` (line 364) | Approximate equality | **No.** |
| `FixLib.shiftl_toUint(uint192, int8)` and rounding variant (lines 380, 387) | Strip scale and decimal-shift to integer | **No.** Callers (BackingManager, BasketHandler, GnosisTrade, DutchTrade) reimplement the formula. |
| `FixLib.mulu_toUint(uint192, uint256)` and rounding variant (lines 406, 413) | Multiply, then strip scale, returning integer | **`mulu_toUint` ✓** (rounding variant only). The header notes the FLOOR-default overload is not modeled. |
| `FixLib.mul_toUint(uint192, uint192)` and rounding variant (lines 424, 431) | Multiply two fixes and strip scale | **No.** |
| `FixLib.muluDivu` (lines 443, 455) | a * b / c on (uint192, uint256, uint256) | **No.** |
| `FixLib.mulDiv` (lines 468, 480) | a * b / c on (uint192, uint192, uint192) with rounding | **No** — the safety-guarded variant at line 562 is what TradeLib uses, and the simulation models that piece in `simulations/TradeLib.v` directly. |
| `FixLib.safeMul(uint192, uint192, RoundingMode) -> uint192` (line 494) | Saturating multiply (returns FIX_MAX on overflow) | **No.** |
| `FixLib.safeDiv(uint192, uint192, RoundingMode) -> uint192` (line 544) | Saturating divide | **No** — modeled in `simulations/IssuancePremium.v::safeDiv_ceil` for the CEIL specialization only. |
| `FixLib.safeMulDiv(uint192, uint192, uint192, RoundingMode) -> uint192` (line 562) | Saturating mul-div, used by TradeLib | **No** at the FixLib level — `simulations/TradeLib.v::safeMulDiv` carries a separate model for the kernel TradeLib actually invokes. |
| `mulDiv256(uint256, uint256, uint256)` (line 622) and rounding variant (line 653) | Full-precision 256-bit mul-div using Newton iteration; the inner kernel of `safeMulDiv` | **No.** Header notes the inner uint256 overflow is not separately bounded. |
| `fullMul(uint256, uint256) -> (hi, lo)` (line 677) | 512-bit multiply primitive | **No.** |
| `sqrt256(uint256) -> uint256` (line 697) | Newton-iteration sqrt | **No.** |

### What the simulation *does* faithfully model

- The full `RoundingMode` enum and `divrnd` semantics (FLOOR / ROUND / CEIL).
- `safeWrap : Z -> option Z` matching production's `_safeWrap` revert, surfaced via `_opt` wrappers.
- The seven core arithmetic operations (`mul`, `div`, `mulu`, `plus`, `minus`, comparisons) in both unchecked-Z and uint192-bounded variants.
- `powu` with the same conditional structure as production lines 317-330, using a `Z.log2 y + 1` fuel parameter (since `y` is uint48-bounded, this terminates).
- `shiftl` including all three documented edge cases: `x = 0`, `decimals <= -59` (saturation per rounding mode), `decimals >= 58` (overflow → `None`).
- `mulu_toUint` (the rounding variant) — the only "result-as-uint" function modeled.

### Implications for proof transferability

1. Lemmas using only `mul`, `div`, `mulu`, `plus`, `minus`, `powu`, and `shiftl` carry to production directly (modulo uint192 boundedness, which is the responsibility of `_opt` callers).
2. Lemmas about `safeMulDiv` or `safeDiv` rely on the **per-callsite** simulations in `TradeLib.v` and `IssuancePremium.v`. The fact that production routes these through `mulDiv256` (a Newton-iteration full-precision kernel) is *not* modeled — proofs that depend on intermediate-precision properties (e.g. that `safeMulDiv` produces a result equal to `(a*b/c)` even when `a*b > 2^256`) carry only by manual argument, not by the sim.
3. Any production callsite that uses `safeMul`, `safeDiv`, `near`, `divu`, `mulDiv`, or `muluDivu` outside of TradeLib / IssuancePremium has **no Fixed-side simulation coverage** — proofs must reason about those callsites either by re-deriving the operation in `Z` or by reading the operation's effect from the call's surrounding context. The CAS xchecks (`cas/fixlib/`) pin some specific values but are not exhaustive.
4. The conditional rearrangement in `powu` (sim line 152 comment) means the sim's `powu` is provably equal to production's only via the `powu_safe` lemma chain in `proofs/Fixed_safety.v` — direct definitional equality does not hold.

## Furnace (gold-standard audit)

The simulation captures **the per-period melt math (`(1 - (1-r)^N) *
bal`), the storage-mutating `melt(now, currentBalance)` call, and both
the divergent and production-faithful `setRatio` paths
(`setRatio` writes directly; `setRatio_with_melt` calls `melt` at the
old ratio first)**. It omits **the `init()` lifecycle, the actual
`rToken.melt(amount)` token-burn side effect, the governance modifier
on `setRatio`, and the `block.timestamp` / `rToken.balanceOf`
indirection** (sim takes both as inputs, header documents this). The
proofs against this model are correct for the math kernel; transfer
to production requires (i) the caller passing the live
`rToken.balanceOf(this)` rather than a stale snapshot, (ii) proofs
that depend on the new-ratio-applies-to-next-period semantic to use
`setRatio_with_melt`, not `setRatio`.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `MAX_RATIO` (uint192 constant, 1e14) | Cap on per-period melt fraction | **`MAX_RATIO ✓`** as `Z` constant. |
| `rToken` (IRToken private) | Pointer to the RToken contract; supplies `balanceOf(this)` and receives `melt(amount)` | None. The simulation accepts `currentBalance` as an explicit `now`-time argument. |
| `ratio` (uint192) | The per-period melt fraction | **`Storage.ratio` ✓**. |
| `lastPayout` (uint48) | Timestamp of last payout | **`Storage.lastPayout` ✓** but bounded as `0 <= ... <= UINT256_MAX` in `Valid.t` (the field name was renamed to `lastPayout_u256` per the audit follow-up; production type is uint48 and the loose bound is a known gap — see cross-cutting finding 3). |
| `lastPayoutBal` (uint256) | Cached RToken balance at last payout | **`Storage.lastPayoutBal` ✓**. |
| `__gap` (uint256[47]) | OZ upgrades reserved storage | None. |
| `Component`-inherited storage (governance role, paused/frozen flags, etc.) | Auth and pause | None. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(IMain, uint192 ratio_)` | Sets `rToken`, calls `setRatio(ratio_)`, snapshots `lastPayout = now`, `lastPayoutBal = rToken.balanceOf(this)` | **No.** |
| `melt()` (line 65) | Computes payout amount, updates `lastPayout`, `lastPayoutBal`, calls `rToken.melt(amount)` | **`melt` ✓** as `(s, now, currentBalance) -> (s', amount)`. The `rToken.melt(amount)` token-burn side effect is **not modeled** — sim just decrements `lastPayoutBal`. |
| `setRatio(uint192 ratio_)` (line 83) — governance-gated | Reverts if `ratio_ > MAX_RATIO`; calls `melt()`; writes `ratio = ratio_`; emits `RatioSet` | **Two variants modeled:** (a) `setRatio` writes directly without calling melt — flagged as DIVERGENCE in the simulation header; (b) `setRatio_with_melt` matches production's call ordering. Governance modifier and the `RatioSet` event are not modeled. |
| Component-inherited (`pause`, `freeze`, `requireGovernanceOnly`) | Pause/freeze guards on melt; governance gate on setRatio | **No.** |

### What the simulation *does* faithfully model

- The integral form `payoutRatio = 1 - (1-ratio)^N` (sim line 67–69 mirroring production line 72) — i.e. the closed-form sum of N geometric per-period melts.
- The early-return `if (now < lastPayout + 1) return` short-circuit at sim line 63 / production line 66.
- The `lastPayout += numPeriods` semantics (sim and production both add `numPeriods`, not "set to `now`" — relevant if `now > lastPayout + numPeriods` due to the `uint48` cast in production, which the sim doesn't model).
- The `lastPayoutBal' = currentBalance - amount` semantic (sim line 74 / production line 77). This *omits* the post-melt balance change: production's `rToken.melt(amount)` call burns tokens *after* the assignment, so on the next call `currentBalance` will reflect the new balance — the sim's caller must supply that fresh balance.
- The `setRatio_with_melt` composition (sim lines 105–116) which captures one period of accrual at the old ratio, then writes the new ratio.
- `MAX_RATIO = 1e14` cap on `setRatio`.

### Implications for proof transferability

1. Lemmas about `melt` carry to production *if* the caller supplies the live `rToken.balanceOf(this)` as `currentBalance`. The sim cannot witness divergence between `currentBalance` and the post-burn balance from the previous melt — but production's `rToken.melt(amount)` happens at the end of the same call, so the next caller's read sees the post-burn balance, and the sim is faithful.
2. The `setRatio_with_melt` operation makes the simulation *production-faithful for ordering*. The bare `setRatio` still exists for proofs that don't care about ordering (header line 79–87). A reviewer should check that no chain-level lemma uses `setRatio` where `setRatio_with_melt` would be called in production — see cross-cutting finding 2.
3. Lemmas about token-burn conservation (e.g. "RToken total supply decreases by `amount` after `melt`") *cannot* be stated in this simulation because the `rToken.melt(amount)` call is not modeled. Such lemmas live downstream of the sim, in integration files that thread RToken's storage state through.
4. The governance gate on `setRatio` is unmodeled: the simulation treats setRatio as available to any caller, with `MAX_RATIO` as the only cap. Production additionally requires `requireGovernanceOnly()` (production line 83 modifier) — the sim's lemmas hold for any caller that respects the cap, which is strictly weaker than production's reachability.
5. The `init()` snapshot semantic ("lastPayout = now at init") is unmodeled. Lemmas that depend on the genesis state are vacuous on storage states the simulation regards as well-formed but production's `init` would never produce.

## Distributor (gold-standard audit)

The simulation captures **the inner-loop conservation math
(`totals`, `tokensPerShare`, `distributeAmounts`) plus the DAO-fee-aware
extension (`distributeAmounts_with_dao_fee`, `feeShareInflation`,
`paidOutShares`) added during the audit follow-up**. It omits **the
storage-mutating governance ops (`setDistribution`, `setDistributions`,
`init`), the `distribute` external entry (auth + reward-accounting +
ERC20 transfers), and the EnumerableSet ordering guarantee**. The
proofs against this model are correct for the per-call accounting
math; transferring them to production requires verifying (i) callers
have already discharged the auth/erc20-identity gates, and (ii) the
order-of-iteration matches what `EnumerableSet` exposes (which
guarantees insertion-order traversal — sim uses a plain list).

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `destinations` (EnumerableSet.AddressSet) | The set of distribution addresses | **Plain `list (U256.t * RevenueShare.t)`** — equivalent on content, but the sim does not witness EnumerableSet's ordering guarantee. |
| `distribution[address]` (mapping) | RevenueShare per destination | Inlined into the `Storage` list as the second tuple element. |
| `FURNACE` / `ST_RSR` (constant addresses 1 / 2) | Sentinel addresses for furnace and StRSR routing | Not modeled — sim treats every destination as a generic address; the `addrTo == FURNACE/ST_RSR` rewrite (production lines 155–161) and `accountRewards` flag-setting are not represented. |
| `MAX_DESTINATIONS_ALLOWED` (uint8 = 100), `MAX_DISTRIBUTION` (uint16 = 10000) | Per-share and total-destinations governance caps | **`MAX_DISTRIBUTION ✓`, `MAX_DESTINATIONS ✓`** as constants, but the sim's operations do not enforce them at write time (no `setDistribution` modeled). |
| `rsr`, `rToken`, `furnace`, `stRSR`, `rTokenTrader`, `rsrTrader` (component pointers) | Routing + token identity + auth | **None.** |
| `__gap` (uint256[44]) | OZ reserved storage | None. |
| Component-inherited (governance role, pause/frozen flags) | Auth | None. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(IMain, RevenueShare)` (line 44) | Sets up `destinations` with FURNACE / ST_RSR seeded from `dist`; caches components | **No.** |
| `setDistribution(address dest, RevenueShare)` (line 61) — governance-gated | Validates and writes a single destination's share; calls `_ensureSufficientTotal` post-write; opportunistic `distributeTokenToBuy()` calls on RsrTrader / RTokenTrader | **No.** |
| `setDistributions(address[] dests, RevenueShare[] shares)` (line 81) — governance-gated | Batch version of `setDistribution` | **No.** |
| `distribute(IERC20 erc20, uint256 amount)` (line 120) — RevenueTrader-gated | The entry point: validates auth + erc20 identity, computes `tokensPerShare`, transfers per destination, pays DAO fee, calls `furnace.melt()` / `stRSR.payoutRewards()` based on `accountRewards` | **Partial.** The math kernel is `distributeAmounts` / `distributeAmounts_with_dao_fee`; the auth check, the `tokensPerShare != 0` revert (production line 134), the `transferFrom` ERC20 calls, the FURNACE/ST_RSR address rewrites, the `daoFeeRegistry.getFeeDetails(rToken)` indirection, and the post-distribute `payoutRewards()` / `melt()` accounting calls are all unmodeled. |
| `totals()` (line 204) | Public view: aggregate rTokenTotal/rsrTotal across destinations, applies DAO fee inflation if `daoFeeRegistry` is set | **`totals` ✓** for the inner loop; **`feeShareInflation` ✓** for the DAO-fee adjustment. The wiring (consult `main.daoFeeRegistry()`, call `getFeeDetails(rToken)`) is unmodeled — sim takes `feeNumerator` and `feeDenominator` as arguments. |
| `_setDistribution(address, RevenueShare)` (line 240) | The internal validator: enforces the 8 `require` checks (non-zero dest, not furnace/stRSR/rsr/rToken/daoFeeRegistry, FURNACE.rsrDist=0, ST_RSR.rTokenDist=0, share caps, MAX_DESTINATIONS) | **No.** |
| `_ensureSufficientTotal(uint24, uint24)` (line 269) | Asserts `rTokenTotal + rsrTotal >= MAX_DISTRIBUTION` | **No.** |
| `cacheComponents()` (line 274) | Re-reads component pointers from `main`; called post-upgrade | **No.** |

### What the simulation *does* faithfully model

- `totals(s) = (sum of rTokenDist, sum of rsrDist)` over the destinations list — the inner loop at production lines 204–211, ignoring the DAO-fee branch.
- `tokensPerShare(s, amount, isRSR) = amount / totalShares` (FLOOR), with the explicit `totalShares = 0 -> 0` short-circuit at sim line 92 (production reverts here; sim returns 0 — see cross-cutting finding 1).
- `distributeAmounts(s, amount, isRSR) = (per-destination amts list, dust = amount - sum(amts))`. The list is in the same order as the `Storage` list (sim) which corresponds to EnumerableSet insertion order in production.
- `distributeAmounts_with_dao_fee` mirrors the production `totals()` inflation: only the rsr leg is inflated (sim line 207–217 mirroring production line 220–224); the rToken leg's `tokensPerShare` is unchanged. The DAO-fee residual `(totalShares' - paidOutShares) * tps` is computed exactly as production line 186.
- `feeShareInflation` is defensive on malformed configs: returns 0 when `feeNumerator = 0` or `feeDenominator <= feeNumerator` (sim mirrors production's revert-via-checked-subtraction behaviour by returning a zero contribution rather than letting the math underflow).
- The `DistResult.t` record bundles the conservation invariant `sum(amts) + daoFee + dust = amount` (achievable when `totalShares != 0`).

### Implications for proof transferability

1. The conservation invariant `sum(transferAmts) + dust = amount` (no DAO fee) and `sum(amts) + daoFee + dust = amount` (with DAO fee) is precisely what the simulation establishes. It transfers to production directly *iff*: (a) the caller has already validated `tokensPerShare != 0` (production reverts; sim returns 0), and (b) the EnumerableSet's iteration order matches the order of `Storage`.
2. The auth gate (`require(caller == rsrTrader || rTokenTrader)`) is unmodeled — proofs about `distributeAmounts` apply to *any* caller. Production additionally requires the caller be one of the two RevenueTraders.
3. The `erc20 == rsr || erc20 == rToken` identity check is unmodeled — sim's `isRSR` flag is treated as an arbitrary boolean. Production reverts if neither identity matches.
4. The post-distribute `furnace.melt()` / `stRSR.payoutRewards()` calls (production lines 192–199) are unmodeled. Composition lemmas ("Distributor distributes then Furnace melts") cannot be stated against this simulation; they would need an integration file that threads both states.
5. The DAO-fee leg coverage was added in the follow-up (`distributeAmounts_with_dao_fee`); legacy proofs against `distributeAmounts` apply only to deployments where `daoFeeRegistry` is unset OR `feeNumerator = 0`. Specific xchecks in `proofs/CAS_additional_findings.v` formalize the ⩾1% DAO fee bug pinned in the audit.
6. The `MAX_DESTINATIONS = 100` and per-share `MAX_DISTRIBUTION = 10000` caps are constants in the sim but unenforced at write time (no `setDistribution`). Proofs assuming "the destinations list has length ≤ 100" must carry that as a Valid-style hypothesis.

## BackingManager (gold-standard audit)

The simulation captures **two layers**: (1) a pure-math kernel
(`computeNewBasketsAndNeeded`, `computeSurplusSplit`); (2) an operation
surface added in the audit follow-up — `forwardRevenueIter`,
`forwardRevenue`, `prepareRecollateralizationTrade`,
`settleRecollateralizationTrade` — composing the kernel with
`Rebalance.basketRange` and `TradeLib.buyAmount`, plus a `Storage.t`
record (`basketsNeeded`, `backingBuffer`, `tradeStatus`,
`pendingTrade`) and an explicit `TradeStatus` state machine
(NONE / OPEN / SETTLED). It omits **the asset-registry indirection
(sim takes a pre-resolved `AssetList` as input), the oracle layer,
the trade *execution* (only preparation and settlement bookkeeping —
the actual ERC20 transfers and Gnosis interactions live in
DutchTrade/GnosisTrade simulations), the `fullyCollateralized()` /
`basketHandler.isReady()` gates, the `tradingDelay` time-gate, the
duplicate-token revert, the reentrancy modifier, the SafeERC20
calls inside `forwardRevenue`, and the auth/governance surface
(`grantRTokenAllowance`, `setBackingBuffer`, `setTradingDelay`)**.
The proofs against this model are correct for the iteration math
and the state-machine transitions; transferability requires the
caller to discharge the auth, oracle, and registry boundaries.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `assetRegistry`, `basketHandler`, `distributor`, `rToken`, `rsr`, `stRSR`, `rsrTrader`, `rTokenTrader`, `furnace` (component pointers) | Cross-component routing | None — sim takes their data (asset list, totals, basketsHeldBottom, etc.) as inputs. |
| `MAX_TRADING_DELAY` (uint48 = 1 year) | Cap on `tradingDelay` setter | None. |
| `MAX_BACKING_BUFFER` (uint192 = FIX_ONE) | Cap on `backingBuffer` setter | **`MAX_BACKING_BUFFER ✓`** — enforced by `Valid.bufferInputs.backingBuffer_le_max`. |
| `tradingDelay` (uint48) | Time gate on `rebalance` after basket switch | None. The `block.timestamp >= basketHandler.timestamp() + tradingDelay` check at production line 123 is unmodeled. |
| `backingBuffer` (uint192, governance-set) | Extra collateral fraction held before recognising revenue | **`Storage.backingBuffer ✓`**. |
| `tradeEnd[TradeKind]` (mapping kind→uint48) | Per-kind last endTime; DoS prevention at production line 117 | None — sim's `TradeStatus` is a single flag, not per-kind. |
| `tokensOut[IERC20]` (mapping erc20→uint192) | Tokens currently out on a trade; included in `bals[i]` at production line 298 | None. |
| `tradesOpen` (uint8, parent `TradingP1`) | Counter of open trades | Modeled abstractly as `TradeStatus.t` (NONE / OPEN / SETTLED). |
| `__gap` (uint256[38]) | OZ reserved storage | None. |
| TradingP1-inherited (`maxTradeSlippage`, `minTradeVolume`) | Trade-sizing params | Passed in as arguments to `prepareRecollateralizationTrade`. |
| Component-inherited (governance role, paused/frozen flags) | Auth and pause | None — `requireNotTradingPausedOrFrozen()` at production lines 109/179 unmodeled. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(IMain, uint48 tradingDelay_, uint192 backingBuffer_, uint192 maxTradeSlippage_, uint192 minTradeVolume_)` (line 49) | Sets up component cache, calls setTradingDelay / setBackingBuffer | **No.** Sim takes `Storage.init(basketsNeeded, backingBuffer)` as a constructor only. |
| `grantRTokenAllowance(IERC20 erc20)` (line 69) | Grants RToken max allowance over a registered erc20 | **No.** |
| `settleTrade(IERC20 sell)` (line 85) | Settles the trade for `sell`; chains into `rebalance(kind)` if caller is the trade itself | **Partial** — `settleRecollateralizationTrade` covers the OPEN→NONE bookkeeping; the chain-into-rebalance and the `super.settleTrade` indirection are unmodeled. |
| `rebalance(TradeKind kind)` (line 108) | Full recollateralization: refresh registry, check gates, compute `basketsHeld`, dissolve held RToken, call `prepareRecollateralizationTrade` lib, either start a trade or compromise | **Partial** — `prepareRecollateralizationTrade` (sim) covers the post-gating composition (basketRange + TradeLib.buyAmount → TradeStatus.OPEN). The pre-call gates (`tradesOpen == 0`, `basketHandler.isReady()`, `tradingDelay`, `basketsHeld.bottom < rToken.basketsNeeded()`, RToken-balance dissolve, RSR-seizure-when-sellERC20-is-rsr at line 159–163), and the haircut path (`compromiseBasketsNeeded`) are **unmodeled** — the sim treats the haircut as a settlement variant. |
| `forwardRevenue(IERC20[] erc20s)` (line 178) | Forward held RSR to stRSR, mint revenue RToken if `baskets > basketsNeeded`, distribute surpluses across rsrTrader/rTokenTrader | **`forwardRevenue` ✓** for the math + iteration aggregate (sim line 408). The `rsr.balanceOf(this)` transfer to stRSR (production line 212–216), the `rToken.mint(...)` call (line 222), `requireNotTradingPausedOrFrozen` (line 179), `ArrayLib.allUnique(erc20s)` revert (line 180), `assetRegistry.refresh` (line 182), the four pre-gates (`tradesOpen == 0`, `isReady`, `tradingDelay`, `basketsHeld.bottom >= basketsNeeded`), and the per-asset `safeTransfer` (lines 253, 256) are **unmodeled**. |
| `tradingContext(BasketRange basketsHeld)` (line 272) | Builds the per-asset `quantities[]` and `bals[]` arrays for the registry | **No** — sim takes the AssetList as an input. |
| `compromiseBasketsNeeded(uint192 basketsHeldBottom)` private (line 309) | Sets `rToken.basketsNeeded := basketsHeldBottom` (haircut) | **Partial** — modeled as a `settleRecollateralizationTrade` variant where `newBasketsNeeded` is set directly; the sim does not flag this as semantically distinct from a normal settle, but production is. |
| `forceSettleTrade(ITrade trade)` (line 321) — governance | Force-close a stuck trade | **No.** |
| `setTradingDelay(uint48)` (line 327) — governance | Validates and writes `tradingDelay` | **No.** |
| `setBackingBuffer(uint192)` (line 335) — governance | Validates `<= MAX_BACKING_BUFFER` and writes `backingBuffer` | **No.** |
| `cacheComponents()` (line 343) | Re-reads component pointers post-upgrade | **No.** |

### What the simulation *does* faithfully model

- `computeNewBasketsAndNeeded(basketsHeldBottom, basketsNeeded, backingBuffer)` produces `(basketsNeeded', mintAmount, needed)`, with `mintAmount > 0` only when `basketsHeldBottom > basketsNeeded * (1 + buffer)` and `needed = CEIL(basketsNeeded' * (1 + buffer))` — the post-#1283 CEIL mitigation.
- `computeSurplusSplit(needed, quantity, bal, decimals, rTokenTotal, rsrTotal)` reproduces the per-asset `bal > req` branch (production lines 243–261), including the explicit `tokensPerShare = 0 → dust = delta, both shares = 0` path which production handles as `continue` (sim line 202–207).
- `Result.Revert` when `totalShares = 0` mirrors the production division-by-zero pre-check at line 246 (production has `// no div-by-0: Distributor guarantees ...`; sim makes the would-be revert explicit).
- `forwardRevenueIter` walks the asset list, calling `computeSurplusSplit` for each row, accumulating splits + `(rsrSum, rTokenSum, dustSum)` aggregates. Conservation across the iteration is preserved by `stepAggregate`.
- `forwardRevenue` composes `computeNewBasketsAndNeeded` with `forwardRevenueIter`, threading the result through `Storage.t` post-state. The `mintAmount` is surfaced; whether it's zero-or-positive is what production's `if (baskets > basketsNeeded) rToken.mint(...)` keys on.
- `prepareRecollateralizationTrade` transitions `tradeStatus: NONE → OPEN` when `needsTrade` fires (range.low < basketsNeeded < range.high+1), capturing the sell/buy ERC20s, sellAmount, and buyAmount from `TradeLib.buyAmount`.
- `settleRecollateralizationTrade` transitions `tradeStatus: OPEN → NONE` and writes `basketsNeeded := newBasketsNeeded`. Auth check (`_msgSender() == address(trade)`) is documented as unmodeled.
- `Valid.bufferInputs` and `Valid.storage` carry uint192 bounds + the `tradeStatus`/`pendingTrade` consistency invariant.

### Implications for proof transferability

1. Conservation lemmas about `forwardRevenue` (e.g. "sum(rsr) + sum(rTok) + sum(dust) = sum(deltas) across all assets") transfer directly *within* the simulation's boundary — they say nothing about the actual `safeTransfer` calls in production, only about the bookkeeping math.
2. The `rebalance` gates (RToken-dissolve, `basketsHeld.bottom >= basketsNeeded` early-return at line 133, RSR seizure when `sellERC20 == rsr`, lines 159–163) are *entirely unmodeled*. Lemmas about `prepareRecollateralizationTrade` apply to a much wider input space than production's actual reachable set.
3. The most surprising divergence: the `compromiseBasketsNeeded` haircut path is collapsed into `settleRecollateralizationTrade`'s `newBasketsNeeded` argument. Production has two structurally distinct paths (start-trade vs haircut) gated by the lib's `doTrade` boolean; the sim only models the post-decision settle. A reviewer auditing "the haircut branch is correctly handled" cannot answer the question with this sim alone.
4. The asset-registry boundary is the biggest scoping decision: `forwardRevenue` and `prepareRecollateralizationTrade` consume an `AssetList` as input. In production, that list is built inside `tradingContext()` from `assetRegistry.getRegistry()` plus `basketHandler.quantityUnsafe(...)` plus `asset.bal(this)` plus `tokensOut[erc20]` plus the RSR-from-stRSR boost (production line 301). Each of these is a potential failure or staleness mode the simulation cannot witness.
5. The `tradingDelay` / `isReady` / `tradesOpen == 0` / `notTradingPausedOrFrozen` four-fold pre-gate is unmodeled. Lemmas hold even when the protocol is paused, the basket isn't ready, or another trade is open — production reverts in all those cases.
6. The "duplicate tokens" revert (`ArrayLib.allUnique(erc20s)`, line 180) is unmodeled: a caller passing a duplicate ERC20 to `forwardRevenue` would, in the sim, double-count surplus from that asset.
7. The `tradeEnd[kind]` per-kind DoS guard (line 117) and `tokensOut[erc20]` accounting (line 86, 168) are unmodeled — both are 3.0.0 / 3.1.0 additions specifically to prevent same-block trade chains. Sim cannot witness their absence.
8. `setBackingBuffer` and `setTradingDelay` (governance setters) are unmodeled. Live-vs-frozen for `backingBuffer` is recorded under cross-cutting finding 2.

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

**Quote math + basket-state lifecycle.** Two layers:
- **Layer 1 — Quote math kernel.** `quote_one`, `quote`,
  `quoteQuantities`, `redeem_one` over the live `Basket` (list of
  `(asset, refAmt)`).
- **Layer 2 — Basket-state lifecycle.** `setPrimeBasket`,
  `refreshBasket` operate on a `Storage` record `{basket, primeBasket,
  backupConfigs, nonce, disabled}`, mirroring production
  `BasketHandlerP1`'s state. The previous `Definition Storage : Set
  := list BasketEntry.t` is renamed to `Definition Basket` so existing
  proofs about quote semantics carry over without churn.

**Lifecycle modeled**:
- `setPrimeBasket` validates `MIN_TARGET_AMT <= targetAmt[i] <=
  MAX_TARGET_AMT` (1e12 / 1e21 from production lines 31–32),
  rejects empty / over-cap (`MAX_BASKET_LENGTH = 64`) lists, rejects
  duplicate erc20s. Successful calls write the new prime config and
  increment `nonce` by 1. Returns `option Storage.t`.
- `refreshBasket` is total over `Storage.t × list AssetStatus.t`.
  Faithful to `BasketLibP1.nextBasket`: surfaces good prime collateral
  in order, then for each target name with positive unsound weight,
  selects up to `BackupConfig.max` good backups and distributes the
  unsound weight evenly (floor quotient) across them. Sets
  `disabled = true` iff the next-basket selection failed; otherwise
  writes the new basket and increments `nonce`.

**Audit theorems** (in `Audit.v`):
- `audit_setPrimeBasket_validates`: storage validity preserved.
- `audit_refreshBasket_preserves_validity`: storage validity preserved
  on both success and failure paths.
- `audit_refreshBasket_targetAmt_conservation`: in the all-sound case,
  exact targetAmt sum conservation across the refresh.
- `audit_refreshBasket_disabled_implies_no_backup`: contrapositive
  characterising when disabled flips to true.

**Gaps that remain** (intentionally out of scope per the simulation
header):
- Asset-registry indirection — sim TAKES the AssetStatus list as
  input rather than reading it from a registry.
- Oracle layer — `pegPrice` etc. not consulted.
- Full Collateral status state machine — already modeled in
  `simulations/Collateral.v`; this sim consumes the boolean DISABLED
  outcome via `AssetStatus.t`.
- Governance modifier on `setPrimeBasket` (gated, not modeled).
- `requireConstantConfigTargets` (reweightable RTokens); the
  `forceSetPrimeBasket` / spell entry path is not modeled separately.
- Per-backup `targetPerRef` weighting: production divides
  `unsoundPrimeWt / (targetPerRef * size)`; sim sets `targetPerRef =
  FIX_ONE` and divides by `size` alone — same algebraic shape, the
  oracle-derived `targetPerRef` lookup is the elided piece.
- Warmup period, basket history, `lastCollateralized`, governance
  flags (`reweightable`, `enableIssuancePremium`).
- Quote-time `revenueHiding` decay and per-token issuance premium
  (modeled separately in `IssuancePremium.v`).

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

6. **Per-domain operation surface expansion. ✓ DONE.**

   All three big surfaces called out in the original audit landed in
   parallel sub-agent dispatches.

   - **BasketHandler `setPrimeBasket` / `refreshBasket`. ✓ DONE.**
     The simulation now carries a `Storage.t` record (basket,
     primeBasket, backupConfigs, nonce, disabled) alongside the
     legacy quote math kernel. `setPrimeBasket` validates target-
     amount bounds, basket size, and erc20 uniqueness, then writes
     the prime config and increments the nonce. `refreshBasket` is
     a total operation that consumes a per-erc20 AssetStatus list
     and rebuilds the basket from good primes plus per-target backup
     selection (mirroring `BasketLibP1.nextBasket`'s structure),
     setting `disabled = true` only when the next-basket selection
     fails. Asset-registry / oracle indirection are explicitly
     out of scope — the AssetStatus list is the modeled boundary.
     Validity preservation, target-amount conservation, and
     contrapositive disabled-iff-no-backup theorems are pinned in
     `BasketHandler_validity.v` / `BasketHandler_chain.v`. CAS
     witnesses live under `cas/basket_handler/set_prime_basket.gp`
     and `refresh_basket.gp`. See the BasketHandler section above
     for the full coverage map.

   - **BackingManager `forwardRevenue` / recollateralization
     state machine. ✓ DONE.**
     Layer 2 of the simulation now covers `forwardRevenueIter`
     (multi-asset iterator over `computeSurplusSplit`),
     `forwardRevenue` (composes `computeNewBasketsAndNeeded` with
     the iterator), `prepareRecollateralizationTrade` (composes
     `RebalanceLib.basketRange` with `TradeLib.buyAmount`), and
     `settleRecollateralizationTrade` (the OPEN→NONE transition).
     Asset-registry indirection, oracle layer, trade execution
     itself, and `fullyCollateralized()` gating remain explicitly
     out of scope — the AssetList and pre-priced range inputs are
     the modeled boundary. Conservation and validity preservation
     across the iteration are pinned in
     `BackingManager_forward_iter.v`. CAS witnesses live under
     `cas/backing_manager/forward_revenue_iter.gp` and
     `recollateralization_state_machine.gp`.

   - **StRSR `seizeRSR` / `cancelUnstake` / era model. ✓ DONE.**
     Phases A–D landed:
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
