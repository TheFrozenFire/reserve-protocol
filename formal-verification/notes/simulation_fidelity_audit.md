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

## Rebalance / RecollateralizationLib (gold-standard audit)

The simulation captures **the algebraic skeleton of `basketRange`**:
its final clipping step (`high = min(rawHigh, supply)`,
`low = min(rawLow, high)`) and the noise-bound primitives
(`dustNoiseBU`, `noise_loose`, `noise_tight`) used by Echidna's fuzzing
property. It omits **the per-asset oracle loop that derives
`deltaTop` and `uoaBottom` from the registry, the `BUs unpriced`
revert, the FIX_MAX-overflow reverts on `_safeWrap`, the asset-skip
predicate (lines 147–152), and the entire `nextTradePair` /
`isBetterSurplus` selection logic**. The proofs against this model
are correct for the abstract relation between aggregate slack and
the clipped output; they say nothing about the per-asset accumulation
that produces those slack figures in production. This is the most
heavily-scoped simulation in the tree relative to its production
counterpart.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| (none — RecollateralizationLib is a stateless library) | n/a | n/a |
| Caller-side `TradingContext` | Bundles basketsHeld, bh, ar, stRSR, rsr, rToken, minTradeVolume, maxTradeSlippage, quantities[], bals[] | **`RangeInputs.t`** carries supplyTotal, basketsHeldBottom, basketsHeldTop, lowSlack, highSlack — the aggregate result of folding TradingContext through the per-asset loop. |
| Caller-side `Registry` | erc20s[], assets[] arrays from `assetRegistry.getRegistry()` | None — modeled as folded-into-slack. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `prepareRecollateralizationTrade(TradingContext, Registry) -> (doTrade, TradeRequest, TradePrices)` (line 33) | Calls `basketRange`, `nextTradePair`, then `prepareTradeSell` or `prepareTradeToCoverDeficit` based on whether sellLow=0 or sell is unsound | **No.** Modeled at the BackingManager-sim level (`prepareRecollateralizationTrade` there abstracts the asset-pick and calls `TradeLib.buyAmount` directly). |
| `basketRange(TradingContext, Registry) -> BasketRange` (line 108) | Per-asset accumulation of `deltaTop` and `uoaBottom` from oracle prices, slippage, dust loss, then final clipping | **Partial.** Sim's `basketRange : RangeInputs -> BasketRange` covers only the final clipping at production lines 223–226 (`if range.top > basketsNeeded then ...`, `if range.bottom > range.top then ...`). The full per-asset loop (lines 139–200) and the `(buPriceLow, buPriceHigh) = ctx.bh.price(false)` call (line 116) are **unmodeled**. |
| `nextTradePair(TradingContext, Registry, BasketRange) -> TradeInfo` (line 274) | Picks the (sell, buy) pair with max surplus / max deficit; tracks SOUND vs IFFY/DISABLED priority for the sell side | **No.** This is the asset-pick logic; sim's `prepareRecollateralizationTrade` (in BackingManager.v) takes the chosen pair as input. |
| `isBetterSurplus(MaxSurplusDeficit, CollateralStatus, uint192)` (line 381) | Tiebreaker when comparing surplus candidates: SOUND > IFFY > DISABLED | **No.** |

### What the simulation *does* faithfully model

- The final clipping at production lines 223–226: `range.top := min(rawHigh, basketsNeeded)`, `range.bottom := min(rawLow, range.top)` — sim's `basketRange` mirrors this directly.
- The noise envelope used by FuzzP1's `isBasketRangeSmaller`: `noise_loose(bl, mtv, bup) = bl * dustNoiseBU + bl^2 + 2`.
- The tight alternative bound `noise_tight = bl * dustNoiseBU + 4*bl + 4` (strictly smaller for `bl >= 5`).
- The `dustNoiseBU(mtv, buPriceHigh) = ceil(mtv * FIX_ONE / buPriceHigh)` formula.
- `Valid.inputs` carries the structural invariants the production code maintains pre-clipping: `basketsHeldBottom <= basketsHeldTop`, `basketsHeldTop <= supplyTotal`, non-negative slacks, `supplyTotal <= FIX_MAX`.

### Implications for proof transferability

1. Lemmas about `basketRange` are statements about the abstract function `basketRange : RangeInputs -> BasketRange`, *not* about production's per-asset loop. They say "given any (basketsHeldBottom, basketsHeldTop, lowSlack, highSlack, supplyTotal) satisfying `Valid.inputs`, the clipped output respects the algebraic envelope". They do *not* say "production produces `(lowSlack, highSlack)` matching the noise model on real oracle inputs" — that claim is what the CAS scripts in `cas/rebalance/` work toward, but the rocq simulation does not bridge.
2. The `BUs unpriced` revert at production line 117 is unmodeled. Lemmas hold for ranges that production would reject as unpriced.
3. The FIX_MAX-overflow reverts on `_safeWrap` (production lines 206, 210, 220) are unmodeled. The simulation uses `Z` arithmetic and assumes inputs are bounded.
4. The asset-skip predicate at production lines 147–152 (skip dust-balance assets not in basket, when `quantities[i] == 0` and `!isEnoughToSell`) is folded into the abstract slack: a reviewer cannot tell from the sim whether a particular asset contributed to `lowSlack`.
5. The most surprising divergence: production's `basketRange` skips RToken itself (`if (reg.erc20s[i] == IERC20(address(ctx.rToken))) continue;` at line 141). The sim has no notion of asset identity, so this skip is implicit in the slack values rather than visible in the model.
6. The "deficit + slippage" path at production lines 218–220 (`uoaBottom.mulDiv(FIX_ONE - maxTradeSlippage, buPriceHigh, FLOOR)`) is implicit in `lowSlack`. The simulation cannot witness the maxTradeSlippage parameter at all — proofs cannot reason about live-vs-frozen of that governance value.
7. The header is honest about the scope: this is an algebraic skeleton, not a production-faithful model. Coverage claims should read "noise envelope and final clipping", not "rebalance basketRange".

## TradeLib (gold-standard audit)

The simulation captures **the buy-amount kernel inside
`prepareTradeSell` (the post-#1283 mitigation: `inner = mul(s, FIX_ONE
- slippage, CEIL)`, then `safeMulDiv(inner, sellLow, buyHigh, CEIL)`),
the pre-mitigation FLOOR variant (`buyAmountPre`) for rounding-direction
witnesses, the `coverDeficitSellAmount` kernel, `minTradeSize`, and
`isEnoughToSell_whole` (the dust-threshold predicate without the
quanta-rounding side)**. It omits **the full `prepareTradeSell` /
`prepareTradeToCoverDeficit` functions (asset-registry queries
`sell.maxTradeVolume`, `sell.erc20Decimals`, the shiftl_toUint to
qSellTok / qBuyTok, the assertion / require chain at the entry, the
`maxTradeSize` cap), the `isEnoughToSell` quanta-rounding side
(`shiftl_toUint(amt, decimals) > 1`), and the `maxTradeSize` private
function entirely**. The proofs against this model are correct for
the slippage-sufficiency math; transferring them to production
requires the caller to discharge the asset-registry boundary and the
sell-amount cap.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| (none — TradeLib is a stateless library) | n/a | n/a |
| Caller-side `TradeInfo { sell, buy, sellAmount, buyAmount, prices }` | Bundles asset pointers, amounts, sell-low/buy-high/sell-high/buy-low D18 prices | None — sim takes the four scalars `(s, slippage, sellLow, buyHigh)` directly. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `prepareTradeSell(TradeInfo, minTradeVolume, maxTradeSlippage) -> (notDust, TradeRequest)` (line 42) | Validates prices, dust-checks, caps `s` at `maxTradeSize`, computes `b` via the inner-mul / safeMulDiv chain, shifts both into qTok | **Partial.** The kernel `s.mul(FIX_ONE.minus(slippage), CEIL).safeMulDiv(sellLow, buyHigh, CEIL)` (production line 76–80) is captured by `buyAmount`. The `assert(buyHigh != 0 && buyHigh != FIX_MAX && sellLow != FIX_MAX)` at line 48–52, the `notDust = isEnoughToSell(...)` check (line 54), the `maxSell` cap (line 67) and `s > maxSell ? s = maxSell` clip (line 69), the `trade.prices.sellHigh != FIX_MAX` branch with the `require(maxSell > 1, "trade sizing error")` at line 68, the `require(sellLow == 0, "trade pricing error")` at line 71, and the final `shiftl_toUint(int8(decimals), FLOOR)` / `shiftl_toUint(int8(decimals), CEIL)` lifts (lines 83–84) are all **unmodeled**. |
| `prepareTradeToCoverDeficit(TradeInfo, minTradeVolume, maxTradeSlippage) -> (notDust, TradeRequest)` (line 118) | Asserts non-zero / non-MAX prices, fixMax-clips `buyAmount` to at-least-`minTradeSize`, computes `exactSellAmount = buyAmount * buyHigh / sellLow CEIL`, divides by `(1 - slippage)` CEIL, fixMin-clips with sellAmount, then calls `prepareTradeSell` | **Partial.** The composition kernel `exactSell = ceil(b * buyHigh / sellLow); slippedSell = ceil(exactSell / (FIX_ONE - slippage))` is captured by `coverDeficitSellAmount` (sim line 112). The `fixMax(buyAmount, minTradeSize(...))` floor on the buy amount (line 131), the `fixMin(slippedSell, sellAmount)` cap (line 147), the entry-point asserts (lines 123–128), and the recursive `prepareTradeSell` call (line 148) are **unmodeled**. |
| `isEnoughToSell(asset, amt, price, minTradeVolume) -> bool` (line 156) | Returns `amt >= minTradeSize(...) && shiftl_toUint(amt, decimals) > 1` | **Partial.** Sim's `isEnoughToSell_whole` covers the LHS only (the whole-token side); the `shiftl_toUint(amt, decimals) > 1` quanta-rounding RHS is **unmodeled** (decimals-dependent — header explicitly defers). |
| `minTradeSize(uint192 minTradeVolume, uint192 price) -> uint192` private (line 174) | `price == 0 ? FIX_MAX : minTradeVolume.div(price, CEIL)`, with a min-of-1 floor | **`minTradeSize` ✓**. |
| `maxTradeSize(IAsset sell, IAsset buy, uint192 price) -> uint192` private (line 182) | `min(sell.maxTradeVolume(), buy.maxTradeVolume()).safeDiv(price, FLOOR)`, with min-of-1 floor | **No.** This is the cap that production applies in `prepareTradeSell` line 67; sim has no analog. |

### What the simulation *does* faithfully model

- `safeMulDiv(a, b, c, mode)` with the four-way edge-case dispatch: `a=0||b=0 → 0`; `a=FIX_MAX||b=FIX_MAX||c=0 → FIX_MAX` (saturate); else `divrnd(a*b, c, mode)` clamped at FIX_MAX. Header notes the production `mulDiv256` Newton-iteration kernel for full-precision is *not* modeled — the sim uses exact `Z` arithmetic (no overflow hazard at this level).
- `buyAmount(s, slippage, sellLow, buyHigh)`: the exact composition `safeMulDiv(mul(s, FIX_ONE - slippage, CEIL), sellLow, buyHigh, CEIL)` — both rounding stages CEIL.
- `buyAmountPre`: same composition with FLOOR on the inner mul, used to witness `buyAmount >= buyAmountPre` (the post-#1283 mitigation strictly increases the buy floor).
- `coverDeficitSellAmount(b, slippage, sellLow, buyHigh)`: the exact composition `ceil(ceil(b * buyHigh / sellLow) / (FIX_ONE - slippage))`.
- `minTradeSize(minTradeVolume, price)` including the `price = 0 → FIX_MAX` saturation and the `size = 0 → 1` floor.
- `isEnoughToSell_whole(amt, price, minTradeVolume) = (minTradeSize <= amt)` — the whole-token comparison from production line 163.
- `Valid.buyInputs` carries `slippage <= FIX_ONE` (the production assert) and `0 < buyHigh` (the production require).

### Implications for proof transferability

1. Lemmas about `buyAmount` (slippage-sufficiency, CEIL-rounding direction) carry to production *iff* the caller has already capped `s` at `maxTradeSize`. The sim cannot witness violations of that cap.
2. The `notDust` flag is unmodeled — proofs say nothing about whether the trade should be skipped; they only say "if the trade does fire, the buy amount is at-or-above the floor".
3. The `shiftl_toUint(amt, decimals) > 1` quanta side of `isEnoughToSell` is what defends against trading-platform rounding loss for low-decimal sell tokens (e.g. WBTC at 8 dec). The sim only models the whole-token side; lemmas that conclude "amt is enough to sell" carry only the necessary condition, not the sufficient one.
4. The asset-registry indirection (`sell.erc20Decimals()`, `sell.maxTradeVolume()`) means proofs at the simulation level work in {sellTok} D18 units; production's `req.sellAmount` and `req.minBuyAmount` are in {qSellTok}/{qBuyTok} integer units. The decimal-shift step at production lines 83–84 is unmodeled — lemmas about the integer trade request require an additional decimal-correctness argument at integration sites.
5. The most surprising divergence is the asymmetry between `buyAmount` and `coverDeficitSellAmount` modeling. Both are kernels — but `coverDeficitSellAmount` is the *inner* kernel of `prepareTradeToCoverDeficit`, and `prepareTradeToCoverDeficit` then calls `prepareTradeSell` recursively (production line 148). The sim cannot express that recursive composition; lemmas about `coverDeficitSellAmount` are statements about one half of one branch of the trade-prep tree.
6. The `buyAmount`/`buyAmountPre` rounding-direction CAS witness (`cas/trade_lib/ceil_rounding_witness.gp`) pairs with the simulation lemmas to give the slippage-sufficiency proof its strength. The CAS scripts compute exact rationals where the sim works in `Z`; together they cover the rounding question without modeling overflow.

## BasketHandler (gold-standard audit)

The simulation captures **two layers**: (1) the quote math kernel
(`quote_one`, `quote`, `quoteQuantities`, `redeem_one`) over a
`Basket : list BasketEntry.t`; (2) the basket-state lifecycle
(`setPrimeBasket`, `refreshBasket`) over a `Storage` record
(`basket, primeBasket, backupConfigs, nonce, disabled`), mirroring
production's `BasketLibP1.nextBasket` selection logic. It omits **the
asset-registry indirection (sim takes `AssetStatus` list as input),
the oracle layer (`pegPrice` not consulted), the full Collateral
state machine (modeled separately in `Collateral.v`), the warmup
period and basket history, the governance flags `reweightable` and
`enableIssuancePremium`, the `forceSetPrimeBasket` spell path, the
`requireConstantConfigTargets` check, the `setBackupConfig`
governance op, the `quoteCustomRedemption` and `getHistoricalBasket`
backwards-compat reads, and the price/issuancePremium fold-in inside
`price()`**. Per-backup targetPerRef weighting is approximated as
`FIX_ONE` (header documents this). The proofs against this model are
correct for the basket-shape lifecycle and quote algebra; transfer
to production requires (i) the caller has already discharged the
asset-registry boundary, (ii) the warmup period and lifecycle
gates outside this sim are honoured.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `MIN_TARGET_AMT`, `MAX_TARGET_AMT`, `MAX_BACKUP_ERC20S = 64` | Bounds on per-prime target weights and backup array size | **All three modeled as constants ✓** (`MIN_TARGET_AMT`, `MAX_TARGET_AMT`, `MAX_BASKET_LENGTH = 64` — note rename: production has no explicit prime-basket length cap, sim applies the backup cap defensively to the prime list as well). |
| `MIN_WARMUP_PERIOD`, `MAX_WARMUP_PERIOD` (60s / 1y) | Bounds on `warmupPeriod` setter | **No.** |
| `assetRegistry`, `backingManager`, `rsr`, `rToken`, `stRSR` (component pointers) | Cross-component routing | **None.** |
| `config: BasketConfig { erc20s, targetAmts, targetNames, backups }` | Governance-set prime + backup config | **`primeBasket : list PrimeEntry.t` + `backupConfigs : list BackupEntry.t` ✓** — flattened from the mappings, but content-equivalent. |
| `basket: Basket` (struct with erc20s + refAmts mapping) | The live basket | **`basket : Basket` ✓** as `list BasketEntry.t`. |
| `nonce` (uint48) | Basket version counter | **`nonce : U256.t` ✓**. The uint48 bound is loose in `Valid.t.nonce_u256` (`<= UINT256_MAX`, not `<= UINT48_MAX`). |
| `timestamp` (uint48) | Last basket switch timestamp; consumed by warmup gate | **No.** |
| `disabled` (bool) | Basket health flag — quote/issue/redeem gated when true | **`disabled : bool` ✓**. |
| `_targetNames` (Bytes32Set, transient) | Function-local in `_switchBasket` | Computed by `unique_target_names` (sim line 439). |
| `_newBasket` (Basket, transient) | Function-local in `_switchBasket` | Computed via `goods ++ backups` inside `refreshBasket` (sim line 525). |
| `warmupPeriod` (uint48), `lastStatusTimestamp` (uint48), `lastStatus` (CollateralStatus) | 3.0.0 warmup gate | **None.** |
| `basketHistory` (mapping uint48 -> Basket) | 3.0.0 historical reads for redemption | **None.** |
| `_targetAmts` (Bytes32-to-uint map, transient) | Used inside `requireConstantConfigTargets` | **None.** |
| `reweightable` (bool, immutable post-init) | Whether prime targets can change | **None** — sim assumes the unconditional setPrimeBasket path. |
| `lastCollateralized` (uint48) | Most recent fully-collateralized nonce | **None.** |
| `enableIssuancePremium` (bool) | 4.0.0 governance toggle for the issuance-premium feature | **None** — modeled as input to `IssuancePremium.v`. |
| `__gap` storage | OZ reserved | **None.** |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(IMain, bool reweightable, uint48 warmupPeriod, bool enableIssuancePremium)` (line 109) | Sets reweightable / warmupPeriod / enableIssuancePremium | **No.** |
| `disableBasket()` (line 138) — backingManager-only | Sets `disabled = true`; emits BasketSet | **No.** |
| `refreshBasket()` (line 159) external — governance OR registry | Calls `assetRegistry.refresh()` then `_switchBasket()`; internally checks `requireConstantConfigTargets` for non-reweightable RTokens | **`refreshBasket` ✓** at the math/selection level. The `assetRegistry.refresh()` precondition, the `requireConstantConfigTargets` check, and the governance/registry auth gate are **unmodeled** — sim takes the AssetStatus list as input. |
| `trackStatus()` (line 176) | Updates `lastStatus`, `lastStatusTimestamp`, emits events; consumed by warmup gate | **No.** |
| `setPrimeBasket(IERC20[], uint192[])` (line 198) — governance-gated | Calls `_setPrimeBasket(false)` (the constant-targets path) | **`setPrimeBasket` ✓** at the math/validation level. The governance gate, `requireConstantConfigTargets`-when-not-reweightable check, and the `assetRegistry.toColl(_).targetName()` lookup are **unmodeled** — sim takes targetName as input on each PrimeEntry. |
| `forceSetPrimeBasket(IERC20[], uint192[])` (line 208) — long-spell-only | Calls `_setPrimeBasket(true)` to bypass constant-targets check | **No** as a separate operation; the sim's `setPrimeBasket` is the unconditional write (post-validation), parameterised by an explicit allow list. |
| `_setPrimeBasket(IERC20[], uint192[], bool disableTargetCheck)` (line 229) private | The implementation: validates targetAmts, builds the prime config | **`setPrimeBasket` ✓** for the validation + write; the disableTargetCheck branch isn't surfaced (sim is the always-write path post-validation). |
| `setBackupConfig(bytes32 targetName, uint256 max, IERC20[] erc20s)` (line 289) — governance | Validates + writes the per-target backup config | **No.** Sim's `Storage.backupConfigs` is mutated only via constructor / direct field-setting in proofs. |
| `fullyCollateralized()` (line 312) view | Returns `bool`: are we above `basketsNeeded`? | **No.** |
| `status()` (line 319) view | Aggregates per-collateral statuses to a basket-level CollateralStatus | **No** — sim's `disabled` is the only basket-level flag. |
| `isReady()` (line 336) view | True iff status==SOUND AND warmup elapsed | **No.** |
| `quantity(IERC20)` (line 348) view | refAmts / refPerTok with CEIL (registry indirection + collateral lookup) | **No** at the public-entry level — quote math kernel works directly on `BasketEntry.refAmt`. |
| `quantityUnsafe(IERC20, IAsset)` (line 364) | Same as quantity but skips asset-isCollateral check | **No.** |
| `issuancePremium(ICollateral)` (line 371) | The feature flag-gated premium curve | **Modeled separately in `IssuancePremium.v`.** |
| `_quantity(IERC20, ICollateral, RoundingMode)` (line 396) private | `refAmts.div(refPerTok, rounding)` | Implicit in `quote_one` which uses `mulu_toUint` directly on `refAmt`. |
| `price()` / `price(bool applyIssuancePremium)` (lines 414, 424) | Per-asset price aggregation, with optional issuance-premium fold-in | **No.** |
| `quote(uint192 amount, RoundingMode)` (line 472) view | Per-asset {qTok} list at a fresh-quote rounding | **`quote` ✓** at the algebraic level (`refAmt * baskets / FIX_ONE`); the production version applies the per-collateral `_quantity` (with issuancePremium and refPerTok lookups) which the sim collapses by setting refPerTok=FIX_ONE and not applying premium. |
| `quote(uint192 amount, bool applyIssuancePremium, RoundingMode)` (line 487) | Same but with the issuance-premium fold-in | **No** — premium is modeled in `IssuancePremium.v` and consumed independently. |
| `quoteCustomRedemption(uint48[], uint192[], uint192)` (line 526) | Historical-basket redemption using basketHistory | **No.** |
| `basketsHeldBy(address)` (line 615) view | Per-account basket-held bottom/top range | **No.** |
| `setWarmupPeriod(uint48)` (line 638) — governance | Validates + writes warmupPeriod | **No.** |
| `setIssuancePremiumEnabled(bool)` (line 646) — governance | Toggles enableIssuancePremium | **No.** |
| `_switchBasket()` (line 659) private | The full basket switch: builds targetNames, calls `BasketLibP1.nextBasket`, writes the new basket + nonce, sets disabled flag | **`refreshBasket` ✓** as the sim-side analog; per-backup targetPerRef weighting is approximated as `FIX_ONE`. |
| `requireValidCollArray(IERC20[])` (line 688) private | Enforces non-empty, no-duplicates, no-zero-address | **`erc20s_unique` ✓** for the no-duplicates branch; non-empty and no-zero-address are modeled as `(len =? 0)` and absence of further address validation. |
| `getHistoricalBasket(uint48)` (line 709) view | Backwards-compat read | **No.** |
| `getPrimeBasket()` (line 743), `getBackupConfig(bytes32)` (line 767) | View accessors | Implicit via record projections. |

### What the simulation *does* faithfully model

- The `quote_one` algebraic core: `qTok = refAmt * baskets / FIX_ONE` (sim line 144 = `FixLib.mulu_toUint refAmt baskets mode`). This is correct *iff* the production caller has already applied `_quantity`'s `refAmts.div(refPerTok, rounding)` — sim collapses that by working at a `refPerTok = FIX_ONE` calibration.
- `redeem_one` as the FLOOR-inverse of `quote_one` for the round-trip safety claim, including the `refAmt = 0 → 0` defensive return.
- The full `setPrimeBasket` validation chain: empty / over-cap (`MAX_BASKET_LENGTH = 64`), all targetAmts in `[MIN_TARGET_AMT, MAX_TARGET_AMT]`, no duplicate erc20s. Successful writes increment `nonce` by 1.
- `refreshBasket` as a total operation, mirroring `BasketLibP1.nextBasket`'s structure: surface good prime entries (in input order), then for each target name with positive unsound weight, select up to `BackupConfig.max` good backups and distribute the unsound weight evenly. `disabled = true` iff next-basket selection failed.
- `unique_target_names` preserves first-occurrence order, mirroring production's `_targetNames` Bytes32Set population at line 181.
- `Valid.t` carries: prime size bound, target-amt validity, prime erc20 uniqueness, nonce range, basket refAmt non-negativity. Audit theorems in `Audit.v` pin storage validity, target-amt conservation, and the disabled-iff-no-backup contrapositive.

### Implications for proof transferability

1. The most surprising divergence: production divides per-backup weight by `(targetPerRef * size)` (`unsoundPrimeWt / (targetPerRef * size)`) where `targetPerRef` is the per-collateral oracle-derived fixed-point ratio. The sim hard-codes `targetPerRef = FIX_ONE`, dividing only by `size`. **For non-fiat collateral with `targetPerRef ≠ FIX_ONE`, the sim's `refreshBasket` produces a different basket than production**. Header documents this; the algebraic shape is preserved but the calibration is off.
2. The asset-registry boundary is large: sim takes `AssetStatus` list as input. Production builds it inside the `_switchBasket` loop at line 666–684 by calling `assetRegistry.toColl(erc20).status()` per asset. Lemmas about `refreshBasket` apply to *any* AssetStatus list, not the production-reachable ones (which respect the registry's structural invariants — no duplicates, all-registered, etc.).
3. The `requireConstantConfigTargets` check (production line 234, called from `_setPrimeBasket(false)`) prevents non-reweightable RTokens from changing target-name composition. Sim's `setPrimeBasket` is the unconditional write — proofs about it apply to both reweightable and non-reweightable deployments, but reachable-state divergence applies for the latter.
4. The warmup-period gate (`isReady()`) is the precondition for a new basket to take effect post-refresh. Sim does not model it; lemmas about post-refresh quote behaviour assume the warmup is complete (or treat the gate as an integration responsibility).
5. The quote-time `applyIssuancePremium` fold-in (production line 424–452) is unmodeled. Lemmas about `quote()` cover the no-premium calibration; for the premium calibration, callers must compose the sim's `quote_one` with `IssuancePremium.v`'s output manually.
6. The `basketHistory` and `quoteCustomRedemption` 3.0.0 mechanism is entirely unmodeled. The sim's `redeem_one` is for the live basket only.
7. The "disabled at init" semantic (sim's `empty_storage` has `disabled = true` matching production line 158) is faithful, but the `init()` function itself isn't modeled — the sim operates on arbitrary `Storage.t` values, including states production's `init` would never produce.

## DutchTrade (gold-standard audit)

The simulation captures **the four-phase price-decay curve `_price`
(geometric, two linear segments, flat), `_bidAmount`, the FLOOR-rounded
variant `bidAmount_floor_variant` for rounding-direction proofs, and a
storage record `{startTime, endTime, bestPrice, worstPrice, sellAmount,
buyDecimals}` matching the production immutable-after-init slots**. It
omits **the `TradeStatus` state machine (NOT_STARTED → OPEN → PENDING
→ CLOSED), the `BidType` (NONE / TRANSFER / CALLBACK / FILL)
classification, the trusted-filler subsystem (`activeTrustedFill`,
`savedFillPrice`, `createTrustedFill`), the `bid()` / `bidWithCallback()`
/ `settle()` / `transferToOriginAfterTradeComplete()` operations, the
`init()` lifecycle and price-validation requires, the `lot()` view, the
`canSettle()` gate, the broker / origin pointers, and the
`reportViolation` invariant**. The proofs against this model are
correct for the price/amount math; transferring them to production
requires the auction is in OPEN state and `t ∈ [startTime, endTime]`
(the sim's totalisation by clamping at endpoints does not match
production's revert).

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `KIND` (constant `TradeKind.DUTCH_AUCTION`) | Identifies auction kind | None. |
| `bidType` (BidType enum) | NONE / TRANSFER / CALLBACK / FILL — the bid mechanism used | None. |
| `status` (TradeStatus) | State machine: NOT_STARTED / OPEN / PENDING / CLOSED — also reentrancy guard | None. |
| `broker` (IBroker) | Cloning factory; `reportViolation()` callback | None. |
| `origin` (ITrading) | The originating trader (BackingManager or RevenueTrader) | None. |
| `sell`, `buy` (IERC20Metadata) | Token pointers for the auction pair | None. |
| `sellAmount` (uint192) | Lot size in {sellTok} (D18) | **`Auction.sellAmount` ✓**. |
| `startTime`, `endTime` (uint48) | Auction window | **`Auction.startTime`, `Auction.endTime` ✓** with `Valid.t` carrying uint48 bounds. |
| `bestPrice`, `worstPrice` (uint192) | Auction price corners (D18) | **`Auction.bestPrice`, `Auction.worstPrice` ✓**. |
| `bidder` (address) | Set on `bid()` to record the winning bidder | None. |
| `activeTrustedFill` (IBaseTrustedFiller), `savedFillPrice` (uint192) | Trusted-filler subsystem (3.4.0+) | None. |
| `buyDecimals` (read on demand from `buy.decimals()`) | Decimals of the buy token, for shiftl_toUint | **`Auction.buyDecimals` ✓** as input — sim accepts the value directly rather than reading from `buy.decimals()`. |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(ITrading origin_, IAsset sell_, IAsset buy_, uint256 sellAmount_, uint48 auctionLength, TradePrices prices)` (line 171) — state-locked | Validates prices, sells funded, sets timing + price corners; status: NOT_STARTED → OPEN | **No.** Sim treats `Auction.t` as already-initialized. |
| `bid()` (line 223) — closeTrustedFiller modifier | At current price, transfers buy from bidder, sets bidder, calls `origin.settleTrade(sell)`, reportViolation if cleared in geometric phase | **No.** Side effects (token transfer, status mutation) unmodeled. |
| `bidWithCallback(bytes data)` (line 259) | Callback variant of bid() | **No.** |
| `bidAmount(uint48 timestamp)` external view (line 154) | Public wrapper around `_bidAmount(_price(timestamp))` | **`bidAmount` ✓** in the sim. |
| `lot()` view (line 147) | `sellAmount.shiftl_toUint(int8(sell.decimals()))` — qSellTok size of the lot | **No.** |
| `createTrustedFill(address targetFiller, bytes32 deploymentSalt)` (line 303) | Sets up a trusted filler for the auction | **No.** |
| `settle()` (line 342) — state-locked, closeTrustedFiller, origin-only | Settles the trade: handles BidType.FILL by checking buy balance, transfers tokens to origin/bidder; status: OPEN → CLOSED | **No.** |
| `transferToOriginAfterTradeComplete(IERC20Metadata)` (line 381) | Escape hatch: post-CLOSED, transfer any erc20 to origin | **No.** |
| `canSettle()` view (line 388) | Returns true iff settle would succeed (status == OPEN, not in active-fill, after endTime or filled or bidder set) | **No.** |
| `_price(uint48 timestamp)` private view (line 421) | The four-phase curve; reverts if timestamp outside `[startTime, endTime]` | **`bidPrice` ✓** at the math level; the **out-of-range revert is replaced with clamping at the nearest endpoint** (header documents this divergence). |
| `_bidAmount(uint192 price)` view (line 472) | `sellAmount.mul(price, CEIL).shiftl_toUint(int8(buy.decimals()), CEIL)` | **`bidAmount_at_price` ✓** with the shift modeled inline (sim line 130–136). |
| `_closeTrustedFill()` private (line 478) | Tears down `activeTrustedFill` if non-zero | **No.** |

### What the simulation *does* faithfully model

- The four-phase dispatch in `_price`: phase1 (`progression < 20%`, geometric decay via `bestPrice * 1.5 / BASE^k`, CEIL), phase2 (`< 45%`, linear from 1.5×best down to best, FLOOR), phase3 (`< 95%`, linear from best down to worst, FLOOR), phase4 (constant at worst). Constants `MAX_EXP = 6502287e18`, `BASE_DEC = 999999e12`, `ONE_POINT_FIVE = 150e16` mirror production exactly.
- `progression(a, t) = (t - startTime) * FIX_ONE / (endTime - startTime)` — note: production uses `divuu` (line 433) which the sim simplifies to integer division (FLOOR). Equivalent algebraically; the sim doesn't model `divuu`'s overflow guards explicitly.
- `bidAmount_at_price`: the `mul(sellAmount, price, CEIL)` followed by `shiftl_toUint(buy.decimals(), CEIL)` decimal lift. Both rounding stages CEIL — bidder-favorable.
- `bidAmount_floor_variant`: same composition with FLOOR everywhere, used to witness `bidAmount >= floor_variant` in CAS xchecks (cas/dutch_trade/).
- `Valid.t` carries: `startTime < endTime`, `worstPrice <= bestPrice`, `0 < bestPrice`, `0 <= worstPrice`, `0 <= sellAmount`, `0 <= buyDecimals <= 36`, plus uint48 bounds on startTime / endTime added in the audit follow-up.

### Implications for proof transferability

1. The most surprising divergence: out-of-range `t` returns the nearest endpoint instead of reverting. Lemmas about `bidPrice` are *stronger* than the production function — they cover inputs production rejects via the `require(timestamp >= _startTime, ...)` / `require(timestamp <= _endTime, ...)` checks at production lines 424–425. Cross-cutting finding 1 records this; transferability of `bidPrice` lemmas requires a `Valid.in_range` precondition at integration sites.
2. The state machine (NOT_STARTED → OPEN → PENDING → CLOSED) is entirely unmodeled. Lemmas about `bidPrice` apply *whether or not the auction is OPEN* — production's `bid()` has `require(status == TradeStatus.OPEN)` at line 225, which the sim cannot witness.
3. The `BidType.FILL` branch and the trusted-filler subsystem (which can pre-fill the trade at a saved price) are unmodeled. Settlement-time math involving `_bidAmount(savedFillPrice)` and the buy-balance check at production line 353 has no sim coverage.
4. The "geometric phase clears trigger reportViolation" invariant (production lines 238–240, 356–358) is unmodeled — sim has no Broker pointer.
5. `init()`'s price-validation requires (`prices.sellLow != 0 && prices.sellHigh != 0 && prices.sellHigh < FIX_MAX / 1000` at line 187, similar for buy at line 191) are unmodeled. The sim's `Valid.t` enforces `0 < bestPrice`, which is weaker — production caps the upstream-derived bestPrice/worstPrice via the FIX_MAX/1000 constraint, the sim allows up to FIX_MAX.
6. The `init()` derivation `worstPrice = sellLow.mulDiv(FIX_ONE - maxTradeSlippage, buyHigh, FLOOR)` and `bestPrice = sellHigh.div(buyLow, CEIL)` (production lines 209–214) is unmodeled. Lemmas about `bidPrice` apply to *any* `(bestPrice, worstPrice)` satisfying `Valid.t`, not specifically those production's init produces.
7. The CAS xchecks (`cas/dutch_trade/`) sample the price curve at concrete timestamps and pin specific output values — they pair with the simulation lemmas to give a faithful coverage on the math, even where the lifecycle is unmodeled.

## GnosisTrade (gold-standard audit)

The simulation captures **the settlement-floor math: `minBuyAmount`
(the post-#1283 CEIL chain mirroring TradeLib.prepareTradeSell lifted
into qBuyTok), `worstCasePrice` in D27, the `settle` function with
its `boughtAmt+1` / `max(soldAmt, 1)` defensive paddings, the
`settlement_floor` inversion theorem, the early-return when
`sellBalAfter >= initBal` (production line 219 guard), `canSettle`
gating, and `cancellationEndTime` formula**. It omits **the
`TradeStatus` state machine, the `init()` lifecycle (auction
creation via Gnosis EasyAuction, the `_sellAmount` fee-numerator
adjustment, the `minBuyAmtPerOrder` derivation, the `safeApprove`
allowance, the storage writes), the `transferToOriginAfterTradeComplete`
escape hatch, the `isAuctionCleared` view that reads
`gnosis.auctionData(auctionId)`, the broker / origin / gnosis
external pointers, and the safeTransfer side effects inside
`settle()`**. The proofs against this model are correct for the
settle math; transferring them requires (i) the trade is OPEN,
(ii) the caller is `origin`, (iii) the auction is cleared.

### State omitted

| Production state | Purpose | Simulation analog |
|---|---|---|
| `KIND` (constant `TradeKind.BATCH_AUCTION`) | Identifies auction kind | None. |
| `FEE_DENOMINATOR = 1000` | Used in `_sellAmount` adjustment for Gnosis fee | **`FEE_DENOMINATOR ✓`** as constant; not used in any sim function (header notes the post-#1175 fee-aware path is what the sim captures). |
| `CANCEL_WINDOW = 9e17` (D18) | First 90% of auction is cancellable | **`CANCEL_WINDOW ✓`** in `cancellationEndTime`. |
| `MAX_ORDERS = 5000` | Cap on auction order count for gas | None. |
| `DEFAULT_MIN_BID = FIX_ONE / 100` | Minimum bid floor used in `minBuyAmtPerOrder` | None. |
| `gnosis` (immutable IGnosis) | Gnosis EasyAuction contract | None. |
| `status` (TradeStatus) | NOT_STARTED → OPEN → PENDING → CLOSED state machine + reentrancy guard | **Modeled as boolean `status_open` in `canSettle`** — not as a full state machine. |
| `gnosis_DEPRECATED` (IGnosis) | Storage-compat slot from pre-4.0.0 (gnosis was non-immutable) | None. |
| `auctionId` (uint256) | Returned by `gnosis.initiateAuction()` | None. |
| `broker` (IBroker) | Cloning factory; `reportViolation` callback when clearingPrice < worstCasePrice | None. |
| `origin` (address) | The originating trader; only `origin` may call `settle()` | None. |
| `sell`, `buy` (IERC20Metadata) | Token pointers | None. |
| `initBal` (uint256, qSellTok) | Sell-token balance at `init()` | **Passed in as input to `settle`** — not stored in sim. |
| `sellAmount` (uint192, sellTok D18) | Whole-token sell quantity (≠ initBal due to fee adjustment) | **Implicit in `minBuyAmount`'s sellAmount input.** |
| `endTime` (uint48) | Timestamp after which the auction can be settled | **Passed as input to `canSettle`.** |
| `worstCasePrice` (uint192, D27) | Set in init(); checked in settle() | **Passed as input to `settle`.** |

### Operations omitted

| Production function | Effect | Modeled? |
|---|---|---|
| `init(IBroker broker_, address origin_, uint48 batchAuctionLength, TradeRequest req)` (line 91) — state-locked | Validates sell/min-buy ≤ uint96; computes `worstCasePrice = shiftl_toFix(req.minBuyAmount, 9).divu(req.sellAmount, FLOOR)`; computes `_sellAmount` adjusted for Gnosis fee; computes `minBuyAmtPerOrder`; calls `safeApproveFallbackToMax`; calls `gnosis.initiateAuction(...)`; stores `cancellationEndTime`, `endTime`, `auctionId`, sell/buy/origin/broker | **Partial.** The `worstCasePrice` formula is captured by sim's `worstCasePrice` (line 117). The `_sellAmount = req.sellAmount * FEE_DENOMINATOR / (FEE_DENOMINATOR + gnosis.feeNumerator())` fee-adjustment, `minBuyAmtPerOrder` derivation (max of `minBuyAmount / MAX_ORDERS` and `DEFAULT_MIN_BID.shiftl_toUint(buy.decimals())`), `safeApprove` allowance, `gnosis.initiateAuction` call, and storage writes are **all unmodeled**. |
| `settle()` (line 185) — state-locked, origin-only | Calls `gnosis.settleAuction(auctionId)` if not yet cleared; transfers sell/buy balances to origin; checks `clearingPrice < worstCasePrice` and calls `broker.reportViolation()` | **Partial.** The clearing-price math (`shiftl_toFix(adjustedBuyAmt, 9).divu(adjustedSoldAmt, FLOOR)`) and the violation comparison are captured in sim's `settle`. The `gnosis.settleAuction(auctionId)` call, the `assert(isAuctionCleared())` post-condition, the `safeTransfer(origin, sellBal)` and `safeTransfer(origin, boughtAmt)` interactions, the `broker.reportViolation()` callback, and the `require(msg.sender == origin)` auth gate are **all unmodeled**. |
| `transferToOriginAfterTradeComplete(IERC20)` (line 235) | Post-CLOSED escape hatch | **No.** |
| `canSettle()` (line 242) view | Returns `status == OPEN && endTime <= block.timestamp` | **`canSettle` ✓** as a pure predicate over `(now, endTime, status_open)`. |
| `isAuctionCleared()` (line 248) private view | Reads `gnosis.auctionData(auctionId).clearingPriceOrder != bytes32(0)` | **No** — sim assumes the auction has cleared and operates on post-clearance balances. |

### What the simulation *does* faithfully model

- `minBuyAmount(sellAmount, slippage, sellLow, buyHigh, buyDec)`: the full TradeLib chain into qBuyTok — `inner = mul(sellAmount, FIX_ONE - slippage, CEIL)`, `b = safeMulDiv_ceil(inner, sellLow, buyHigh)`, `shiftl_toUint_ceil(b, buyDec)`. All three rounding stages CEIL — bidder-favorable, keeping the settlement floor at-or-above the exact-rational ideal.
- `worstCasePrice(minBuyAmount_qBuy, sellAmount_qSell)`: the FLOOR-rounded `(minBuyAmount * 1e27) / sellAmount` (sim line 117–122). FLOOR is trader-favorable: lowers the floor by < 1 D27 wei.
- `settle(initBal, sellBalAfter, boughtAmt, worstCase)`: the `if (sellBal < initBal)` guard at production line 219 is the early-return at sim line 154. When the guard fires (i.e. the trade returned 100% of the sell tokens), `checked = false` and no violation check happens. Otherwise the sim computes `soldAmt = initBal - sellBalAfter`, `adjustedSoldAmt = max(soldAmt, 1)`, `adjustedBuyAmt = boughtAmt + 1`, `clearingPrice = (adjustedBuyAmt * 1e27) / adjustedSoldAmt FLOOR`, `violation = clearingPrice < worstCase`. The +1 / max(_, 1) defensive paddings exactly mirror production lines 222–227.
- `settlement_floor(worstCase, soldAmt)`: the inversion of the violation check — the minimum `boughtAmt` keeping `clearingPrice >= worstCasePrice` is `ceil(worstCasePrice * max(soldAmt, 1) / 1e27) - 1`, clamped at 0. This is the load-bearing post-condition for "successful settle implies trader was paid at least the floor".
- `cancellationEndTime(startTime, auctionLength) = startTime + auctionLength * CANCEL_WINDOW / FIX_ONE` (sim line 193–194 = production line 150–152).

### Implications for proof transferability

1. The most surprising divergence: `worstCasePrice` is set in `init()` from `req.minBuyAmount` (which is what TradeLib hands the broker). The sim's `worstCasePrice` is *parameterised* on the qBuy / qSell scalars rather than tied to the TradeLib chain — so a CAS-side counterexample (`CAS_additional_findings.v`) where production's `init()` passes a `req.minBuyAmount` that doesn't account for `gnosis.feeNumerator()` corresponds to an integration-level gap, not a sim-level one. Header is honest about this: "the simulation captures the post-fee-aware computation".
2. The full state machine (NOT_STARTED → OPEN → PENDING → CLOSED) is collapsed to a single boolean (`status_open` in `canSettle`). Lemmas about `settle` apply to *any* OPEN auction, regardless of whether the production state machine has performed the OPEN→PENDING transition (which is a reentrancy guard, not a substantive change to the math).
3. The `gnosis.settleAuction(auctionId)` external call at production line 197 is unmodeled. Sim's `settle` operates on post-clearance balances directly. Lemmas about settlement assume the Gnosis-side cleared correctly; failure modes there (auction not cleared, bytes32(0) `clearingPriceOrder`) are out of scope.
4. The `safeTransfer(origin, sellBal)` / `safeTransfer(origin, boughtAmt)` interactions at production lines 215–216 are unmodeled. Lemmas about settle bookkeeping say nothing about whether the funds actually reach origin — only about the violation flag.
5. The `_sellAmount` fee-adjustment in `init()` (production lines 119–125: `_sellAmount = req.sellAmount * FEE_DENOMINATOR / (FEE_DENOMINATOR + gnosis.feeNumerator())`) reduces what's sent to Gnosis to compensate for the fee that Gnosis takes. Sim does not model this; the `worstCasePrice` is computed from `req.minBuyAmount` and `req.sellAmount` (the originator-side numbers), not from `_sellAmount` (the post-fee number). This is the bug pinned in `proofs/CAS_additional_findings.v`.
6. The `broker.reportViolation()` callback is unmodeled — lemmas about violation surface a boolean flag, not the broker side effect.
7. The `cancel`-window enforcement is partially modeled: `cancellationEndTime` is computed but the actual revert path inside Gnosis (when cancellation is attempted past it) lives outside this simulation.

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
