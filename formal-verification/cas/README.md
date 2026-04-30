# cas/ — Algebraic Verification (PARI/GP) for Reserve smart contracts

Symbolic and numerical computations that cross-check claims about contract
math the Rocq layer proves formally. PARI/GP runs each script in seconds;
failures surface as concrete witnesses ready to drop into Foundry or
Hardhat as regression tests.

Run the suite:

```sh
./run-check.sh
```

Each script is self-contained. `gp -q < script.gp` runs one in isolation.

## Why CAS in addition to Rocq?

- **Rocq layer** (`../rocq/`): proves logical soundness of the Reserve
  math. Per-domain Gallina simulations, invariant lemmas, validity
  preservation, and a system-level joint bound — see `../rocq/README.md`.
- **CAS layer** (here): validates that the model the Rocq proof reasons
  about matches the production contract's semantics, by exact-rational
  computation over calibrated inputs.

These cover orthogonal failure modes: a Rocq proof can be impeccable yet
verifying the wrong model; a CAS sweep can catch boundary anomalies before
any proof is attempted. Together they bracket the same claim from two
sides. The `_xcheck.v` and `_witnesses.v` files under `../rocq/proofs/`
pin specific CAS-found values as `vm_compute; reflexivity` theorems —
numerical drift between the layers fails the build.

## Coverage

### `fixlib/` — FixLib boundary anomalies

| File | Probes |
|------|--------|
| `safe_muldiv_certora_witness.gp` | Replays Certora finding #1 (`safeMulDiv` → 0 instead of FIX_MAX). Generates a 4,753-element boundary corpus; minimum-overflow witness is `safeMulDiv(2^96, 2^96, 1, CEIL) = FIX_MAX`. |
| `safe_div_propagation.gp` | Replays Certora finding #2 (FIX_MAX must propagate through `safeDiv`). Sweep shows the bug-affected region is the entire `b ≥ FIX_ONE` range; magnitude scales with `1/b`. |
| `mul_rounding_direction.gp` | Default-rounding change `mul(x,y) := mul(x,y,FLOOR)`. Density measurement: 49.3% of random uint192 pairs disagree under ROUND vs FLOOR; gap is always exactly 1 wei. |
| `powu_correctness.gp` | Validates `FixLib.powu` (fixed-point exponentiation by squaring) at canonical inputs and boundary cases (`x = 0`, `x = FIX_ONE`, `y = 0`, `y = 1`); cross-checks against analytic `1 - (1-r)^N` over N up to 10000. |

### `throttle/` — ThrottleLib invariants

| File | Probes |
|------|--------|
| `cap_invariant.gp` | INV-1 (cap), INV-3 (positive use decreases by amount), INV-5 (revert iff overdraw), monotonicity in time. Overflow analysis: `4.11e29` safety margin between practical limits and uint256 bounds. |

### `rebalance/` — RebalancingLib basket-range bound

| File | Probes |
|------|--------|
| `basket_range_noise.gp` | Validates the `roundingNoise = bl * (mtv*FIX_ONE/buPriceHigh + bl) + 2` heuristic used by `BackingManagerP1Fuzz.isBasketRangeSmaller` on `origin/fuzz`. Tightness ratios across calibrated parameter grids identify regions where the harness skip-check fires (effectively bypassing the property check). |

### `strsr/` — StRSR exchange-rate accounting

| File | Probes |
|------|--------|
| `exchange_rate_evolution.gp` | Stake invariant `stakeRSR * stakeRate ≥ totalStakes * FIX_ONE`, era-reset trigger (boundary at `newRSR ≤ 1e15` wei), compound-payout identity `1 - (1-r)^N` ≡ geometric pool decay (verified zero wei difference at N=10). |
| `withdrawal_queue.gp` | FIFO ordering of unstake withdrawals; `stakeRSR + queueRSR` conservation across unstake; round-trip exactness for stake → unstake at fixed exchange rate. |

### `furnace/` — Furnace melt curve

| File | Probes |
|------|--------|
| `melt_curve.gp` | Compound-payout identity for the RToken burn rate: `payoutAmount = bal * (1 - (1-r)^N)` matches geometric pool decay; `payoutRatio ≤ FIX_ONE` cap; verified to within 9.7e-16 relative error vs analytic geometric simulation. |

### `distributor/` — revenue split conservation

| File | Probes |
|------|--------|
| `share_conservation.gp` | `sum(transferAmts) + dust = amount` exactly across canonical Reserve distribution tables, prime-share dust calculations, and boundary cases (single destination, all-zero shares, sub-totalShares amounts). |

### `trade_lib/` — buyAmount and slippage

| File | Probes |
|------|--------|
| `slippage_sufficiency.gp` | `buyAmount` lower-bound holds across the slippage range \[0%, FIX_ONE); calibrated against canonical (sellLow, buyHigh) inputs. |
| `ceil_rounding_witness.gp` | The Certora #1283 mitigation witness: post-fix `buyAmount` strictly exceeds the pre-fix value at canonical inputs by exactly 1 wei. |

### `dutch_trade/` — Dutch auction price decay

| File | Probes |
|------|--------|
| `price_decay.gp` | Phase-by-phase price-decay schedule (phase 1 starts at ~1000× best price, phase 4 saturates at worst); `bidPrice` boundaries at progression 20%/45%/95%/100%. |
| `bid_rounding.gp` | FLOOR vs CEIL `bidAmount_at_price` divergence at minimum-price 6-decimal (USDC) and 18-decimal scenarios; the gap is bounded by 1 wei but the rounding direction must favor the seller. |

### `gnosis_trade/` — auction settlement

| File | Probes |
|------|--------|
| `min_buy_amount.gp` | `worstCasePrice` calculations across canonical (mba, sa) inputs; section (6) characterizes the **governance-conditional auction-fee gap** — when `feeNumerator > 0`, the effective ratio diverges from `worstCasePrice` by a deterministic monotone amount. |
| `settlement_floor.gp` | `settlement_floor` computation; `canSettle` boundary witnesses (inclusive boundary, +1 pad absorbs minBuy-1, exhausts at minBuy-2); cancellationEndTime offset behavior. |

### `basket_handler/` — quote rounding

| File | Probes |
|------|--------|
| `quote_rounding_direction.gp` | FLOOR vs CEIL `quote_one` divergence at non-exact-divides; the gap is bounded by 1 wei and CEIL is required to match production. |
| `quote_round_trip.gp` | `quote → redeem` round-trip identity at `refPerTok = FIX_ONE`; lossy non-extraction at sub-basket amounts; linearity of `quoteQuantities` in baskets. |

### `backing_manager/` — forwardRevenue accounting

| File | Probes |
|------|--------|
| `forward_revenue_conservation.gp` | `computeSurplusSplit` outputs (`rsrAmount + rTokenAmount + dust = delta`) at canonical (delta, totalShares) inputs, including off-by-multiple cases. |
| `backing_buffer_ceil_witness.gp` | Certora-audited buffer math `needed = basketsNeeded.mul(FIX_ONE + backingBuffer, CEIL)`; pinpoints the smallest input where CEIL strictly exceeds FLOOR (the post-#1283 mitigation surface). |

### `collateral/` — status state machine and refPerTok monotonicity

| File | Probes |
|------|--------|
| `status_state_machine.gp` | SOUND ↔ IFFY ↔ DISABLED transitions across `softDefault` / `hardDefault` / `cure` paths; DISABLED is terminal; IFFY → DISABLED after `delayUntilDefault`. |
| `ref_per_tok_monotonicity.gp` | Cached `refPerTokMax` is non-decreasing across `refresh` calls; underlying refPerTok dropping below cached max triggers hard default. |

### `issuance_premium/` — under-peg premium curve

| File | Probes |
|------|--------|
| `premium_curve.gp` | Premium values at canonical RToken-deployment peg points (USDC at 0.99/0.95, FRAX at 0.998, LUSD at 0.995); saturation at FIX_MAX; fall-through paths when `enable=false` or `lastSave` is stale. |

### `deprecation/` — RToken deprecation script audit

| File | Probes |
|------|--------|
| `rtoken_deprecation.gp` | Discovered the **PR #1285 sequencing bug**: `setDistribution(FURNACE, (0,0))` before `setDistribution(ST_RSR, (0, 10000))` reverts because the intermediate state has cumulative `rTokenDist = 0 < MAX_DISTRIBUTION = 10000`. Pinned as a Rocq counterexample theorem in `../rocq/proofs/Distributor_deprecation_bug.v`. |

### `rebalance/` (additional)

| File | Probes |
|------|--------|
| `noise_bound_tightness.gp` | Tightness analysis of the `roundingNoise` heuristic across calibrated parameter grids; identifies grid points where the bound is loose by orders of magnitude. |
| `basket_range_simulation.gp` | Numerical `basketRange` simulation at calibration matching the on-chain RebalancingLib computation. |

## Adding a new script

1. Place under `<domain>/<name>.gp`.
2. Each invariant probe should print `OK` or `FAIL` so `run-check.sh` can detect failure via grep.
3. Use exact rationals where possible; force float arithmetic only at I/O boundaries (multiply by `1.0` immediately before a `printf("%f", ...)`, never inside the verification computation itself).
4. Add the path to the `scripts=( ... )` array in `run-check.sh`.
5. Cross-reference the production source line in a header comment so future
   readers can verify the script tracks the contract.
