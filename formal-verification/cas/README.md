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

## Why CAS in addition to FV?

- **Rocq layer** (planned): proves logical soundness of the Reserve math.
- **CAS layer** (here): validates that the model the Rocq proof reasons
  about matches the production contract's semantics, by exact-rational
  computation over calibrated inputs.

These cover orthogonal failure modes: a Rocq proof can be impeccable yet
verifying the wrong model; a CAS sweep can catch boundary anomalies before
any proof is attempted. Together they bracket the same claim from two
sides.

## Coverage

### `fixlib/` — FixLib boundary anomalies

| File | Probes |
|------|--------|
| `safe_muldiv_certora_witness.gp` | Replays Certora finding #1 (`safeMulDiv` → 0 instead of FIX_MAX). Generates a 4,753-element boundary corpus; minimum-overflow witness is `safeMulDiv(2^96, 2^96, 1, CEIL) = FIX_MAX`. |
| `safe_div_propagation.gp` | Replays Certora finding #2 (FIX_MAX must propagate through `safeDiv`). Sweep shows the bug-affected region is the entire `b ≥ FIX_ONE` range; magnitude scales with `1/b`. |
| `mul_rounding_direction.gp` | Default-rounding change `mul(x,y) := mul(x,y,FLOOR)`. Density measurement: 49.3% of random uint192 pairs disagree under ROUND vs FLOOR; gap is always exactly 1 wei. |

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

## Adding a new script

1. Place under `<domain>/<name>.gp`.
2. Each invariant probe should print `OK` or `FAIL` so `run-check.sh` can detect failure via grep.
3. Use exact rationals where possible; force float arithmetic only at I/O boundaries (multiply by `1.0` immediately before a `printf("%f", ...)`, never inside the verification computation itself).
4. Add the path to the `scripts=( ... )` array in `run-check.sh`.
5. Cross-reference the production source line in a header comment so future
   readers can verify the script tracks the contract.
