# Solidity harnesses for solc-rocq translation

Solidity input fixtures for the auto-translation pipeline. Not deployed
contracts. These files exist solely as inputs to `solc --ir-rocq`, which
emits Yul-derived Rocq from each top-level contract. See
`../README.md` for the dual-track Rocq + CAS methodology these
harnesses feed into.

The harnesses are deliberately minimal: storage + constructor +
non-pure external entry points, no inheritance, single-line function
signatures. That shape is what the upstream `rocq-of-solidity`
optimizer can ingest reliably; deviation triggers a `std::length_error`
crash in solc-rocq.

## Layout

```
contracts/
├── ThrottleHarness.sol         -- wraps ThrottleLib.useAvailable
├── FurnaceMathHarness.sol      -- wraps Furnace's payoutRatio + amount math
├── BackingManagerMathHarness.sol  -- forwardRevenue accounting
├── DistributorMathHarness.sol  -- distributeAmounts share split
├── StandaloneThrottle.sol      -- self-contained Throttle (no _relaxed/ deps)
└── _relaxed/                   -- pragma-relaxed copies (^0.8.28) of FixLib + Throttle
```

Investigation artifacts (`_probe/`) used to characterize the
`solc-rocq` optimizer crash surface live under
[`../notes/probes/`](../notes/probes/), not here.

## Why `_relaxed/` exists

The production `Fixed.sol` and `Throttle.sol` declare `pragma solidity
0.8.28` (exact). The locally-built `solc-rocq` reports its version as
`0.8.29-develop` and refuses files pinned to a different exact version.
Rather than fight the version check, `_relaxed/` holds copies pragma'd to
`^0.8.28` so the harnesses can `import "./_relaxed/Fixed.sol"`. The
content is identical to the production source. Only the pragma differs.

## Why these files don't follow project lint style

Listed in `../../.solhintignore`. The shape constraints from `solc-rocq`
override the project's prettier/solhint rules. Single-line function
signatures often exceed 100 chars, and the `_relaxed/Fixed.sol` copy
inherits the visibility-marker omissions that the production file
already gets exempted for.

## Translating

```sh
# From formal-verification/, with Docker (rocq-build:full image)
# running on the colima-rocq context:
bash scripts/solc-rocq contracts/ThrottleHarness.sol --ir-rocq
```

Output lands in `../rocq/<HarnessName>.v` as auto-generated Yul-derived
Rocq. These files are **not committed**: they are regenerable, not
referenced by the active proof tree, and would add ~10K lines of
auto-generated content for an unused workstream. The Yul-equivalence
work that would consume them is parked (see `../README.md`).

## Adding a new harness

1. Write the harness as a single contract with constructor + a small
   surface of `external` entry points. Do not inherit; flatten.
2. Keep all function signatures on a single line; the optimizer
   crashes on multi-line signatures in non-trivial cases.
3. Test the build: `bash scripts/solc-rocq contracts/<NewHarness>.sol --ir-rocq`.
4. If solc-rocq crashes, see [`../notes/probes/`](../notes/probes/) for
   the existing bisect probes and add a new one isolating the
   triggering construct.
