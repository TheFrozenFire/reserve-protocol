# Dual-track verification: Rocq + CAS for Reserve smart contracts

## Why two layers

A formal verification effort has two distinct failure modes:

1. **Logical unsoundness** — the proof has a hole, the lemma chain doesn't actually establish what it claims. Caught by an interactive theorem prover (Rocq, Lean).
2. **Modeling error** — the proof is impeccable, but the abstract model the proof reasons about doesn't faithfully capture what the production code does. Caught by running both models on calibrated inputs and checking they agree.

These are **orthogonal**. A protocol can have a beautiful Rocq proof of a vacuous claim, or a perfect numerical match against a buggy specification. The dual-track pattern bracket the same property from two sides:

- The **Rocq layer** (`rocq/`) proves *logical soundness*: under the assumptions of the model, the invariant holds for all inputs.
- The **CAS layer** (`cas/`) validates *faithfulness*: the claimed identities and bounds actually agree with concrete computation across calibrated parameters.

This pattern transfers cleanly to smart contract math because:

- Smart contract math is integer / fixed-point arithmetic, which PARI/GP handles natively as exact rationals.
- Calibration data (RToken supplies, basket parameters, fee ratios) is already in-tree (`deployments.json`, governance configs).
- The historically dominant bug class for SC math libraries is *boundary anomalies in fixed-point arithmetic* — the exact class CAS is best at finding.

## Where each layer applies

| Domain | Rocq | CAS | Why |
|---|---|---|---|
| FixLib (`Fixed.sol`) | ✓ | ✓✓ | Pure functions; CAS sweeps boundary corpora trivially. Complements the Certora FixLib audit on master. |
| Throttle (`Throttle.sol`) | ✓ | ✓ | State machine over time; Rocq for the invariants, CAS for overflow analysis and time monotonicity. |
| Furnace, StRSR | ✓ | ✓ | Compound-payout identity `1 - (1-r)^N`; CAS validates against geometric simulation. |
| Rebalance / RebalancingLib | ✓ | ✓✓ | Fuzz harness is currently fighting hand-tuned rounding bound; CAS surfaces the closed form, Rocq proves it. |
| Distributor share splits | ✓ | ✓ | Share-conservation under arbitrary distributions. |
| BackingManager state machine | ✓✓ | – | Cross-component lifecycle invariants — Rocq territory. |
| Reentrancy / access control | ✓✓ | – | Control-flow, not algebraic. CAS doesn't see call stacks. |
| Cross-contract storage coupling | ✓✓ | – | Same as above. |

(✓ = applies; ✓✓ = primary tool; – = doesn't apply)

## How a property graduates between layers

A property typically progresses:

1. **Audit-style witness** (one concrete input, e.g. the Certora FixLib regression cases). Lives in `test/libraries/Fixed.test.ts` as a hand-written `it()` block.
2. **CAS-derived witness corpus**. Generalize the audit witness to an equivalence class via PARI/GP boundary sweep. Pick the cleanest representative (`safeMulDiv(2^96, 2^96, 1, CEIL) == FIX_MAX` instead of the audit's `2^191+1, 2^192-2, 2^127`). Emit a Foundry `.t.sol` via `cas/_export/foundry_regression_corpus.gp`.
3. **Rocq simulation lemma**. Hand-write the contract's clean functional model in `rocq/simulations/`; prove the invariant on the simulation. The simulation is typed; mistakes show up at type-check time before any proof effort.
4. **Yul-translation equivalence**. Run `solc --ir-rocq` to emit the low-level translation, then prove `run_<fn>` lemmas connecting the Yul-derived monadic Rocq to the simulation. The CAS witnesses double as sanity tests for the translation: production Solidity, CAS PARI/GP, and Rocq simulation must all agree on the witness inputs.
5. **CI gate**. The Foundry regression test runs in CI; the CAS suite runs via `./run-check.sh`; the Rocq proofs compile under `rocq -Q ... .v` and any future change to the contract that breaks the lemma fails the build.

## Property catalog

The Rocq tree organizes proofs into seven tiers per domain:

| Tier | File pattern | Role |
|---|---|---|
| Simulation | `rocq/simulations/<Domain>.v` | Clean Gallina spec of the contract operations |
| Invariants | `rocq/proofs/<Domain>.v` | Per-operation correctness lemmas |
| Cross-checks | `rocq/proofs/<Domain>_xcheck.v` | `vm_compute; reflexivity` against CAS witness values |
| Validity preservation | `rocq/proofs/<Domain>_validity.v` | Operation preserves `Valid.t` |
| Composition | `rocq/proofs/<Domain>_chain.v` | Multi-step preservation (e.g. `setRatio → melt`) |
| Witnesses | `rocq/proofs/<Domain>_witnesses.v` | Boundary-point reflex theorems |
| uint256 bounds | `rocq/proofs/<Domain>_uint256_bounds.v` | Storage-state ceiling derivations |

Above the per-domain tiers:

| File | Role |
|---|---|
| `rocq/proofs/Integration_*.v` | Cross-domain composition (revenue path, supply decay, unstake lifecycle, etc.) |
| `rocq/proofs/EndToEnd*.v` | System-level joint invariants combining 8 (storage) or 13 (storage + functional) domains |
| `rocq/proofs/Distributor_deprecation_bug.v` | PR #1285 sequencing failure formalized as a counterexample theorem |
| `rocq/proofs/CAS_additional_findings.v` | Auction-fee `reportViolation` gap (governance-conditional) |
| `rocq/Audit.v` | Top-level handoff index — `Notation`-aliases for the load-bearing theorems by audit-friendly names |

Coverage is dense: every domain has all seven tiers populated. The CAS
layer has 26 scripts; the Rocq layer cross-checks each via either a
`_xcheck.v` or `_witnesses.v` file. Numerical drift between the two
layers fails the build.

For a navigation start, read `rocq/Audit.v` from the top — it surfaces
the most decision-relevant theorems in 7 sections.

## Layout

```
formal-verification/
├── README.md                    -- this file (methodology + layout + build)
├── contracts/                   -- Solidity harnesses for solc --ir-rocq
│   ├── _relaxed/                -- pragma-relaxed copies (^0.8.28) of FixLib + ThrottleLib
│   ├── ThrottleHarness.sol
│   ├── FurnaceMathHarness.sol
│   └── ...                      -- one harness per domain
├── cas/                         -- PARI/GP scripts
│   ├── README.md
│   ├── WISDOM.md
│   ├── run-check.sh             -- runs the suite (26 scripts)
│   ├── fixlib/                  -- 4 scripts
│   ├── throttle/                -- 1 script
│   ├── furnace/                 -- 1 script
│   ├── rebalance/               -- 3 scripts
│   ├── strsr/                   -- 2 scripts
│   ├── distributor/             -- 1 script
│   ├── trade_lib/               -- 2 scripts
│   ├── dutch_trade/             -- 2 scripts
│   ├── gnosis_trade/            -- 2 scripts
│   ├── basket_handler/          -- 2 scripts
│   ├── backing_manager/         -- 2 scripts
│   ├── collateral/              -- 2 scripts
│   ├── issuance_premium/        -- 1 script
│   ├── deprecation/             -- 1 script
│   └── _export/                 -- meta: emits Foundry .t.sol from CAS witnesses
├── rocq/
│   ├── _RocqProject             -- coqc load paths and target list
│   ├── Audit.v                  -- handoff index of audit-relevant theorems
│   ├── simulations/             -- 13 Gallina specs
│   ├── proofs/                  -- per-tier proof files (~100 files)
│   └── <auto-translated harnesses>.v  -- output of solc --ir-rocq
└── scripts/
    └── rocq-build               -- one-command compile of the proof tree
```

## Building

The Rocq layer compiles natively (no Docker) once an `opam` switch with
Coq 8.20.1 + `coq-hammer-tactics` + `coq-coqutil` + `coq-record-update`
is installed alongside the upstream `rocq-of-solidity` library:

```sh
opam switch create rocq820 ocaml-base-compiler.4.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.1 coq-hammer-tactics coq-coqutil coq-record-update
bash scripts/rocq-build           # compiles the whole tree (~3 min)
bash cas/run-check.sh             # runs the 26 CAS scripts (~10 sec)
```

Docker is used only for the `solc-rocq` auto-translation runs (the path
that emits the Yul-derived Rocq from `contracts/<Harness>.sol`). The
proof compilation and CAS suite both run natively.

## Parked workstreams

Two extension paths were investigated and parked with diagnostic notes:

1. **Yul-equivalence proofs** (`run_<fn>` lemmas tying the simulations
   to the auto-translated Yul-derived Rocq) need an upstream change in
   `rocq-of-solidity`: the runtime substrate has no `Impossible`
   constructor in `RunO.t`, so any function reading `block.timestamp`
   has no inhabitant of the equivalence predicate. Even pure FixLib
   functions are blocked structurally, since the harness translations
   don't emit shallow companion files (the upstream ERC20 sample does).
2. **Auto-translation campaign** beyond the math harnesses: `solc-rocq`
   exhibits unpredictable optimizer crashes on broader Solidity inputs.
   The harness-shape strategy (storage + constructor + non-pure external
   entry points, no inheritance) is what makes the current translations
   reliably emit. Translating, e.g., the full RToken contract would
   require either a bug-fix campaign upstream or hand-written
   simplifications.
