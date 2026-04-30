# Rocq proof tree

Machine-checked Rocq (Coq 8.20.1) proofs covering Reserve's smart-contract
math libraries and core domain logic. Pairs with the `cas/` algebraic
verification suite next to it: CAS finds boundary witnesses; Rocq pins
them as numerical reflex theorems and proves the surrounding invariants
formally.

Zero admits across the tree (the CI workflow grep-checks this). See
`../README.md` for the dual-track methodology.

## Start here

`Audit.v` is the navigation entry point. It re-exports the load-bearing
theorems via `Notation` under audit-friendly names, organized by
section: bug findings, Certora mitigation, Throttle safety, Furnace
correctness, Distributor conservation, Collateral state machine, and
the system-level joint invariant. Reads top-down.

For a deeper read, the per-domain proof tier is laid out below.

## Layout

```
rocq/
├── Audit.v                       -- handoff index of audit-relevant theorems
├── _RocqProject                  -- coqc load paths and target list
├── simulations/                  -- Gallina specs (one file per domain)
└── proofs/
    ├── <Domain>.v                -- per-operation correctness invariants
    ├── <Domain>_xcheck.v         -- vm_compute reflexivity vs CAS witnesses
    ├── <Domain>_validity.v       -- operation preserves Valid.t
    ├── <Domain>_chain.v          -- multi-step preservation (composition)
    ├── <Domain>_witnesses.v      -- boundary-point reflex theorems
    ├── <Domain>_uint256_bounds.v -- storage-state ceiling derivations
    ├── Fixed_*.v                 -- algebraic kernel (algebra, safety,
    │                                chain_extras, mul_mode_witnesses,
    │                                safe_div_witnesses, etc.)
    ├── Integration_*.v           -- cross-domain composition
    ├── EndToEnd*.v               -- system-level joint invariants
    ├── Distributor_deprecation_bug.v   -- PR #1285 counterexample theorem
    └── CAS_additional_findings.v -- governance-conditional auction-fee gap
```

## Per-domain proof tier

Every domain has up to seven tiers of proofs:

| Tier | File pattern | Role |
|---|---|---|
| Simulation | `simulations/<Domain>.v` | Clean Gallina spec of the contract operations |
| Invariants | `proofs/<Domain>.v` | Per-operation correctness lemmas |
| Cross-checks | `proofs/<Domain>_xcheck.v` | `vm_compute; reflexivity` against CAS witness values |
| Validity preservation | `proofs/<Domain>_validity.v` | Operation preserves `Valid.t` |
| Composition | `proofs/<Domain>_chain.v` | Multi-step preservation (e.g. `setRatio → melt`) |
| Witnesses | `proofs/<Domain>_witnesses.v` | Boundary-point reflex theorems |
| uint256 bounds | `proofs/<Domain>_uint256_bounds.v` | Storage-state ceiling derivations |

Domains covered: Throttle, Fixed, Furnace, Distributor, BackingManager,
Rebalance, StRSR, TradeLib, BasketHandler, DutchTrade, GnosisTrade,
Collateral, IssuancePremium. Every domain has all seven tiers populated.

## Build

```sh
# One-time setup:
opam switch create rocq820 ocaml-base-compiler.4.14.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.1 coq-hammer-tactics coq-coqutil coq-record-update

# Compile the whole tree (from formal-verification/):
bash scripts/rocq-build           # ~3:45 native, no Docker

# Compile one file:
bash scripts/rocq-build proofs/Throttle.v
```

The `_RocqProject` is the build manifest. Order matters for cross-file
dependencies: simulations precede their proofs; per-domain proofs precede
the integration files; integration files precede `EndToEnd*.v`.

## Adding files / proof discipline

Proof-discipline gotchas (how to avoid OOM on `powu`, when to use
`injection` over `inversion`, module-name collision handling, the
`Notation` re-export pattern, etc.) are collected in
[`WISDOM.md`](WISDOM.md). Read it before adding new `.v` files.

## Parked workstreams

Two paths were investigated and parked with diagnostic notes:

1. **Yul-equivalence proofs** (`run_<fn>` lemmas tying the simulations
   to the auto-translated Yul-derived Rocq) need upstream changes in
   `rocq-of-solidity` (semantic + structural substrate gaps). Full
   diagnosis in
   [`../notes/yul_equivalence_diagnostic.md`](../notes/yul_equivalence_diagnostic.md).
2. **Auto-translation campaign** beyond the math harnesses: `solc-rocq`
   exhibits unpredictable optimizer crashes on broader Solidity inputs.
