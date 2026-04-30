# Rocq proof tree

Machine-checked Rocq (Coq 8.20.1) proofs covering Reserve's smart-contract
math libraries and core domain logic. Pairs with the `cas/` algebraic
verification suite next to it: CAS finds boundary witnesses; Rocq pins
them as numerical reflex theorems and proves the surrounding invariants
formally.

860 statements (Lemma + Theorem + audit Notation), zero admits, ~3:45
clean rebuild on Apple Silicon native (no Docker). See `../README.md`
for the dual-track methodology.

## Start here

`Audit.v` is the navigation entry point. It re-exports the load-bearing
theorems via `Notation` under audit-friendly names, organized into 7
sections (bug findings, Certora mitigation, Throttle safety, Furnace
correctness, Distributor conservation, Collateral state machine,
system-level joint invariant). Compiles in <1 second; reads top-down.

For a deeper read, the per-domain proof tier is laid out below.

## Layout

```
rocq/
├── Audit.v                       -- handoff index of audit-relevant theorems
├── _RocqProject                  -- coqc load paths and target list
├── simulations/                  -- Gallina specs (one file per domain)
│   ├── Throttle.v       Fixed.v        Furnace.v
│   ├── Distributor.v    BackingManager.v   Rebalance.v
│   ├── StRSR.v          TradeLib.v         BasketHandler.v
│   ├── DutchTrade.v     GnosisTrade.v      Collateral.v
│   └── IssuancePremium.v
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

Coverage is full across 13 domains: Throttle, Fixed, Furnace,
Distributor, BackingManager, Rebalance, StRSR, TradeLib, BasketHandler,
DutchTrade, GnosisTrade, Collateral, IssuancePremium.

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

## Discipline (worth knowing if you add files here)

- **Mark FixLib operations `Opaque` before destructs.** The simulation's
  `powu` definition contains `Z.to_nat (Z.log2 _)` which Coq tries to
  reduce eagerly during `inversion`. The result is OOM. Before any
  `injection`/`destruct` of a hypothesis like `melt s now bal = (s', amt)`,
  declare `Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd`.
- **Use `injection ... as Hs'_eq Hamt_eq; subst <name>` over `inversion ... subst`.**
  The latter does maximal substitution and forces evaluation of the giant
  arithmetic expressions; the former keeps them behind named hypotheses.
- **Do NOT install `Z.to_euclidean_division_equations` zify hook.**
  It explodes `lia` runtime on these proofs.
- **Module-name collisions** are common when both `Reserve.simulations.X`
  and `Reserve.proofs.X` are in scope. The Rocq compiler rejects bare
  `Import X` as ambiguous. Fully qualify: `Import Reserve.simulations.X.X`
  and `Import Reserve.proofs.X.XProofs`.
- **`Notation` not `Theorem ... :=` for re-exports.** Coq's `Theorem`
  with `:=` requires a type annotation; `Notation` gives lossless
  re-export with the original type preserved.

## Parked workstreams

Two paths were investigated and parked with diagnostic notes (see
`../README.md` for full details):

1. **Yul-equivalence proofs** (`run_<fn>` lemmas tying the simulations
   to the auto-translated Yul-derived Rocq) need an upstream change in
   `rocq-of-solidity`: the runtime substrate has no `Impossible`
   constructor in `RunO.t`. Even pure FixLib functions are blocked
   structurally — the harness translations don't emit shallow companion
   files. See `proofs/Fixed_yul_equiv.v` (off the build) for the
   diagnosis.
2. **Auto-translation campaign** beyond the math harnesses: `solc-rocq`
   exhibits unpredictable optimizer crashes on broader Solidity inputs.
