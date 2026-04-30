# Notes — investigation artifacts and parked-workstream diagnostics

Material that doesn't belong in `cas/`, `contracts/`, or `rocq/` but is
worth keeping for future contributors.

## Diagnostics

- [`yul_equivalence_diagnostic.md`](yul_equivalence_diagnostic.md) —
  why Yul-equivalence proofs (`run_<fn>` lemmas tying the auto-translated
  Yul-derived Rocq to the simulation) are currently blocked. Two
  distinct substrate gaps documented (semantic timestamp gap; structural
  shallow-companion-file gap). Concrete unblocking steps listed.

## Bisect probes (`probes/`)

Single-function Solidity contracts used to bisect which constructs trip
`solc-rocq`'s optimizer. Each file isolates one variable so a fresh
optimizer crash on a new harness can be cornered quickly. Useful as
upstream-bug-report fodder if you hit a fresh optimizer crash.
