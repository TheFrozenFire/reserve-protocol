# Notes — investigation artifacts and parked-workstream diagnostics

Material that doesn't belong in `cas/`, `contracts/`, or `rocq/` but is
worth keeping for future contributors. Three categories:

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

## Parked workstreams (overview)

For each parked workstream, the parent `../README.md` carries the
high-level "why parked." The notes here are the engineering details
that are too long for a top-level README but too important to lose.
