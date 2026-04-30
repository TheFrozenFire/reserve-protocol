# Dual-track verification: Rocq + CAS for Reserve smart contracts

## Why two layers

A formal verification effort has two distinct failure modes:

1. **Logical unsoundness**: the proof has a hole, the lemma chain doesn't actually establish what it claims. Caught by an interactive theorem prover (Rocq, Lean).
2. **Modeling error**: the proof is impeccable, but the abstract model the proof reasons about doesn't faithfully capture what the production code does. Caught by running both models on calibrated inputs and checking they agree.

These are **orthogonal**. A protocol can have a beautiful Rocq proof of a vacuous claim, or a perfect numerical match against a buggy specification. The dual-track pattern bracket the same property from two sides:

- The **Rocq layer** (`rocq/`) proves *logical soundness*: under the assumptions of the model, the invariant holds for all inputs.
- The **CAS layer** (`cas/`) validates *faithfulness*: the claimed identities and bounds actually agree with concrete computation across calibrated parameters.

This pattern transfers cleanly to smart contract math because:

- Smart contract math is integer / fixed-point arithmetic, which PARI/GP handles natively as exact rationals.
- Calibration data (RToken supplies, basket parameters, fee ratios) is already in-tree (`deployments.json`, governance configs).
- The historically dominant bug class for SC math libraries is *boundary anomalies in fixed-point arithmetic*. That's the exact class CAS is best at finding.

## Where each layer applies

| Domain | Rocq | CAS | Why |
|---|---|---|---|
| FixLib (`Fixed.sol`) | ✓ | ✓✓ | Pure functions; CAS sweeps boundary corpora trivially. Complements the Certora FixLib audit on master. |
| Throttle (`Throttle.sol`) | ✓ | ✓ | State machine over time; Rocq for the invariants, CAS for overflow analysis and time monotonicity. |
| Furnace, StRSR | ✓ | ✓ | Compound-payout identity `1 - (1-r)^N`; CAS validates against geometric simulation. |
| Rebalance / RebalancingLib | ✓ | ✓✓ | Basket-range rounding bounds: CAS surfaces the closed form, Rocq proves it. |
| Distributor share splits | ✓ | ✓ | Share-conservation under arbitrary distributions. |
| BackingManager state machine | ✓✓ | – | Cross-component lifecycle invariants; Rocq territory. |
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

The Rocq tree organizes proofs into seven per-domain tiers (simulation,
invariants, cross-checks, validity preservation, composition,
witnesses, uint256 bounds) plus cross-domain integration files and two
system-level joint-invariant theorems. Coverage is dense: every
domain has all seven tiers populated. Two formalized bug findings
(PR #1285 deprecation sequencing; governance-conditional auction-fee
`reportViolation` gap) are pinned as machine-checked counterexample
theorems.

For the per-tier file-pattern table, navigation guidance, and proof
discipline notes, see [`rocq/README.md`](rocq/README.md). For a
navigation start, read [`rocq/Audit.v`](rocq/Audit.v) from the top:
it surfaces the most decision-relevant theorems in 7 sections.

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
│   ├── README.md                -- proof-tree navigation + per-tier table
│   ├── WISDOM.md                -- proof-discipline gotchas for contributors
│   ├── _RocqProject             -- coqc load paths and target list
│   ├── Audit.v                  -- handoff index of audit-relevant theorems
│   ├── simulations/             -- 13 Gallina specs
│   ├── proofs/                  -- per-tier proof files (~100 files)
│   └── <auto-translated harnesses>.v  -- output of solc --ir-rocq
├── notes/                       -- investigation artifacts + parked-
│   ├── README.md                   workstream diagnostics
│   ├── yul_equivalence_diagnostic.md
│   └── probes/                  -- bisect probes for solc-rocq optimizer
└── scripts/
    └── rocq-build               -- one-command compile of the proof tree
```

## Building

The Rocq layer compiles natively (no Docker) once Coq 8.20.1 plus
`coq-hammer-tactics`, `coq-coqutil`, `coq-record-update` are installed
alongside a built upstream `rocq-of-solidity` checkout. The CAS layer
needs PARI/GP. Once the prerequisites are in place:

```sh
# from formal-verification/, with rocq-of-solidity built somewhere
# pointed to by $ROCQ_TREE (default $HOME/git/reserve/_tools/rocq-of-solidity):
OPAM_SWITCH=rocq820 bash scripts/rocq-build   # ~3 min, compiles the proof tree
bash cas/run-check.sh                          # ~10 sec, runs 26 CAS scripts
```

The CI workflow at `.github/workflows/formal-verification.yml` runs
both stages on a fresh Ubuntu runner; trigger it manually from the
Actions tab. It mirrors the Debian install steps below and is the
definitive reference for "what works on a clean machine."

### Install prerequisites

The proof tree depends on **Coq 8.20.1** specifically (`vm_compute`
witness reduction and the `coq-hammer-tactics` reconstruction APIs are
version-sensitive). The instructions below set up an isolated opam
switch so it doesn't conflict with any other Coq version on your
machine.

#### macOS (Homebrew)

If you have a Homebrew-installed `gnu-binutils` or `coreutils` ahead
of `/usr/bin` on PATH, also `brew install m4`. Some opam packages
build native code and need GNU `m4`. macOS's bundled `/usr/bin/m4`
suffices when no Homebrew GNU toolchain shadows it.

```sh
brew install opam pari
opam init -y --bare
opam switch create rocq820 ocaml-base-compiler.4.14.1
opam repo add --switch=rocq820 coq-released https://coq.inria.fr/opam/released
opam install --switch=rocq820 -y \
  coq.8.20.1 coq-hammer-tactics coq-coqutil coq-record-update

# Build the upstream rocq-of-solidity library:
git clone https://github.com/formal-land/rocq-of-solidity \
  ~/git/reserve/_tools/rocq-of-solidity
cd ~/git/reserve/_tools/rocq-of-solidity/rocq/RocqOfSolidity
eval "$(opam env --switch=rocq820 --set-switch)"
make all
```

#### Debian / Ubuntu

```sh
sudo apt-get update
sudo apt-get install -y opam pari-gp build-essential m4 unzip git
opam init -y --bare --disable-sandboxing
opam switch create rocq820 ocaml-base-compiler.4.14.1
opam repo add --switch=rocq820 coq-released https://coq.inria.fr/opam/released
opam install --switch=rocq820 -y \
  coq.8.20.1 coq-hammer-tactics coq-coqutil coq-record-update

git clone https://github.com/formal-land/rocq-of-solidity \
  ~/git/reserve/_tools/rocq-of-solidity
cd ~/git/reserve/_tools/rocq-of-solidity/rocq/RocqOfSolidity
eval "$(opam env --switch=rocq820 --set-switch)"
make all
```

#### Arch Linux

```sh
sudo pacman -S --needed opam pari base-devel git
opam init -y --bare
opam switch create rocq820 ocaml-base-compiler.4.14.1
opam repo add --switch=rocq820 coq-released https://coq.inria.fr/opam/released
opam install --switch=rocq820 -y \
  coq.8.20.1 coq-hammer-tactics coq-coqutil coq-record-update

git clone https://github.com/formal-land/rocq-of-solidity \
  ~/git/reserve/_tools/rocq-of-solidity
cd ~/git/reserve/_tools/rocq-of-solidity/rocq/RocqOfSolidity
eval "$(opam env --switch=rocq820 --set-switch)"
make all
```

### Build script flags

`scripts/rocq-build` accepts environment-variable overrides if your
layout differs from the defaults:

| Variable | Default | Purpose |
|---|---|---|
| `ROCQ_TREE` | `$HOME/git/reserve/_tools/rocq-of-solidity` | Path to a built rocq-of-solidity checkout |
| `PROTOCOL_TREE` | self-located from script path | Path to this repository |
| `OPAM_SWITCH` | (unset; uses `coqc` from PATH) | Name of the opam switch to load |

### What runs in Docker (and why)

Docker is used only for the `solc-rocq` auto-translation runs (the
path that emits the Yul-derived Rocq from `contracts/<Harness>.sol`).
The amd64 ELF `solc-rocq` binary is invoked via Docker on non-Linux
hosts. Proof compilation and the CAS suite both run natively. No
Docker required.

## Parked workstreams

Two extension paths were investigated and parked with diagnostic notes:

1. **Yul-equivalence proofs** (`run_<fn>` lemmas tying the simulations
   to the auto-translated Yul-derived Rocq). Two distinct substrate
   gaps in upstream `rocq-of-solidity`: the semantic gap (no
   `Impossible` constructor in `RunO.t` for `block.timestamp`) and the
   structural gap (harness translations don't emit shallow companion
   files). Full diagnosis with concrete unblocking steps in
   [`notes/yul_equivalence_diagnostic.md`](notes/yul_equivalence_diagnostic.md).
2. **Auto-translation campaign** beyond the math harnesses: `solc-rocq`
   exhibits unpredictable optimizer crashes on broader Solidity inputs.
   The harness-shape strategy (storage + constructor + non-pure external
   entry points, no inheritance) is what makes the current translations
   reliably emit. Translating, e.g., the full RToken contract would
   require either a bug-fix campaign upstream or hand-written
   simplifications. Bisect probes for fresh crashes live under
   [`notes/probes/`](notes/probes/).
