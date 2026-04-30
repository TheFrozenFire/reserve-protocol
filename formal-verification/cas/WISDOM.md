# CAS Wisdom (Reserve formal-verification)

Lessons captured while authoring the CAS suite under
`formal-verification/cas/`. Each entry documents a PARI/GP gotcha that
cost real time during this work — captured so the next author hits them
once at most.

## PARI/GP parser quirks

These all bit during script authoring; the workarounds are stable.

- **`for(...)` bodies with multiple statements need `{ }`.** A bare
  `for(i=1, n, expr1; expr2)` parses as a single expression and only
  evaluates `expr1` per iteration. Wrap in braces: `for(i=1, n, { expr1; expr2 })`.
- **Multi-line `printf(...)` is a parser error.** PARI/GP's parser
  treats line breaks inside argument lists as terminators. Put the
  whole `printf` on one line, or wrap the call in `{ ... }` to
  suppress newline-as-terminator handling.
- **Nested `{ }` blocks are rejected** — "embedded braces (in parser)
  is not yet implemented". Hit this when trying to put a
  multi-statement `{ printf(...); }` inside a `for(...)` body that
  was itself inside an outer `{ }` block. Workaround: lift the inner
  block into a top-level helper function.

## Reserve-specific additions

### R001: Reserve fixed-point constants

For consistency across scripts, every `.gp` declares the FixLib
constants directly rather than importing. The canonical set:

```gp
FIX_ONE  = 10^18;          \\ 1.0 in D18 fixed-point
FIX_MAX  = 2^192 - 1;      \\ uint192 max
UINT48_MAX = 2^48 - 1;     \\ block.timestamp ceiling
UINT256_MAX = 2^256 - 1;
```

When a contract uses different constants (e.g. StRSR's
`MAX_STAKE_RATE = 1e9 * FIX_ONE`), declare them at the top with a
source-line comment cross-reference.

### R002: Don't model the bug — model the spec

When replaying audit findings, modelling the *pre-mitigation buggy
behaviour* is fragile (the bug typically depends on Solidity inline
assembly that PARI/GP can't faithfully reproduce). Model the
*intended/post-mitigation behaviour* and let the boundary sweep
identify which inputs would distinguish a saturating implementation
from a non-saturating one. The witness corpus is the deliverable;
the bug reproduction belongs in Foundry.

This is why `safe_muldiv_certora_witness.gp` deliberately stops
modelling pre-mitigation semantics after one attempt — it would
have meant porting `_safeMulDiv`'s 512-bit assembly into PARI/GP for
no useful gain.

### R003: Use ceiling division explicitly

Solidity's `(a + b - 1) / b` ceiling-division pattern is dangerous
in PARI/GP if `a` and `b` are exact rationals (the result is a
rational, not an integer, breaking later integer comparisons).
Define an explicit helper:

```gp
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
```

`\` is integer (floor) division; `%` is modulo. Both are integer ops
in PARI/GP regardless of input type, so this stays in the integers.

### R004: PARI/GP `1.0` casts are safer than they look

For any `printf("%.6f", expr)`, force float by multiplying by `1.0`:

```gp
printf("ratio = %.6f\n", numer * 1.0 / denom);
```

PARI/GP's `%f` directive handles `t_REAL` cleanly; if you pass a
`t_FRAC` it may print as `numer/denom`. The `* 1.0` is the cheapest
way to coerce.

### R005: Calibrate against deployed parameters

CAS's value over abstract proof comes from running on real numbers.
For Reserve, that means:

- Real RToken supplies (look in `deployments.json`)
- Real basket parameters (basketLength, minTradeVolume from
  governance configs)
- Real reward ratios (from RToken Furnace + StRSR settings)

Hard-coded calibration values in scripts should match production
within an order of magnitude. When they don't, the safety margins
the script reports are misleading.

### R006: PARI/GP's `Strprintf` returns a string but doesn't fix W019

When trying to format a value inline within a `printf` argument list
that's inside a `for` loop, `Strprintf` doesn't help — the outer
`printf` still needs braces, and the brace problem is structural.
Use a top-level helper function to keep the inner code single-line.

### R007: `setrand(seed)` for reproducibility

In recent PARI/GP versions (≥ 2.17), the older `set_rand` form is gone;
use `setrand(seed)`. We use the date as seed for run-to-run
reproducibility:

```gp
setrand(20260429);
```

When the input distribution genuinely shouldn't matter to the
result (only the boundary count or the worst-case witness), skip
seeding entirely.

### R008: Run the suite via `./run-check.sh`

The runner greps script output for `FAIL` or `error` (case-insensitive)
to detect failure. For a script to participate, every invariant probe
must print `OK` on success and something containing `FAIL` on failure.
Avoid printing `error` in success paths; otherwise the runner reports
a false positive.
