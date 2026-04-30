# Notes

Engineering details too long for a top-level README but too important
to lose. Currently:

- [`yul_equivalence_diagnostic.md`](yul_equivalence_diagnostic.md)
  documents why `run_<fn>` lemmas (tying the auto-translated
  Yul-derived Rocq to the simulation) are blocked. Two distinct
  substrate gaps in upstream `rocq-of-solidity`: a semantic gap on
  `block.timestamp` and a structural gap on shallow companion files.
  Both have concrete unblocking steps documented.

- [`probes/`](probes/) holds single-function Solidity contracts used
  to bisect which constructs trip `solc-rocq`'s optimizer. If you hit
  a fresh optimizer crash on a new harness, copy the closest probe
  and narrow from there.
