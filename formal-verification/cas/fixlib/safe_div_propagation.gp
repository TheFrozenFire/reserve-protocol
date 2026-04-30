\\ safe_div_propagation.gp
\\
\\ Replays the second Certora Formal Verification finding on FixLib: that
\\ `safeDiv(FIX_MAX, b)` did NOT propagate FIX_MAX as a saturated infinity
\\ for non-degenerate divisors b > 0.
\\
\\ Reference inputs: protocol/test/libraries/Fixed.test.ts
\\   it('safeDiv() does not correctly propagate the FIX_MAX value', ...)
\\
\\ Mitigation: protocol commit 7bf3a1ed (#1283), Fixed.sol:550 — added
\\     if (a == FIX_MAX) return FIX_MAX;
\\ above the `if (b == 0) return FIX_MAX;` check.
\\
\\ Pre-mitigation behaviour at FIX_MAX: the function fell through to
\\     uint256 raw = _divrnd(FIX_ONE_256 * a, uint256(b), rounding);
\\ which for `a = FIX_MAX, b = 2e18` computes FIX_MAX/2 — i.e. silently
\\ scales the saturated value by 1/b instead of preserving it.
\\
\\ This script sweeps b across the practically-relevant range and reports
\\ the magnitude of the saturation error: how far off pre-mitigation would
\\ be from the intended FIX_MAX answer.

print("=== FixLib.safeDiv — FIX_MAX propagation witness ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;

\\ Pre-mitigation semantics for safeDiv(FIX_MAX, b, rounding=ROUND):
\\   raw = floor(FIX_ONE * FIX_MAX / b)
\\   if raw > FIX_MAX, return FIX_MAX (the existing safeDiv saturation
\\     guard further down in the function)
\\   else return raw
\\
\\ The bug surfaces when raw <= FIX_MAX, because then the function returns
\\ a *strictly smaller* value than the saturated answer the caller expected.
pre_mitigation_safeDiv_FIX_MAX(b) = { my(raw); raw = (FIX_ONE * FIX_MAX) \ b; if(raw > FIX_MAX, FIX_MAX, raw); }

\\ Post-mitigation: just FIX_MAX, regardless of b > 0.
post_mitigation_safeDiv_FIX_MAX(b) = FIX_MAX;

\\ ---- The Certora regression input ----
b_witness = 2 * FIX_ONE;  \\ 2e18
print("Regression input: a = FIX_MAX, b = 2e18");
{ printf("  pre-mitigation result  = %d\n", pre_mitigation_safeDiv_FIX_MAX(b_witness)); }
{ printf("  intended (FIX_MAX)     = %d\n", post_mitigation_safeDiv_FIX_MAX(b_witness)); }
{ printf("  ratio (pre / FIX_MAX)  = %.6f\n", pre_mitigation_safeDiv_FIX_MAX(b_witness) * 1.0 / FIX_MAX); }
print("");

\\ ---- Sweep over b ----
\\ The pre-mitigation result is FIX_MAX iff FIX_ONE * FIX_MAX / b > FIX_MAX,
\\ i.e. iff b < FIX_ONE. For b >= FIX_ONE the bug surfaces; for b < FIX_ONE
\\ the saturation guard inside _divrnd kicks in and the result is FIX_MAX
\\ regardless. So the bug-affected region is exactly b in [FIX_ONE, +inf).
print("--- Sweep: pre-mitigation result vs FIX_MAX, by b ---");
print("(intended answer is FIX_MAX everywhere; pre shows the bug magnitude)");
\\ A small helper to keep the loop body single-statement.
report_b(b, label) = printf("  b = %-20s pre = %d (= FIX_MAX/%d)\n", label, pre_mitigation_safeDiv_FIX_MAX(b), FIX_MAX \ pre_mitigation_safeDiv_FIX_MAX(b));
report_b(FIX_ONE,            "FIX_ONE (1e18)");
report_b(2 * FIX_ONE,        "2e18");
report_b(10 * FIX_ONE,       "10e18");
report_b(100 * FIX_ONE,      "100e18");
report_b(10^9 * FIX_ONE,     "1e9 * FIX_ONE");
report_b(10^18 * FIX_ONE,    "1e18 * FIX_ONE = 1e36");
print("");

\\ ---- Boundary characterization ----
\\ Where is the boundary at which the saturation guard inside _divrnd
\\ stops kicking in? Solve FIX_ONE * FIX_MAX / b == FIX_MAX  ->  b == FIX_ONE.
\\ For b = FIX_ONE - 1, raw = FIX_ONE * FIX_MAX / (FIX_ONE - 1), which
\\ is > FIX_MAX. For b = FIX_ONE exactly, raw = FIX_MAX (saturation guard
\\ does not fire because the existing check is `> FIX_MAX`, strict).
\\
\\ So the bug-affected range begins at b = FIX_ONE inclusive.
print("--- Bug-affected boundary characterization ---");
report_b(FIX_ONE - 1, "FIX_ONE - 1");
report_b(FIX_ONE,     "FIX_ONE       (boundary)");
report_b(FIX_ONE + 1, "FIX_ONE + 1");
print("");

\\ ---- Conclusion ----
\\ The post-mitigation early return turns this from a silent value-scaling
\\ bug into a constant-time saturation. The regression test in
\\ Fixed.test.ts only exercises one b value; the sweep above shows the
\\ bug is essentially the entire b >= FIX_ONE region, suggesting that a
\\ slightly broader regression test would be cheap insurance:
\\
\\   it('safeDiv saturates FIX_MAX across b range', async () => {
\\     for (const b of [FIX_ONE, 2n * FIX_ONE, 100n * FIX_ONE, 10n ** 30n])
\\       expect(await caller.safeDiv(MAX_UINT192, b, ROUND)).to.equal(MAX_UINT192);
\\   });
print("Done.");
