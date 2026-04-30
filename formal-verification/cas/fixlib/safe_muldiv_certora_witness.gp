\\ safe_muldiv_certora_witness.gp
\\
\\ Replays the Certora Formal Verification finding on FixLib.safeMulDiv as a
\\ PARI/GP witness — concrete inputs at which the *intended* saturating
\\ behaviour can be cheaply distinguished from a non-saturating implementation.
\\
\\ Reference inputs: protocol/test/libraries/Fixed.test.ts
\\   describe('Certora Regression Tests', ...)
\\     it('safeMulDiv() may return 0 instead of FIX_MAX', ...)
\\
\\ Mitigation: protocol commit 7bf3a1ed (#1283), Certora Formal Verification —
\\ added `if (result_256 >= FIX_MAX) return FIX_MAX;` inside FixLib._safeMulDiv
\\ (Fixed.sol:594).
\\
\\ Scope of this script: confirm the intended answer at the regression inputs,
\\ enumerate other (a, b, c) shapes where the math overflows FIX_MAX, and
\\ surface them as candidate regression-test inputs. We deliberately do NOT
\\ model the pre-mitigation bug — its exact behaviour depends on the inline
\\ assembly in _safeMulDiv and PARI/GP wouldn't faithfully reproduce it
\\ without porting that assembly. CAS's value here is showing that *the
\\ intended saturated answer is FIX_MAX* across a broad witness corpus.

print("=== FixLib.safeMulDiv — Certora witness ===");
print("");

\\ FixLib constants (from contracts/libraries/Fixed.sol)
FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;     \\ uint192.max

\\ Intended (post-mitigation) safeMulDiv behaviour, ROUND-mode-agnostic at
\\ the saturation boundary: if the exact a*b/c is >= FIX_MAX, return
\\ FIX_MAX; otherwise return the floored value.
post_mitigation(a, b, c) = { my(lo); lo = (a * b) \ c; if(lo >= FIX_MAX, FIX_MAX, lo); }

\\ ---- Witness inputs from the Certora regression test ----
xa = 2^191 + 1;
xb = 2^192 - 2;
xc = 2^127;

print("Inputs (from Certora regression test):");
{ printf("  a = 2^191 + 1 = %d\n", xa); }
{ printf("  b = 2^192 - 2 = %d\n", xb); }
{ printf("  c = 2^127     = %d\n", xc); }
print("");

ex = (xa * xb) / xc;
post = post_mitigation(xa, xb, xc);

{ printf("Exact a*b/c (no overflow)        = %d\n", ex); }
{ printf("FIX_MAX (uint192.max)            = %d\n", FIX_MAX); }
{ printf("Intended saturated result        = %d\n", post); }
{ printf("Overflow factor (exact/FIX_MAX)  = %.0f (= 2^%d)\n", ex * 1.0 / FIX_MAX, log(ex * 1.0 / FIX_MAX) / log(2)); }
print("");

\\ ---- Sanity check on the intended semantics ----
if(post == FIX_MAX, print("OK: intended safeMulDiv at witness inputs returns FIX_MAX."), print("FAIL: script semantics disagree with audit."));
print("");

\\ ---- Boundary corpus generation ----
\\ Enumerate (a, b, c) where a*b/c just exceeds FIX_MAX, ordered by how
\\ tightly they sit on the boundary (smallest overflow first). These are
\\ the inputs most likely to surface saturation bugs in any FixLib variant.
\\
\\ Note: PARI/GP rejects nested {} brace blocks (WISDOM W019), so the
\\ inner printf is collapsed onto one line.
print("--- Boundary corpus: minimal-overflow witnesses ---");
\\ A helper to keep the boundary-sweep body free of nested braces.
report_boundary(idx, e) = printf("  a=2^%d  b=2^%d  c=2^%d  exact=%d  overflow=+%d\n", e[1], e[2], e[3], e[4], e[4] - FIX_MAX);
{
  candidates = [];
  for(i = 96, 192,
    a = 2^i;
    for(j = 96, 192,
      b = 2^j;
      for(k = 0, 96,
        c = 2^k;
        if(c == 0, next);
        v = (a * b) \ c;
        if(v > FIX_MAX && v <= 2 * FIX_MAX,
          candidates = concat(candidates, [[i, j, k, v]]);
        );
      );
    );
  );
  printf("Found %d (a=2^i, b=2^j, c=2^k) shapes with FIX_MAX < a*b/c <= 2*FIX_MAX\n", #candidates);
  print("First 8 (smallest overflow first, by exact value):");
  cs = vecsort(candidates, 4);
  for(idx = 1, min(8, #cs), report_boundary(idx, cs[idx]));
}
print("");

\\ ---- Regression-test export hint ----
\\ Each row above translates directly into a Fixed.test.ts case:
\\   it('safeMulDiv saturates at <description>', async () => {
\\     expect(await caller.safeMulDiv(2n**Bn, 2n**Bn, 2n**Bn, CEIL))
\\       .to.equal(MAX_UINT192);
\\   });
\\ The corpus above is a stable, regenerable witness set independent of the
\\ specific bug Certora found — protective against future regressions of any
\\ saturating FIX_MAX path.
print("Done. Run with `gp -q < safe_muldiv_certora_witness.gp`.");
