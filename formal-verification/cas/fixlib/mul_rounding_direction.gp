\\ mul_rounding_direction.gp
\\
\\ Replays the Certora-driven default-rounding change in FixLib.mul:
\\   - Pre  (Fixed.sol, before #1283):  mul(x,y) := mul(x, y, ROUND)
\\   - Post (after #1283):              mul(x,y) := mul(x, y, FLOOR)
\\
\\ The audit didn't surface this as a "bug" with a concrete witness; it
\\ surfaced as a soundness concern at multiple call sites. Pre-mitigation,
\\ the 2-argument mul() rounded HALF-UP, which can over-credit a balance
\\ check or trade quote by 1 wei. Switching to FLOOR makes default-mul
\\ conservative (rounds against the caller), which is what almost every
\\ call site wanted.
\\
\\ This script: (a) shows the inputs where ROUND and FLOOR disagree, the
\\ disagreement magnitude (always exactly 1 fp wei), and the density of
\\ those inputs; (b) confirms that for "near-half" multiplications the
\\ disagreement is ubiquitous, not a corner case.
\\
\\ Reference:
\\   - protocol/contracts/libraries/Fixed.sol  (FixLib.mul, around line 250)
\\   - test/libraries/Fixed.test.ts: mulTest cases now use FLOOR variants
\\     and the table values shifted (`'1.5e-9' * '4.5e-8' = 67e-18` vs
\\     the old `68e-18`).

print("=== FixLib.mul — ROUND vs FLOOR disagreement profile ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;

\\ The Solidity `mul(x, y, mode)` semantics, as fixed-point uint192:
\\   p = x * y                       (in uint256, no overflow up to 2^192*2^192=2^384 — fits)
\\   floor:  p \ FIX_ONE
\\   ceil:   ceildiv(p, FIX_ONE)
\\   round:  floor((2*p + FIX_ONE) / (2*FIX_ONE))   -- half-up
mul_floor(x, y) = (x * y) \ FIX_ONE;
mul_round(x, y) = ((2 * x * y) + FIX_ONE) \ (2 * FIX_ONE);
mul_ceil(x, y)  = { my(p); p = x * y; if(p % FIX_ONE == 0, p \ FIX_ONE, (p \ FIX_ONE) + 1); }

\\ Disagreement predicate.
disagree(x, y) = mul_floor(x, y) != mul_round(x, y);
gap(x, y) = mul_round(x, y) - mul_floor(x, y);

\\ ---- Sanity: at exactly the half-rounding boundary ----
\\ A pair where x*y == k*FIX_ONE + FIX_ONE/2 should disagree by 1.
print("--- At half-rounding boundaries ---");
\\ Pick x*y = 3 * FIX_ONE + FIX_ONE/2 = 3.5 * FIX_ONE
\\ One factorisation: x = FIX_ONE/2 + 0.5*FIX_ONE = ... easier: pick directly.
print("x = 1.5 * FIX_ONE,   y = 3 * FIX_ONE + (FIX_ONE/3)  -- not exact half, used as control");
xa = 3 * FIX_ONE / 2;
ya = 3 * FIX_ONE;
{ printf("  floor = %d  round = %d  ceil = %d  -> disagree(round/floor) = %d\n", mul_floor(xa, ya), mul_round(xa, ya), mul_ceil(xa, ya), disagree(xa, ya)); }

print("x = FIX_ONE,         y = FIX_ONE/2 + 1   (product slightly > FIX_ONE/2)");
xb = FIX_ONE;
yb = FIX_ONE / 2 + 1;
{ printf("  floor = %d  round = %d  gap = %d\n", mul_floor(xb, yb), mul_round(xb, yb), gap(xb, yb)); }

print("x = FIX_ONE,         y = FIX_ONE/2       (product exactly half)");
xc = FIX_ONE;
yc = FIX_ONE / 2;
{ printf("  floor = %d  round = %d  gap = %d\n", mul_floor(xc, yc), mul_round(xc, yc), gap(xc, yc)); }

print("x = FIX_ONE,         y = FIX_ONE/2 - 1   (product slightly < FIX_ONE/2)");
xd = FIX_ONE;
yd = FIX_ONE / 2 - 1;
{ printf("  floor = %d  round = %d  gap = %d\n", mul_floor(xd, yd), mul_round(xd, yd), gap(xd, yd)); }
print("");

\\ ---- Density sweep: at what fraction of "interesting" inputs do they disagree? ----
print("--- Density of disagreement (random sample, fixed seed) ---");
setrand(20260429);
sample(n) = { my(disagreed); disagreed = 0; for(i = 1, n, my(x, y); x = random(FIX_MAX); y = random(FIX_MAX); if(disagree(x, y), disagreed = disagreed + 1)); disagreed; }
{ printf("  N = 1000 random uint192 pairs:  %d disagree (%.1f%%)\n", sample(1000), sample(1000) * 100.0 / 1000); }

\\ Restricted to the *typical Reserve magnitude* — values within a few
\\ orders of FIX_ONE (the "1.0" point), where rounding direction matters
\\ for fees, ratios, and quotes.
sample_near_one(n) = { my(disagreed, x, y); disagreed = 0; for(i = 1, n, x = random(100 * FIX_ONE); y = random(100 * FIX_ONE); if(disagree(x, y), disagreed = disagreed + 1)); disagreed; }
{ printf("  N = 1000 random pairs in [0, 100*FIX_ONE]: %d disagree (%.1f%%)\n", sample_near_one(1000), sample_near_one(1000) * 100.0 / 1000); }
print("");

\\ ---- Magnitude of disagreement ----
\\ The gap is always exactly 0 or 1 wei. Verify across a sweep.
print("--- Gap magnitudes across a structured sweep ---");
max_gap = 0;
{
  for(i = 1, 200,
    x = random(FIX_MAX);
    y = random(FIX_MAX);
    g = gap(x, y);
    if(g > max_gap, max_gap = g);
  );
}
{ printf("  Max gap observed across 200 random pairs: %d (expected: 0 or 1)\n", max_gap); }
print("");

\\ ---- Reserve-side significance ----
\\ The implication of switching default mul() from ROUND to FLOOR:
\\ every call site that wrote `a.mul(b)` — i.e., didn't pass a rounding
\\ mode — now rounds *down* by 1 wei when the product would have rounded
\\ up. For fee accrual, this means the protocol *credits less* to the
\\ DAO, never more. For trade quotes, the quote is conservative and the
\\ caller must beat it. For basket math, downstream balances are
\\ slightly understated, which is safe (BackingManager won't think it
\\ has more than it has).
\\
\\ The audit's call-site flips to explicit CEIL (BackingManager,
\\ TradeLib, ReadFacet) are the cases where rounding *up* is the safe
\\ direction (UoA inflation prevention), which is the dual of this fix.
print("Done.");
