\\ basket_range_noise.gp
\\
\\ CAS-side validation of the basket-range rounding-noise bound used by
\\ the Echidna rebalancing scenario in BackingManagerP1Fuzz.isBasketRangeSmaller
\\ (origin/fuzz:contracts/fuzz/FuzzP1.sol:200-258).
\\
\\ The formula in production:
\\
\\   dustNoiseBU   = ceil(minTradeVolume * FIX_ONE / buPriceHigh)
\\   roundingNoise = basketLength * (dustNoiseBU + basketLength) + 2
\\
\\ Components (per the in-source comment):
\\   1. mulDiv compound rounding: bounded above by 4 * basketLength + 2 BU,
\\      and the comment claims this is <= basketLength^2 for basketLength >= 5.
\\   2. minTradeVolume dust flips: up to basketLength tokens flip a dust
\\      threshold; per flip contributes ~minTradeVolume UoA, converted to
\\      BU as minTradeVolume * FIX_ONE / buPriceHigh.
\\
\\ The harness compares this noise against `slippageTolerance` and skips
\\ the property check when noise >= tolerance. When the skip fires, the
\\ harness silently passes — so a tight, conservative bound matters: too
\\ loose and bugs hide under the skip; too tight and the harness reports
\\ false positives.
\\
\\ This script:
\\   (a) numerically validates the comment's claim 4*BL + 2 <= BL^2
\\       for BL >= 5;
\\   (b) plots roundingNoise across plausible (BL, mtv, buPriceHigh)
\\       grids;
\\   (c) identifies the parameter region where the skip-check fires;
\\   (d) flags configurations where the bound looks suspiciously loose
\\       or tight relative to the slippage tolerance.

print("=== RebalancingLib basket-range noise bound — CAS validation ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;

\\ The production formula, exactly as written.
dustNoiseBU(mtv, buPriceHigh) = { my(num, q); num = mtv * FIX_ONE; q = num \ buPriceHigh; if(num % buPriceHigh == 0, q, q + 1); }
roundingNoise(bl, mtv, buPriceHigh) = bl * (dustNoiseBU(mtv, buPriceHigh) + bl) + 2;

\\ The slippage-tolerance side (from same function).
slippageTolerance(prevBottom, maxTradeSlippage) = (prevBottom * maxTradeSlippage) \ FIX_ONE;

\\ ---- (a) Validate 4*BL + 2 <= BL^2  for BL >= 5 ----
print("--- (a) Comment's claim: 4*BL + 2 <= BL^2  for BL >= 5 ---");
fail_a = 0;
report_bl(bl) = printf("  BL=%2d:  4*BL+2 = %4d   BL^2 = %5d   gap = %d\n", bl, 4*bl + 2, bl^2, bl^2 - (4*bl + 2));
{
  for(bl = 5, 30,
    if(4*bl + 2 > bl^2, fail_a = fail_a + 1);
  );
}
report_bl(5);
report_bl(10);
report_bl(20);
report_bl(30);
if(fail_a == 0, print("  OK across BL in [5, 30]."), printf("  FAIL: %d violations.\n", fail_a));
print("");

\\ ---- (b) roundingNoise across plausible production parameters ----
print("--- (b) roundingNoise across plausible (BL, minTradeVolume, buPriceHigh) ---");
\\ Real DTF parameters:
\\   - basketLength: small DTFs ~3, large ~30
\\   - minTradeVolume: $1 to $1000, in UoA which uses 18 decimals like FIX_ONE
\\   - buPriceHigh: ~$1 (for $1 BU), typically FIX_ONE
report_grid(bl, mtv_label, mtv, bup_label, bup) = printf("  BL=%2d  mtv=%-8s  buPriceHigh=%-12s  noise = %d BU (%.2f * BL)\n", bl, mtv_label, bup_label, roundingNoise(bl, mtv, bup), roundingNoise(bl, mtv, bup) * 1.0 / bl);
report_grid(5,  "$10",   10 * FIX_ONE,   "$1",  FIX_ONE);
report_grid(5,  "$100",  100 * FIX_ONE,  "$1",  FIX_ONE);
report_grid(5,  "$1000", 1000 * FIX_ONE, "$1",  FIX_ONE);
report_grid(20, "$10",   10 * FIX_ONE,   "$1",  FIX_ONE);
report_grid(20, "$100",  100 * FIX_ONE,  "$1",  FIX_ONE);
report_grid(20, "$1000", 1000 * FIX_ONE, "$1",  FIX_ONE);
\\ Now buPriceHigh > $1 (e.g. ETH+ where each BU is ~3000 UoA)
report_grid(7,  "$10",   10 * FIX_ONE,   "$3k", 3000 * FIX_ONE);
report_grid(7,  "$100",  100 * FIX_ONE,  "$3k", 3000 * FIX_ONE);
print("");

\\ ---- (c) Skip-check region: when does roundingNoise >= slippageTolerance? ----
print("--- (c) Skip-check fires when noise >= slippage tolerance ---");
\\ slippageTolerance = prevBottom * maxTradeSlippage / FIX_ONE
\\ Calibration: prevBottom = $1M in BU = 1e6 * FIX_ONE; maxTradeSlippage = 0.01 (1%)
prevBottom_cal = 10^6 * FIX_ONE;
report_skip(slip_pct, slip_label) = { my(slip, n, t, fires); slip = slip_pct * FIX_ONE \ 10000; t = slippageTolerance(prevBottom_cal, slip); n = roundingNoise(7, 100 * FIX_ONE, FIX_ONE); fires = if(n >= t, "YES (skip fires)", "no"); printf("  prevBottom=$1M, BL=7, mtv=$100, slip=%-6s -> tol=%-25d noise=%-15d %s\n", slip_label, t, n, fires); }
\\ slip_pct argument is in basis points (0.01% = 1)
report_skip(1,    "0.01%");
report_skip(10,   "0.1%");
report_skip(100,  "1%");
report_skip(1000, "10%");
print("");

\\ ---- (d) Flag suspiciously loose / tight regions ----
print("--- (d) Tightness ratio: slippageTolerance / roundingNoise ---");
\\ Ratio < 1 means skip fires (noise dominates). Ratio in [1, 10] is
\\ tight (small bug magnitudes can hide). Ratio > 100 is loose (the
\\ harness has plenty of headroom).
report_tightness(bl, mtv_label, mtv, prev_label, prev, slip_pct) = { my(slip, n, t, ratio); slip = slip_pct * FIX_ONE \ 10000; t = slippageTolerance(prev, slip); n = roundingNoise(bl, mtv, FIX_ONE); ratio = if(n == 0, 99999, t * 1.0 / n); printf("  BL=%2d mtv=%-6s prev=%-8s slip=%-5s  ratio = %.2f\n", bl, mtv_label, prev_label, Strprintf("%d.%02d%%", slip_pct \ 100, slip_pct % 100), ratio); }
report_tightness(5,  "$10",   10 * FIX_ONE,   "$1M",   10^6 * FIX_ONE,   100);
report_tightness(20, "$10",   10 * FIX_ONE,   "$1M",   10^6 * FIX_ONE,   100);
report_tightness(20, "$1000", 1000 * FIX_ONE, "$1M",   10^6 * FIX_ONE,   100);
report_tightness(20, "$1000", 1000 * FIX_ONE, "$100M", 10^8 * FIX_ONE,   100);
report_tightness(20, "$1000", 1000 * FIX_ONE, "$10k",  10^4 * FIX_ONE,   100);
report_tightness(20, "$1000", 1000 * FIX_ONE, "$10k",  10^4 * FIX_ONE,    10);
print("");

\\ ---- Conclusion ----
\\ The bound's structure has two terms (mulDiv + dust); the dust term
\\ dominates when buPriceHigh is small or minTradeVolume is large. The
\\ skip-check then fires for low-tolerance regions, leaving them
\\ effectively unverified — which is precisely the territory the recent
\\ 20 fuzz-branch commits are tweaking.
\\
\\ A Rocq proof of the form
\\   |basketRange_post - basketRange_pre| <= roundingNoise(BL, mtv, bup)
\\ would replace the empirical heuristic with a provable invariant. The
\\ CAS validation here is a regression net for that proof: any future
\\ tightening of the bound must still satisfy the calibrations above,
\\ and any loosening must remain consistent with the slippage tolerance
\\ at typical RToken parameters.
print("Done.");
