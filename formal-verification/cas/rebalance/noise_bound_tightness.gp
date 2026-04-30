\\ noise_bound_tightness.gp
\\
\\ Companion to basket_range_noise.gp: derives a *tighter* alternative
\\ rounding-noise bound and quantifies the regimes where the looser
\\ production bound forces the harness skip-check to fire unnecessarily.
\\
\\ Production bound (from FuzzP1.sol::isBasketRangeSmaller):
\\   noise_loose = bl * dustNoiseBU + bl^2 + 2
\\
\\ Tight bound (from the same comment, used as the "actual mulDiv
\\ accumulation" before substituting the bl^2 approximation):
\\   noise_tight = bl * dustNoiseBU + (4 * bl + 2) + 2
\\                = bl * dustNoiseBU + 4*bl + 4
\\
\\ Why two? The comment says "Two calls compound: worst case = 4 * bl + 2
\\ BU, bounded above by bl^2 for bl >= 5." So bl^2 is a safe over-
\\ approximation; replacing it with the tight form costs nothing in
\\ correctness and reclaims headroom in the slippage tolerance.
\\
\\ Reference: protocol (origin/fuzz):contracts/fuzz/FuzzP1.sol:200-258

print("=== Rebalance noise-bound tightness analysis ===");
print("");

FIX_ONE = 10^18;

dustNoiseBU(mtv, buPriceHigh) = { my(num, q); num = mtv * FIX_ONE; q = num \ buPriceHigh; if(num % buPriceHigh == 0, q, q + 1); }

\\ Two bounds. Both are correct upper bounds on the actual rounding error;
\\ the tight one is a strictly smaller upper bound for bl >= 5.
noise_loose(bl, mtv, bup) = bl * dustNoiseBU(mtv, bup) + bl^2 + 2;
noise_tight(bl, mtv, bup) = bl * dustNoiseBU(mtv, bup) + 4 * bl + 4;

\\ Slippage tolerance term, identical to what isBasketRangeSmaller computes.
slippageTolerance(prevBottom, maxTradeSlippage) = (prevBottom * maxTradeSlippage) \ FIX_ONE;

\\ ---- (a) Validate: noise_tight <= noise_loose for all bl >= 5 ----
print("--- (a) Tight bound is no looser than production bound ---");
fail_a = 0;
{
  for(bl = 5, 50,
    nl = noise_loose(bl, 100 * FIX_ONE, FIX_ONE);
    nt = noise_tight(bl, 100 * FIX_ONE, FIX_ONE);
    if(nt > nl, fail_a = fail_a + 1);
  );
}
report_bl_compare(bl) = printf("  BL=%2d:  loose = %d   tight = %d   savings = %d\n", bl, noise_loose(bl, 0, FIX_ONE), noise_tight(bl, 0, FIX_ONE), noise_loose(bl, 0, FIX_ONE) - noise_tight(bl, 0, FIX_ONE));
\\ When mtv = 0 the dust term vanishes; only the rounding term remains.
print("  (with mtv=0, only the rounding term remains; this isolates the bl^2 vs 4*bl+2 difference)");
report_bl_compare(5);
report_bl_compare(10);
report_bl_compare(20);
report_bl_compare(30);
report_bl_compare(50);
if(fail_a == 0, print("  OK: tight is always <= loose"), printf("  FAIL: %d cases where tight > loose\n", fail_a));
print("");

\\ ---- (b) When does tightening unblock the harness skip-check? ----
\\ Skip fires when noise >= slippageTolerance. Tightening flips
\\ "skip fires" to "skip does not fire" exactly when:
\\   noise_loose >= tol > noise_tight
\\
\\ This is the regime where the harness would *currently* skip, but a
\\ tightened bound would let the property check fire.
print("--- (b) Regimes where tightening unblocks the property check ---");
\\ Calibration: small DTF, prevBottom=$10k in BU, maxTradeSlippage=0.1%.
prev_small = 10^4 * FIX_ONE;
slip_pcts = [10, 100, 1000];   \\ in basis points: 0.1%, 1%, 10%
report_unblock(bl, mtv_label, mtv, slip_bp) = { my(slip, tol, nl, nt, status); slip = slip_bp * FIX_ONE \ 10000; tol = slippageTolerance(prev_small, slip); nl = noise_loose(bl, mtv, FIX_ONE); nt = noise_tight(bl, mtv, FIX_ONE); status = if(tol > nt && tol <= nl, "UNBLOCKED-by-tighten", if(tol > nl, "already firing", "still skipped")); printf("  BL=%2d mtv=%-6s slip=%-6s tol=%-25d nl=%-15d nt=%-15d %s\n", bl, mtv_label, Strprintf("%d.%02d%%", slip_bp \ 100, slip_bp % 100), tol, nl, nt, status); }
report_unblock(10,  "$0",   0,            10);
report_unblock(10,  "$0",   0,            100);
report_unblock(20,  "$0",   0,            10);
report_unblock(20,  "$10",  10 * FIX_ONE, 100);
report_unblock(30,  "$10",  10 * FIX_ONE, 1000);
\\ Calibration with mid-sized DTF.
prev_mid = 10^6 * FIX_ONE;
{ printf("\n  (now with prev = $1M)\n"); }
slippageTolerance_mid(bp) = (prev_mid * (bp * FIX_ONE \ 10000)) \ FIX_ONE;
report_unblock_mid(bl, mtv_label, mtv, slip_bp) = { my(tol, nl, nt, status); tol = slippageTolerance_mid(slip_bp); nl = noise_loose(bl, mtv, FIX_ONE); nt = noise_tight(bl, mtv, FIX_ONE); status = if(tol > nt && tol <= nl, "UNBLOCKED-by-tighten", if(tol > nl, "already firing", "still skipped")); printf("  BL=%2d mtv=%-6s slip=%-6s tol=%-25d nl=%-15d nt=%-15d %s\n", bl, mtv_label, Strprintf("%d.%02d%%", slip_bp \ 100, slip_bp % 100), tol, nl, nt, status); }
report_unblock_mid(20, "$100", 100 * FIX_ONE, 1);
report_unblock_mid(20, "$100", 100 * FIX_ONE, 100);
report_unblock_mid(30, "$0",   0,            1);
print("");

\\ ---- (c) Tightness ratio across BL ----
print("--- (c) tight/loose ratio across BL (mtv = 0, isolates rounding term) ---");
report_ratio(bl) = printf("  BL=%2d: ratio %.4f (tight saves %.1f%%)\n", bl, noise_tight(bl, 0, FIX_ONE) * 1.0 / noise_loose(bl, 0, FIX_ONE), 100 * (1 - noise_tight(bl, 0, FIX_ONE) * 1.0 / noise_loose(bl, 0, FIX_ONE)));
report_ratio(5);
report_ratio(10);
report_ratio(20);
report_ratio(30);
report_ratio(50);
print("  As BL grows, tightening reclaims more headroom: at BL=50, the tight");
print("  bound is 8% of the loose bound — i.e. 12x more sensitive.");
print("");

\\ ---- (d) Recommendation ----
print("--- (d) Recommendation ---");
print("  In FuzzP1.sol::isBasketRangeSmaller, replace");
print("    roundingNoise = bl * (dustNoiseBU + bl) + 2;");
print("  with");
print("    roundingNoise = bl * dustNoiseBU + 4 * bl + 4;");
print("  This is provably no looser (per the in-source comment) and");
print("  reclaims the bl^2 - 4*bl rounding headroom. In the rounding-");
print("  dominated regime (mtv = 0 or buPriceHigh large), the property");
print("  check fires on inputs the current heuristic skips.");
print("");

print("OK: analysis complete.");
print("Done.");
