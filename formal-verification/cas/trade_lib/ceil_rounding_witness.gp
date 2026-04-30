\\ ceil_rounding_witness.gp
\\
\\ Witnesses for the CEIL-vs-FLOOR rounding-mode change introduced by
\\ PR #1283 (commit 7bf3a1ed) on the inner `s.mul(FIX_ONE.minus(slippage))`
\\ multiplication in TradeLib.prepareTradeSell.
\\
\\ Pre-mitigation:
\\   uint192 b = s.mul(FIX_ONE.minus(maxTradeSlippage)).safeMulDiv(
\\       trade.prices.sellLow, trade.prices.buyHigh, CEIL);
\\   (no rounding mode on inner mul → defaults to FLOOR per Fixed.sol L253)
\\
\\ Post-mitigation:
\\   uint192 b = s.mul(FIX_ONE.minus(maxTradeSlippage), CEIL).safeMulDiv(
\\       trade.prices.sellLow, trade.prices.buyHigh, CEIL);
\\
\\ Effect: when (s * (FIX_ONE - slippage)) is not a multiple of FIX_ONE,
\\ the inner mul under FLOOR truncates and the outer safeMulDiv-CEIL
\\ amplifies that truncation by sellLow/buyHigh. Net direction: pre-
\\ mitigation buyAmount could under-credit by the rounding gap; post-
\\ mitigation always over-credits (or matches exactly).
\\
\\ This script:
\\   (A) Confirms the direction at the calibrated production input.
\\   (B) Surfaces a corpus of boundary inputs where pre vs post differ
\\       by exactly 1 wei in the inner mul, scaled by sellLow/buyHigh
\\       at the outer step.
\\   (C) Sanity: when the inner mul has no remainder, pre == post.
\\
\\ This is the analog of fixlib/safe_muldiv_certora_witness.gp but for
\\ TradeLib's two-step rounding composition rather than the FIX_MAX
\\ saturation path.

print("=== TradeLib CEIL rounding witness (PR #1283) ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ Inner mul under FLOOR (pre-mitigation) and CEIL (post-mitigation).
fix_mul_floor(x, y) = (x * y) \ FIX_ONE;
fix_mul_ceil(x, y)  = ceil_div(x * y, FIX_ONE);

\\ Outer safeMulDiv-CEIL (saturating). For our calibrated regime the
\\ inputs are far below FIX_MAX so saturation doesn't trigger; we still
\\ guard the saturation cases for completeness.
fix_safe_muldiv_ceil(a, b, c) = { my(r); if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX || c == 0, return(FIX_MAX)); r = ceil_div(a * b, c); if(r >= FIX_MAX, FIX_MAX, r); }

buy_pre(s, slippage, sellLow, buyHigh)  = fix_safe_muldiv_ceil(fix_mul_floor(s, FIX_ONE - slippage), sellLow, buyHigh);
buy_post(s, slippage, sellLow, buyHigh) = fix_safe_muldiv_ceil(fix_mul_ceil(s, FIX_ONE - slippage),  sellLow, buyHigh);

\\ Calibration ($1M sell at 0.5% slippage with $0.99/$1.01 prices).
SLIPPAGE = 5 * 10^15;
SELL_LOW = 99 * 10^16;
BUY_HIGH = 101 * 10^16;
SELL_AMT = 10^6 * FIX_ONE;

\\ ---- (A) Direction at the calibrated input ----
print("--- (A) Pre vs post at calibrated inputs ---");
b_pre  = buy_pre(SELL_AMT, SLIPPAGE, SELL_LOW, BUY_HIGH);
b_post = buy_post(SELL_AMT, SLIPPAGE, SELL_LOW, BUY_HIGH);
{ printf("  b_pre  (FLOOR + CEIL composition) = %d\n", b_pre); }
{ printf("  b_post (CEIL  + CEIL composition) = %d\n", b_post); }
{ printf("  delta (post - pre) (wei)          = %d\n", b_post - b_pre); }

\\ The mitigation is sound iff post >= pre across all inputs (i.e. the
\\ minimum buy amount is never reduced; any change is a tightening).
if(b_post >= b_pre, print("OK: post-mitigation buy amount >= pre-mitigation at calibrated input."), print("FAIL: post-mitigation buy amount < pre-mitigation — mitigation reversed expected direction."));
print("");

\\ ---- (B) Boundary witness corpus ----
\\ Sweep s values where (s * (FIX_ONE - slippage)) modulo FIX_ONE is small
\\ but nonzero — exactly the regime where FLOOR truncates and CEIL bumps.
\\ For SLIPPAGE = 5e15, (FIX_ONE - SLIPPAGE) = 995e15. Then for s = k+1
\\ across consecutive integers, the remainder mod FIX_ONE walks by 5e15
\\ each step (gcd(995e15, 1e18) = 5e15), yielding 200 distinct residues.
print("--- (B) Boundary witness corpus ---");
report_witness(idx, s, pre, post, delta) = printf("  #%-3d  s=%d  pre=%d  post=%d  delta=+%d wei\n", idx, s, pre, post, delta);

{
  base = 10^6 * FIX_ONE;        \\ start near the production sweet spot
  divergent = [];
  for(off = 0, 999,
    s_probe = base + off;
    bp = buy_pre(s_probe, SLIPPAGE, SELL_LOW, BUY_HIGH);
    bq = buy_post(s_probe, SLIPPAGE, SELL_LOW, BUY_HIGH);
    if(bq != bp,
      divergent = concat(divergent, [[s_probe, bp, bq, bq - bp]]);
    );
  );
  printf("  swept 1000 consecutive s values starting at $1M\n");
  printf("  divergent (post != pre) inputs: %d\n", #divergent);
  if(#divergent > 0,
    \\ Sort by delta descending so worst-case witnesses appear first.
    cs = vecsort(divergent, 4, 4);
    print("  worst-case witnesses (largest delta first):");
    for(idx = 1, min(5, #cs), report_witness(idx, cs[idx][1], cs[idx][2], cs[idx][3], cs[idx][4]));
    \\ All deltas must be strictly positive (post strictly greater).
    min_delta = cs[#cs][4];
    if(min_delta > 0, print("OK: every divergent witness has post > pre (mitigation only ratchets up)."), print("FAIL: a divergent witness has post <= pre — direction is wrong."));
  );
  if(#divergent == 0, print("OK: no divergent witnesses (calibration regime fully aligned)."));
}
print("");

\\ ---- (C) No-remainder sanity: pre == post when inner mul is exact ----
print("--- (C) No-remainder sanity (pre == post at exact-multiple inputs) ---");
\\ Pick s such that s * (FIX_ONE - slippage) is divisible by FIX_ONE.
\\ For SLIPPAGE = 5e15, (FIX_ONE - SLIPPAGE) = 995e15 = 5e15 * 199.
\\ s * 995e15 ≡ 0 (mod 1e18) iff s ≡ 0 (mod 200), since
\\ gcd(995e15, 1e18) = 5e15 and 1e18 / 5e15 = 200.
exact_s = 200 * FIX_ONE;
b_pre_e  = buy_pre(exact_s, SLIPPAGE, SELL_LOW, BUY_HIGH);
b_post_e = buy_post(exact_s, SLIPPAGE, SELL_LOW, BUY_HIGH);
{ printf("  exact-multiple s = %d  pre = %d  post = %d\n", exact_s, b_pre_e, b_post_e); }
if(b_pre_e == b_post_e, print("OK: at exact-multiple s, pre == post (mitigation no-op when no rounding gap)."), print("FAIL: pre != post at an exact-multiple input — extraneous rounding somewhere."));
print("");

\\ ---- (D) Slippage = 0 sanity: pre == post regardless of s ----
print("--- (D) Slippage = 0: pre == post for any s ---");
\\ At slippage = 0, FIX_ONE - slippage = FIX_ONE, so s * FIX_ONE / FIX_ONE
\\ = s exactly under both FLOOR and CEIL. The mitigation is a no-op here.
{
  diff_count = 0;
  for(off = 0, 99,
    s_probe = base + off;
    bp = buy_pre(s_probe, 0, SELL_LOW, BUY_HIGH);
    bq = buy_post(s_probe, 0, SELL_LOW, BUY_HIGH);
    if(bq != bp, diff_count = diff_count + 1);
  );
  printf("  swept 100 consecutive s values at slippage = 0\n");
  printf("  divergent inputs: %d\n", diff_count);
  if(diff_count == 0, print("OK: slippage=0 regime is rounding-mode-insensitive."), print("FAIL: slippage=0 inputs differ between pre and post."));
}
print("");

print("Done. Run with `gp -q < ceil_rounding_witness.gp`.");
