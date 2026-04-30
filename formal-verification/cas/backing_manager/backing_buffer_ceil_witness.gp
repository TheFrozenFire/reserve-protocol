\\ backing_buffer_ceil_witness.gp
\\
\\ Witnesses for the CEIL-vs-FLOOR rounding-mode change introduced by
\\ PR #1283 (commit 7bf3a1ed) on the `needed` computation in
\\ BackingManager.forwardRevenue.
\\
\\ Pre-mitigation:
\\   uint192 needed = rToken.basketsNeeded().mul(FIX_ONE + backingBuffer);
\\   (no rounding mode → defaults to FLOOR per Fixed.sol)
\\
\\ Post-mitigation:
\\   uint192 needed = rToken.basketsNeeded().mul(FIX_ONE + backingBuffer, CEIL);
\\
\\ Effect: when (basketsNeeded * (FIX_ONE + backingBuffer)) is not a
\\ multiple of FIX_ONE, the FLOOR truncation under-charges by 1 wei,
\\ which let 1 wei of collateral leak out as "excess" before
\\ basketsNeeded was fully covered. Post-mitigation always holds back
\\ at least the exact-rational ceiling, so any leak is impossible.
\\
\\ This script:
\\   (A) Confirms direction at calibrated input.
\\   (B) Surfaces a witness corpus where pre/post differ by 1 wei.
\\   (C) Verifies the gap is exactly 0 or 1 wei (never larger).
\\   (D) Sanity: at backingBuffer = 0, pre == post regardless of basketsNeeded.
\\   (E) High-buffer regime: at MAX_BACKING_BUFFER and at fractional buf
\\       values near MAX, where the CEIL bump is most likely to fire.

print("=== BackingManager backing-buffer CEIL witness (PR #1283) ===");
print("");

FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;
MAX_BACKING_BUFFER = FIX_ONE;          \\ contracts/p1/BackingManager.sol L34

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ Pre / post-mitigation inner mul.
fix_mul_floor(x, y) = (x * y) \ FIX_ONE;
fix_mul_ceil(x, y)  = ceil_div(x * y, FIX_ONE);

needed_pre(bn, buf)  = fix_mul_floor(bn, FIX_ONE + buf);
needed_post(bn, buf) = fix_mul_ceil(bn, FIX_ONE + buf);

\\ Calibration ($1M BU, 1% buffer).
BASKETS_NEEDED = 10^6 * FIX_ONE;
BACKING_BUFFER = 10^16;

\\ ---- (A) Direction at the calibrated input ----
print("--- (A) Pre vs post at calibrated inputs ---");
n_pre  = needed_pre(BASKETS_NEEDED, BACKING_BUFFER);
n_post = needed_post(BASKETS_NEEDED, BACKING_BUFFER);
{ printf("  needed_pre  (FLOOR) = %d\n", n_pre); }
{ printf("  needed_post (CEIL)  = %d\n", n_post); }
{ printf("  delta (post - pre) wei = %d\n", n_post - n_pre); }
if(n_post >= n_pre, print("OK: post-mitigation needed >= pre-mitigation needed at calibration."), print("FAIL: post-mitigation needed < pre-mitigation needed."));
\\ At the calibrated round-number input the product is exact, so pre==post.
if(n_post == n_pre, print("OK: at the calibrated round-number input, no divergence (CEIL no-op)."), print("OK: at calibrated input, post bumped above pre by an explicit wei (mitigation active)."));
print("");

\\ ---- (B) Boundary witness corpus near production ----
print("--- (B) Boundary witness corpus (basketsNeeded sweep at buf=1%) ---");
\\ At buf = 1e16, FIX_ONE + buf = 101 * 10^16. gcd(101e16, 1e18) = 1e16,
\\ so the residue (bn * (101e16)) mod 1e18 walks through 100 distinct
\\ values as bn increments. Therefore ~99/100 consecutive bn values are
\\ divergent — a dense corpus.
report_witness(idx, bn, p, q, d) = printf("  #%-3d  bn=%d  pre=%d  post=%d  delta=+%d wei\n", idx, bn, p, q, d);

{
  base = BASKETS_NEEDED;
  div = [];
  for(off = 0, 199,
    bn = base + off;
    p = needed_pre(bn, BACKING_BUFFER);
    q = needed_post(bn, BACKING_BUFFER);
    if(q != p, div = concat(div, [[bn, p, q, q - p]]));
  );
  printf("  swept 200 consecutive bn values starting at $1M\n");
  printf("  divergent inputs: %d\n", #div);
  if(#div > 0,
    \\ Worst-case = largest delta. Show the first five witnesses.
    cs = vecsort(div, 4, 4);
    print("  first 5 witnesses (by largest delta):");
    for(i = 1, min(5, #div), report_witness(i, cs[i][1], cs[i][2], cs[i][3], cs[i][4]));
    min_d = cs[#div][4];
    if(min_d > 0, print("  OK: every divergent witness has post > pre (mitigation only ratchets up)."), print("  FAIL: a divergent witness has post <= pre."));
    if(cs[1][4] <= 1, print("  OK: worst-case gap is 1 wei (D18 rounding bound)."), print("  FAIL: gap exceeds 1 wei."));
  );
  if(#div == 0, print("  (no divergent witnesses in this slice — try a different buf)"));
}
print("");

\\ ---- (C) Gap is exactly 0 or 1 wei across a wide sweep ----
print("--- (C) Gap is in {0, 1} wei across all (bn, buf) ---");
setrand(20260429);
{
  N = 10000;
  gap0 = 0;
  gap1 = 0;
  gap_other = 0;
  for(i = 1, N,
    bn = 1 + random(10^9 * FIX_ONE);
    buf = random(MAX_BACKING_BUFFER + 1);
    g = needed_post(bn, buf) - needed_pre(bn, buf);
    if(g == 0, gap0 = gap0 + 1,
      if(g == 1, gap1 = gap1 + 1, gap_other = gap_other + 1));
  );
  printf("  N=%d random samples: gap=0: %d, gap=1: %d, gap>1: %d\n", N, gap0, gap1, gap_other);
  if(gap_other == 0, print("  OK: gap is always in {0, 1} wei."), print("  FAIL: observed a gap > 1 wei."));
}
print("");

\\ ---- (D) backingBuffer = 0 ----
print("--- (D) backingBuffer = 0: pre == post for any basketsNeeded ---");
{
  diff = 0;
  for(off = 0, 999,
    bn = BASKETS_NEEDED + off;
    p = needed_pre(bn, 0);
    q = needed_post(bn, 0);
    if(q != p, diff = diff + 1);
    if(p != bn, diff = diff + 1);            \\ also verify needed == basketsNeeded
  );
  printf("  swept 1000 consecutive bn values at buf=0\n");
  printf("  divergent or non-identity inputs: %d\n", diff);
  if(diff == 0, print("  OK: buf=0 regime is rounding-mode-insensitive and identity."), print("  FAIL: buf=0 inputs differ between pre/post or fail identity."));
}
print("");

\\ ---- (E) High-buffer regime: maximally divergent witnesses ----
print("--- (E) Buffer near MAX_BACKING_BUFFER: most divergent witnesses ---");
\\ The CEIL bump fires when (bn * (FIX_ONE + buf)) mod FIX_ONE != 0.
\\ For buf = MAX - 1 = FIX_ONE - 1, the residue cycles densely.
report_high(idx, bn, buf, p, q) = printf("  #%-2d  bn=%d  buf=%d  pre=%d  post=%d  delta=+%d wei\n", idx, bn, buf, p, q, q - p);
{
  high_bufs = [MAX_BACKING_BUFFER, MAX_BACKING_BUFFER - 1, MAX_BACKING_BUFFER \ 2 + 1, MAX_BACKING_BUFFER \ 2 - 1, MAX_BACKING_BUFFER \ 4 - 1];
  any_fail = 0;
  for(j = 1, #high_bufs,
    buf = high_bufs[j];
    \\ pick the smallest bn that produces a 1-wei gap.
    found = 0;
    for(bn = 1, 1000,
      p = needed_pre(bn, buf);
      q = needed_post(bn, buf);
      if(q > p,
        report_high(j, bn, buf, p, q);
        if(q - p > 1, any_fail = 1);
        found = 1;
        break;
      );
    );
    if(found == 0,
      printf("  buf=%d: no witness in bn=[1, 1000] (this buf has special algebraic structure)\n", buf);
    );
  );
  if(any_fail == 0, print("  OK: high-buffer witnesses respect the 1-wei gap bound."), print("  FAIL: high-buffer regime exhibits gap > 1 wei."));
}
print("");

\\ ---- (F) MAX_BACKING_BUFFER (= FIX_ONE) is exactly 2x ----
print("--- (F) buf = MAX_BACKING_BUFFER: needed = 2 * basketsNeeded exactly ---");
{
  doubled_ok = 1;
  for(off = 0, 99,
    bn = BASKETS_NEEDED + off;
    n_max = needed_post(bn, MAX_BACKING_BUFFER);
    if(n_max != 2 * bn, doubled_ok = 0);
  );
  if(doubled_ok, print("  OK: at buf=MAX, needed_post == 2 * basketsNeeded for 100 consecutive bn values."), print("  FAIL: needed at buf=MAX deviates from 2*basketsNeeded — algebraic mismatch."));
}
print("");

print("Done. Run with `gp -q < backing_buffer_ceil_witness.gp`.");
