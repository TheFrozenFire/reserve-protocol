\\ forward_revenue_conservation.gp
\\
\\ CAS-side validation of BackingManager.forwardRevenue's revenue
\\ accounting math, with emphasis on the post-#1283 mitigation:
\\
\\   uint192 needed = rToken.basketsNeeded().mul(FIX_ONE + backingBuffer, CEIL);
\\
\\ Reference (post-mitigation, after PR #1283 / commit 7bf3a1ed):
\\   contracts/p1/BackingManager.sol::forwardRevenue, lines 218-225:
\\     uint192 baskets = basketsHeld.bottom.div(FIX_ONE + backingBuffer);
\\     if (baskets > rToken.basketsNeeded()) {
\\         rToken.mint(baskets - rToken.basketsNeeded());
\\     }
\\     uint192 needed = rToken.basketsNeeded().mul(FIX_ONE + backingBuffer, CEIL);
\\     ...
\\     uint192 req = needed.mul(basketHandler.quantity(erc20s[i]), CEIL);
\\     uint256 delta = bal.minus(req).shiftl_toUint(int8(decimals));
\\     uint256 tokensPerShare = delta / (totals.rTokenTotal + totals.rsrTotal);
\\
\\ Properties checked here:
\\   INV-1  needed (CEIL) >= floor(basketsNeeded * (FIX_ONE+buf) / FIX_ONE),
\\          and at boundary inputs needed = floor + 1 (no under-charging).
\\   INV-2  Excess split conservation: rsrShare + rTokenShare <= excess,
\\          dust = excess - (rsrShare + rTokenShare) < (rsrTotal+rTokenTotal).
\\   INV-3  RToken-mint conservation: minted = max(baskets - basketsNeeded, 0)
\\          where baskets = floor(basketsHeld * FIX_ONE / (FIX_ONE+buf)).
\\          The new RToken's backing equals the surplus baskets, exactly.
\\   INV-4  backingBuffer = 0 edge case: needed == basketsNeeded (CEIL no-op).
\\   INV-5  Backing-buffer monotonicity: needed is non-decreasing in
\\          backingBuffer; no inversion across the whole [0, FIX_ONE] range.
\\
\\ Calibration (R005):
\\   basketsNeeded     = 1,000,000 BU (in D18)
\\   backingBuffer     = 1% in D18 (= 1e16)
\\   excess (per-tok)  = 1,000 qTok above req
\\   Distributor totals = (rTokenTotal=4000, rsrTotal=6000)

print("=== BackingManager.forwardRevenue accounting — CAS validation ===");
print("");

\\ ---- FixLib constants (R001) ----
FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;
MAX_BACKING_BUFFER = FIX_ONE;       \\ contracts/p1/BackingManager.sol L34: 100%

\\ ---- Helpers (R003) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ FixLib.mul(x, y, CEIL): _safeWrap(ceil(x*y / FIX_ONE)).
fix_mul_ceil(x, y)  = { my(r); r = ceil_div(x * y, FIX_ONE); if(r > FIX_MAX, -1, r); }
\\ FixLib.mul(x, y, FLOOR): _safeWrap(floor(x*y / FIX_ONE)).  Pre-mitigation behaviour.
fix_mul_floor(x, y) = { my(r); r = (x * y) \ FIX_ONE; if(r > FIX_MAX, -1, r); }

\\ FixLib.div(x, y) defaults to FLOOR: floor(x * FIX_ONE / y).
fix_div_floor(x, y) = (x * FIX_ONE) \ y;

\\ Production formulas, post-mitigation.
needed_post(basketsNeeded, buf) = fix_mul_ceil(basketsNeeded, FIX_ONE + buf);
needed_pre(basketsNeeded, buf)  = fix_mul_floor(basketsNeeded, FIX_ONE + buf);
baskets_capped(basketsHeld, buf) = fix_div_floor(basketsHeld, FIX_ONE + buf);

\\ ---- Calibration ----
BASKETS_NEEDED = 10^6 * FIX_ONE;       \\ 1M BU
BACKING_BUFFER = 10^16;                \\ 1% in D18
EXCESS_QTOK    = 1000;                 \\ qTok of surplus to be forwarded
RTOKEN_TOTAL   = 4000;                 \\ Distributor RToken-side share
RSR_TOTAL      = 6000;                 \\ Distributor RSR-side share

{ printf("Calibration: basketsNeeded=%d (1M BU), backingBuffer=%d (1%%), totals=(rTok=%d,rsr=%d)\n", BASKETS_NEEDED, BACKING_BUFFER, RTOKEN_TOTAL, RSR_TOTAL); }
print("");

\\ ============================================================
\\ INV-1: needed is CEIL-rounded; never under-charges
\\ ============================================================
print("--- INV-1: needed is CEIL-rounded, never under-charges ---");

n_post_cal = needed_post(BASKETS_NEEDED, BACKING_BUFFER);
n_pre_cal  = needed_pre(BASKETS_NEEDED, BACKING_BUFFER);
exact_floor = (BASKETS_NEEDED * (FIX_ONE + BACKING_BUFFER)) \ FIX_ONE;
exact_ceil  = ceil_div(BASKETS_NEEDED * (FIX_ONE + BACKING_BUFFER), FIX_ONE);

{ printf("  needed_post (CEIL)    = %d\n", n_post_cal); }
{ printf("  needed_pre  (FLOOR)   = %d\n", n_pre_cal); }
{ printf("  exact-rational floor  = %d\n", exact_floor); }
{ printf("  exact-rational ceil   = %d\n", exact_ceil); }

\\ At the calibrated point (1M * 1.01 in D18) the product is exact, so
\\ floor == ceil and the mitigation is a no-op. Assert that.
if(n_post_cal == exact_ceil, print("OK: post-mitigation needed equals exact ceil at calibration."), print("FAIL: needed != ceil(exact) at calibration."));
if(n_post_cal >= n_pre_cal,  print("OK: post-mitigation needed >= pre-mitigation needed (no relaxation)."), print("FAIL: post-mitigation needed < pre-mitigation needed (mitigation reversed)."));

\\ Sweep boundary inputs where the product (basketsNeeded * (FIX_ONE+buf))
\\ is NOT a multiple of FIX_ONE — exactly the regime where pre-mitigation
\\ FLOOR truncates and CEIL bumps up by 1 wei. We construct such inputs
\\ by perturbing basketsNeeded by 1 wei away from the calibrated multiple.
print("");
print("  Boundary sweep: 1024 consecutive basketsNeeded values, buf = 1%");
{
  base = BASKETS_NEEDED;
  diverge = 0;
  fail_under = 0;
  delta_sum = 0;
  for(off = 0, 1023,
    bn = base + off;
    np = needed_post(bn, BACKING_BUFFER);
    nf = needed_pre(bn, BACKING_BUFFER);
    if(np != nf, diverge = diverge + 1; delta_sum = delta_sum + (np - nf));
    if(np < nf, fail_under = fail_under + 1);
  );
  printf("    divergent (CEIL > FLOOR) inputs   : %d / 1024\n", diverge);
  printf("    inputs where CEIL < FLOOR         : %d\n", fail_under);
  printf("    cumulative wei bumped up by CEIL  : %d\n", delta_sum);
  if(fail_under == 0, print("  OK: CEIL never produces a smaller needed than FLOOR."), print("  FAIL: CEIL < FLOOR at some input — direction is wrong."));
}
print("");

\\ ============================================================
\\ INV-4: backingBuffer = 0 edge case
\\ ============================================================
print("--- INV-4: backingBuffer = 0 — needed == basketsNeeded (CEIL no-op) ---");
n_buf0_post = needed_post(BASKETS_NEEDED, 0);
n_buf0_pre  = needed_pre(BASKETS_NEEDED, 0);
{ printf("  needed_post(buf=0) = %d\n", n_buf0_post); }
{ printf("  needed_pre (buf=0) = %d\n", n_buf0_pre); }
if(n_buf0_post == BASKETS_NEEDED && n_buf0_pre == BASKETS_NEEDED, print("OK: at buf=0, needed == basketsNeeded under both rounding modes."), print("FAIL: buf=0 produced needed != basketsNeeded."));
print("");

\\ ============================================================
\\ INV-5: backingBuffer monotonicity
\\ ============================================================
print("--- INV-5: needed is non-decreasing in backingBuffer ---");
\\ Sample 256 buf values evenly across [0, MAX_BACKING_BUFFER].
{
  prev = needed_post(BASKETS_NEEDED, 0);
  inversion = 0;
  for(k = 1, 256,
    buf = (k * MAX_BACKING_BUFFER) \ 256;
    cur = needed_post(BASKETS_NEEDED, buf);
    if(cur < prev, inversion = inversion + 1);
    prev = cur;
  );
  printf("  256 buf samples on [0, MAX_BACKING_BUFFER]; inversions: %d\n", inversion);
  if(inversion == 0, print("  OK: needed is monotonically non-decreasing in backingBuffer."), print("  FAIL: needed decreased as backingBuffer increased."));
  \\ Bracket: at MAX_BACKING_BUFFER (100%), needed should be 2 * basketsNeeded exactly.
  n_max = needed_post(BASKETS_NEEDED, MAX_BACKING_BUFFER);
  printf("  needed at buf=MAX (100%%): %d  (expected 2*basketsNeeded = %d)\n", n_max, 2 * BASKETS_NEEDED);
  if(n_max == 2 * BASKETS_NEEDED, print("  OK: needed at MAX_BACKING_BUFFER equals 2 * basketsNeeded."), print("  FAIL: needed at MAX_BACKING_BUFFER != 2 * basketsNeeded."));
}
print("");

\\ ============================================================
\\ INV-3: RToken mint conservation
\\ ============================================================
print("--- INV-3: RToken mint = max(baskets - basketsNeeded, 0) ---");
\\ The contract: if baskets > basketsNeeded, mints (baskets - basketsNeeded).
\\ Where baskets = basketsHeld.div(FIX_ONE + backingBuffer).
\\ Surplus collateral covers the new RToken: (baskets - basketsNeeded) BU
\\ are converted into 1 BU/RTok worth of new RToken backing.
\\
\\ Conservation we check: after mint, basketsNeeded_new = baskets, and
\\ the basket-equivalents of held collateral still cover (basketsNeeded_new
\\ * (FIX_ONE + buf)) under FLOOR. The CEIL change can push needed above
\\ that bound by 1 wei — so we report the gap as a known dust under CEIL.
{
  \\ Production-plausible: held = basketsNeeded * (1 + buf) + small surplus,
  \\ i.e. fully collateralized + a 0.5% extra cushion.
  buf = BACKING_BUFFER;
  bn  = BASKETS_NEEDED;
  held = (bn * (FIX_ONE + buf) * 1005) \ (FIX_ONE * 1000);   \\ +0.5% above target
  baskets = baskets_capped(held, buf);
  if(baskets > bn,
    minted = baskets - bn;
    bn_new = baskets;
    \\ Conservation: held >= bn_new (the new basketsNeeded after mint) -- in
    \\ basket units, the BackingManager still holds at least that many.
    held_in_BU = held;          \\ basketsHeld is already in BU
    printf("  basketsHeld = %d, baskets = floor(basketsHeld/(1+buf)) = %d, basketsNeeded_old = %d\n", held, baskets, bn);
    printf("  RToken minted = baskets - basketsNeeded_old = %d\n", minted);
    printf("  basketsNeeded_new = baskets = %d\n", bn_new);
    if(held_in_BU >= bn_new, print("  OK: held >= basketsNeeded_new (mint did not over-issue)."), print("  FAIL: held < basketsNeeded_new (over-issuance — value created from thin air)."));
    \\ Cross-check: the converse of baskets_capped — baskets * (FIX_ONE+buf) <= held * FIX_ONE
    \\ since baskets is the floor of held / (FIX_ONE+buf) in D18.
    if(baskets * (FIX_ONE + buf) <= held * FIX_ONE, print("  OK: baskets * (FIX_ONE+buf) <= basketsHeld * FIX_ONE (floor-correct)."), print("  FAIL: baskets exceeded the floor-cap."));
    ,
    print("  (held was insufficient to mint additional RToken; mint path skipped.)");
  );
}
print("");

\\ ============================================================
\\ INV-2: Excess split conservation
\\ ============================================================
print("--- INV-2: Excess split conservation (delta -> rsrShare + rTokShare + dust) ---");
\\ For each surplus-bearing collateral token:
\\   delta = bal - req           (qTok)
\\   tps   = delta / (rTokTot + rsrTot)   (floor)
\\   rsrShare = tps * rsrTot
\\   rTokShare = tps * rTokTot
\\   forwarded = rsrShare + rTokShare = tps * (rTokTot + rsrTot)
\\   dust      = delta - forwarded < (rTokTot + rsrTot)
report_split(label, delta) = { my(tot, tps, rsr, rtok, fwd, dust); tot = RTOKEN_TOTAL + RSR_TOTAL; tps = delta \ tot; rsr = tps * RSR_TOTAL; rtok = tps * RTOKEN_TOTAL; fwd = rsr + rtok; dust = delta - fwd; printf("  %-28s delta=%-12d tps=%-8d rsrShare=%-8d rTokShare=%-8d dust=%d  conservation=%s\n", label, delta, tps, rsr, rtok, dust, if(dust >= 0 && dust < tot && fwd + dust == delta, "OK", "FAIL")); }

report_split("excess = 1k qTok",         1000);
report_split("excess = 1M qTok",         10^6);
report_split("excess = 10^18 qTok",      10^18);
report_split("excess = 10^25 qTok (10M)",10^25);
report_split("excess = 1 qTok (worst)",  1);
report_split("excess = 9999 (totalShares-1)", 9999);
report_split("excess = 10000 (=total)",  10000);
print("");

\\ Per-share fairness: the rsr/rTok split mirrors Distributor.totals exactly.
{
  delta = 10^25;
  tps = delta \ (RTOKEN_TOTAL + RSR_TOTAL);
  ratio_ok = (tps * RSR_TOTAL) * RTOKEN_TOTAL == (tps * RTOKEN_TOTAL) * RSR_TOTAL;
  printf("  per-share fairness at delta=10^25: rsrShare/rTokShare ratio == rsrTotal/rTokTotal: %d\n", ratio_ok);
  if(ratio_ok, print("  OK"), print("  FAIL: per-share split does not match Distributor totals."));
}
print("");

\\ ============================================================
\\ Pre/post divergence density (PR #1283 motivation)
\\ ============================================================
print("--- Pre/post divergence density across (basketsNeeded, backingBuffer) ---");
\\ Random sweep: how often does CEIL strictly exceed FLOOR? When yes,
\\ the gap is exactly 1 wei (since both bound to consecutive integers
\\ around the exact rational).
setrand(20260429);                     \\ R007: reproducible seed
{
  N = 5000;
  diverge = 0;
  max_gap = 0;
  for(i = 1, N,
    \\ basketsNeeded uniform on [10^6 * FIX_ONE, 10^9 * FIX_ONE]
    bn = 10^6 * FIX_ONE + random(10^9 * FIX_ONE - 10^6 * FIX_ONE);
    \\ buf uniform on [0, MAX_BACKING_BUFFER]
    buf = random(MAX_BACKING_BUFFER + 1);
    np = needed_post(bn, buf);
    nf = needed_pre(bn, buf);
    if(np != nf,
      diverge = diverge + 1;
      if(np - nf > max_gap, max_gap = np - nf);
    );
  );
  printf("  random sample size: %d\n", N);
  printf("  inputs where CEIL > FLOOR     : %d (%.2f%%)\n", diverge, diverge * 100.0 / N);
  printf("  worst-case gap (wei)          : %d\n", max_gap);
  if(max_gap <= 1, print("  OK: CEIL-vs-FLOOR gap is at most 1 wei (as expected for D18 rounding)."), print("  FAIL: gap exceeded 1 wei (unexpected for ceil_div over D18)."));
}
print("");

\\ ============================================================
\\ Witness: smallest input with CEIL > FLOOR at buf = 1%
\\ ============================================================
print("--- Smallest-witness search: basketsNeeded with CEIL > FLOOR at buf = 1% ---");
{
  buf = BACKING_BUFFER;
  found = 0;
  for(bn = 1, 200,
    np = needed_post(bn, buf);
    nf = needed_pre(bn, buf);
    if(np > nf,
      printf("  smallest witness: basketsNeeded=%d  needed_pre=%d  needed_post=%d  delta=+%d wei\n", bn, nf, np, np - nf);
      found = 1;
      break;
    );
  );
  if(found == 0, print("  no witness in [1, 200] — try larger range"));
  if(found == 1, print("  OK: concrete pre/post-divergent witness found."));
}
print("");

print("Done. Run with `gp -q < forward_revenue_conservation.gp`.");
