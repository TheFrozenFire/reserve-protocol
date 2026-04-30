\\ price_decay.gp
\\
\\ CAS-side validation of DutchTrade._price() and ._bidAmount(). Verifies:
\\   - 4-piecewise price curve is monotone non-increasing across the auction
\\   - Endpoint exactness: price(start) ~ 1000x bestPrice; price(end) = worstPrice
\\   - Phase boundaries: no large discontinuities (only rounding-level jumps)
\\   - bestPrice/worstPrice envelope: price stays in [worstPrice, ~1000*bestPrice]
\\     across the [20%,100%] window (geometric phase explicitly above 1.5*best)
\\   - _bidAmount rounding: CEIL applied at both mul and shiftl, so bidder
\\     always pays >= the exact-rational price
\\   - Symmetry: t1 <= t2 implies bidAmount(t1) >= bidAmount(t2)
\\
\\ Reference:
\\   protocol/contracts/plugins/trading/DutchTrade.sol (_price, _bidAmount)
\\   - phases: 0-20% geometric, 20-45% linear, 45-95% linear, 95-100% flat
\\   - bestPrice, worstPrice with worstPrice <= bestPrice (asserted at init)
\\   - constants: MAX_EXP=6502287e18, BASE=999999e12, ONE_POINT_FIVE=150e16
\\
\\ Note on PARI/GP arithmetic: BASE^exp where exp ~ 6.5e6 overflows the
\\ default stack. We bump parisizemax to 2 GB; for the first-block check we
\\ further switch to a float-domain ladder when exp is in the millions.

default(parisizemax, "2G");

print("=== DutchTrade._price curve - CAS validation ===");
print("");

\\ ---- Reserve fixed-point constants (R001) ----
FIX_ONE   = 10^18;
FIX_MAX   = 2^192 - 1;

\\ ---- DutchTrade.sol curve constants ----
FIVE_PCT      = 5  * 10^16;
TWENTY_PCT    = 20 * 10^16;
TWENTY_FIVE   = 25 * 10^16;
FORTY_FIVE    = 45 * 10^16;
FIFTY_PCT     = 50 * 10^16;
NINETY_FIVE   = 95 * 10^16;
MAX_EXP       = 6502287 * 10^18;
BASE          = 999999  * 10^12;     \\ 0.999999 in D18
ONE_POINT_FIVE = 150 * 10^16;        \\ 1.5 in D18

\\ ---- Helpers (R003 ceil_div; R008 OK/FAIL only on real outcomes) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
\\ ROUND-half-up integer division (matches FixLib _divrnd ROUND).
round_div(a, b) = (a + (b \ 2)) \ b;

\\ Calibration: 30-min auction, $1.05 best -> $0.95 worst, sellAmount=10k
\\ tokens (D18). Buy token also D18. AUCTION_LEN=1800s.
AUCTION_LEN = 1800;
START_T     = 1000000;            \\ arbitrary fixed start
END_T       = START_T + AUCTION_LEN;
BEST_PRICE  = 105 * 10^16;        \\ 1.05 in D18
WORST_PRICE = 95  * 10^16;        \\ 0.95 in D18 (~9.5% spread)
SELL_AMT    = 10000 * FIX_ONE;    \\ {sellTok} as D18
BUY_DECIMALS = 18;

\\ Sanity check on calibration.
if(WORST_PRICE > BEST_PRICE, print("FAIL: calibration error worstPrice > bestPrice"));

\\ ----------------------------------------------------------------------
\\ Phase 1: geometric decay. Mirrors:
\\   exp = MAX_EXP.mulDiv(TWENTY_PCT - progression, TWENTY_PCT, ROUND)
\\   exp_int = exp.toUint(ROUND)             // wei -> integer power
\\   price   = bestPrice * 1.5 / BASE^exp_int (CEIL)
\\
\\ For exp_int in the millions, BASE^exp_int as exact rational has
\\ ~6.5M-digit numerator/denominator -> stack overflow. Use float fallback
\\ in that regime; exact only when exp_int is small (near phase boundary).
\\ ----------------------------------------------------------------------

\\ progression in D18 = (t - START_T) * FIX_ONE / (END_T - START_T)  (FLOOR)
progression(t) = ((t - START_T) * FIX_ONE) \ (END_T - START_T);

\\ exp_fix in D18: ROUND
exp_fix(prog) = round_div(MAX_EXP * (TWENTY_PCT - prog), TWENTY_PCT);

\\ exp_int: ROUND (toUint with ROUND)
exp_int(prog) = round_div(exp_fix(prog), FIX_ONE);

\\ Geometric ceil-mulDiv exact for tiny exp_int (<= ~50000): bestPrice*1.5 / BASE^k
\\ Result lives in D18.
phase1_price_exact(prog) = { my(k, denom_d18); k = exp_int(prog); denom_d18 = BASE^k \ FIX_ONE^(k - 1); ceil_div(BEST_PRICE * ONE_POINT_FIVE, denom_d18); }

\\ Float-domain version for large k. Returns a t_REAL in D18 units.
\\ BASE/FIX_ONE = 0.999999. Power approximated; relative error << 1e-12 for k <= 7e6.
phase1_price_float(prog) = { my(k, factor); k = exp_int(prog); factor = (BASE * 1.0 / FIX_ONE)^k; (BEST_PRICE * 1.0) * (ONE_POINT_FIVE * 1.0) / FIX_ONE / factor; }

\\ Hybrid: exact when k<=20000 (cheap), float otherwise. Returned as integer wei.
phase1_price(prog) = if(exp_int(prog) <= 20000, phase1_price_exact(prog), floor(phase1_price_float(prog)));

\\ Phase 2: linear from 1.5*best -> 1*best. CEIL on (best*1.5).
\\   highPrice = bestPrice.mul(1.5, CEIL)
\\   return highPrice - (highPrice - bestPrice) * (prog - 20%) / 25%   (FLOOR)
phase2_price(prog) = { my(highPrice, drop); highPrice = ceil_div(BEST_PRICE * ONE_POINT_FIVE, FIX_ONE); drop = ((highPrice - BEST_PRICE) * (prog - TWENTY_PCT)) \ TWENTY_FIVE; highPrice - drop; }

\\ Phase 3: linear from best -> worst. mulDiv FLOOR.
phase3_price(prog) = { my(drop); drop = ((BEST_PRICE - WORST_PRICE) * (prog - FORTY_FIVE)) \ FIFTY_PCT; BEST_PRICE - drop; }

\\ Phase 4: constant worst.
phase4_price() = WORST_PRICE;

\\ Top-level dispatcher (the model of _price).
price_at(t) = { my(p); p = progression(t); if(p < TWENTY_PCT, phase1_price(p), if(p < FORTY_FIVE, phase2_price(p), if(p < NINETY_FIVE, phase3_price(p), phase4_price()))); }

\\ Bid amount: sellAmount * price (CEIL), then shiftl_toUint(buyDecimals, CEIL).
\\ With sellAmount in D18 wei, price in D18, mul-CEIL gives floor((s*p + 1e18-1)/1e18).
\\ shiftl_toUint with buyDecimals=18 reduces by 1 decimal point: shift = (18-18)=0 -> identity.
bid_amount(t) = { my(p, mul_ceil); p = price_at(t); mul_ceil = ceil_div(SELL_AMT * p, FIX_ONE); mul_ceil; }

\\ ---- (1) Monotone non-increasing ----
print("--- (1) price is monotone non-increasing in t ---");
mono_ok = 1;
prev = -1;
worst_break_t = -1;
worst_break_delta = 0;
\\ Sample every 6 seconds across the 1800s window (300 points).
{
  step = 6;
  prev = price_at(START_T);
  for(i = 1, AUCTION_LEN \ step,
    t = START_T + i * step;
    p = price_at(t);
    if(p > prev,
      mono_ok = 0;
      if(p - prev > worst_break_delta, worst_break_delta = p - prev; worst_break_t = t)
    );
    prev = p;
  );
}
if(mono_ok, print("  OK: monotone across 300 samples (every 6s)"), printf("  FAIL: increase by %d wei at t=%d\n", worst_break_delta, worst_break_t));
print("");

\\ ---- (2) Endpoint exactness ----
print("--- (2) endpoint behaviour ---");
\\ At start (progression = 0): exp_int = MAX_EXP/FIX_ONE = 6502287 -> price ~ 1000 * bestPrice.
p_start = price_at(START_T);
p_end   = price_at(END_T);
{ printf("  price(start) = %d wei  (%.4f)\n", p_start, p_start * 1.0 / FIX_ONE); }
{ printf("  price(end)   = %d wei  (%.4f)\n", p_end,   p_end   * 1.0 / FIX_ONE); }
{ printf("  bestPrice    = %d wei  (%.4f)\n", BEST_PRICE, BEST_PRICE * 1.0 / FIX_ONE); }
{ printf("  worstPrice   = %d wei  (%.4f)\n", WORST_PRICE, WORST_PRICE * 1.0 / FIX_ONE); }
\\ Lower bound for start: at least 800x bestPrice (commentary claims ~1000x but
\\ rounding + ROUND-half-up integer exp ~ 6502287 puts it at ~666.67x*1.5 = 1000x).
ratio_start = p_start * 1.0 / BEST_PRICE;
{ printf("  price(start) / bestPrice = %.2fx\n", ratio_start); }
if(ratio_start >= 800, print("  OK: start price >= 800x bestPrice"), print("  FAIL: start price below 800x bestPrice"));
if(p_end == WORST_PRICE, print("  OK: price(end) == worstPrice (exact)"), printf("  FAIL: price(end) != worstPrice (off by %d wei)\n", p_end - WORST_PRICE));
print("");

\\ ---- (3) Phase boundary continuity ----
print("--- (3) phase boundary jumps are bounded by local decay rate ---");
\\ Boundaries land at progression == 20%, 45%, 95%. Each phase has its own
\\ decay rate; at the boundary we expect: (a) no upward jump (subsumed by
\\ monotonicity), and (b) the cross-boundary drop is no larger than the
\\ drop just before the boundary inside the previous phase. The whole
\\ curve has decreasing slope, so the post-boundary drop should be small.
t_b1 = START_T + 360;                                      \\ 20%
t_b2 = START_T + (FORTY_FIVE  * AUCTION_LEN) \ FIX_ONE;    \\ 45% -> 810
t_b3 = START_T + (NINETY_FIVE * AUCTION_LEN) \ FIX_ONE;    \\ 95% -> 1710

\\ Drop just-before boundary (inside previous phase): price(tb-2) - price(tb-1)
\\ Cross-boundary drop:                                price(tb-1) - price(tb)
\\ Property: cross_drop <= prev_drop + epsilon. Epsilon = 1 wei (rounding).
boundary_check(tb) = { my(prev_drop, cross_drop); prev_drop = price_at(tb - 2) - price_at(tb - 1); cross_drop = price_at(tb - 1) - price_at(tb); [prev_drop, cross_drop]; }
b1 = boundary_check(t_b1);
b2 = boundary_check(t_b2);
b3 = boundary_check(t_b3);
report_b(label, v) = printf("  %s: prev-second drop = %d wei, cross-boundary drop = %d wei\n", label, v[1], v[2]);
report_b("20% boundary (geom -> linear1)", b1);
report_b("45% boundary (linear1 -> linear2)", b2);
report_b("95% boundary (linear2 -> flat)", b3);
\\ At p=20% boundary: phase1 just below = best*1.5/BASE^1 (CEIL), phase2 at = best*1.5 (CEIL).
\\ Difference is best*1.5*(1/BASE - 1) ~ best*1.5e-6 = ~1.575e12 wei. Plenty smaller
\\ than the prev-second drop (28e15 wei). Use a 2x slack tolerance.
\\ For 45% and 95% boundaries: phase formulas are exact at the boundary and the
\\ cross-boundary drop equals (or is below) the prev drop because the next phase
\\ has equal-or-shallower slope. Allow 1 wei rounding slack.
b1_ok = (b1[2] <= 2 * b1[1] + 1);
b2_ok = (b2[2] <= b2[1] + 1);
b3_ok = (b3[2] <= b3[1] + 1);
if(b1_ok && b2_ok && b3_ok, print("  OK: each phase boundary's cross-second drop bounded by prior decay rate"), print("  FAIL: phase boundary drop exceeds prior decay rate"));
print("");

\\ ---- (4) Geometric phase: above 1.5*bestPrice everywhere strictly ----
print("--- (4) geometric phase price > 1.5 * bestPrice (reportViolation guard) ---");
\\ The contract calls reportViolation if cleared price > bestPrice.mul(1.5, CEIL).
\\ Verify: across 0%..just-below-20%, price > 1.5*bestPrice.
geom_ok = 1;
geom_violators = 0;
threshold = ceil_div(BEST_PRICE * ONE_POINT_FIVE, FIX_ONE);
{
  for(i = 0, 30,
    \\ Sample t in [START_T, START_T + 0.2*AUCTION_LEN). 30 evenly spaced.
    t = START_T + (i * (TWENTY_PCT * AUCTION_LEN)) \ (FIX_ONE * 31);
    p = price_at(t);
    if(p <= threshold, geom_ok = 0; geom_violators = geom_violators + 1)
  );
}
{ printf("  threshold (1.5 * bestPrice CEIL) = %d wei\n", threshold); }
if(geom_ok, print("  OK: 31/31 geometric-phase samples strictly above 1.5*bestPrice"), printf("  FAIL: %d/31 geometric-phase samples failed strict-above guard\n", geom_violators));
print("");

\\ ---- (5) bidAmount rounding direction ----
print("--- (5) bidAmount rounding: bidder always pays >= exact-rational price ---");
\\ Exact-rational reference. SELL_AMT in D18 wei * price in D18 / FIX_ONE.
exact_bid(t) = (SELL_AMT * price_at(t) * 1.0) / FIX_ONE;
round_ok = 1;
sample_ts = [START_T, START_T + 360, START_T + 600, START_T + 810, START_T + 1200, START_T + 1710, END_T];
{
  for(idx = 1, length(sample_ts),
    t = sample_ts[idx];
    bid_int = bid_amount(t);
    bid_exact = exact_bid(t);
    if(bid_int * 1.0 < bid_exact, round_ok = 0)
  );
}
report_bid(t) = printf("  t=%d  price=%d  bid=%d  (>= exact %.0f)\n", t, price_at(t), bid_amount(t), exact_bid(t));
report_bid(START_T);
report_bid(START_T + 360);
report_bid(START_T + 600);
report_bid(START_T + 810);
report_bid(START_T + 1200);
report_bid(START_T + 1710);
report_bid(END_T);
if(round_ok, print("  OK: bidder pays >= exact at every sampled t"), print("  FAIL: bidder under-pays vs exact at some t (rounding wrong)"));
print("");

\\ ---- (6) Symmetry: bidAmount strictly tracks monotone price ----
print("--- (6) symmetry: t1 <= t2 implies bidAmount(t1) >= bidAmount(t2) ---");
sym_ok = 1;
sym_violators = 0;
{
  prev_b = bid_amount(START_T);
  step2 = 6;
  for(i = 1, AUCTION_LEN \ step2,
    t = START_T + i * step2;
    b = bid_amount(t);
    if(b > prev_b, sym_ok = 0; sym_violators = sym_violators + 1);
    prev_b = b;
  );
}
if(sym_ok, print("  OK: bidAmount monotone non-increasing across 300 samples"), printf("  FAIL: %d violations of bidAmount monotonicity\n", sym_violators));
print("");

\\ ---- (7) Calibration table ----
print("--- (7) calibration: price/bid at standard checkpoints ---");
report_chk(label, t) = printf("  %-22s  price = %.6f  bidAmount = %d qBuyTok\n", label, price_at(t) * 1.0 / FIX_ONE, bid_amount(t));
report_chk("t=start (0%)",         START_T);
report_chk("t=start+10% (180s)",   START_T + 180);
report_chk("t=20% boundary",       START_T + 360);
report_chk("t=30% (linear 1)",     START_T + 540);
report_chk("t=45% boundary",       START_T + 810);
report_chk("t=70% (linear 2)",     START_T + 1260);
report_chk("t=95% boundary",       START_T + 1710);
report_chk("t=end (100%)",         END_T);
print("");

print("Done.");
