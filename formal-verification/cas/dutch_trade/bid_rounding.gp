\\ bid_rounding.gp
\\
\\ CAS-side validation of DutchTrade._bidAmount() rounding direction across
\\ asymmetric buy-token decimals. The contract:
\\
\\   amountIn = sellAmount.mul(price, CEIL).shiftl_toUint(buyDecimals, CEIL)
\\
\\ is meant to ensure the bidder always pays *at least* the exact-rational
\\ price * sellAmount. We probe two regimes:
\\
\\   - 18-decimal buy token (no decimal shift; only mul-CEIL applies)
\\   - 6-decimal buy token  (USDC; shiftl_toUint reduces by 12 decimals)
\\
\\ The 6-decimal case is where rounding behaviour matters most: a single
\\ wei of qBuyTok corresponds to 1e12 wei of D18 fixed-point, so any
\\ accidental FLOOR could under-deliver $0.000001 per bid trivially.
\\
\\ Reference:
\\   protocol/contracts/plugins/trading/DutchTrade.sol::_bidAmount
\\   protocol/contracts/libraries/Fixed.sol::shiftl_toUint (CEIL branch)

print("=== DutchTrade._bidAmount rounding - CAS validation ===");
print("");

\\ ---- Reserve fixed-point constants ----
FIX_ONE = 10^18;

\\ ---- Helpers ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
\\ FixLib mul(x, y, CEIL) on D18 fixed-point.
mul_fix_ceil(x, y) = ceil_div(x * y, FIX_ONE);
\\ FixLib mul(x, y, FLOOR).
mul_fix_floor(x, y) = (x * y) \ FIX_ONE;
\\ shiftl_toUint(x, decimals, CEIL): for decimals < 18, divides by 10^(18-d) ceiled.
shiftl_to_uint_ceil(x, decimals) = { my(shift); shift = 18 - decimals; if(shift <= 0, x * 10^(-shift), ceil_div(x, 10^shift)); }
shiftl_to_uint_floor(x, decimals) = { my(shift); shift = 18 - decimals; if(shift <= 0, x * 10^(-shift), x \ 10^shift); }

\\ Production model.
bid_amount_production(sell_d18, price_d18, buy_decimals) = shiftl_to_uint_ceil(mul_fix_ceil(sell_d18, price_d18), buy_decimals);

\\ Hypothetical FLOOR-only variant for comparison (the bug).
bid_amount_floor(sell_d18, price_d18, buy_decimals) = shiftl_to_uint_floor(mul_fix_floor(sell_d18, price_d18), buy_decimals);

\\ Exact rational. Returns t_REAL.
bid_amount_exact(sell_d18, price_d18, buy_decimals) = (sell_d18 * 1.0) * (price_d18 * 1.0) / FIX_ONE / 10^(18 - buy_decimals);

\\ ---- (1) 18-decimal buy token: bidder pays >= exact ----
print("--- (1) 18-decimal buy token: production never under-pays ---");
\\ Calibration: 10000 sellTok @ several prices straddling FIX_ONE.
SELL = 10000 * FIX_ONE;
prices_18 = [1, 950000000000000000, 1000000000000000000, 1050000000000000000, 1234567890123456789, 1575000000000000001];
\\ Helper lifted to top level to dodge W019 (no nested braces).
underpays_18(p) = bid_amount_production(SELL, p, 18) * 1.0 < bid_amount_exact(SELL, p, 18);
ok18 = 1;
for(i = 1, length(prices_18), if(underpays_18(prices_18[i]), ok18 = 0));
report18(p) = printf("  price=%-22d  prod=%-25d  exact=%.0f\n", p, bid_amount_production(SELL, p, 18), bid_amount_exact(SELL, p, 18));
report18(950000000000000000);
report18(1000000000000000000);
report18(1050000000000000000);
report18(1234567890123456789);
report18(1575000000000000001);
if(ok18, print("  OK: bidder pays >= exact at every probed price (18-dec buy)"), print("  FAIL: bidder under-pays at some price (18-dec buy)"));
print("");

\\ ---- (2) 6-decimal buy token (USDC): bidder pays >= exact ----
print("--- (2) 6-decimal buy token (USDC): production never under-pays ---");
\\ With 6 decimals, the answer is in qUSDC = USDC * 10^6. A bid of $9500
\\ for 10k tokens at $0.95 should be 9_500_000_000 qUSDC.
prices_usdc = [1, 950000000000000000, 1000000000000000000, 1050000000000000000, 1234567890123456789];
underpays_6(p) = bid_amount_production(SELL, p, 6) * 1.0 < bid_amount_exact(SELL, p, 6);
ok6 = 1;
for(i = 1, length(prices_usdc), if(underpays_6(prices_usdc[i]), ok6 = 0));
report6(p) = printf("  price=%-22d  prod=%-15d  exact=%.6f\n", p, bid_amount_production(SELL, p, 6), bid_amount_exact(SELL, p, 6));
report6(950000000000000000);
report6(1000000000000000000);
report6(1050000000000000000);
report6(1234567890123456789);
if(ok6, print("  OK: bidder pays >= exact at every probed price (6-dec buy)"), print("  FAIL: bidder under-pays at some price (6-dec buy)"));
print("");

\\ ---- (3) Show CEIL > FLOOR variant on rounding-prone inputs ----
print("--- (3) CEIL discipline strictly tightens vs FLOOR variant ---");
\\ Where the two differ, CEIL must be strictly greater (by exactly 1 unit at
\\ each rounding step). Pick a price that triggers rounding in both stages.
SELL_ODD = 10000 * FIX_ONE + 1;            \\ +1 wei sellTok
PRICE_ODD = 1234567890123456789;           \\ pseudorandom non-trivial price
prod6  = bid_amount_production(SELL_ODD, PRICE_ODD, 6);
floor6 = bid_amount_floor(SELL_ODD, PRICE_ODD, 6);
diff6  = prod6 - floor6;
{ printf("  6-dec  CEIL bid  = %d qBuyTok\n", prod6); }
{ printf("  6-dec  FLOOR bid = %d qBuyTok\n", floor6); }
{ printf("  difference       = %d qBuyTok (CEIL adds at least one unit when rounding triggers)\n", diff6); }
\\ The CEIL variant must be at least as large as the FLOOR variant.
if(prod6 >= floor6, print("  OK: CEIL >= FLOOR (no under-payment regression risk)"), print("  FAIL: CEIL bid less than FLOOR bid"));
print("");

\\ ---- (4) Worst-case under-payment of FLOOR (the avoided bug) ----
print("--- (4) magnitude of avoided under-payment (CEIL vs FLOOR) ---");
\\ Across a corpus of (sell, price) pairs, count how often the two agree
\\ vs disagree on the 6-dec output, and report the max disagreement.
disagree = 0;
max_gap = 0;
N_SAMPLES = 500;
setrand(20260429);
\\ Helpers lifted to top level (W019). Use globals to accumulate.
sample_gap_6(s, p) = bid_amount_production(s, p, 6) - bid_amount_floor(s, p, 6);
record_gap(g) = if(g > 0, disagree = disagree + 1; if(g > max_gap, max_gap = g));
for(i = 1, N_SAMPLES, record_gap(sample_gap_6(1 + random(10^25), 1 + random(2 * FIX_ONE))));
{ printf("  %d/%d random pairs disagree under CEIL vs FLOOR\n", disagree, N_SAMPLES); }
{ printf("  max disagreement: %d qBuyTok (= $%.6f at $1/USDC)\n", max_gap, max_gap * 1.0 / 10^6); }
\\ Theoretical bound on disagreement: 1 unit each from mul-CEIL and shiftl-CEIL,
\\ so max gap is 2 qBuyTok per bid.
if(max_gap <= 2, print("  OK: max gap bounded by 2 qBuyTok (one unit per rounding step)"), print("  FAIL: gap exceeds the 2-qBuyTok rounding bound"));
print("");

print("Done.");
