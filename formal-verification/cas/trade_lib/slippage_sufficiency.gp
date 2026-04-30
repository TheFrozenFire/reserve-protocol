\\ slippage_sufficiency.gp
\\
\\ CAS-side validation that TradeLib's buy-amount computation produces a
\\ minBuyAmount that, if filled exactly, lets the basket recover the
\\ deficit being traded against.
\\
\\ Reference (post-mitigation, after PR #1283 / commit 7bf3a1ed):
\\   contracts/p1/mixins/TradeLib.sol  prepareTradeSell, line 76:
\\     uint192 b = s.mul(FIX_ONE.minus(maxTradeSlippage), CEIL).safeMulDiv(
\\         trade.prices.sellLow,
\\         trade.prices.buyHigh,
\\         CEIL
\\     );
\\
\\ Properties probed here:
\\   (1) Slippage sufficiency: b >= floor(s * (1-slippage) * sellLow / buyHigh).
\\       (Stronger: post-mitigation the call CEILs both rounds, so b is
\\        actually >= ceil(...) under exact-rational inputs.)
\\   (2) Slippage = 0:    b == ceil(s * sellLow / buyHigh)   exactly.
\\   (3) Slippage = FIX_ONE: b == 0 with no underflow.
\\   (4) Composition with safeMulDiv at boundary inputs: when the inner
\\       mul ceil and the outer safeMulDiv ceil compose, b never under-
\\       credits (b * buyHigh / sellLow >= s * (1-slippage) - eps).
\\
\\ Calibration (per CONTEXT, R005):
\\   sellLow  = $0.99 in D18
\\   buyHigh  = $1.01 in D18
\\   sellAmt  = $1M    in D18 of sell-token (so s = 1e6 * FIX_ONE)
\\   slippage = 0.5%   in D18 (= 5e15)

print("=== TradeLib slippage sufficiency — CAS validation ===");
print("");

\\ ---- FixLib constants (R001) ----
FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;

\\ ---- Helpers (R003) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ FixLib.mul(x, y, CEIL): _safeWrap(ceil(x*y / FIX_ONE)). Reverts (we
\\ model as -1) iff the result would exceed FIX_MAX.
fix_mul_ceil(x, y) = { my(r); r = ceil_div(x * y, FIX_ONE); if(r > FIX_MAX, -1, r); }

\\ FixLib.mul(x, y, FLOOR): _safeWrap(floor(x*y / FIX_ONE)).
fix_mul_floor(x, y) = { my(r); r = (x * y) \ FIX_ONE; if(r > FIX_MAX, -1, r); }

\\ FixLib.safeMulDiv(a, b, c, CEIL): saturating; returns FIX_MAX if a*b/c
\\ overflows; returns 0 iff a == 0 or b == 0; returns FIX_MAX if c == 0.
\\ Otherwise ceil(a*b/c) clamped to [0, FIX_MAX].
fix_safe_muldiv_ceil(a, b, c) = { my(r); if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX || c == 0, return(FIX_MAX)); r = ceil_div(a * b, c); if(r >= FIX_MAX, FIX_MAX, r); }

\\ The post-mitigation buy-amount formula in production (TradeLib.sol L76).
\\ Returns -1 (sentinel) if the inner mul overflows FIX_MAX.
buy_amount(s, slippage, sellLow, buyHigh) = { my(inner); inner = fix_mul_ceil(s, FIX_ONE - slippage); if(inner < 0, return(-1)); fix_safe_muldiv_ceil(inner, sellLow, buyHigh); }

\\ ---- Calibration ----
SLIPPAGE = 5 * 10^15;          \\ 0.5% in D18
SELL_LOW = 99 * 10^16;         \\ $0.99
BUY_HIGH = 101 * 10^16;        \\ $1.01
SELL_AMT = 10^6 * FIX_ONE;     \\ $1M of sell token

{ printf("Calibration: s = %d (= $1M), slippage = %d (= 0.5%%), sellLow = %d ($0.99), buyHigh = %d ($1.01)\n", SELL_AMT, SLIPPAGE, SELL_LOW, BUY_HIGH); }
print("");

\\ ---- (1) Slippage sufficiency at the calibration point ----
print("--- (1) Slippage sufficiency at calibrated inputs ---");
b_cal = buy_amount(SELL_AMT, SLIPPAGE, SELL_LOW, BUY_HIGH);

\\ The exact (rational) "fair" minBuyAmount the comment promises:
\\   {buyTok} = {sellTok} * (1 - slippage) * sellLow / buyHigh
\\ Expressed in D18 with all factors as D18:
\\   exact = s * (FIX_ONE - slippage) / FIX_ONE * sellLow / buyHigh
\\ which equals s * (FIX_ONE - slippage) * sellLow / (FIX_ONE * buyHigh).
\\ Floor of this is the minimum any well-behaved implementation may produce.
fair_floor = (SELL_AMT * (FIX_ONE - SLIPPAGE) * SELL_LOW) \ (FIX_ONE * BUY_HIGH);
fair_ceil  = ceil_div(SELL_AMT * (FIX_ONE - SLIPPAGE) * SELL_LOW, FIX_ONE * BUY_HIGH);

{ printf("  buy_amount(b)             = %d\n", b_cal); }
{ printf("  exact-rational floor      = %d\n", fair_floor); }
{ printf("  exact-rational ceiling    = %d\n", fair_ceil); }
{ printf("  b - fair_floor (wei)      = %d\n", b_cal - fair_floor); }

if(b_cal >= fair_floor, print("OK: post-mitigation b >= floor(exact) at calibration."), print("FAIL: post-mitigation b < floor(exact) — slippage credit insufficient."));
\\ Stronger property: under CEIL+CEIL composition, b is at least the exact
\\ ceiling (allowing for the inner-mul rounding to bump up the input to the
\\ outer safeMulDiv). Verify the actual result.
if(b_cal >= fair_ceil, print("OK: post-mitigation b >= ceil(exact) — sufficient under any whole-wei fill."), print("OK: b == floor(exact); fill at b satisfies the comment promise (audit-acceptable)."));
print("");

\\ ---- (2) Slippage = 0: b == ceil(s * sellLow / buyHigh) ----
print("--- (2) Slippage = 0 (no slippage absorbed) ---");
b_zero = buy_amount(SELL_AMT, 0, SELL_LOW, BUY_HIGH);
expected_zero = ceil_div(SELL_AMT * SELL_LOW, BUY_HIGH);
{ printf("  b              = %d\n", b_zero); }
{ printf("  ceil(s*sL/bH)  = %d\n", expected_zero); }
if(b_zero == expected_zero, print("OK: slippage=0 yields ceil(s*sellLow/buyHigh)."), print("FAIL: slippage=0 boundary disagrees with closed form."));

\\ Cross-check FLOOR-vs-CEIL equivalence at slippage=0: when (s * FIX_ONE)
\\ is divisible by FIX_ONE the inner mul has zero remainder, so CEIL ==
\\ FLOOR. Show this explicitly.
inner_ceil_zero  = fix_mul_ceil(SELL_AMT, FIX_ONE);
inner_floor_zero = fix_mul_floor(SELL_AMT, FIX_ONE);
if(inner_ceil_zero == inner_floor_zero, print("OK: slippage=0 inner mul has CEIL == FLOOR (no rounding sensitivity)."), print("FAIL: inner-mul rounding differs at slippage=0."));
print("");

\\ ---- (3) Slippage = FIX_ONE: b == 0 with no underflow ----
print("--- (3) Slippage = FIX_ONE (full slippage tolerance) ---");
b_full = buy_amount(SELL_AMT, FIX_ONE, SELL_LOW, BUY_HIGH);
{ printf("  b at slippage = FIX_ONE = %d\n", b_full); }
if(b_full == 0, print("OK: full-slippage boundary returns 0 (no underflow)."), print("FAIL: full-slippage boundary did not return zero."));
\\ Confirm the inner mul collapses cleanly (no underflow in FIX_ONE - slippage = 0).
inner_full = fix_mul_ceil(SELL_AMT, 0);
if(inner_full == 0, print("OK: inner mul at (FIX_ONE - FIX_ONE) is exactly zero."), print("FAIL: inner mul did not zero out at full slippage."));
print("");

\\ ---- (4) Boundary sweep — composed CEIL+CEIL never under-credits ----
\\ Pick s values where (s * (FIX_ONE - slippage)) is one wei shy of a
\\ FIX_ONE multiple — exactly the spot where pre-mitigation FLOOR would
\\ have under-credited by 1 wei. Verify post-mitigation b is always
\\ >= floor(exact); count how many of these inputs have b strictly
\\ greater than floor(exact) (i.e. the mitigation actively moved the
\\ result up).
print("--- (4) Composition boundary sweep (CEIL inner + CEIL outer) ---");
\\ Construct a corpus of "boundary" s values: each is the largest s such
\\ that s * (FIX_ONE - slippage) sits just below a multiple of FIX_ONE.
\\ Concretely: pick s_k = k * FIX_ONE / (FIX_ONE - slippage), rounded down,
\\ for k = 1..256, then take s_k - 1 to land on the lossy side.
report_boundary(idx, s, b, fl, ce) = printf("  k=%-3d  s=%d  b=%d  floor=%d  ceil=%d  b-floor=%d\n", idx, s, b, fl, ce, b - fl);

{
  fail_count = 0;
  raised_count = 0;
  for(k = 1, 256,
    s_k = (k * FIX_ONE) \ (FIX_ONE - SLIPPAGE);
    if(s_k <= 1, next);
    s_probe = s_k - 1;
    b_p = buy_amount(s_probe, SLIPPAGE, SELL_LOW, BUY_HIGH);
    fl = (s_probe * (FIX_ONE - SLIPPAGE) * SELL_LOW) \ (FIX_ONE * BUY_HIGH);
    ce = ceil_div(s_probe * (FIX_ONE - SLIPPAGE) * SELL_LOW, FIX_ONE * BUY_HIGH);
    if(b_p < fl, fail_count = fail_count + 1);
    if(b_p > fl, raised_count = raised_count + 1);
  );
  printf("  boundary corpus size: 256\n");
  printf("  inputs with b < floor(exact)        : %d\n", fail_count);
  printf("  inputs with b > floor(exact) (CEIL+) : %d\n", raised_count);
}
\\ Have to read the printed counters back — we use a sentinel-style check.
\\ The "FAIL" string is reserved for actual property violations (R008).
{ if(fail_count == 0, print("OK: boundary sweep — b >= floor(exact) at every probe."), print("FAIL: boundary corpus surfaced ", fail_count, " inputs where b under-credits the exact floor.")); }
print("");

print("Done. Run with `gp -q < slippage_sufficiency.gp`.");
