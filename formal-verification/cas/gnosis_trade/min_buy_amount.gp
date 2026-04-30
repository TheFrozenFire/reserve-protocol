\\ min_buy_amount.gp
\\
\\ CAS-side validation of the Gnosis batch-auction min-buy-amount derivation.
\\ Two layers compose to produce the floor that the auction must beat:
\\
\\   (A) TradeLib.prepareTradeSell (contracts/p1/mixins/TradeLib.sol L76):
\\         b = s.mul(FIX_ONE - slippage, CEIL)
\\              .safeMulDiv(sellLow, buyHigh, CEIL)
\\         req.minBuyAmount = b.shiftl_toUint(buyDecimals, CEIL)   {qBuyTok}
\\         req.sellAmount   = s.shiftl_toUint(sellDecimals, FLOOR) {qSellTok}
\\
\\   (B) GnosisTrade.init (contracts/plugins/trading/GnosisTrade.sol L114):
\\         worstCasePrice = shiftl_toFix(req.minBuyAmount, 9)
\\                              .divu(req.sellAmount, FLOOR)        D27{qBuyTok/qSellTok}
\\
\\ Combined, worstCasePrice is the auction's enforced settlement floor:
\\ at settle(), the contract checks
\\         clearingPrice = shiftl_toFix(boughtAmt+1, 9).divu(max(soldAmt,1), FLOOR)
\\         require(clearingPrice >= worstCasePrice)
\\
\\ Properties probed:
\\   (1) Rounding direction: minBuyAmount uses CEIL at every step, so the
\\       floor it imposes is *at least* the exact-rational ideal. (Mirrors
\\       trade_lib/slippage_sufficiency.gp's finding for the upstream half.)
\\   (2) Slippage = 0  -> minBuyAmount = ceil(sellAmount * sellLow/buyHigh)
\\       (decimal-shifted) and worstCasePrice == sellLow/buyHigh in D27.
\\   (3) Slippage = maxTradeSlippage -> ceiling-rounding never lets
\\       worstCasePrice drop below
\\         (1-slippage) * sellLow / buyHigh - eps_rounding.
\\   (4) Decimal asymmetry: 6-decimal buy tokens (USDC) vs 18-decimal sell
\\       tokens land on the right qBuyTok boundary; the CEIL on
\\       shiftl_toUint adds at most 1 qBuyTok of bidder-favorable rounding.
\\   (5) divu FLOOR in worstCasePrice direction: the FLOOR rounding is
\\       *trader*-favorable (lowers the floor by < 1 wei of D27) — verify
\\       the loss is bounded.
\\   (6) Auction fee adjustment: the _sellAmount sent to Gnosis is reduced
\\       by FEE_DENOMINATOR / (FEE_DENOMINATOR + feeNumerator), but
\\       worstCasePrice is computed against the *unfeed* req.sellAmount —
\\       so the actual auction-clearing price needed is correspondingly
\\       lower. Verify the relationship.
\\
\\ Calibration (per task brief, R005):
\\   sellAmount        = 10000 tokens (D18)
\\   sellPrice (sellLow) = $0.99
\\   buyPrice  (buyHigh) = $1.01
\\   maxTradeSlippage  = 1%   (1e16 in D18)
\\   buyDecimals       in {6, 18}
\\   sellDecimals      = 18
\\   feeNumerator      = 0 (current EasyAuction setting; we also probe 5)

print("=== GnosisTrade min-buy / worstCasePrice — CAS validation ===");
print("");

\\ ---- Reserve fixed-point constants (R001) ----
FIX_ONE   = 10^18;
FIX_MAX   = 2^192 - 1;
D27_ONE   = 10^27;

\\ ---- Helpers (R003) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

fix_mul_ceil(x, y)  = { my(r); r = ceil_div(x * y, FIX_ONE); if(r > FIX_MAX, -1, r); }
fix_mul_floor(x, y) = { my(r); r = (x * y) \ FIX_ONE; if(r > FIX_MAX, -1, r); }
fix_safe_muldiv_ceil(a, b, c) = { my(r); if(a == 0 || b == 0, return(0)); if(c == 0, return(FIX_MAX)); r = ceil_div(a * b, c); if(r >= FIX_MAX, FIX_MAX, r); }

\\ shiftl_toUint(x, d, mode): for d < 18, divides by 10^(18-d). For d >= 18 multiplies.
shiftl_to_uint_ceil(x, d)  = { my(sh); sh = 18 - d; if(sh <= 0, x * 10^(-sh), ceil_div(x, 10^sh)); }
shiftl_to_uint_floor(x, d) = { my(sh); sh = 18 - d; if(sh <= 0, x * 10^(-sh), x \ 10^sh); }

\\ shiftl_toFix(x, shiftLeft, FLOOR): x * 10^(shiftLeft + 18).  Used in init() with shiftLeft = 9
\\ to lift req.minBuyAmount {qBuyTok} into D27 wei before the divu.
shiftl_to_fix(x, shiftLeft) = x * 10^(shiftLeft + 18);

\\ FixLib.divu(x, y, FLOOR): integer floor division of (already-D-something) x by y.
divu_floor(x, y) = x \ y;

\\ ---- Model: TradeLib's b in D18, then shiftl_toUint -> minBuyAmount in qBuyTok ----
\\ Returns [b_D18, minBuyAmount_qBuyTok]. -1 sentinel on overflow.
buy_amount_pipeline(s_d18, slippage_d18, sellLow_d18, buyHigh_d18, buyDecimals) = {
  my(inner, b, mba);
  inner = fix_mul_ceil(s_d18, FIX_ONE - slippage_d18);
  if(inner < 0, return([-1, -1]));
  b = fix_safe_muldiv_ceil(inner, sellLow_d18, buyHigh_d18);
  mba = shiftl_to_uint_ceil(b, buyDecimals);
  [b, mba];
}

\\ ---- Model: GnosisTrade.init worstCasePrice (D27{qBuyTok/qSellTok}) ----
worst_case_price(minBuyAmount_qBuyTok, sellAmount_qSellTok) = {
  my(lifted);
  lifted = shiftl_to_fix(minBuyAmount_qBuyTok, 9);   \\ D27 wei
  divu_floor(lifted, sellAmount_qSellTok);
}

\\ ---- Calibration ----
SLIPPAGE = 1 * 10^16;            \\ 1% in D18
SELL_LOW = 99 * 10^16;           \\ $0.99
BUY_HIGH = 101 * 10^16;          \\ $1.01
SELL_TOK = 10000 * FIX_ONE;      \\ 10k tokens, in D18 wei
SELL_DEC = 18;
SELL_AMT_QSELL = SELL_TOK;       \\ shiftl_toUint(.,18,FLOOR) is identity at decimals=18

\\ Sanity
if(SELL_LOW > BUY_HIGH, print("FAIL: calibration sellLow > buyHigh"));
if(SLIPPAGE > FIX_ONE, print("FAIL: calibration slippage > 1"));

\\ ---- (1) CEIL discipline at every step ----
print("--- (1) minBuyAmount CEILs at every step (no under-floor risk) ---");
\\ Compare CEIL pipeline vs hypothetical FLOOR pipeline. CEIL must be >= FLOOR.
buy_amount_floor_pipeline(s, slip, slo, bhi, bd) = { my(inner, b); inner = fix_mul_floor(s, FIX_ONE - slip); b = (inner * slo) \ bhi; shiftl_to_uint_floor(b, bd); }
ceil_18  = buy_amount_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH, 18)[2];
floor_18 = buy_amount_floor_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH, 18);
ceil_6   = buy_amount_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH,  6)[2];
floor_6  = buy_amount_floor_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH,  6);
{ printf("  18-dec buy: CEIL minBuy = %d qBuyTok, FLOOR minBuy = %d qBuyTok, gap = %d\n", ceil_18, floor_18, ceil_18 - floor_18); }
{ printf("   6-dec buy: CEIL minBuy = %d qBuyTok, FLOOR minBuy = %d qBuyTok, gap = %d\n", ceil_6,  floor_6,  ceil_6  - floor_6); }
if(ceil_18 >= floor_18 && ceil_6 >= floor_6, print("  OK: CEIL pipeline never below FLOOR pipeline"), print("  FAIL: CEIL pipeline below FLOOR (rounding regression)"));
print("");

\\ ---- (2) Slippage = 0: minBuyAmount = ceil(sellAmount * sellLow/buyHigh), exactly ----
print("--- (2) zero-slippage equivalence: minBuy = ceil(s * sellLow / buyHigh) (decimal-shifted) ---");
\\ With slippage=0, fix_mul_ceil(s, FIX_ONE) == s exactly (no rounding lost).
\\ Then safeMulDiv CEIL gives ceil(s * sellLow / buyHigh) in D18.
zero_pipe = buy_amount_pipeline(SELL_TOK, 0, SELL_LOW, BUY_HIGH, 18);
expected_b_d18 = ceil_div(SELL_TOK * SELL_LOW, BUY_HIGH);
expected_mba_18 = expected_b_d18;       \\ shiftl_toUint at decimals=18 with CEIL is identity
{ printf("  computed b (D18) = %d\n", zero_pipe[1]); }
{ printf("  expected b (D18) = %d\n", expected_b_d18); }
if(zero_pipe[1] == expected_b_d18 && zero_pipe[2] == expected_mba_18, print("  OK: zero-slippage minBuy == exact ceil(s*sellLow/buyHigh)"), print("  FAIL: zero-slippage minBuy diverges from exact ceiling"));
\\ Cross-check worstCasePrice: it should ~= sellLow/buyHigh expressed in D27.
wcp_zero = worst_case_price(zero_pipe[2], SELL_AMT_QSELL);
exact_wcp_d27 = (SELL_LOW * D27_ONE) \ BUY_HIGH;            \\ floor of sellLow/buyHigh * 1e27
{ printf("  worstCasePrice (D27) = %d  (%.8f buy/sell)\n", wcp_zero, wcp_zero * 1.0 / D27_ONE); }
{ printf("  exact sellLow/buyHigh in D27 = %d (%.8f)\n", exact_wcp_d27, exact_wcp_d27 * 1.0 / D27_ONE); }
\\ With CEIL on numerator and FLOOR on the divu, |wcp_zero - exact| <= 10^9 (one D18 wei lifted to D27).
diff_zero = abs(wcp_zero - exact_wcp_d27);
if(diff_zero <= 10^9, print("  OK: zero-slippage worstCasePrice within 1 D18-wei of exact (D27 scale)"), printf("  FAIL: worstCasePrice off by %d wei (D27)\n", diff_zero));
print("");

\\ ---- (3) maxTradeSlippage = 1%: worstCasePrice >= floor((1-slip)*sellLow/buyHigh) ----
print("--- (3) 1%% slippage: worstCasePrice never drops below (1-slip)*sellLow/buyHigh - rounding ---");
pipe = buy_amount_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH, 18);
mba = pipe[2];
wcp = worst_case_price(mba, SELL_AMT_QSELL);
\\ The exact rational floor: (1 - slippage/FIX_ONE) * sellLow / buyHigh, in D27.
\\ Numerator: (FIX_ONE - SLIPPAGE) * SELL_LOW * D27_ONE / FIX_ONE / BUY_HIGH (floor).
exact_floor = ((FIX_ONE - SLIPPAGE) * SELL_LOW * D27_ONE) \ (FIX_ONE * BUY_HIGH);
{ printf("  minBuyAmount     = %d qBuyTok (= %.6f tokens)\n", mba, mba * 1.0 / FIX_ONE); }
{ printf("  worstCasePrice   = %d  (%.8f buy/sell, D27)\n", wcp, wcp * 1.0 / D27_ONE); }
{ printf("  exact (1-slip)*sellLow/buyHigh = %d (%.8f, D27)\n", exact_floor, exact_floor * 1.0 / D27_ONE); }
\\ Because both ceils run trader-favorably and divu floors back, the gap is bounded by ~ FIX_ONE per D27.
\\ Allow 2 * 10^9 D27-wei slack (one wei from each ceil step, lifted by 10^9 into D27).
if(wcp >= exact_floor - 2 * 10^9, print("  OK: worstCasePrice >= exact (1-slip)*sellLow/buyHigh - 2 D18-wei (D27)"), printf("  FAIL: worstCasePrice short by %d D27-wei\n", exact_floor - wcp));
print("");

\\ ---- (4) Decimal asymmetry: 6-dec buy token ----
print("--- (4) 6-decimal buy token (USDC): qBuyTok shift lands on the right boundary ---");
pipe6 = buy_amount_pipeline(SELL_TOK, SLIPPAGE, SELL_LOW, BUY_HIGH, 6);
b6 = pipe6[1];
mba6 = pipe6[2];
\\ Exact ceil(b * 10^(-12)) in qBuyTok = USDC * 1e6.
exact_mba6 = ceil_div(b6, 10^12);
{ printf("  b (D18)        = %d\n", b6); }
{ printf("  minBuy (qUSDC) = %d  (= $%.6f)\n", mba6, mba6 * 1.0 / 10^6); }
{ printf("  exact ceil(b/1e12) = %d\n", exact_mba6); }
if(mba6 == exact_mba6, print("  OK: shiftl_toUint CEIL lands on exact ceiling"), printf("  FAIL: minBuy off by %d qUSDC from exact ceiling\n", mba6 - exact_mba6));
\\ The qBuyTok-level worstCasePrice for 6-dec is in D27{qUSDC/qSellTok} =
\\   minBuyAmount * 10^9 / sellAmount_qSellTok.
\\ Verify: this represents at least (1-slip)*sellLow/buyHigh after the unit shift.
wcp6 = worst_case_price(mba6, SELL_AMT_QSELL);
\\ Equivalent exact: (1-slip)*sellLow/buyHigh, expressed in D27{qUSDC/qSellTok}.
\\   = (1-slip)*sellLow/buyHigh (dimensionless tok/tok) * 10^9 / 10^12  -- wait: D27 means scaled by 1e27.
\\   minBuy is in qUSDC; sellAmount in qSellTok = qD18Tok. So D27{qUSDC/qSellTok}
\\   = (mba/10^6 USDC) / (sa/10^18 sellTok) * 10^27 = mba * 10^9 / sa.  Matches.
\\ Cross check: convert to dimensionless tok/tok: wcp6 / 10^9 / 10^(18-6) = wcp6 / 10^21.
{ printf("  wcp6 (D27{qUSDC/qSellTok}) = %d  (%.8f tok/tok dimensionless = wcp6 / 10^21)\n", wcp6, wcp6 * 1.0 / 10^21); }
\\ Unit conversion: D27{qUSDC/qSellTok} = (USDC/sellTok dimensionless) * 10^27 *
\\   10^(buyDecimals - sellDecimals) -- but more directly: wcp6 = mba_qUSDC * 10^9 / sa_qSellTok.
\\ Since mba_qUSDC = mba_USDC * 10^6 and sa_qSellTok = sa_sellTok * 10^18, the
\\ dimensionless tok/tok ratio is wcp6 / 10^(27 + 6 - 18) = wcp6 / 10^15.
\\ Wait — re-derive: wcp6 [D27{qUSDC/qSellTok}] / 10^27 == qUSDC/qSellTok (a dimensional ratio).
\\ To get USDC/sellTok (dimensionless after pricing), multiply by 10^(sellDec - buyDec) = 10^12.
\\ So tok/tok = wcp6 * 10^12 / 10^27 = wcp6 / 10^15.
{ printf("  wcp6 -> dimensionless USDC/sellTok = %.8f (wcp6 / 10^15)\n", wcp6 * 1.0 / 10^15); }
\\ Compare to (1-slip)*sellLow/buyHigh as a dimensionless tok/tok ratio.
\\ (1-slip)*sellLow/buyHigh in D18 is a fraction; in dimensionless terms it's that / FIX_ONE.
\\ Build it scaled by 10^15 for direct comparison to wcp6.
exact_floor6_scaled = ((FIX_ONE - SLIPPAGE) * SELL_LOW * 10^15) \ (FIX_ONE * BUY_HIGH);
gap6 = wcp6 - exact_floor6_scaled;
{ printf("  exact (1-slip)*sellLow/buyHigh scaled by 10^15 = %d\n", exact_floor6_scaled); }
{ printf("  gap = %d   (1 qUSDC at this unit = 10^6 wcp6-wei)\n", gap6); }
\\ Allowed slack: 1 qUSDC ceiling at the shiftl + 1 D18-wei from the upstream pipeline.
\\ 1 qUSDC = 10^6 wcp6-wei (since wcp6_scaled = mba_qUSDC * 10^6 / sa_sellTok). Allow 10^7 budget.
if(gap6 >= 0 && gap6 <= 10^7, print("  OK: 6-dec wcp >= exact tok/tok ratio (within 1 qUSDC ceil + 1 wei pipeline slack)"), printf("  FAIL: 6-dec wcp gap %d outside [0, 1e7] qBuyTok-granularity budget\n", gap6));
print("");

\\ ---- (5) divu FLOOR in worstCasePrice: bounded loss ----
print("--- (5) worstCasePrice = shiftl_toFix(.,9).divu(.,FLOOR) loses < 1 D27-wei ---");
\\ The contract uses divu FLOOR, so worstCasePrice could under-estimate the true ratio
\\ by less than 1 D27-wei. With minBuyAmount in qBuyTok and a 10^18-scale sellAmount,
\\ the ratio is in D27 wei, so the floor truncation is < 1 wei. Verify via residual.
\\ residual = (mba * 10^27 - wcp * sa) must be in [0, sa).
mba18 = pipe[2];
sa = SELL_AMT_QSELL;
wcp18 = worst_case_price(mba18, sa);
residual = mba18 * D27_ONE - wcp18 * sa;
{ printf("  residual = mba*1e27 - wcp*sa = %d   (must satisfy 0 <= residual < sa = %d)\n", residual, sa); }
if(residual >= 0 && residual < sa, print("  OK: divu FLOOR residual within [0, sellAmount) — quotient is exact floor"), print("  FAIL: divu FLOOR residual out of expected range"));
print("");

\\ ---- (6) Fee adjustment: _sellAmount = sellAmount * 1000 / (1000 + feeNumerator) ----
print("--- (6) auction fee scales _sellAmount but worstCasePrice tracks unfee'd sellAmount ---");
\\ When feeNumerator = 0 (current EasyAuction), _sellAmount == req.sellAmount.
\\ For probe, we model feeNumerator in {0, 5, 10}.
FEE_DENOM = 1000;
\\ Helper. _divrnd FLOOR is just a \ b.
fee_adjust(sa_qsell, fee_num) = (sa_qsell * FEE_DENOM) \ (FEE_DENOM + fee_num);
\\ For each fee, the auction operator must produce at least minBuyAmount qBuyTok using
\\ at most _sellAmount qSellTok. Effective minimum clearing price (qBuy/qSell) is
\\ minBuyAmount / _sellAmount, *not* minBuyAmount / sellAmount. Verify worstCasePrice
\\ (computed against the unfeed sellAmount) is a *looser* check — i.e. easier to satisfy.
fee_check(fee_num) = {
  my(sa_eff, ratio_against_eff, ratio_against_full, sa_qsell, mba_check);
  sa_qsell = SELL_AMT_QSELL;
  mba_check = mba18;
  sa_eff = fee_adjust(sa_qsell, fee_num);
  ratio_against_eff = (mba_check * D27_ONE) \ sa_eff;
  ratio_against_full = wcp18;
  printf("  feeNumerator=%-2d  _sellAmount=%-26d  ratio(/eff)=%d  ratio(/full)=%d\n", fee_num, sa_eff, ratio_against_eff, ratio_against_full);
  ratio_against_eff >= ratio_against_full;
}
ok_f0 = fee_check(0);
ok_f5 = fee_check(5);
ok_f10 = fee_check(10);
if(ok_f0 && ok_f5 && ok_f10, print("  OK: ratio against fee'd _sellAmount >= worstCasePrice (auction floor stricter than reportViolation floor)"), print("  FAIL: fee-adjusted clearing-ratio falls below worstCasePrice"));
print("");

\\ ---- (7) Calibration table ----
print("--- (7) calibration summary ---");
{ printf("  sellAmount  = %d qSellTok (10000 D18 tokens)\n", SELL_AMT_QSELL); }
{ printf("  sellLow     = %d  ($0.99)\n", SELL_LOW); }
{ printf("  buyHigh     = %d  ($1.01)\n", BUY_HIGH); }
{ printf("  slippage    = %d  (1%%)\n", SLIPPAGE); }
{ printf("  18-dec minBuyAmount = %d qBuyTok (%.4f tokens)\n", mba18, mba18 * 1.0 / FIX_ONE); }
{ printf("   6-dec minBuyAmount = %d qBuyTok ($%.6f)\n", mba6, mba6 * 1.0 / 10^6); }
{ printf("  18-dec worstCasePrice = %.8f buy/sell (D27)\n", wcp18 * 1.0 / D27_ONE); }
print("");

print("Done.");
