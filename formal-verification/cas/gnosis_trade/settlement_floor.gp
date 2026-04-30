\\ settlement_floor.gp
\\
\\ CAS-side validation of GnosisTrade.settle() — the close-out arithmetic
\\ that decides (a) how much sellTok was actually consumed, (b) the
\\ effective clearing price, and (c) whether broker.reportViolation()
\\ fires.
\\
\\ Reference (contracts/plugins/trading/GnosisTrade.sol):
\\   - settle(): L185-230. Computes
\\         soldAmt        = initBal - sellBal                    {qSellTok}
\\         adjustedSoldAmt = max(soldAmt, 1)                      {qSellTok}
\\         adjustedBuyAmt  = boughtAmt + 1                        {qBuyTok}
\\         clearingPrice   = shiftl_toFix(adjustedBuyAmt, 9)
\\                              .divu(adjustedSoldAmt, FLOOR)      D27{qBuy/qSell}
\\         if (clearingPrice < worstCasePrice) reportViolation()
\\
\\   - canSettle(): L242-244. status == OPEN && endTime <= block.timestamp.
\\
\\   - cancellationEndTime in init(): L150-152.
\\         block.timestamp + (batchAuctionLength * CANCEL_WINDOW) / FIX_ONE
\\       with CANCEL_WINDOW = 9e17 (= 0.9). I.e. cancellation is allowed
\\       only during the FIRST 90% of the auction; the LAST 10% is
\\       cancellation-locked. (The task brief said "last 10%"; that's
\\       what the contract enforces — verifying boundary direction.)
\\
\\ Properties probed:
\\   (1) Conservation: initBal == soldAmt + sellBal_after for any partial
\\       fill 0 <= soldAmt <= initBal.  (Direct from settle()'s L219-220.)
\\   (2) Settlement floor at full fill: clearingPrice >= worstCasePrice
\\       whenever the auction returned at least minBuyAmount.
\\   (3) Settlement floor at partial fill: when Gnosis returns leftover
\\       sell + scaled-down buy, the +1 defensive padding still keeps
\\       clearingPrice computable; the reportViolation predicate fires
\\       iff and only if buyer under-paid net of pad.
\\   (4) Zero-soldAmt edge case (auction returned 100% leftover): no
\\       division-by-zero; max(soldAmt,1) keeps clearingPrice well-defined,
\\       and (boughtAmt+1)/1 cannot be < worstCasePrice for any nontrivial
\\       worstCasePrice > 1 (auction returned no buy-tokens, but also no
\\       sell-tokens were sold — should NOT trigger reportViolation
\\       because the if(sellBal < initBal) guard skips entirely).
\\   (5) Decimal asymmetry: 6-dec buy token (USDC) settlement still lands
\\       on the right floor; the +1 pad represents 1e-6 USDC, negligible
\\       at any production-relevant fill size.
\\   (6) canSettle() boundary: returns true at endTime exactly (<=, not <).
\\   (7) cancellationEndTime: locks at start + 0.9*length. At length=1800s,
\\       cancellation closes at +1620s, leaves a 180s last-10%% lock.
\\
\\ Calibration (per task brief, R005):
\\   sellAmount        = 10000 sellTok (D18)            -> initBal = 1e22 qSellTok
\\   sellPrice         = $0.99
\\   buyPrice          = $1.01
\\   maxTradeSlippage  = 1%
\\   auctionLength     = 1800s
\\   minBuyAmount      = 9703.960... USDC-equivalents

print("=== GnosisTrade.settle() — CAS validation ===");
print("");

\\ ---- Reserve fixed-point constants (R001) ----
FIX_ONE   = 10^18;
FIX_MAX   = 2^192 - 1;
D27_ONE   = 10^27;
CANCEL_WINDOW = 9 * 10^17;       \\ 0.9 in D18

\\ ---- Helpers (R003) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
shiftl_to_uint_ceil(x, d)  = { my(sh); sh = 18 - d; if(sh <= 0, x * 10^(-sh), ceil_div(x, 10^sh)); }
shiftl_to_uint_floor(x, d) = { my(sh); sh = 18 - d; if(sh <= 0, x * 10^(-sh), x \ 10^sh); }
shiftl_to_fix(x, sh) = x * 10^(sh + 18);
fix_mul_ceil(x, y) = ceil_div(x * y, FIX_ONE);
fix_safe_muldiv_ceil(a, b, c) = if(a == 0 || b == 0, 0, ceil_div(a * b, c));

\\ ---- Calibration ----
SLIPPAGE = 1 * 10^16;            \\ 1%
SELL_LOW = 99 * 10^16;           \\ $0.99
BUY_HIGH = 101 * 10^16;          \\ $1.01
SELL_TOK_D18 = 10000 * FIX_ONE;
SELL_DEC = 18;
INIT_BAL_18 = SELL_TOK_D18;      \\ qSellTok at 18 decimals = D18 wei
AUCTION_LEN = 1800;
START_T = 1000000;
END_T = START_T + AUCTION_LEN;

\\ Compute the production minBuyAmount (matches min_buy_amount.gp).
inner = ceil_div(SELL_TOK_D18 * (FIX_ONE - SLIPPAGE), FIX_ONE);
b_d18 = ceil_div(inner * SELL_LOW, BUY_HIGH);
MIN_BUY_18 = b_d18;                       \\ shiftl_toUint(.,18,CEIL) = identity
MIN_BUY_6  = ceil_div(b_d18, 10^12);
WCP_18 = (MIN_BUY_18 * D27_ONE) \ INIT_BAL_18;
WCP_6_PER_QSELL = (MIN_BUY_6 * 10^9 * 10^18) \ INIT_BAL_18;
{ printf("  minBuyAmount (18-dec): %d qBuyTok\n", MIN_BUY_18); }
{ printf("  minBuyAmount  (6-dec): %d qBuyTok ($%.6f)\n", MIN_BUY_6, MIN_BUY_6 * 1.0 / 10^6); }
{ printf("  worstCasePrice (18-dec, D27{qBuy/qSell}) = %d\n", WCP_18); }
{ printf("  worstCasePrice  (6-dec, D27{qUSDC/qSell}) = %d\n", WCP_6_PER_QSELL); }
print("");

\\ ---- Model: settle() clearing price + violation predicate ----
\\ Returns [clearingPrice_D27, violation_bool, soldAmt, sellBalAfter].
settle_model(initBal, sellBalAfter, boughtAmt, wcp) = {
  my(soldAmt, adjSold, adjBuy, clearing, violation);
  soldAmt = initBal - sellBalAfter;
  if(sellBalAfter >= initBal,                       \\ skip if-block in production
    return([0, 0, 0, sellBalAfter])
  );
  adjSold = if(soldAmt > 1, soldAmt, 1);
  adjBuy  = boughtAmt + 1;
  clearing = (adjBuy * D27_ONE) \ adjSold;
  violation = if(clearing < wcp, 1, 0);
  [clearing, violation, soldAmt, sellBalAfter];
}

\\ ---- (1) Conservation: initBal = soldAmt + sellBal_after, every fill ----
print("--- (1) settlement conservation: initBal == soldAmt + sellBalAfter ---");
cons_ok = 1;
\\ Sweep partial-fill ratios from 0% (no fill) to 100%.
fills_pct = [0, 1, 5, 25, 50, 75, 90, 95, 99, 100];
for(i = 1, length(fills_pct), {
  pct = fills_pct[i];
  sellBalAfter = (INIT_BAL_18 * (100 - pct)) \ 100;
  \\ Boughtamt: in production, an honest auction returns ~ pct% * minBuyAmount.
  bought = (MIN_BUY_18 * pct) \ 100;
  r = settle_model(INIT_BAL_18, sellBalAfter, bought, WCP_18);
  reconstructed = r[3] + r[4];
  if(reconstructed != INIT_BAL_18, cons_ok = 0);
});
report_fill(pct) = { my(sba, bgt, r); sba = (INIT_BAL_18 * (100 - pct)) \ 100; bgt = (MIN_BUY_18 * pct) \ 100; r = settle_model(INIT_BAL_18, sba, bgt, WCP_18); printf("  fill=%3d%%  sold=%-22d leftover=%-22d  clearing=%d  violation=%d\n", pct, r[3], r[4], r[1], r[2]); }
report_fill(0); report_fill(50); report_fill(100);
if(cons_ok, print("  OK: conservation holds across every probed fill ratio"), print("  FAIL: conservation breaks at some fill"));
print("");

\\ ---- (2) Floor at full fill (honest auction) ----
print("--- (2) full-fill: clearingPrice >= worstCasePrice (no violation) ---");
\\ Honest auction at 100% fill: bought == minBuyAmount exactly (lower bound).
r_full = settle_model(INIT_BAL_18, 0, MIN_BUY_18, WCP_18);
{ printf("  bought=%d  sold=%d  clearing=%d  worstCase=%d\n", MIN_BUY_18, r_full[3], r_full[1], WCP_18); }
if(r_full[2] == 0, print("  OK: full-fill at min-buy does not trigger reportViolation"), print("  FAIL: full-fill triggered violation"));
\\ Edge: bought = minBuyAmount - 1 (one wei under) at full sold. Should violate.
r_under = settle_model(INIT_BAL_18, 0, MIN_BUY_18 - 1, WCP_18);
{ printf("  bought=minBuy-1=%d  clearing=%d  violation=%d\n", MIN_BUY_18 - 1, r_under[1], r_under[2]); }
\\ Note: due to the +1 pad in adjBuy = bought+1, bought = minBuy-1 -> adjBuy = minBuy
\\ which matches the floor exactly — boundary case. Verify the pad effect.
\\ Honest precise floor witness: bought = minBuyAmount - 2 (two wei under) WILL violate.
r_under2 = settle_model(INIT_BAL_18, 0, MIN_BUY_18 - 2, WCP_18);
{ printf("  bought=minBuy-2=%d  clearing=%d  violation=%d  (the +1 pad absorbs 1 wei; 2 wei breaks floor)\n", MIN_BUY_18 - 2, r_under2[1], r_under2[2]); }
if(r_under2[2] == 1, print("  OK: 2-wei under-payment correctly flagged as violation"), print("  FAIL: 2-wei under-payment did not violate (pad too generous)"));
print("");

\\ ---- (3) Partial-fill floor: clearing >= worstCase iff buyer paid pro-rata ----
print("--- (3) partial-fill: clearingPrice still measured against worstCasePrice ---");
\\ Gnosis can fill partially. The floor check uses (sold, bought) AFTER settlement;
\\ since clearingPrice = bought/sold, a partial fill at the SAME unit price has
\\ identical clearingPrice. Verify across fills 10%..90%.
pf_ok = 1;
pf_sample(pct) = { my(sba, bgt, r); sba = (INIT_BAL_18 * (100 - pct)) \ 100; bgt = (MIN_BUY_18 * pct) \ 100; r = settle_model(INIT_BAL_18, sba, bgt, WCP_18); r; }
for(p = 10, 90, if(p % 10 == 0, my(r); r = pf_sample(p); if(r[2] != 0, pf_ok = 0)));
{ my(r); r = pf_sample(50); printf("  fill=50%%  bought=%d  sold=%d  clearing=%d  worstCase=%d\n", (MIN_BUY_18*50)\100, r[3], r[1], WCP_18); }
\\ Witness for partial under-payment: at 50% fill, deliver bought = (minBuy*50/100) - 100 (under by 100 wei).
underpay_witness = (MIN_BUY_18 * 50) \ 100 - 100;
r_pwit = settle_model(INIT_BAL_18, INIT_BAL_18 \ 2, underpay_witness, WCP_18);
{ printf("  partial witness: 50%% sold, 100-wei buy under-payment -> clearing=%d, violation=%d\n", r_pwit[1], r_pwit[2]); }
if(pf_ok, print("  OK: pro-rata partial fills never trigger reportViolation"), print("  FAIL: partial fill triggered violation despite pro-rata pricing"));
if(r_pwit[2] == 1, print("  OK: 100-wei under-payment at 50%% fill correctly flagged"), print("  FAIL: under-payment at partial fill not flagged"));
print("");

\\ ---- (4) Zero-soldAmt edge: auction cleared with no fill ----
print("--- (4) zero-fill edge: sellBalAfter == initBal skips violation check ---");
r_zero = settle_model(INIT_BAL_18, INIT_BAL_18, 0, WCP_18);
{ printf("  sold=%d  bought=%d  clearing=%d  violation=%d\n", r_zero[3], 0, r_zero[1], r_zero[2]); }
\\ The if(sellBal < initBal) guard at L219 means soldAmt-block doesn't execute,
\\ so reportViolation cannot fire. Our settle_model returns [0, 0, 0, ...] for that case.
if(r_zero[2] == 0 && r_zero[3] == 0, print("  OK: zero-fill skips floor check (no spurious violation)"), print("  FAIL: zero-fill behaviour wrong"));
\\ Also: 1-wei sold edge. soldAmt=1, bought=0 (worst-case griefer): adjBuy=1, adjSold=1, clearing=1e27.
\\ For non-tiny worstCasePrice this still flags violation since 1e27 < ~9.7e26 false here (1e27 > 9.7e26).
\\ Pick a high worstCase to demonstrate the path.
WCP_HIGH = 2 * D27_ONE;          \\ 2.0 in D27
r_one = settle_model(INIT_BAL_18, INIT_BAL_18 - 1, 0, WCP_HIGH);
{ printf("  1-wei sold, 0 bought, wcp=2.0 D27: clearing=%d violation=%d (expect violation)\n", r_one[1], r_one[2]); }
if(r_one[2] == 1, print("  OK: 1-wei-sold-zero-bought triggers violation against high worstCase"), print("  FAIL: 1-wei-sold-zero-bought did not flag violation"));
print("");

\\ ---- (5) 6-decimal buy token (USDC) settlement ----
print("--- (5) 6-dec settlement: +1 qUSDC pad equals $1e-6 (negligible) ---");
\\ For 6-dec USDC, the worstCasePrice is in D27{qUSDC/qSellTok}. Settlement uses
\\ clearingPrice = (boughtAmt+1) * 1e9 / max(soldAmt,1). +1 pad is 1 qUSDC.
clear6(sold_qsell, bought_qusdc) = { my(adjS, adjB); adjS = if(sold_qsell > 1, sold_qsell, 1); adjB = bought_qusdc + 1; (adjB * D27_ONE) \ adjS; }
\\ Honest 100% fill: bought = MIN_BUY_6 qUSDC, sold = INIT_BAL_18 qSellTok.
cl6_full = clear6(INIT_BAL_18, MIN_BUY_6);
{ printf("  full fill: clearing=%d  worstCase=%d  delta=%d (qUSDC-granularity)\n", cl6_full, WCP_6_PER_QSELL, cl6_full - WCP_6_PER_QSELL); }
\\ The +1 qUSDC pad at this calibration adds 1e9 D27-wei to clearing — small vs typical
\\ 9.7e14 magnitude (~1 in 1e6).
if(cl6_full >= WCP_6_PER_QSELL, print("  OK: 6-dec full fill clears worst-case price"), print("  FAIL: 6-dec full fill below worst-case"));
\\ 1-qUSDC under-payment witness: bought = MIN_BUY_6 - 1 should still pass (pad absorbs).
cl6_under1 = clear6(INIT_BAL_18, MIN_BUY_6 - 1);
{ printf("  bought=minBuy6 - 1: clearing=%d  worstCase=%d  pass=%d\n", cl6_under1, WCP_6_PER_QSELL, cl6_under1 >= WCP_6_PER_QSELL); }
if(cl6_under1 >= WCP_6_PER_QSELL, print("  OK: 1-qUSDC-under absorbed by +1 pad (no violation)"), print("  FAIL: 1-qUSDC-under triggered violation"));
\\ 2-qUSDC under should violate.
cl6_under2 = clear6(INIT_BAL_18, MIN_BUY_6 - 2);
{ printf("  bought=minBuy6 - 2: clearing=%d  worstCase=%d  pass=%d\n", cl6_under2, WCP_6_PER_QSELL, cl6_under2 >= WCP_6_PER_QSELL); }
if(cl6_under2 < WCP_6_PER_QSELL, print("  OK: 2-qUSDC under-payment flagged"), print("  FAIL: 2-qUSDC under-payment not flagged"));
print("");

\\ ---- (6) canSettle() boundary direction ----
print("--- (6) canSettle() flips at endTime (endTime <= block.timestamp) ---");
can_settle(now, end) = (end <= now);          \\ status==OPEN assumed
b_before = can_settle(END_T - 1, END_T);
b_at     = can_settle(END_T,     END_T);
b_after  = can_settle(END_T + 1, END_T);
{ printf("  t = endTime - 1: canSettle = %d (expect 0)\n", b_before); }
{ printf("  t = endTime    : canSettle = %d (expect 1)\n", b_at); }
{ printf("  t = endTime + 1: canSettle = %d (expect 1)\n", b_after); }
if(!b_before && b_at && b_after, print("  OK: canSettle flips at endTime, inclusive (<=, not <)"), print("  FAIL: canSettle boundary direction is wrong"));
print("");

\\ ---- (7) cancellationEndTime: 90% of auction is cancellable; last 10% locked ----
print("--- (7) cancellation lock at last 10%% (CANCEL_WINDOW = 0.9) ---");
\\ Production: cancellationEndTime = block.timestamp_init + (length * CANCEL_WINDOW) / FIX_ONE.
\\ With length=1800, CANCEL_WINDOW=9e17/1e18 -> 1800*9e17/1e18 = 1620s.
cancel_end = START_T + (AUCTION_LEN * CANCEL_WINDOW) \ FIX_ONE;
{ printf("  auctionLength = %ds  cancellationEndTime = startTime + %ds  endTime = startTime + %ds\n", AUCTION_LEN, cancel_end - START_T, END_T - START_T); }
\\ Last-10% window: [cancel_end, END_T]. At length=1800, that's [+1620, +1800] = 180s.
last_pct_dur = END_T - cancel_end;
last_pct_frac = last_pct_dur * FIX_ONE \ AUCTION_LEN;
{ printf("  last-window duration = %ds  fraction of auction = %.4f\n", last_pct_dur, last_pct_frac * 1.0 / FIX_ONE); }
\\ Boundary: cancellation should be ALLOWED at cancel_end - 1, NOT at cancel_end + 1.
\\ (EasyAuction's cancel-after-`cancellationEndTime` is reverted; we model the predicate.)
can_cancel(now) = (now < cancel_end);
{ printf("  t = cancel_end - 1: can_cancel = %d (expect 1)\n", can_cancel(cancel_end - 1)); }
{ printf("  t = cancel_end    : can_cancel = %d (expect 0)\n", can_cancel(cancel_end)); }
{ printf("  t = endTime - 1   : can_cancel = %d (expect 0)\n", can_cancel(END_T - 1)); }
\\ Properties: 0.10 frac matches 10% lock; 1620s within [1620, 1620].
if(last_pct_dur == 180 && abs(last_pct_frac - FIX_ONE \ 10) <= 1, print("  OK: last-10%% lock = 180s = 0.1 of auction (CANCEL_WINDOW = 0.9 verified)"), print("  FAIL: cancellation lock window is not 10%%"));
\\ Boundary direction:
if(can_cancel(cancel_end - 1) && !can_cancel(cancel_end) && !can_cancel(END_T - 1), print("  OK: cancellation-allowed predicate flips strictly at cancel_end"), print("  FAIL: cancel boundary direction wrong"));
print("");

\\ ---- (8) Calibration table ----
print("--- (8) settlement scenarios at production calibration ---");
{ printf("  initBal       = %d qSellTok\n", INIT_BAL_18); }
{ printf("  minBuyAmount  = %d qBuyTok (18-dec)\n", MIN_BUY_18); }
{ printf("  worstCasePrice (D27) = %d\n", WCP_18); }
{ printf("  endTime       = startTime + %ds\n", END_T - START_T); }
{ printf("  cancellation locks at startTime + %ds (last %ds)\n", cancel_end - START_T, last_pct_dur); }
print("");

print("Done.");
