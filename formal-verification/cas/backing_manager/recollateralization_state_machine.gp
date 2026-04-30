\\ recollateralization_state_machine.gp
\\
\\ CAS-side validation of the BackingManager recollateralization state
\\ machine: the prepareRecollateralizationTrade and
\\ settleRecollateralizationTrade transitions.
\\
\\ State alphabet:  NONE | OPEN | SETTLED
\\
\\ Transitions modeled (production reference: BackingManager.sol L108-L173
\\ for prepare via rebalance(), and L85-L102 for settleTrade):
\\   prepare(NONE)   -> OPEN  if needsTrade(range, basketsNeeded)
\\   prepare(NONE)   -> NONE  otherwise (no-op)
\\   settle (OPEN)   -> NONE  with basketsNeeded' = settlement.newBasketsNeeded
\\   settle (NONE)   -> NONE  (no-op)
\\
\\ Invariants checked:
\\   STATE-1  Initial state is NONE with no pending trade.
\\   STATE-2  prepare on NONE yields either NONE (storage unchanged) or
\\            OPEN (with pendingTrade = Some pt).
\\   STATE-3  settle on OPEN yields NONE with pendingTrade = None.
\\   STATE-4  Round-trip: prepare(s) -> settle(_) returns to NONE state.
\\   STATE-5  needsTrade exactly when range.low < basketsNeeded < range.high+1.
\\   STATE-6  prepare is idempotent on the no-trade branch.
\\   STATE-7  After settle, basketsNeeded = settlement.newBasketsNeeded.
\\   STATE-8  Composition of basketRange + buyAmount: prepare's pendingTrade
\\            buyAmount field equals direct TradeLib.buyAmount call.

print("=== BackingManager recollateralization state machine — CAS validation ===");
print("");

\\ ---- Constants ----
FIX_ONE   = 10^18;
FIX_MAX   = 2^192 - 1;

\\ ---- Helpers (single-line PARI/GP) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
fix_mul_ceil(x, y)  = ceil_div(x * y, FIX_ONE);
fix_mul_floor(x, y) = (x * y) \ FIX_ONE;

\\ TradeLib.safeMulDiv: saturating CEIL.  Returns FIX_MAX on saturation, 0 on a=0/b=0.
safe_muldiv_ceil(a, b, c) = { my(r); if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX || c == 0, return(FIX_MAX)); r = ceil_div(a * b, c); if(r > FIX_MAX, FIX_MAX, r); }

\\ TradeLib.buyAmount(s, slippage, sellLow, buyHigh) — post-mitigation CEIL inner mul.
buyAmount(s, slippage, sellLow, buyHigh) = { my(inner); inner = fix_mul_ceil(s, FIX_ONE - slippage); safe_muldiv_ceil(inner, sellLow, buyHigh); }

\\ RebalanceLib.basketRange returns [low, high].
basket_range(supplyTotal, bhBottom, bhTop, lowSlack, highSlack) = { my(rh, rl, h1, l1); rh = bhTop + highSlack; rl = bhBottom - lowSlack; h1 = min(rh, supplyTotal); l1 = min(rl, h1); return([l1, h1]); }

\\ needsTrade(rngLow, rngHigh, basketsNeeded):  rngLow < bn < rngHigh + 1.
needs_trade(rngLow, rngHigh, basketsNeeded) = (rngLow < basketsNeeded) && (basketsNeeded < rngHigh + 1);

\\ State machine encoding:
\\   storage = [basketsNeeded, backingBuffer, status, pendingTrade]
\\   status: 0 = NONE, 1 = OPEN, 2 = SETTLED
\\   pendingTrade: 0 = None; vector [sellAmt, buyAmt] = Some _

\\ prepare(s, supplyTotal, bhBottom, bhTop, lowSlack, highSlack, sellAmt, slip, sLow, bHigh)
prepare(s, sup, bhB, bhT, lS, hS, sa, sl, sLo, bHi) = { my(rng, bn, ba, pt); rng = basket_range(sup, bhB, bhT, lS, hS); bn = s[1]; if(needs_trade(rng[1], rng[2], bn), ba = buyAmount(sa, sl, sLo, bHi); pt = [sa, ba]; return([bn, s[2], 1, pt]); , return(s); ); }

\\ settle(s, newBasketsNeeded):  OPEN -> NONE, basketsNeeded := newBasketsNeeded.
settle(s, newBn) = { if(s[3] == 1, return([newBn, s[2], 0, 0]); , return(s); ); }

\\ ---- Calibration ----
INITIAL_BN = 10^6 * FIX_ONE;       \\ 1M BU
BACKING_BUFFER = 10^16;            \\ 1%
S0 = [INITIAL_BN, BACKING_BUFFER, 0, 0];   \\ NONE state, no pendingTrade

print("Calibration: basketsNeeded=1M BU, backingBuffer=1%, status=NONE");
print("");

\\ ============================================================
\\ STATE-1: initial state is NONE with no pending trade
\\ ============================================================
print("--- STATE-1: initial state is NONE with pendingTrade = None ---");
{
  if(S0[3] == 0 && S0[4] == 0,
    print("  OK: initial state matches the (NONE, None) invariant."),
    print("  FAIL: initial state has unexpected status or pendingTrade."));
}
print("");

\\ ============================================================
\\ STATE-2: prepare on NONE yields NONE-or-OPEN
\\ ============================================================
print("--- STATE-2: prepare(NONE) -> NONE | OPEN ---");
\\ Case A: range tight (no trade): bhBot = bhTop = bn so range = (bn, bn) and bn < bn is false.
{
  print("  Case A: tight range (no trade)");
  s1 = prepare(S0, INITIAL_BN, INITIAL_BN, INITIAL_BN, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  printf("    s' status=%d  pt=%s\n", s1[3], if(s1[4] == 0, "None", "Some(.)"));
  if(s1[3] == 0 && s1[4] == 0,
    print("    OK: tight-range prepare leaves storage in NONE state."),
    print("    FAIL: tight-range prepare unexpectedly transitioned."));
}
\\ Case B: loose range (trade needed). bhBot = bn/2 < bn; bhTop = bn so high = bn, low = bn/2.
\\         needsTrade(bn/2, bn, bn) = (bn/2 < bn) && (bn < bn+1) = true.
{
  print("  Case B: loose range (trade needed)");
  bhBot = INITIAL_BN \ 2;
  bhTop = INITIAL_BN;
  s1 = prepare(S0, INITIAL_BN, bhBot, bhTop, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  printf("    s' status=%d  pt=%s\n", s1[3], if(s1[4] == 0, "None", "Some(.)"));
  if(s1[3] == 1 && s1[4] != 0,
    print("    OK: loose-range prepare transitioned to OPEN with pendingTrade."),
    print("    FAIL: loose-range prepare did not transition to OPEN."));
}
print("");

\\ ============================================================
\\ STATE-3: settle on OPEN yields NONE
\\ ============================================================
print("--- STATE-3: settle(OPEN) -> NONE ---");
{
  bhBot = INITIAL_BN \ 2;
  bhTop = INITIAL_BN;
  s_open = prepare(S0, INITIAL_BN, bhBot, bhTop, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  if(s_open[3] != 1, print("  setup issue: prepare did not yield OPEN"));
  new_bn = INITIAL_BN \ 2;            \\ haircut to 0.5M BU
  s_after = settle(s_open, new_bn);
  printf("  s_after status=%d  bn=%d  pt=%s\n", s_after[3], s_after[1], if(s_after[4] == 0, "None", "Some(.)"));
  if(s_after[3] == 0 && s_after[4] == 0 && s_after[1] == new_bn,
    print("  OK: settle returned to NONE with new basketsNeeded."),
    print("  FAIL: settle did not return to NONE / basketsNeeded mismatch."));
}
print("");

\\ ============================================================
\\ STATE-4: round-trip prepare -> settle returns to NONE
\\ ============================================================
print("--- STATE-4: prepare -> settle round-trip ---");
{
  bhBot = INITIAL_BN \ 2;
  bhTop = INITIAL_BN;
  new_bn = INITIAL_BN \ 2;
  s1 = prepare(S0, INITIAL_BN, bhBot, bhTop, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  s2 = settle(s1, new_bn);
  if(s2[3] == 0 && s2[4] == 0,
    print("  OK: prepare -> settle round-trip ends in NONE state."),
    print("  FAIL: round-trip did not return to NONE."));
}
print("");

\\ ============================================================
\\ STATE-5: needsTrade window
\\ ============================================================
print("--- STATE-5: needsTrade(range, bn) iff range.low < bn <= range.high ---");
{
  setrand(20260430);
  N = 500;
  mismatch = 0;
  for(i = 1, N,
    bn = 1 + random(10^9 * FIX_ONE);
    rngLow = random(2 * 10^9 * FIX_ONE);
    rngHigh = rngLow + random(10^9 * FIX_ONE);
    nt = needs_trade(rngLow, rngHigh, bn);
    expected = (rngLow < bn) && (bn <= rngHigh);
    if(nt != expected, mismatch = mismatch + 1);
  );
  printf("  N=%d random tuples; mismatches: %d\n", N, mismatch);
  if(mismatch == 0,
    print("  OK: needsTrade matches the algebraic predicate."),
    print("  FAIL: needsTrade diverges from the algebraic predicate."));
}
print("");

\\ ============================================================
\\ STATE-6: prepare is idempotent on the no-trade branch
\\ ============================================================
print("--- STATE-6: prepare-prepare on tight range is idempotent ---");
{
  s1 = prepare(S0, INITIAL_BN, INITIAL_BN, INITIAL_BN, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  s2 = prepare(s1, INITIAL_BN, INITIAL_BN, INITIAL_BN, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  if(s1 == s2,
    print("  OK: prepare on tight range is a fixpoint."),
    print("  FAIL: prepare on tight range diverged on second call."));
}
print("");

\\ ============================================================
\\ STATE-7: settle's new basketsNeeded is what was passed in
\\ ============================================================
print("--- STATE-7: settle preserves the caller-supplied basketsNeeded ---");
{
  bhBot = INITIAL_BN \ 2;
  bhTop = INITIAL_BN;
  s1 = prepare(S0, INITIAL_BN, bhBot, bhTop, 0, 0, 10^20, 10^16, FIX_ONE, FIX_ONE);
  bad = 0;
  for(k = 1, 11,
    target_bn = INITIAL_BN \ 10 + (k - 1) * (INITIAL_BN \ 10);
    s2 = settle(s1, target_bn);
    if(s2[1] != target_bn, bad = bad + 1);
  );
  printf("  Tested 11 different newBasketsNeeded values; bad: %d\n", bad);
  if(bad == 0,
    print("  OK: settle threads newBasketsNeeded through unchanged."),
    print("  FAIL: settle did not preserve newBasketsNeeded."));
}
print("");

\\ ============================================================
\\ STATE-8: composition of basketRange + buyAmount
\\ ============================================================
print("--- STATE-8: prepare composes basketRange + buyAmount correctly ---");
{
  bhBot = INITIAL_BN \ 2;
  bhTop = INITIAL_BN;
  sellAmt = 10^20;
  slip = 10^16;          \\ 1% slippage
  sLow = FIX_ONE;
  bHigh = FIX_ONE;
  s1 = prepare(S0, INITIAL_BN, bhBot, bhTop, 0, 0, sellAmt, slip, sLow, bHigh);
  if(s1[3] != 1 || s1[4] == 0,
    print("  FAIL: prepare did not yield OPEN state with pendingTrade."),
    expected_buy = buyAmount(sellAmt, slip, sLow, bHigh);
    actual_buy   = s1[4][2];
    printf("  expected buyAmount = %d\n", expected_buy);
    printf("  actual   buyAmount = %d\n", actual_buy);
    if(expected_buy == actual_buy,
      print("  OK: composition matches direct TradeLib.buyAmount call."),
      print("  FAIL: composition diverges from TradeLib.buyAmount.")));
}
print("");

\\ ============================================================
\\ STATE-9: settle on NONE is a no-op
\\ ============================================================
print("--- STATE-9: settle on NONE is a no-op ---");
{
  s1 = settle(S0, INITIAL_BN \ 4);
  if(s1 == S0,
    print("  OK: settle on NONE leaves storage unchanged."),
    print("  FAIL: settle on NONE mutated storage."));
}
print("");

print("Done. Run with `gp -q < recollateralization_state_machine.gp`.");
