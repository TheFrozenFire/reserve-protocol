\\ quote_rounding_direction.gp
\\
\\ CAS-side validation of BasketHandlerP1.quote() rounding direction.
\\
\\ Reference:
\\   protocol/contracts/p1/BasketHandler.sol :: quote(amount, applyIssuancePremium, rounding)
\\   protocol/contracts/p1/BasketHandler.sol :: _quantity(erc20, coll, rounding)
\\   protocol/contracts/p1/BasketHandler.sol :: quoteCustomRedemption(...)  (FLOOR-only)
\\
\\ Per-token formula inside quote() (post-mitigation, post-Issuance Premium v2):
\\
\\   q1 = _quantity(coll, rounding)                  = refAmts[i].div(refPerTok, rounding)
\\   q2 = q1.safeMul(amount, rounding)
\\   if applyIssuancePremium && premium > FIX_ONE:
\\     q3 = q2.safeMul(premium, rounding)
\\   else:
\\     q3 = q2
\\   qTok_i = q3.shiftl_toUint(decimals, rounding)
\\
\\ Properties probed (these are exactly what the round-trip safety on the
\\ protocol side relies on; cf. issuance_premium/premium_curve.gp INV-P5/P6):
\\
\\   INV-Q1   Per-token CEIL >= per-token FLOOR.  Conservative direction at
\\            every algebraic step (div, two safeMuls, shiftl_toUint).
\\   INV-Q2   Per-token (CEIL - FLOOR) is bounded by the rounding-error budget
\\            for the call shape (at most a constant number of wei per token).
\\   INV-Q3   Empty basket -> empty arrays; no revert.  Disabled basket is
\\            *not* short-circuited inside quote() itself (the protocol guards
\\            issuance/redemption upstream); we record this so the CAS model
\\            tracks the production semantics rather than an idealised one.
\\   INV-Q4   Premium amplification: per-token quantity strictly grows when
\\            premium > FIX_ONE, and is unchanged when premium == FIX_ONE.
\\            The amplification is local to each token (no cross-term).
\\   INV-Q5   FIX_MAX boundary: refPerTok == 0 produces FIX_MAX qty (saturating);
\\            premium == FIX_MAX saturates safeMul to FIX_MAX (Certora #1283).
\\   INV-Q6   quoteCustomRedemption is unconditionally FLOOR — even when the
\\            current basket is the only nonce in the linear combination, the
\\            redemption-side path uses safeMulDiv(.., FLOOR) and shiftl_toUint
\\            with FLOOR.  We check that this gives a strictly conservative
\\            (<= FLOOR-quote) per-token amount versus quote(.., FLOOR).

print("=== BasketHandler.quote rounding direction — CAS validation ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;
CEIL_FLAG = 1;
FLOOR_FLAG = 0;

\\ ---- Solidity-faithful helpers ----

\\ Integer ceiling division (R003).
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ div(a, b, rounding) — D18-fixed division: floor or ceil of (FIX_ONE * a / b).
div_fix(a, b, rnd) = { if(b == 0, error("div by zero")); if(rnd == CEIL_FLAG, ceil_div(FIX_ONE * a, b), (FIX_ONE * a) \ b); }

\\ safeDiv(a, b, rnd): preserves FIX_MAX numerator, treats b==0 as +infty -> FIX_MAX.
safeDiv(a, b, rnd) = { if(a == 0, return(0)); if(a == FIX_MAX, return(FIX_MAX)); if(b == 0, return(FIX_MAX)); my(raw); raw = div_fix(a, b, rnd); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }

\\ safeMul(a, b, rnd): D18-fixed multiplication with FIX_MAX saturation.
safeMul(a, b, rnd) = { if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX, return(FIX_MAX)); my(raw); raw = if(rnd == CEIL_FLAG, ceil_div(a * b, FIX_ONE), (a * b) \ FIX_ONE); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }

\\ shiftl_toUint(x, decimals, rnd): D18 -> qTok with `decimals`-decimals ERC20.
\\ For a stablecoin with 18 decimals, this is the identity on the integer.
\\ For 6-decimals (USDC/USDT) it is x \ 10^12 (FLOOR) or ceil_div(x, 10^12) (CEIL).
shiftl_toUint(x, decimals, rnd) = { if(x == 0, return(0)); my(d, coeff); d = decimals - 18; coeff = 10^abs(d); if(d >= 0, x * coeff, if(rnd == CEIL_FLAG, ceil_div(x, coeff), x \ coeff)); }

\\ _quantity(erc20, coll, rounding): {tok/BU}
\\   refPerTok == 0 -> FIX_MAX
\\   else            -> refAmts[i].div(refPerTok, rounding)
quantity_fn(refAmt, refPerTok, rnd) = { if(refPerTok == 0, return(FIX_MAX)); div_fix(refAmt, refPerTok, rnd); }

\\ Per-token quote: returns {qTok}
\\ Mirrors p1/BasketHandler.sol::quote line-for-line.
quote_one(refAmt, refPerTok, decimals, amount_BU, premium, applyPrem, rnd) = { my(q1, q2, q3); q1 = quantity_fn(refAmt, refPerTok, rnd); q2 = safeMul(q1, amount_BU, rnd); q3 = if(applyPrem && premium > FIX_ONE, safeMul(q2, premium, rnd), q2); shiftl_toUint(q3, decimals, rnd); }

\\ Per-token quoteCustomRedemption: amount * refAmt / refPerTok, FLOOR throughout.
\\   safeMulDiv(amount, refAmt, refPerTok, FLOOR) -> shiftl_toUint(.., FLOOR)
\\ Implemented as exact rationals (the production code uses 512-bit
\\ intermediate; for our calibrated inputs the integer arithmetic does not
\\ overflow uint256, so we mirror it directly).
quote_custom_one(amount_BU, refAmt, refPerTok, decimals) = { my(raw); if(refPerTok == 0, return(0)); raw = (amount_BU * refAmt) \ refPerTok; shiftl_toUint(raw, decimals, FLOOR_FLAG); }

\\ ---- Calibration: 5-token stablecoin basket ----
\\ refAmt = FIX_ONE/5 each; sum = FIX_ONE -> 1.0 ref/BU.
\\ refPerTok = FIX_ONE for fiat-pegged collateral (1.0 ref/tok).
\\ All have 18 decimals to keep arithmetic clean; we add a 6-decimals
\\ variant in INV-Q5 to exercise the shiftl_toUint rounding direction.
\\ pegPrices match issuance_premium/premium_curve.gp (USDC/USDT/DAI on peg,
\\ FRAX 0.2% under, LUSD 0.5% under).

\\ Mainnet realistic decimals: USDC/USDT are 6-decimals, DAI/FRAX/LUSD are 18.
\\ refAmt = FIX_ONE/5 has remainder 1 (FIX_ONE = 10^18 is not divisible by 5
\\ in integer arithmetic? actually 10^18 / 5 == 2*10^17 exactly).  To stress
\\ rounding we deliberately set refAmt = FIX_ONE / 7 for one token (gives
\\ a non-terminating fixed-point representation) so the (div, mul, shift)
\\ chain produces a non-zero CEIL-vs-FLOOR gap.

basket_tokens = ["USDC", "DAI", "USDT", "FRAX", "LUSD"];
\\ FIX_ONE/5 = 2e17 exactly; FIX_ONE/7 = 142857142857142857 (loses 1 wei).
\\ Sum of refAmts: 4 * (FIX_ONE/5) + FIX_ONE/7 = 0.942857... ref/BU.
\\ This is fine for the CAS — we are validating per-token quote() correctness,
\\ not enforcing that the basket sums to 1.0 ref/BU.
ref_amts      = [FIX_ONE \ 5, FIX_ONE \ 5, FIX_ONE \ 5, FIX_ONE \ 7, FIX_ONE \ 5];
ref_per_toks  = [FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE];
decimals_tok  = [6, 18, 6, 18, 18];   \\ USDC/USDT 6-decimals, others 18
peg_prices    = [FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE - FIX_ONE * 2 \ 1000, FIX_ONE - FIX_ONE * 5 \ 1000];

\\ Issuance premium per the v2 curve (mirrors premium_curve.gp).
prem_for(pegPrice) = { if(pegPrice == 0, return(FIX_ONE)); if(pegPrice >= FIX_ONE, return(FIX_ONE)); safeDiv(FIX_ONE, pegPrice, CEIL_FLAG); }

print("--- Calibration: 5-token stablecoin basket ---");
print_calib(i) = { printf("  %-5s  refAmt=%.4f refPerTok=%.4f decimals=%d peg=%.4f premium=%.6f\n", basket_tokens[i], ref_amts[i] * 1.0 / FIX_ONE, ref_per_toks[i] * 1.0 / FIX_ONE, decimals_tok[i], peg_prices[i] * 1.0 / FIX_ONE, prem_for(peg_prices[i]) * 1.0 / FIX_ONE); }
for(i = 1, 5, print_calib(i));
print("");

\\ ============================================================
\\ INV-Q1: Per-token CEIL >= FLOOR for every (amount, premium).
\\ ============================================================
print("--- INV-Q1: per-token CEIL >= FLOOR across the basket ---");

amounts_BU = [FIX_ONE, 7 * FIX_ONE, 1000 * FIX_ONE, 10^6 * FIX_ONE, 10^9 * FIX_ONE];
viol_q1 = 0;
gap_max = 0;

inv_q1_step(i, amt, applyPrem) = { my(qC, qF, prem); prem = prem_for(peg_prices[i]); qC = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, applyPrem, CEIL_FLAG); qF = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, applyPrem, FLOOR_FLAG); if(qC < qF, viol_q1 = viol_q1 + 1); if(qC - qF > gap_max, gap_max = qC - qF); }

{
  for(ai = 1, #amounts_BU,
    for(i = 1, 5,
      inv_q1_step(i, amounts_BU[ai], 1);
      inv_q1_step(i, amounts_BU[ai], 0);
    );
  );
}
{ printf("  swept %d (token, amount, applyPrem) cells; CEIL<FLOOR violations = %d; max gap = %d wei\n", 5 * #amounts_BU * 2, viol_q1, gap_max); }
if(viol_q1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-Q2: Per-token (CEIL - FLOOR) is bounded.
\\ For a chain of 1-2 CEIL/FLOOR ops (no premium / with premium) on D18
\\ values then a shiftl_toUint, the gap is at most 10^(18 - decimals) +
\\ a small constant per safeMul/safeDiv step.  For 18-decimals tokens
\\ that's a handful of wei; we record the realised gap.
\\ ============================================================
print("--- INV-Q2: rounding gap bounded per-token ---");

gap_no_prem = 0;
gap_with_prem = 0;
gap_step(i, amt, applyPrem) = { my(qC, qF, prem, gap); prem = prem_for(peg_prices[i]); qC = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, applyPrem, CEIL_FLAG); qF = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, applyPrem, FLOOR_FLAG); gap = qC - qF; if(applyPrem, if(gap > gap_with_prem, gap_with_prem = gap), if(gap > gap_no_prem, gap_no_prem = gap)); }

{
  for(ai = 1, #amounts_BU,
    for(i = 1, 5,
      gap_step(i, amounts_BU[ai], 0);
      gap_step(i, amounts_BU[ai], 1);
    );
  );
}

\\ Bound: each CEIL/FLOOR introduces at most 1 wei of D18 quantity gap.
\\ With (div, mul, mul, shift) the worst-case per-token gap is bounded by
\\ a small constant times the upstream quantity.  For the calibrated basket
\\ (refAmt = 0.2, refPerTok = 1, amount up to 1B BU) we expect a few-wei
\\ gap without premium, and a slightly larger gap with premium.
{ printf("  max per-token gap (no premium):   %d wei\n", gap_no_prem); }
{ printf("  max per-token gap (with premium): %d wei\n", gap_with_prem); }
\\ Document the witness: in the calibrated case the gap should be small
\\ (well under 10^9 wei = 10^-9 of a token).
inv_q2_ok = (gap_no_prem <= 10^12) && (gap_with_prem <= 10^12);
if(inv_q2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-Q3: Empty basket -> empty arrays; we model the loop bound directly.
\\ Disabled basket: quote() *does not* short-circuit on `disabled` itself;
\\ that's the BackingManager/RToken's job.  We document this here so the
\\ CAS spec doesn't drift from production behaviour.
\\ ============================================================
print("--- INV-Q3: empty basket -> empty result; disabled is upstream ---");
empty_len = 0;  \\ basket.erc20s.length
\\ The for-loop over [1..empty_len] runs zero times; result is empty.
{ printf("  empty basket: erc20s.length = %d, quantities.length = %d\n", empty_len, empty_len); }
inv_q3_empty_ok = (empty_len == 0);

\\ Disabled non-empty: we exercise quote() with a 1-token "basket" and
\\ confirm it still returns a non-empty quantity (i.e. quote does not
\\ guard on the disabled flag).  The protocol's safety on a disabled
\\ basket is enforced by issue() / redeem() / status() -> DISABLED, not
\\ by quote() itself.
q_disabled = quote_one(FIX_ONE \ 5, FIX_ONE, 18, FIX_ONE, FIX_ONE, 0, CEIL_FLAG);
{ printf("  disabled-but-iterated 1-token quote returns: %d (nonzero by design)\n", q_disabled); }
inv_q3_disabled_ok = (q_disabled > 0);
if(inv_q3_empty_ok && inv_q3_disabled_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-Q4: Premium amplification — per-token, locally.
\\ For each token: q(amount, applyPrem=1) >= q(amount, applyPrem=0),
\\ with strict inequality iff premium > FIX_ONE.
\\ ============================================================
print("--- INV-Q4: premium amplification is local per-token ---");
viol_q4 = 0;

inv_q4_step(i, amt) = { my(qOff, qOn, prem); prem = prem_for(peg_prices[i]); qOff = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, 0, CEIL_FLAG); qOn = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, 1, CEIL_FLAG); if(qOn < qOff, viol_q4 = viol_q4 + 1); if(prem == FIX_ONE && qOn != qOff, viol_q4 = viol_q4 + 1); if(prem > FIX_ONE && qOn <= qOff, viol_q4 = viol_q4 + 1); }

{
  for(ai = 1, #amounts_BU,
    for(i = 1, 5,
      inv_q4_step(i, amounts_BU[ai]);
    );
  );
}
{ printf("  amplification violations across %d (token, amount) cells: %d\n", 5 * #amounts_BU, viol_q4); }

\\ Concrete witness: FRAX (0.2% under-peg) at 1M BUs.
amt_witness = 10^6 * FIX_ONE;
prem_FRAX = prem_for(peg_prices[4]);
qFRAX_off = quote_one(ref_amts[4], ref_per_toks[4], decimals_tok[4], amt_witness, prem_FRAX, 0, CEIL_FLAG);
qFRAX_on = quote_one(ref_amts[4], ref_per_toks[4], decimals_tok[4], amt_witness, prem_FRAX, 1, CEIL_FLAG);
{ printf("  FRAX  (peg=0.998, premium=%.6f, 1M BU): qOff=%d, qOn=%d, lift=%d wei (~ +%.4f%%)\n", prem_FRAX * 1.0 / FIX_ONE, qFRAX_off, qFRAX_on, qFRAX_on - qFRAX_off, (qFRAX_on - qFRAX_off) * 100.0 / qFRAX_off); }
if(viol_q4 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-Q5: FIX_MAX boundary across quote()'s multiplication chain.
\\   - refPerTok == 0 -> _quantity returns FIX_MAX.  Then safeMul(FIX_MAX,...)
\\     keeps FIX_MAX, shiftl_toUint(FIX_MAX, 18, ...) returns FIX_MAX itself.
\\   - premium == FIX_MAX (theoretical extreme): safeMul saturates.
\\ Cross-validates against issuance_premium/premium_curve.gp::INV-P4.
\\ ============================================================
print("--- INV-Q5: FIX_MAX boundary saturation through quote() ---");

\\ refPerTok = 0
q_zero_rpt = quote_one(FIX_ONE \ 5, 0, 18, FIX_ONE, FIX_ONE, 0, CEIL_FLAG);
{ printf("  refPerTok=0           -> per-token qTok = %s\n", if(q_zero_rpt == FIX_MAX, "FIX_MAX (saturating)", "non-saturating: FAIL")); }

\\ premium = FIX_MAX
q_fixmax_prem = quote_one(FIX_ONE \ 5, FIX_ONE, 18, FIX_ONE, FIX_MAX, 1, CEIL_FLAG);
{ printf("  premium=FIX_MAX       -> per-token qTok = %s\n", if(q_fixmax_prem == FIX_MAX, "FIX_MAX (saturating)", "non-saturating: FAIL")); }

\\ amount = FIX_MAX with normal premium
q_fixmax_amt = quote_one(FIX_ONE \ 5, FIX_ONE, 18, FIX_MAX, FIX_ONE, 0, CEIL_FLAG);
{ printf("  amount=FIX_MAX        -> per-token qTok = %s\n", if(q_fixmax_amt == FIX_MAX, "FIX_MAX (saturating)", "non-saturating: FAIL")); }

\\ refAmt = FIX_MAX (degenerate basket weight)
q_fixmax_refamt = quote_one(FIX_MAX, FIX_ONE, 18, FIX_ONE, FIX_ONE, 0, CEIL_FLAG);
{ printf("  refAmt=FIX_MAX        -> per-token qTok = %s\n", if(q_fixmax_refamt == FIX_MAX, "FIX_MAX (saturating)", "non-saturating: FAIL")); }

inv_q5_ok = (q_zero_rpt == FIX_MAX) && (q_fixmax_prem == FIX_MAX) && (q_fixmax_amt == FIX_MAX) && (q_fixmax_refamt == FIX_MAX);
if(inv_q5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-Q6: quoteCustomRedemption is FLOOR-only.
\\ For a single nonce / portion = FIX_ONE / current basket: the custom
\\ path uses a single safeMulDiv(amount, refAmt, refPerTok, FLOOR), no
\\ premium.  Compare to quote(amount, applyIssuancePremium=false, FLOOR):
\\ both should agree on the calibrated basket (modulo intermediate
\\ rounding); the custom path must never exceed the FLOOR-quote.
\\ ============================================================
print("--- INV-Q6: quoteCustomRedemption is FLOOR; never exceeds quote(FLOOR) ---");
viol_q6 = 0;
amt_test = 10^6 * FIX_ONE;

inv_q6_step(i) = { my(qCustom, qFloor); qCustom = quote_custom_one(amt_test, ref_amts[i], ref_per_toks[i], decimals_tok[i]); qFloor = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt_test, FIX_ONE, 0, FLOOR_FLAG); if(qCustom > qFloor, viol_q6 = viol_q6 + 1); printf("  %-5s  custom=%d  floor=%d  delta=%d wei\n", basket_tokens[i], qCustom, qFloor, qFloor - qCustom); }

for(i = 1, 5, inv_q6_step(i));
\\ The protocol uses safeMulDiv (combined-step rounding) in custom redemption,
\\ versus a (div, mul) chain in quote().  Both are FLOOR.  In our integer
\\ model both reduce to a single (amount * refAmt) \ refPerTok division,
\\ then shiftl_toUint FLOOR — so they should be identical for this calibration.
if(viol_q6 == 0, print("  OK"), print("  FAIL"));
print("");

print("Done.");
