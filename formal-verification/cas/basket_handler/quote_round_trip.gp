\\ quote_round_trip.gp
\\
\\ CAS-side validation of the issuance/redemption round-trip property
\\ for BasketHandlerP1.quote().  This is the load-bearing safety claim:
\\ a sequence of issue(amount, CEIL, premium) followed by redeem(qTok, FLOOR)
\\ never extracts more BU value than was deposited.
\\
\\ Reference:
\\   protocol/contracts/p1/BasketHandler.sol :: quote(amount, applyIssuancePremium, rounding)
\\   protocol/contracts/p1/RToken.sol         :: issueTo (quote with CEIL)
\\   protocol/contracts/p1/RToken.sol         :: redeemTo / redeemCustom (quote with FLOOR)
\\
\\ Properties probed:
\\
\\   INV-RT1  Linearity in amount: per-token quote(2*amount) is within a
\\            small constant (rounding budget) of 2 * quote(amount).
\\            Formally, |q(k*amount) - k*q(amount)| <= k wei for the
\\            FLOOR direction and similarly for CEIL.  Compounding amounts
\\            up to k = 100 keeps the gap proportional and small.
\\
\\   INV-RT2  Round-trip non-extraction: for each per-token leg,
\\            redeem-side qTok (FLOOR) <= issuance-side qTok (CEIL),
\\            so the protocol holds at least as many tokens as it must
\\            return for the corresponding redemption.  This is the
\\            invariant that justifies dual rounding directions.
\\
\\   INV-RT3  Round-trip BU recovery: starting from `amount_in` BU,
\\            issue gives qTok with CEIL+premium; redeeming THOSE qTok
\\            (treated as a basket-unit-equivalent count via the
\\            inverse formula) recovers at most `amount_in` BU.
\\            Concretely we compute the implied BU of the redeemed
\\            tokens via floor inversion and check `amount_out <= amount_in`,
\\            with the gap bounded by per-token rounding error.
\\
\\   INV-RT4  Linearity scaling sweep: across amounts in {1, 2, 5, 10,
\\            100, 1e6, 1e9} BU we record the realised gap per token to
\\            confirm the rounding budget grows linearly (not super-linearly)
\\            in the amount.  If it ever scaled super-linearly that would
\\            indicate a compounding-rounding bug (the round-trip would
\\            erode value the more you transacted).
\\
\\   INV-RT5  Custom-redemption round trip: the same linearity / non-extraction
\\            holds for quoteCustomRedemption in the single-nonce case
\\            (portion = FIX_ONE).
\\
\\ Calibration matches quote_rounding_direction.gp.

print("=== BasketHandler.quote round-trip — CAS validation ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;
CEIL_FLAG = 1;
FLOOR_FLAG = 0;

\\ ---- Solidity-faithful helpers (duplicated from quote_rounding_direction.gp) ----

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
div_fix(a, b, rnd) = { if(b == 0, error("div by zero")); if(rnd == CEIL_FLAG, ceil_div(FIX_ONE * a, b), (FIX_ONE * a) \ b); }
safeDiv(a, b, rnd) = { if(a == 0, return(0)); if(a == FIX_MAX, return(FIX_MAX)); if(b == 0, return(FIX_MAX)); my(raw); raw = div_fix(a, b, rnd); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }
safeMul(a, b, rnd) = { if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX, return(FIX_MAX)); my(raw); raw = if(rnd == CEIL_FLAG, ceil_div(a * b, FIX_ONE), (a * b) \ FIX_ONE); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }
shiftl_toUint(x, decimals, rnd) = { if(x == 0, return(0)); my(d, coeff); d = decimals - 18; coeff = 10^abs(d); if(d >= 0, x * coeff, if(rnd == CEIL_FLAG, ceil_div(x, coeff), x \ coeff)); }
quantity_fn(refAmt, refPerTok, rnd) = { if(refPerTok == 0, return(FIX_MAX)); div_fix(refAmt, refPerTok, rnd); }
quote_one(refAmt, refPerTok, decimals, amount_BU, premium, applyPrem, rnd) = { my(q1, q2, q3); q1 = quantity_fn(refAmt, refPerTok, rnd); q2 = safeMul(q1, amount_BU, rnd); q3 = if(applyPrem && premium > FIX_ONE, safeMul(q2, premium, rnd), q2); shiftl_toUint(q3, decimals, rnd); }
quote_custom_one(amount_BU, refAmt, refPerTok, decimals) = { my(raw); if(refPerTok == 0, return(0)); raw = (amount_BU * refAmt) \ refPerTok; shiftl_toUint(raw, decimals, FLOOR_FLAG); }

\\ Inverse: given a per-token qTok and (refAmt, refPerTok, decimals), what
\\ amount of BU does it correspond to under FLOOR redemption?  This is the
\\ "implied BU" we use to detect value extraction.  For a 18-decimals
\\ stablecoin with refPerTok = FIX_ONE, refAmt = FIX_ONE/5:
\\   qTok = amount_BU * refAmt / FIX_ONE     (FLOOR)
\\ -> amount_BU >= qTok * FIX_ONE / refAmt    (FLOOR inverse)
\\ We compute amount_BU = floor(qTok * 10^(18-decimals) * FIX_ONE / refAmt)
\\ as the conservative back-out that the protocol never exceeds.
implied_BU(qTok, refAmt, refPerTok, decimals) = { my(raw); if(refAmt == 0, return(0)); raw = qTok * 10^(18 - decimals) * refPerTok \ refAmt; raw; }

\\ ---- Calibration ----
\\ Mainnet realistic decimals match quote_rounding_direction.gp:
\\ USDC/USDT 6-decimals; FRAX uses FIX_ONE/7 refAmt to surface real
\\ rounding behaviour rather than clean-divisor zeros.
basket_tokens = ["USDC", "DAI", "USDT", "FRAX", "LUSD"];
ref_amts      = [FIX_ONE \ 5, FIX_ONE \ 5, FIX_ONE \ 5, FIX_ONE \ 7, FIX_ONE \ 5];
ref_per_toks  = [FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE];
decimals_tok  = [6, 18, 6, 18, 18];
peg_prices    = [FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE - FIX_ONE * 2 \ 1000, FIX_ONE - FIX_ONE * 5 \ 1000];

prem_for(pegPrice) = { if(pegPrice == 0, return(FIX_ONE)); if(pegPrice >= FIX_ONE, return(FIX_ONE)); safeDiv(FIX_ONE, pegPrice, CEIL_FLAG); }

\\ ============================================================
\\ INV-RT1: Linearity in amount — quote(k * amount) ~ k * quote(amount).
\\ ============================================================
print("--- INV-RT1: linearity in amount (FLOOR direction, no premium) ---");
base_amount = FIX_ONE;
ks = [2, 3, 5, 10, 100];
viol_rt1 = 0;
worst_gap_rt1 = 0;

inv_rt1_step(i, k) = { my(qk, q1, lhs, rhs, gap); qk = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], k * base_amount, FIX_ONE, 0, FLOOR_FLAG); q1 = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], base_amount, FIX_ONE, 0, FLOOR_FLAG); lhs = qk; rhs = k * q1; gap = abs(lhs - rhs); if(gap > k, viol_rt1 = viol_rt1 + 1); if(gap > worst_gap_rt1, worst_gap_rt1 = gap); }

{
  for(ki = 1, #ks,
    for(i = 1, 5,
      inv_rt1_step(i, ks[ki]);
    );
  );
}
{ printf("  swept %d (token, k) cells; |q(k*x) - k*q(x)| > k violations = %d; worst gap = %d wei\n", 5 * #ks, viol_rt1, worst_gap_rt1); }

\\ Witness: k = 100 on USDC (clean baseline).
qk100 = quote_one(ref_amts[1], ref_per_toks[1], decimals_tok[1], 100 * base_amount, FIX_ONE, 0, FLOOR_FLAG);
q1_USDC = quote_one(ref_amts[1], ref_per_toks[1], decimals_tok[1], base_amount, FIX_ONE, 0, FLOOR_FLAG);
{ printf("  USDC: q(100 BU) = %d, 100 * q(1 BU) = %d, gap = %d wei\n", qk100, 100 * q1_USDC, qk100 - 100 * q1_USDC); }
if(viol_rt1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RT2: Round-trip non-extraction.
\\ For each token: redeem-side qTok (FLOOR, no premium) <= issue-side qTok
\\ (CEIL, with premium).  This is the per-token version of "issue then
\\ redeem returns no more value than was put in".
\\ ============================================================
print("--- INV-RT2: redeem(FLOOR) <= issue(CEIL+premium) per-token ---");
viol_rt2 = 0;
amounts = [FIX_ONE, 1000 * FIX_ONE, 10^6 * FIX_ONE, 10^9 * FIX_ONE];

inv_rt2_step(i, amt) = { my(qIssue, qRedeem, prem); prem = prem_for(peg_prices[i]); qIssue = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, prem, 1, CEIL_FLAG); qRedeem = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amt, FIX_ONE, 0, FLOOR_FLAG); if(qRedeem > qIssue, viol_rt2 = viol_rt2 + 1); }

{
  for(ai = 1, #amounts,
    for(i = 1, 5,
      inv_rt2_step(i, amounts[ai]);
    );
  );
}
{ printf("  swept %d (token, amount) cells; redeem > issue violations = %d\n", 5 * #amounts, viol_rt2); }

\\ Concrete witness on FRAX (premium > FIX_ONE) at 1M BU.
amt_w = 10^6 * FIX_ONE;
prem_FRAX = prem_for(peg_prices[4]);
qIssue_FRAX = quote_one(ref_amts[4], ref_per_toks[4], decimals_tok[4], amt_w, prem_FRAX, 1, CEIL_FLAG);
qRedeem_FRAX = quote_one(ref_amts[4], ref_per_toks[4], decimals_tok[4], amt_w, FIX_ONE, 0, FLOOR_FLAG);
{ printf("  FRAX 1M BU: issue (CEIL, prem=%.6f) = %d  redeem (FLOOR, no prem) = %d  surplus = %d wei (~ %.4f%%)\n", prem_FRAX * 1.0 / FIX_ONE, qIssue_FRAX, qRedeem_FRAX, qIssue_FRAX - qRedeem_FRAX, (qIssue_FRAX - qRedeem_FRAX) * 100.0 / qRedeem_FRAX); }
if(viol_rt2 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RT3: Round-trip BU recovery.
\\ Issue amount_in BU on the (no-premium, peg-stable) sub-basket
\\ {USDC, DAI, USDT}; for each token compute implied_BU by FLOOR-inversion;
\\ the minimum across tokens bounds the recoverable BU on redemption.
\\ Check: minimum implied <= amount_in (no value extraction) AND >=
\\ amount_in - 1 wei (the rounding budget).
\\ ============================================================
print("--- INV-RT3: redemption recovers <= issued BU (per-token floor inversion) ---");
amount_in = 10^6 * FIX_ONE;

\\ Issue side: CEIL, no premium, on the on-peg sub-basket.
implied_min = FIX_MAX;
inv_rt3_step(i) = { my(qIssue, implied); qIssue = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amount_in, FIX_ONE, 0, CEIL_FLAG); implied = implied_BU(qIssue, ref_amts[i], ref_per_toks[i], decimals_tok[i]); if(implied < implied_min, implied_min = implied); printf("  %-5s  qIssue=%d  implied BU=%d (vs amount_in=%d)\n", basket_tokens[i], qIssue, implied, amount_in); }

\\ Restrict to the on-peg sub-basket so we test the no-premium path.
\\ FRAX/LUSD have premium > FIX_ONE, which inflates qIssue and so increases
\\ implied_BU above amount_in for those tokens — that's the *protocol's
\\ surplus*, not value extraction by the user.  We test those separately.
print("  -- on-peg sub-basket (no premium charged) --");
{ for(i = 1, 3, inv_rt3_step(i)); }
{ printf("  min implied BU over sub-basket = %d  (must be >= amount_in - 1 = %d  AND  <= amount_in = %d)\n", implied_min, amount_in - 1, amount_in); }
inv_rt3_lower = (implied_min >= amount_in - 1);
inv_rt3_upper = (implied_min <= amount_in);
{ printf("  lower bound (no extraction by rounding loss) ok: %s; upper bound (no value created) ok: %s\n", if(inv_rt3_lower, "yes", "no"), if(inv_rt3_upper, "yes", "no")); }

\\ Cross-check the under-peg leg: premium amplification means the protocol
\\ collects more tokens than 1.0 ref/BU, so implied_BU_FRAX > amount_in.
\\ That's the *intended* surplus — a guarantee on the protocol's side, not
\\ a violation of round-trip safety.
qIssue_FRAX = quote_one(ref_amts[4], ref_per_toks[4], decimals_tok[4], amount_in, prem_FRAX, 1, CEIL_FLAG);
implied_FRAX = implied_BU(qIssue_FRAX, ref_amts[4], ref_per_toks[4], decimals_tok[4]);
{ printf("  FRAX (premium %.6f): qIssue=%d -> implied BU=%d (surplus %d wei -- protocol-side, expected)\n", prem_FRAX * 1.0 / FIX_ONE, qIssue_FRAX, implied_FRAX, implied_FRAX - amount_in); }
inv_rt3_premium_consistent = (implied_FRAX > amount_in);

if(inv_rt3_lower && inv_rt3_upper && inv_rt3_premium_consistent, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RT4: Linearity scaling sweep — gap grows linearly in amount.
\\ ============================================================
print("--- INV-RT4: linearity gap scales linearly with amount ---");
\\ For USDC (clean stable, no premium), measure gap vs k * q(1 BU) at
\\ several scales.  If gap / k stays bounded, the rounding budget is
\\ linear (the desired behaviour).
sweep_amounts = [1, 2, 5, 10, 100, 10^6, 10^9];
q1_unit = quote_one(ref_amts[1], ref_per_toks[1], decimals_tok[1], FIX_ONE, FIX_ONE, 0, FLOOR_FLAG);
worst_per_BU_gap = 0;

inv_rt4_step(k) = { my(qk, gap, gap_per_BU); qk = quote_one(ref_amts[1], ref_per_toks[1], decimals_tok[1], k * FIX_ONE, FIX_ONE, 0, FLOOR_FLAG); gap = abs(qk - k * q1_unit); gap_per_BU = if(k > 0, gap * 1.0 / k, 0); if(gap_per_BU > worst_per_BU_gap, worst_per_BU_gap = gap_per_BU); printf("  k=%-12d  q(k*1BU)=%-30d  k*q(1BU)=%-30d  gap=%-12d  gap/k=%.6f wei/BU\n", k, qk, k * q1_unit, gap, gap_per_BU); }

{ for(ki = 1, #sweep_amounts, inv_rt4_step(sweep_amounts[ki])); }
{ printf("  worst gap-per-BU across the sweep: %.6f wei (must be << 1)\n", worst_per_BU_gap); }
\\ Linear bound: gap_per_BU <= 1 (one wei per BU is the theoretical FLOOR
\\ rounding budget).  In our calibration (clean ratio) it is ~0.
inv_rt4_ok = (worst_per_BU_gap <= 1);
if(inv_rt4_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RT5: quoteCustomRedemption single-nonce round trip.
\\ For portion=FIX_ONE on the current basket nonce, custom redemption
\\ should agree with quote(amount, FLOOR, applyPremium=false) per token.
\\ ============================================================
print("--- INV-RT5: quoteCustomRedemption agrees with quote(FLOOR) per-token ---");
viol_rt5 = 0;
amount_test = 10^6 * FIX_ONE;

inv_rt5_step(i) = { my(qCustom, qFloor, gap); qCustom = quote_custom_one(amount_test, ref_amts[i], ref_per_toks[i], decimals_tok[i]); qFloor = quote_one(ref_amts[i], ref_per_toks[i], decimals_tok[i], amount_test, FIX_ONE, 0, FLOOR_FLAG); gap = abs(qCustom - qFloor); if(gap > 1, viol_rt5 = viol_rt5 + 1); printf("  %-5s  custom=%d  floor=%d  gap=%d wei\n", basket_tokens[i], qCustom, qFloor, gap); }

for(i = 1, 5, inv_rt5_step(i));
{ printf("  custom-vs-floor disagreements above 1 wei: %d\n", viol_rt5); }
if(viol_rt5 == 0, print("  OK"), print("  FAIL"));
print("");

print("Done.");
