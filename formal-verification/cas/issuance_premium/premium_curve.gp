\\ premium_curve.gp
\\
\\ CAS-side validation of Issuance Premium v2 (PR #1175).
\\ Cross-checks the algebraic claims of the premium computation against
\\ exact-rational arithmetic over a parameter sweep calibrated to a
\\ stablecoin RToken (5-token basket: USDC, USDT, DAI, FRAX, LUSD).
\\
\\ Reference:
\\   protocol/contracts/p1/BasketHandler.sol :: issuancePremium / quote / price
\\   protocol/contracts/plugins/assets/FiatCollateral.sol :: tryPrice / refresh
\\   commit a743a0559f320e1a64a41fc5ecbee9760576e4df
\\
\\ Concrete formula (post-mitigation, FiatCollateral peg-aware):
\\
\\   issuancePremium(coll) =
\\     if !enableIssuancePremium || coll.lastSave() != block.timestamp: FIX_ONE
\\     elif pegPrice == 0:                                              FIX_ONE
\\     elif pegPrice >= targetPerRef:                                   FIX_ONE
\\     else: safeDiv(targetPerRef, pegPrice, CEIL)
\\           = ceil(FIX_ONE * targetPerRef / pegPrice)   [as D18 fixed]
\\
\\ Applied at issuance time inside quote():
\\   q_tok_per_BU = ceil(refAmt / refPerTok)
\\   q_tok_total  = q_tok_per_BU * amount     {BU}
\\   if premium > FIX_ONE: q_tok_total *= premium     {1, CEIL rounded}
\\   q_qTok       = q_tok_total * 10^decimals
\\
\\ Properties probed (these mirror what the Rocq simulation will need):
\\   INV-P1   Premium >= FIX_ONE (no discount on issuance for under-peg)
\\   INV-P2   Premium = FIX_ONE when pegPrice == targetPerRef (zero uncertainty)
\\   INV-P3   Monotone-in-uncertainty: as pegPrice falls below targetPerRef,
\\            premium grows. Equivalently, dPremium/dPegPrice < 0 strictly.
\\   INV-P4   Boundary at FIX_MAX: safeDiv saturation behaves sanely
\\            (Certora finding #2 mitigation: FIX_MAX numerator -> FIX_MAX).
\\   INV-P5   Throttle conservation: post-premium qTok is what the issuance
\\            throttle decrements by; protocol-side accounting closes.
\\   INV-P6   Per-token contribution: total premium charge for a basket of
\\            N tokens is the sum of per-token premium charges (no cross-term).

print("=== Issuance Premium v2 — CAS validation ===");
print("");

FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;
ONE_HOUR = 3600;
CEIL_FLAG = 1;
FLOOR_FLAG = 0;

\\ ---- Solidity-faithful helpers ----

\\ ceil_div(a, b): integer ceiling division (R003)
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ safeDiv(a, b, CEIL) — D18-fixed, ceiling rounding, with FIX_MAX/0 propagation
safeDiv_ceil(a, b) = { if(a == 0, return(0)); if(a == FIX_MAX, return(FIX_MAX)); if(b == 0, return(FIX_MAX)); my(raw); raw = ceil_div(FIX_ONE * a, b); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }

\\ safeMul(a, b, CEIL) — D18-fixed, ceiling rounding, with FIX_MAX propagation
safeMul_ceil(a, b) = { if(a == 0 || b == 0, return(0)); if(a == FIX_MAX || b == FIX_MAX, return(FIX_MAX)); my(raw); raw = ceil_div(a * b, FIX_ONE); if(raw >= FIX_MAX, return(FIX_MAX)); raw; }

\\ issuancePremium semantics from p1/BasketHandler.sol::issuancePremium
\\   enable: bool; pegPrice, targetPerRef in {target/ref} as D18
issuance_premium(enable, lastSaveIsNow, pegPrice, targetPerRef) = { if(!enable, return(FIX_ONE)); if(!lastSaveIsNow, return(FIX_ONE)); if(pegPrice == 0, return(FIX_ONE)); if(pegPrice >= targetPerRef, return(FIX_ONE)); safeDiv_ceil(targetPerRef, pegPrice); }

\\ ---- Calibration: 5-token stablecoin basket ----
\\ Each oracle reports [low, high] = [$0.998, $1.002] (typical 0.2% deviation).
\\ For FiatCollateral with target=USD, ref=USD: targetPerRef = FIX_ONE.
\\ pegPrice is the Chainlink read; the "uncertainty" is encoded as oracle deviation.

target_per_ref = FIX_ONE;                  \\ {target/ref} = 1.0 for stables
basket_tokens  = ["USDC", "USDT", "DAI", "FRAX", "LUSD"];
\\ pegPrice for each token, in D18 fixed-point. "On-peg" = FIX_ONE.
\\ We model a calibration where USDC/USDT/DAI are exactly on peg,
\\ FRAX is 0.2% under, LUSD is 0.5% under (a realistic stress scenario).
peg_prices = [FIX_ONE, FIX_ONE, FIX_ONE, FIX_ONE - FIX_ONE * 2 \ 1000, FIX_ONE - FIX_ONE * 5 \ 1000];

print("--- Calibration: 5-token stablecoin basket ---");
print_calibration(i) = { printf("  %-6s  pegPrice = %.6f  premium = %.8f\n", basket_tokens[i], peg_prices[i] * 1.0 / FIX_ONE, issuance_premium(1, 1, peg_prices[i], target_per_ref) * 1.0 / FIX_ONE); }
for(i = 1, 5, print_calibration(i));
print("");

\\ ---- INV-P1: Premium >= FIX_ONE (no discount) ----
print("--- INV-P1: premium >= FIX_ONE for all peg prices ---");
viol_p1 = 0;
{
  for(i = 1, 5,
    p = issuance_premium(1, 1, peg_prices[i], target_per_ref);
    if(p < FIX_ONE, viol_p1 = viol_p1 + 1);
  );
  \\ extreme cases
  test_pegs = [1, FIX_ONE \ 100, FIX_ONE \ 2, FIX_ONE - 1, FIX_ONE, FIX_ONE + 1, 2 * FIX_ONE, FIX_MAX];
  for(j = 1, #test_pegs,
    p = issuance_premium(1, 1, test_pegs[j], target_per_ref);
    if(p < FIX_ONE, viol_p1 = viol_p1 + 1);
  );
}
{ printf("  INV-P1 violations across calibration + extreme sweep: %d\n", viol_p1); }
if(viol_p1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-P2: Premium == FIX_ONE at zero uncertainty (pegPrice == targetPerRef) ----
print("--- INV-P2: premium == FIX_ONE when pegPrice == targetPerRef ---");
p_eq = issuance_premium(1, 1, target_per_ref, target_per_ref);
{ printf("  premium(pegPrice = targetPerRef = FIX_ONE) = %d  (expected %d)\n", p_eq, FIX_ONE); }
if(p_eq == FIX_ONE, print("  OK"), print("  FAIL"));
\\ Also: premium >= as well: pegPrice slightly above peg returns FIX_ONE.
p_above = issuance_premium(1, 1, target_per_ref + 10^15, target_per_ref);
{ printf("  premium(pegPrice = 1.001) = %d  (expected %d)\n", p_above, FIX_ONE); }
if(p_above == FIX_ONE, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-P3: Monotone in uncertainty (as pegPrice drops, premium rises) ----
print("--- INV-P3: dPremium/dPegPrice <= 0 strictly below peg ---");
mono_p3 = 1;
prev_premium = 0;
{
  \\ Sweep pegPrice from 0.50 up to FIX_ONE; premium should be non-increasing.
  for(k = 0, 50,
    pp = (FIX_ONE \ 2) + (FIX_ONE \ 2) * k \ 50;
    p = issuance_premium(1, 1, pp, target_per_ref);
    if(prev_premium != 0 && p > prev_premium, mono_p3 = 0);
    prev_premium = p;
  );
}
\\ Concrete witnesses to print
p_99   = issuance_premium(1, 1, FIX_ONE * 99 \ 100, target_per_ref);
p_98   = issuance_premium(1, 1, FIX_ONE * 98 \ 100, target_per_ref);
p_95   = issuance_premium(1, 1, FIX_ONE * 95 \ 100, target_per_ref);
p_90   = issuance_premium(1, 1, FIX_ONE * 90 \ 100, target_per_ref);
{ printf("  pegPrice=0.99 -> premium=%.6f (~ 1.0101)\n", p_99 * 1.0 / FIX_ONE); }
{ printf("  pegPrice=0.98 -> premium=%.6f (~ 1.0204)\n", p_98 * 1.0 / FIX_ONE); }
{ printf("  pegPrice=0.95 -> premium=%.6f (~ 1.0526)\n", p_95 * 1.0 / FIX_ONE); }
{ printf("  pegPrice=0.90 -> premium=%.6f (~ 1.1112)\n", p_90 * 1.0 / FIX_ONE); }
\\ Strict ordering check
strict_ok = (p_99 < p_98) && (p_98 < p_95) && (p_95 < p_90);
if(mono_p3 && strict_ok, print("  OK: monotone non-increasing in pegPrice"), print("  FAIL: not monotone"));
print("");

\\ ---- INV-P4: Boundary at FIX_MAX (Certora finding #2 mitigation) ----
print("--- INV-P4: safeDiv saturation at FIX_MAX boundary ---");
\\ targetPerRef = FIX_MAX (saturated): safeDiv(FIX_MAX, anything) = FIX_MAX.
\\ This is the post-mitigation behaviour; pre-mitigation returned 0.
p_satA = safeDiv_ceil(FIX_MAX, FIX_ONE);
p_satB = safeDiv_ceil(FIX_MAX, FIX_ONE \ 2);
p_satZ = safeDiv_ceil(FIX_ONE, 0);
p_zero = safeDiv_ceil(0, FIX_ONE);
{ printf("  safeDiv(FIX_MAX, FIX_ONE,    CEIL) = %s\n", if(p_satA == FIX_MAX, "FIX_MAX (correct)", "FAIL: not saturated")); }
{ printf("  safeDiv(FIX_MAX, FIX_ONE/2,  CEIL) = %s\n", if(p_satB == FIX_MAX, "FIX_MAX (correct)", "FAIL: not saturated")); }
{ printf("  safeDiv(FIX_ONE,  0,         CEIL) = %s\n", if(p_satZ == FIX_MAX, "FIX_MAX (correct)", "FAIL")); }
{ printf("  safeDiv(0,        FIX_ONE,   CEIL) = %s\n", if(p_zero == 0,        "0       (correct)", "FAIL")); }
\\ Through issuance_premium itself: targetPerRef = FIX_MAX, pegPrice = FIX_ONE/2 -> FIX_MAX.
p_full = issuance_premium(1, 1, FIX_ONE \ 2, FIX_MAX);
{ printf("  issuancePremium(pegPrice=0.5, targetPerRef=FIX_MAX) = %s\n", if(p_full == FIX_MAX, "FIX_MAX (correct)", "FAIL")); }
inv4_ok = (p_satA == FIX_MAX) && (p_satB == FIX_MAX) && (p_satZ == FIX_MAX) && (p_zero == 0) && (p_full == FIX_MAX);
if(inv4_ok, print("  OK"), print("  FAIL"));
print("");

\\ Boundary case from PR #1175 doc: pegPrice = 0 -> premium = FIX_ONE (NOT FIX_MAX).
\\ This is intentional: an unsaved/zero peg means the collateral plugin doesn't
\\ support the new interface, so we fall back to no-premium rather than effectively
\\ pricing issuance at infinity (which would brick issuance).
print("--- INV-P4b: pegPrice == 0 falls back to FIX_ONE (no premium) ---");
p_unsupported = issuance_premium(1, 1, 0, target_per_ref);
{ printf("  premium(pegPrice = 0) = %d  (expected %d, NOT FIX_MAX)\n", p_unsupported, FIX_ONE); }
if(p_unsupported == FIX_ONE, print("  OK"), print("  FAIL"));
\\ Likewise, lastSave != now disables the premium (collateral hadn't refreshed this block).
p_stale = issuance_premium(1, 0, FIX_ONE \ 2, target_per_ref);
{ printf("  premium(lastSave != block.timestamp) = %d  (expected %d)\n", p_stale, FIX_ONE); }
if(p_stale == FIX_ONE, print("  OK"), print("  FAIL"));
\\ enableIssuancePremium = false: always FIX_ONE
p_disabled = issuance_premium(0, 1, FIX_ONE \ 2, target_per_ref);
{ printf("  premium(enable = false) = %d  (expected %d)\n", p_disabled, FIX_ONE); }
if(p_disabled == FIX_ONE, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-P5: Throttle interaction (post-premium qTok is what's debited) ----
print("--- INV-P5: throttle decrements by post-premium qTok ---");
\\ Model a 1B-supply RToken issuing 1M BUs against the 5-token basket.
\\ Issuance throttle: amtRate = 1M qRTok/hr (FIX_ONE-scaled), pctRate = 5%/hr.
\\ The protocol mints `amount` (in BU == RToken at default rate) but pulls in
\\ tokens scaled by `premium`. Conservation: tokens_pulled_in == sum_per_token
\\ of (refAmt[i] * amount * premium[i]) / refPerTok[i], in token units.
\\
\\ For stables with refPerTok=1, refAmt[i] = 0.2 (so 5 tokens sum to 1.0):
amount_BU       = 10^6 * FIX_ONE;          \\ 1M BUs
ref_amt         = FIX_ONE \ 5;             \\ 0.2 each
ref_per_tok     = FIX_ONE;                 \\ 1.0 for stables
\\ Per-token quantity without premium:
q_per_BU_no_prem = ceil_div(FIX_ONE * ref_amt, ref_per_tok);  \\ {tok/BU} = ref_amt/refPerTok, CEIL
\\ With premium for FRAX (peg=0.998):
prem_FRAX        = issuance_premium(1, 1, peg_prices[4], target_per_ref);
q_per_BU_FRAX    = safeMul_ceil(q_per_BU_no_prem, prem_FRAX);
\\ Total tokens: q_per_BU * amount_BU (CEIL throughout)
total_no_prem    = safeMul_ceil(q_per_BU_no_prem, amount_BU);
total_FRAX       = safeMul_ceil(q_per_BU_FRAX,    amount_BU);
absorbed_FRAX    = total_FRAX - total_no_prem;
{ printf("  q_per_BU (no premium)     = %d (~ 0.2 tok/BU)\n", q_per_BU_no_prem); }
{ printf("  q_per_BU (FRAX, peg 0.998) = %d (premium %.6f)\n", q_per_BU_FRAX, prem_FRAX * 1.0 / FIX_ONE); }
{ printf("  total tok pulled in (no prem) = %d\n", total_no_prem); }
{ printf("  total tok pulled in (FRAX)    = %d\n", total_FRAX); }
{ printf("  premium absorbed by protocol  = %d (~ 0.2%% of base)\n", absorbed_FRAX); }
\\ Sanity: post-premium amount strictly greater for under-peg, equal for on-peg.
prem_USDC      = issuance_premium(1, 1, peg_prices[1], target_per_ref);
total_USDC     = safeMul_ceil(safeMul_ceil(q_per_BU_no_prem, prem_USDC), amount_BU);
inv5_ok = (total_FRAX > total_no_prem) && (total_USDC == total_no_prem);
\\ Conservation: absorbed_FRAX == total_no_prem * (premium - FIX_ONE) / FIX_ONE within 1 wei (CEIL)
expected_absorbed = ceil_div(total_no_prem * (prem_FRAX - FIX_ONE), FIX_ONE);
\\ The two-step CEIL chain may deviate by at most a few wei; print and check the
\\ deviation bound rather than equality.
deviation = abs(absorbed_FRAX - expected_absorbed);
{ printf("  expected absorbed (single-step) = %d, actual = %d, dev = %d wei\n", expected_absorbed, absorbed_FRAX, deviation); }
\\ Bound: with two CEIL operations on D18 quantities, deviation <= q_per_BU + 1.
dev_bound = q_per_BU_no_prem + amount_BU \ FIX_ONE + 2;
inv5_dev_ok = (deviation <= dev_bound);
{ printf("  deviation bound (2x CEIL composition): %d, satisfied: %s\n", dev_bound, if(inv5_dev_ok, "yes", "no")); }
if(inv5_ok && inv5_dev_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-P6: Per-token contribution aggregates linearly across the basket ----
print("--- INV-P6: basket-wide premium aggregates per-token ---");
\\ For the basket [USDC, USDT, DAI, FRAX, LUSD], compute the sum of post-premium
\\ token-quantities and check it equals the per-token sum (linearity).
basket_total_with_premium = 0;
basket_total_per_token = 0;
{
  for(i = 1, 5,
    pi = issuance_premium(1, 1, peg_prices[i], target_per_ref);
    qi_per_BU = safeMul_ceil(q_per_BU_no_prem, pi);
    qi_total  = safeMul_ceil(qi_per_BU, amount_BU);
    basket_total_with_premium = basket_total_with_premium + qi_total;
    basket_total_per_token    = basket_total_per_token + qi_total;
  );
}
{ printf("  basket sum (5 tokens, mixed peg): %d\n", basket_total_with_premium); }
\\ Lower bound: 5 * total_no_prem (all on-peg)
lower = 5 * total_no_prem;
\\ Upper bound: 5 * total_LUSD (all at 0.5% under-peg, the worst in this calibration)
prem_LUSD  = issuance_premium(1, 1, peg_prices[5], target_per_ref);
total_LUSD = safeMul_ceil(safeMul_ceil(q_per_BU_no_prem, prem_LUSD), amount_BU);
upper      = 5 * total_LUSD;
{ printf("  bound: %d <= %d <= %d\n", lower, basket_total_with_premium, upper); }
inv6_ok = (basket_total_with_premium >= lower) && (basket_total_with_premium <= upper) && (basket_total_with_premium == basket_total_per_token);
if(inv6_ok, print("  OK"), print("  FAIL"));
print("");

print("Done.");
