\\ ctoken_refresh.gp
\\
\\ CAS-side validation of the CTokenFiatCollateral plugin overrides on
\\ top of the abstract Collateral state machine. Probes:
\\
\\   CT-1  refPerTok arithmetic for cUSDC (refDecimals = 6):
\\         underlyingRefPerTok = exchangeRateStored * 100.
\\   CT-2  refPerTok arithmetic for cDAI  (refDecimals = 18):
\\         underlyingRefPerTok = exchangeRateStored / 1e10.
\\   CT-3  refPerTok arithmetic at the boundary refDecimals = 8 (no shift).
\\   CT-4  Compound-style monotonic accrual: a strictly increasing rate
\\         drives exposedReferencePrice up without ever defaulting.
\\   CT-5  Manipulated accrueInterest: an artificially-jumped rate still
\\         only appreciates exposed (does NOT default the plugin). The
\\         attacker hurts themselves.
\\   CT-6  Rate decrease by 1 wei below the prior exposed: triggers
\\         hard default on the same refresh (boundary witness).
\\   CT-7  exchangeRateCurrent revert path (accrued=false): plugin
\\         marks DISABLED on the refresh.
\\   CT-8  After DISABLED via accrual revert, a subsequent refresh with
\\         accrued=true does NOT recover. DISABLED is terminal across
\\         the plugin override too.
\\
\\ References:
\\   protocol/contracts/plugins/assets/compoundv2/CTokenFiatCollateral.sol
\\     refresh()                  L44-63
\\     underlyingRefPerTok()      L66-70

print("=== CTokenFiatCollateral plugin overrides — CAS validation ===");
print("");

FIX_ONE     = 10^18;
FIX_MAX     = 2^192 - 1;
UINT48_MAX  = 2^48 - 1;
NEVER       = UINT48_MAX;

\\ ---- Calibration ----
delayUntilDefault = 86400;       \\ {s} 24h
revenueHiding     = 10^12;       \\ 1 ppm
revenueShowing    = FIX_ONE - revenueHiding;
defaultThreshold  = FIX_ONE / 20;
targetPerRef      = FIX_ONE;
peg_delta         = (targetPerRef * defaultThreshold) \ FIX_ONE;
pegBottom = targetPerRef - peg_delta;
pegTop    = targetPerRef + peg_delta;
t0 = 1700000000;

\\ ---- Status decoder ----
status_of(wd, now) = if(wd == NEVER, 0, if(wd > now, 1, 2));

\\ ---- markStatus per FiatCollateral.sol#L180-L199 ----
mark(wd, st, now, dud) = { my(sum); if(wd <= now, return(wd)); if(st == 0, return(NEVER)); if(st == 1, sum = now + dud; if(sum >= NEVER, return(NEVER)); if(sum < wd, return(sum)); return(wd)); if(st == 2, return(now)); wd; }

\\ ---- updateExposed per AppreciatingFiatCollateral.sol#L86-L96 ----
update_exposed(exposed, underlying, revShowing) = { my(hidden); hidden = (underlying * revShowing) \ FIX_ONE; if(underlying < exposed, return(["ok", underlying, 1])); if(hidden > exposed, return(["ok", hidden, 0])); ["ok", exposed, 0]; }

\\ ---- Plugin-specific refPerTok shift ----
\\ For refDecimals <= 8: rate * 10^(8 - refDecimals).
\\ For refDecimals  > 8: rate \ 10^(refDecimals - 8) (FLOOR).
ref_per_tok(rate, refDec) = if(refDec <= 8, rate * 10^(8 - refDec), rate \ 10^(refDec - 8));

\\ ---- Plugin refresh: composes parent refresh with the accrual catch ----
\\ State is [whenDefault, exposed]. Returns [whenDefault', exposed', defaulted_this_step].
ctoken_refresh(state, rate, refDec, pegPrice, low, now, accrued) = { my(wd, exposed, underlying, ue, exposed_after, wd_after_hard, soft, wd_after_soft, wd_final); wd = state[1]; exposed = state[2]; underlying = ref_per_tok(rate, refDec); ue = update_exposed(exposed, underlying, revenueShowing); exposed_after = ue[2]; wd_after_hard = if(ue[3] == 1, mark(wd, 2, now, delayUntilDefault), wd); soft = if(pegPrice < pegBottom || pegPrice > pegTop || low == 0, 1, 0); wd_after_soft = mark(wd_after_hard, soft, now, delayUntilDefault); wd_final = if(accrued, wd_after_soft, mark(wd_after_soft, 2, now, delayUntilDefault)); [wd_final, exposed_after, ue[3]]; }

\\ ---- CT-1: cUSDC arithmetic ----
print("--- CT-1: cUSDC refPerTok arithmetic (refDecimals=6, shift = +2) ---");
\\ Production cUSDC: exchangeRateStored ~= 2.2e23 -> refPerTok ~= 2.2e25 / 100 ?
\\ Actually for cUSDC: rate scale = 10^(6 + 10) = 10^16. After * 100 = 10^18 scale.
\\ Calibrate rate so that refPerTok = FIX_ONE * 1.05 (5% appreciation since launch).
expected_refPerTok = (FIX_ONE * 105) \ 100;  \\ 1.05e18
rate_cusdc = expected_refPerTok \ 100;       \\ 1.05e16
got_refPerTok = ref_per_tok(rate_cusdc, 6);
{ printf("  rate = %d (cUSDC scale)\n", rate_cusdc); }
{ printf("  refPerTok = %d  (expect %d)\n", got_refPerTok, expected_refPerTok); }
ct1_ok = (got_refPerTok == expected_refPerTok);
if(ct1_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-2: cDAI arithmetic ----
print("--- CT-2: cDAI refPerTok arithmetic (refDecimals=18, shift = -10) ---");
\\ For cDAI, rate scale = 10^(18 + 10) = 10^28. After / 10^10 = 10^18 scale.
expected_refPerTok2 = (FIX_ONE * 105) \ 100;
rate_cdai = expected_refPerTok2 * 10^10;
got_refPerTok2 = ref_per_tok(rate_cdai, 18);
{ printf("  rate = %d (cDAI scale)\n", rate_cdai); }
{ printf("  refPerTok = %d  (expect %d)\n", got_refPerTok2, expected_refPerTok2); }
ct2_ok = (got_refPerTok2 == expected_refPerTok2);
if(ct2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-3: refDecimals = 8 boundary (no shift) ----
print("--- CT-3: refPerTok at refDecimals = 8 (identity shift) ---");
rate_id = (FIX_ONE * 12) \ 10;
got_id = ref_per_tok(rate_id, 8);
{ printf("  rate = %d, refPerTok = %d (expect %d)\n", rate_id, got_id, rate_id); }
ct3_ok = (got_id == rate_id);
if(ct3_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-4: monotonic accrual drives exposed up, never defaults ----
print("--- CT-4: Compound monotonic accrual: refPerTok up, no default ---");
\\ Five consecutive blocks, rate increasing by 1% each step.
\\ Use cUSDC calibration. Initial state: SOUND, exposed=0.
state = [NEVER, 0];
rates = [10^16, (10^16 * 101) \ 100, (10^16 * 102) \ 100, (10^16 * 103) \ 100, (10^16 * 104) \ 100];
ct4_defs = 0;
ct4_prev_exp = 0;
ct4_violations = 0;
{
  for(i = 1, 5,
    res = ctoken_refresh(state, rates[i], 6, FIX_ONE, FIX_ONE \ 2, t0 + 13 * (i - 1), 1);
    state = [res[1], res[2]];
    ct4_defs = ct4_defs + res[3];
    if(state[2] < ct4_prev_exp, ct4_violations = ct4_violations + 1);
    ct4_prev_exp = state[2];
  );
}
{ printf("  After 5 monotone steps: exposed=%d, whenDefault=%d (NEVER=%d)\n", state[2], state[1], NEVER); }
{ printf("  Hard-defaults: %d (expect 0). Monotonicity violations: %d (expect 0).\n", ct4_defs, ct4_violations); }
ct4_ok = (ct4_defs == 0) && (ct4_violations == 0) && (state[1] == NEVER);
if(ct4_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-5: Manipulated accrueInterest: jumped rate just appreciates ----
print("--- CT-5: Artificial accrual jump appreciates without defaulting ---");
\\ Imagine an attacker manages to get exchangeRateStored to jump by 50% in
\\ a single block. The plugin can't tell the rate is artificial — it just
\\ appreciates exposed. No default.
state2 = [NEVER, ref_per_tok(10^16, 6)];  \\ start with exposed = 1.0
rate_jumped = (10^16 * 150) \ 100;       \\ 50% jump
res5 = ctoken_refresh(state2, rate_jumped, 6, FIX_ONE, FIX_ONE \ 2, t0, 1);
{ printf("  Pre exposed = %d\n", state2[2]); }
{ printf("  Post exposed = %d (expect strictly larger)\n", res5[2]); }
{ printf("  defaulted_this_step = %d (expect 0)\n", res5[3]); }
{ printf("  whenDefault = %d (expect NEVER = %d)\n", res5[1], NEVER); }
ct5_ok = (res5[2] > state2[2]) && (res5[3] == 0) && (res5[1] == NEVER);
if(ct5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-6: 1-wei rate decrease triggers hard default ----
print("--- CT-6: rate decrease (boundary): hard default ---");
\\ Calibrate: exposed = ref_per_tok(rate0, 6); then rate0 - 1 -> hard default.
rate0 = 10^16;
exposed0 = ref_per_tok(rate0, 6);
state3 = [NEVER, exposed0];
\\ underlying for rate0-1 is ref_per_tok(rate0-1, 6). For refDec=6, shift is *100,
\\ so any 1-unit decrease in rate -> 100-unit decrease in underlying. underlying < exposed.
res6 = ctoken_refresh(state3, rate0 - 1, 6, FIX_ONE, FIX_ONE \ 2, t0, 1);
{ printf("  Pre exposed = %d, post exposed = %d (expect strictly less)\n", exposed0, res6[2]); }
{ printf("  defaulted_this_step = %d (expect 1)\n", res6[3]); }
{ printf("  whenDefault = %d (status DISABLED iff <= now=%d)\n", res6[1], t0); }
{ printf("  status now: %d (expect 2 = DISABLED)\n", status_of(res6[1], t0)); }
ct6_ok = (res6[2] < exposed0) && (res6[3] == 1) && (status_of(res6[1], t0) == 2);
if(ct6_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-7: exchangeRateCurrent revert -> DISABLED ----
print("--- CT-7: accrual revert (accrued=false) -> DISABLED ---");
state4 = [NEVER, ref_per_tok(10^16, 6)];
res7 = ctoken_refresh(state4, 10^16, 6, FIX_ONE, FIX_ONE \ 2, t0, 0);
{ printf("  Pre status = SOUND. After accrual revert: whenDefault = %d\n", res7[1]); }
{ printf("  status now = %d (expect 2 = DISABLED)\n", status_of(res7[1], t0)); }
ct7_ok = (status_of(res7[1], t0) == 2);
if(ct7_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CT-8: DISABLED via accrual revert is terminal ----
print("--- CT-8: DISABLED via accrual revert is terminal under recovery ---");
state5 = [res7[1], res7[2]];   \\ start from CT-7's DISABLED post-state
\\ Now feed a "good" refresh with accrued=true and a strongly-appreciating rate.
res8 = ctoken_refresh(state5, (10^16 * 200) \ 100, 6, FIX_ONE, FIX_ONE \ 2, t0 + 100, 1);
{ printf("  After recovery attempt: whenDefault = %d (expect unchanged %d)\n", res8[1], state5[1]); }
{ printf("  status now = %d (expect 2 = DISABLED)\n", status_of(res8[1], t0 + 100)); }
ct8_ok = (res8[1] == state5[1]) && (status_of(res8[1], t0 + 100) == 2);
if(ct8_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- Summary ----
print("--- Summary: CTokenFiatCollateral plugin overrides ---");
print("  refPerTok(rate, refDecimals) is purely a base-10 shift that scales");
print("  the cToken's exchangeRateStored() to a {ref/tok} FIX_ONE-scale value.");
print("  refresh() is the parent refresh composed with a DISABLED branch on");
print("  exchangeRateCurrent() revert. Hard default on a rate decrease is");
print("  inherited from the parent's updateExposed; the only plugin-specific");
print("  default trigger is the accrual revert path.");
print("");
print("Done.");
