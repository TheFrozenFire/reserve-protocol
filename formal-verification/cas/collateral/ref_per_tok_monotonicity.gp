\\ ref_per_tok_monotonicity.gp
\\
\\ CAS-side validation of AppreciatingFiatCollateral.refresh()'s update rule
\\ for `exposedReferencePrice` (the value returned by refPerTok()).
\\
\\ Production logic, lines 86-96 of AppreciatingFiatCollateral.sol:
\\
\\   underlying = underlyingRefPerTok()                      {ref/tok}
\\   hidden     = underlying * revenueShowing                {ref/tok} * {1}
\\   if (underlying < exposedReferencePrice) {
\\       exposedReferencePrice = underlying;                 \\ DROP
\\       markStatus(DISABLED);                               \\ HARD DEFAULT
\\   } else if (hidden > exposedReferencePrice) {
\\       exposedReferencePrice = hidden;                     \\ APPRECIATE
\\   } \\ else: small drawdown within revenueHiding -> no change
\\
\\ Properties probed:
\\
\\   M-1  Sound path: exposedReferencePrice is non-decreasing across any
\\         finite sequence of refreshes that does not include a drop below
\\         the current exposed price.
\\   M-2  Hard default: any underlying refPerTok strictly below the current
\\         exposedReferencePrice triggers DISABLED on this refresh AND drops
\\         exposedReferencePrice to the new (lower) underlying value.
\\         (The drop and the DISABLED flag co-occur — they are inseparable.)
\\   M-3  Revenue-hiding band: drawdowns that keep `underlying` above
\\         `exposedReferencePrice` (which equals the previous high *
\\         revenueShowing) do NOT change exposed price and do NOT default.
\\   M-4  First-refresh boundary: with exposedReferencePrice = 0 (initial),
\\         any positive `underlying` appreciates without defaulting.
\\   M-5  Self-consistency at the cap: hidden == exposedReferencePrice
\\         (exact boundary) does not appreciate (strict `>`).
\\   M-6  Witness: the smallest `underlying` decrement (1 wei) below
\\         exposedReferencePrice triggers hard default.
\\   M-7  Sweep over (revenueHiding, drawdownPct, refreshCount) showing
\\         the monotone-up envelope is preserved.
\\
\\ References:
\\   protocol/contracts/plugins/assets/AppreciatingFiatCollateral.sol
\\     refresh()        L79-136
\\     refPerTok()      L139-141   returns exposedReferencePrice

print("=== AppreciatingFiatCollateral.refPerTok monotonicity — CAS validation ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;

\\ Aave V3 USDC-style calibration: revenueHiding = 1e-6, refPerTok starts ~1.0
\\ and grows ~5%/year via supply index appreciation.
revenueHiding = 10^12;             \\ 1e-6 in FIX (1 ppm)
revenueShowing = FIX_ONE - revenueHiding;

\\ ---- Solidity-faithful refresh-update for exposedReferencePrice ----
\\ Returns ["state", new_exposed, defaulted_this_step].
\\   defaulted = 1 iff underlying < exposed (hard default branch).
update_exposed(exposed, underlying, revShowing) = { my(hidden, defaulted, new_exposed); hidden = (underlying * revShowing) \ FIX_ONE; if(underlying < exposed, return(["ok", underlying, 1])); if(hidden > exposed, return(["ok", hidden, 0])); ["ok", exposed, 0]; }

\\ ---- M-1: monotone non-decreasing under sound updates ----
print("--- M-1: refPerTok non-decreasing across sound refreshes ---");
\\ Simulate underlying that grows monotonically, applies revenue-hiding,
\\ check refPerTok output is itself monotone non-decreasing.
mono_violations = 0;
exposed = 0;
prev_exposed = 0;
{
  \\ underlying values at +0%, +0.5%, +1%, +5%, +10%, +20% growth.
  underlyings = [FIX_ONE, FIX_ONE + FIX_ONE \ 200, FIX_ONE + FIX_ONE \ 100, (FIX_ONE * 105) \ 100, (FIX_ONE * 110) \ 100, (FIX_ONE * 120) \ 100];
  for(i = 1, 6,
    u = underlyings[i];
    res = update_exposed(exposed, u, revenueShowing);
    exposed = res[2];
    if(res[3] == 1, mono_violations = mono_violations + 1);
    if(exposed < prev_exposed, mono_violations = mono_violations + 1);
    prev_exposed = exposed;
  );
}
{ printf("  Final exposedReferencePrice after 6 sound updates: %d\n", exposed); }
{ printf("  Monotonicity violations: %d\n", mono_violations); }
if(mono_violations == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-2: hard default lowers exposed and flags DISABLED ----
print("--- M-2: underlying < exposed -> DISABLED + exposed drops ---");
\\ Start at a sound state where exposed = 1e18 (after some appreciation).
exposed_pre = FIX_ONE;
underlying_drop = FIX_ONE - 10^15;  \\ 0.1% drop
res = update_exposed(exposed_pre, underlying_drop, revenueShowing);
{ printf("  exposed_pre = %d\n", exposed_pre); }
{ printf("  underlying  = %d (0.1%% drop)\n", underlying_drop); }
{ printf("  new exposed = %d (expect = underlying)\n", res[2]); }
{ printf("  defaulted   = %d (expect 1)\n", res[3]); }
m2_ok = (res[2] == underlying_drop) && (res[3] == 1);
if(m2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-3: revenue-hiding absorbs small drawdowns ----
print("--- M-3: drawdowns within revenueHiding band do not default ---");
\\ Simulate the canonical case: an appreciation cycle establishes
\\ exposed = u_high * revenueShowing, then underlying dips back to a
\\ value still above exposed. No default; no exposed change.
exposed_init = 0;
u_high = FIX_ONE * 2;            \\ underlying climbs to 2.0
res1 = update_exposed(exposed_init, u_high, revenueShowing);
exposed_after_climb = res1[2];
\\ Tiny drawdown: underlying drops by 0.5 ppm (still > exposed_after_climb).
u_dip = u_high - (u_high \ 2000000);
res2 = update_exposed(exposed_after_climb, u_dip, revenueShowing);
\\ Larger drawdown: 0.99 ppm (still strictly above the hidden band edge).
u_dip2 = u_high - (u_high * 99) \ 100000000;
res3 = update_exposed(exposed_after_climb, u_dip2, revenueShowing);
{ printf("  After climb to u=%d:           exposed = %d\n", u_high, exposed_after_climb); }
{ printf("  exposed = u_high * revShowing = %d\n", (u_high * revenueShowing) \ FIX_ONE); }
{ printf("  Dip to %d (0.5 ppm): defaulted = %d (expect 0)\n", u_dip, res2[3]); }
{ printf("  Dip to %d (0.99 ppm): defaulted = %d (expect 0)\n", u_dip2, res3[3]); }
m3_ok = (res2[3] == 0) && (res3[3] == 0) && (res2[2] == exposed_after_climb) && (res3[2] == exposed_after_climb);
if(m3_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-4: first-refresh boundary (exposed == 0) ----
print("--- M-4: first refresh from exposed = 0 always appreciates ---");
\\ Constructor leaves exposedReferencePrice = 0 (storage default).
\\ The first refresh should bump it to underlying * revenueShowing without
\\ defaulting, regardless of underlying value.
res_a = update_exposed(0, FIX_ONE, revenueShowing);
res_b = update_exposed(0, FIX_ONE * 5, revenueShowing);
res_c = update_exposed(0, 1, revenueShowing);
{ printf("  exposed=0, u=1.0     : new=%d, defaulted=%d\n", res_a[2], res_a[3]); }
{ printf("  exposed=0, u=5.0     : new=%d, defaulted=%d\n", res_b[2], res_b[3]); }
{ printf("  exposed=0, u=1 wei   : new=%d, defaulted=%d\n", res_c[2], res_c[3]); }
\\ Note: u=1 wei makes hidden = 0 (u * revShowing < FIX_ONE), so the
\\ `hidden > exposed` branch fails (0 > 0 is false). exposed stays 0.
\\ This is the contract behaviour, not a bug. underlying < exposed is
\\ also false (1 < 0 is false). So no default, no change. Verify.
m4_ok = (res_a[3] == 0) && (res_b[3] == 0) && (res_c[3] == 0);
m4_ok = m4_ok && (res_a[2] > 0) && (res_b[2] > 0);
if(m4_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-5: hidden == exposed boundary ----
print("--- M-5: hidden == exposed does NOT appreciate (strict >) ---");
\\ Construct an exposed where hidden(u) == exposed exactly. The contract
\\ uses `hiddenReferencePrice > exposedReferencePrice` (strict). Verify
\\ that a u producing equality leaves exposed unchanged.
u_calib = FIX_ONE * 2;
exposed_calib = (u_calib * revenueShowing) \ FIX_ONE;
res_eq = update_exposed(exposed_calib, u_calib, revenueShowing);
\\ One-wei increase in underlying *might* still floor to the same hidden
\\ (revenueShowing < FIX_ONE so a 1-wei step in u may not move hidden).
res_up1 = update_exposed(exposed_calib, u_calib + 1, revenueShowing);
{ printf("  u = 2.0, exposed = hidden = %d\n", exposed_calib); }
{ printf("  Re-refresh same u:    new exposed = %d (expect unchanged)\n", res_eq[2]); }
{ printf("  u + 1 wei:            new exposed = %d (may not change due to floor)\n", res_up1[2]); }
m5_ok = (res_eq[2] == exposed_calib) && (res_eq[3] == 0);
if(m5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-6: 1-wei drop below exposed triggers hard default ----
print("--- M-6: minimal hard-default witness ---");
\\ The smallest possible underlying decrement that triggers the DISABLED
\\ branch: underlying = exposed - 1.
exposed_w = FIX_ONE;             \\ 1.0
underlying_w = exposed_w - 1;
res_w = update_exposed(exposed_w, underlying_w, revenueShowing);
{ printf("  exposed = %d, underlying = exposed - 1 = %d\n", exposed_w, underlying_w); }
{ printf("  defaulted = %d (expect 1), new exposed = %d (expect %d)\n", res_w[3], res_w[2], underlying_w); }
m6_ok = (res_w[3] == 1) && (res_w[2] == underlying_w);
if(m6_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- M-7: parameter sweep ----
print("--- M-7: parameter sweep — monotone-up envelope across (revHiding, sequence) ---");
\\ For each (revenueHiding, underlying-sequence), run the sequence and
\\ verify exposed never decreases except on a default-flagged step.
\\ revenueHiding values: 0 (no hiding), 1 ppm, 1e-4, 1e-3.
do_sweep_one(rh, useq) = { my(rs, exp_, prev_, viol, def_count); rs = FIX_ONE - rh; exp_ = 0; prev_ = 0; viol = 0; def_count = 0; for(i = 1, length(useq), my(r); r = update_exposed(exp_, useq[i], rs); if(r[3] == 1, def_count = def_count + 1, if(r[2] < prev_, viol = viol + 1)); exp_ = r[2]; prev_ = exp_); [viol, def_count]; }

sweep_total_viol = 0;
sweep_total_def  = 0;
{
  rhs = [0, 10^12, 10^14, 10^15];
  \\ Strictly increasing underlying sequence: monotone-up, no defaults.
  useq_up = [FIX_ONE, FIX_ONE + 10^15, FIX_ONE + 10^16, FIX_ONE + 5*10^16, FIX_ONE + 10^17];
  for(j = 1, 4,
    rh = rhs[j];
    r = do_sweep_one(rh, useq_up);
    sweep_total_viol = sweep_total_viol + r[1];
    sweep_total_def  = sweep_total_def  + r[2];
  );
}
{ printf("  Increasing-u sweep: violations = %d, defaults = %d (expect 0, 0)\n", sweep_total_viol, sweep_total_def); }

\\ A dipping sequence: each dip below current exposed should default exactly once.
sweep_dip_def = 0;
{
  useq_dip = [FIX_ONE, FIX_ONE + 10^16, FIX_ONE + 5*10^15, FIX_ONE + 10^16];
  \\ With revenueHiding = 0, exposed = u after climb. Dip from 1.01 to 1.005
  \\ is a 5e15 wei drop -> hard default.
  r = do_sweep_one(0, useq_dip);
  sweep_dip_def = r[2];
}
{ printf("  Dipping-u sweep with rh=0: defaults = %d (expect 1)\n", sweep_dip_def); }
m7_ok = (sweep_total_viol == 0) && (sweep_total_def == 0) && (sweep_dip_def == 1);
if(m7_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- Summary ----
print("--- Summary: refPerTok monotonicity is conditional ---");
print("  Across all sweeps, exposedReferencePrice is non-decreasing whenever");
print("  the underlying stays >= exposed. Any single refresh observing");
print("  underlying < exposed simultaneously DISABLES the collateral and drops");
print("  exposed to the new lower underlying. This is the contract's");
print("  declared invariant: refPerTok is monotone-up modulo hard default.");
print("");

print("Done.");
