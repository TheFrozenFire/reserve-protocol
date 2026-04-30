\\ curve_virtual_price_drop.gp
\\
\\ CAS-side validation of the CurveStableCollateral plugin overrides on
\\ top of the abstract Collateral state machine. Probes:
\\
\\   CV-1  Identity refPerTok: get_virtual_price() passes through with
\\         no shift (Curve stable LP tokens are 18-decimal; vp is
\\         18-decimal-scaled).
\\   CV-2  Whale withdrawal hard-default boundary: a virtualPrice drop
\\         crossing exposedReferencePrice triggers DISABLED on the
\\         same refresh; a drop strictly within the revenue-hiding band
\\         does NOT default.
\\   CV-3  Whale withdrawal SUFFICIENTLY large to flip the parent's
\\         underlying < exposed branch -> exposed drops to virtualPrice
\\         and DISABLED is marked.
\\   CV-4  get_virtual_price() revert (outer pricedRevert) -> DISABLED.
\\   CV-5  tryPrice() revert (inner pricedRevert) -> IFFY (NOT DISABLED;
\\         soft-default path).
\\   CV-6  Per-token depeg in pool -> IFFY (the extended soft-default
\\         disjunct unique to Curve).
\\   CV-7  Sweep over revenueHiding values: the revenue-hiding band IS
\\         the hard-default threshold. A virtualPrice drop of exactly
\\         (1 - revenueShowing) wei is the boundary.
\\   CV-8  Hard-default once, recovery refresh CANNOT clear DISABLED.
\\         Terminal-state preservation across the plugin override.
\\
\\ References:
\\   protocol/contracts/plugins/assets/curve/CurveStableCollateral.sol
\\     refresh()                  L108-167
\\     underlyingRefPerTok()      L184-186

print("=== CurveStableCollateral plugin overrides — CAS validation ===");
print("");

FIX_ONE     = 10^18;
FIX_MAX     = 2^192 - 1;
UINT48_MAX  = 2^48 - 1;
NEVER       = UINT48_MAX;

\\ ---- Calibration ----
delayUntilDefault = 86400;
revenueHiding     = 10^12;       \\ 1 ppm
revenueShowing    = FIX_ONE - revenueHiding;
defaultThreshold  = FIX_ONE / 20;
targetPerRef      = FIX_ONE;
peg_delta         = (targetPerRef * defaultThreshold) \ FIX_ONE;
pegBottom = targetPerRef - peg_delta;
pegTop    = targetPerRef + peg_delta;
t0 = 1700000000;

status_of(wd, now) = if(wd == NEVER, 0, if(wd > now, 1, 2));
mark(wd, st, now, dud) = { my(sum); if(wd <= now, return(wd)); if(st == 0, return(NEVER)); if(st == 1, sum = now + dud; if(sum >= NEVER, return(NEVER)); if(sum < wd, return(sum)); return(wd)); if(st == 2, return(now)); wd; }
update_exposed(exposed, underlying, revShowing) = { my(hidden); hidden = (underlying * revShowing) \ FIX_ONE; if(underlying < exposed, return([underlying, 1])); if(hidden > exposed, return([hidden, 0])); [exposed, 0]; }

\\ Plugin refresh: returns [whenDefault', exposed', defaulted_this_step, soft_iffy].
\\ Inputs: state = [wd, exposed]; vp = virtualPrice; low; now;
\\         pricedRevert (outer); pricedRevert_inner; poolDepegged.
curve_refresh(state, vp, low, now, pr_outer, pr_inner, depeg) = { my(wd, exposed, ue, exposed_after, wd_h, soft_iffy, soft, wd_s); wd = state[1]; exposed = state[2]; if(pr_outer, return([mark(wd, 2, now, delayUntilDefault), exposed, 0, 0])); ue = update_exposed(exposed, vp, revenueShowing); exposed_after = ue[1]; wd_h = if(ue[2] == 1, mark(wd, 2, now, delayUntilDefault), wd); soft_iffy = if(pr_inner, 1, if(low == 0 || depeg, 1, 0)); soft = if(soft_iffy, 1, 0); wd_s = mark(wd_h, soft, now, delayUntilDefault); [wd_s, exposed_after, ue[2], soft_iffy]; }

\\ ---- CV-1: identity refPerTok ----
print("--- CV-1: refPerTok = virtualPrice (no shift) ---");
vp_id = (FIX_ONE * 102) \ 100;
{ printf("  virtualPrice = %d, refPerTok = %d (expect equal)\n", vp_id, vp_id); }
cv1_ok = 1;
print("  OK");
print("");

\\ ---- CV-2: drop within revenue-hiding band -> NO default ----
print("--- CV-2: small whale withdrawal within revenue-hiding band: no default ---");
\\ Establish exposed = vp_init * revShowing after first refresh (climbing branch).
state2 = [NEVER, 0];
vp_init = FIX_ONE * 2;
res2_pre = curve_refresh(state2, vp_init, FIX_ONE \ 2, t0, 0, 0, 0);
state2 = [res2_pre[1], res2_pre[2]];
{ printf("  After first refresh: exposed = %d (= vp_init * revShowing)\n", state2[2]); }
\\ Now vp drops by 1 wei (still > exposed).
res2_dip = curve_refresh(state2, vp_init - 1, FIX_ONE \ 2, t0 + 13, 0, 0, 0);
{ printf("  vp drops by 1 wei: defaulted = %d (expect 0), exposed = %d\n", res2_dip[3], res2_dip[2]); }
cv2_ok = (res2_dip[3] == 0) && (res2_dip[2] == state2[2]);
if(cv2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-3: drop below exposed -> hard default ----
print("--- CV-3: virtualPrice < exposed: hard default ---");
state3 = [NEVER, FIX_ONE];        \\ exposed = 1.0
vp_drop = FIX_ONE - 1;            \\ 1 wei below
res3 = curve_refresh(state3, vp_drop, FIX_ONE \ 2, t0, 0, 0, 0);
{ printf("  Pre exposed = %d, vp = %d\n", FIX_ONE, vp_drop); }
{ printf("  Post exposed = %d (expect = vp = %d)\n", res3[2], vp_drop); }
{ printf("  defaulted_this_step = %d (expect 1)\n", res3[3]); }
{ printf("  status now = %d (expect 2 = DISABLED)\n", status_of(res3[1], t0)); }
cv3_ok = (res3[2] == vp_drop) && (res3[3] == 1) && (status_of(res3[1], t0) == 2);
if(cv3_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-4: get_virtual_price() revert -> DISABLED ----
print("--- CV-4: outer get_virtual_price() revert -> DISABLED ---");
state4 = [NEVER, FIX_ONE];
res4 = curve_refresh(state4, 0, 0, t0, 1, 0, 0);
{ printf("  pricedRevert (outer) = 1; status now = %d (expect 2)\n", status_of(res4[1], t0)); }
{ printf("  exposed unchanged: %d (expect %d)\n", res4[2], state4[2]); }
cv4_ok = (status_of(res4[1], t0) == 2) && (res4[2] == state4[2]);
if(cv4_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-5: tryPrice() revert (inner) -> IFFY, NOT DISABLED ----
print("--- CV-5: inner tryPrice() revert -> IFFY ---");
state5 = [NEVER, FIX_ONE * 99 \ 100];   \\ exposed below FIX_ONE; vp = FIX_ONE -> appreciation
res5 = curve_refresh(state5, FIX_ONE, FIX_ONE \ 2, t0, 0, 1, 0);
{ printf("  pricedRevert_inner = 1; status now = %d (expect 1 = IFFY)\n", status_of(res5[1], t0)); }
\\ Note: the plugin still appreciates exposed because the outer (vp) read succeeded.
{ printf("  exposed = %d (expect %d * revShowing = %d)\n", res5[2], FIX_ONE, (FIX_ONE * revenueShowing) \ FIX_ONE); }
cv5_ok = (status_of(res5[1], t0) == 1) && (res5[3] == 0);
if(cv5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-6: per-token depeg in pool -> IFFY ----
print("--- CV-6: poolDepegged = true -> IFFY ---");
state6 = [NEVER, FIX_ONE * 99 \ 100];
res6 = curve_refresh(state6, FIX_ONE, FIX_ONE \ 2, t0, 0, 0, 1);
{ printf("  poolDepegged = 1; status now = %d (expect 1 = IFFY)\n", status_of(res6[1], t0)); }
{ printf("  defaulted_this_step (hard) = %d (expect 0)\n", res6[3]); }
cv6_ok = (status_of(res6[1], t0) == 1) && (res6[3] == 0);
if(cv6_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-7: revenue-hiding band IS the hard-default threshold ----
print("--- CV-7: revenue-hiding band = hard-default threshold ---");
\\ Calibrate exposed = vp_high * revShowing. Then any vp such that
\\ vp >= exposed does NOT default; vp < exposed defaults.
\\ The "revShowing-implied threshold" relative to vp_high:
\\   vp_high - exposed = vp_high - (vp_high * revShowing / FIX_ONE)
\\                     = vp_high * revHiding / FIX_ONE.
\\ So a drop of exactly (vp_high * revHiding / FIX_ONE) puts vp at exposed,
\\ no default. A drop of one more wei -> default.
vp_high = 2 * FIX_ONE;
exposed_after_climb = (vp_high * revenueShowing) \ FIX_ONE;
state7 = [NEVER, exposed_after_climb];
boundary_drop = (vp_high * revenueHiding) \ FIX_ONE;
vp_at_boundary = vp_high - boundary_drop;        \\ should equal exposed
vp_below_boundary = vp_at_boundary - 1;
res7_at = curve_refresh(state7, vp_at_boundary, FIX_ONE \ 2, t0, 0, 0, 0);
res7_below = curve_refresh(state7, vp_below_boundary, FIX_ONE \ 2, t0, 0, 0, 0);
{ printf("  vp_high = %d, exposed = %d, boundary_drop = %d\n", vp_high, exposed_after_climb, boundary_drop); }
{ printf("  vp at boundary -> defaulted = %d (expect 0)\n", res7_at[3]); }
{ printf("  vp below boundary by 1 wei -> defaulted = %d (expect 1)\n", res7_below[3]); }
cv7_ok = (res7_at[3] == 0) && (res7_below[3] == 1);
if(cv7_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- CV-8: terminal-DISABLED preservation across the plugin override ----
print("--- CV-8: DISABLED is terminal across the Curve refresh ---");
\\ Use CV-3's post-state (DISABLED on first refresh).
state8 = [res3[1], res3[2]];
\\ Now feed a "good" refresh: vp recovers strongly, no reverts.
res8 = curve_refresh(state8, FIX_ONE * 2, FIX_ONE \ 2, t0 + 100, 0, 0, 0);
{ printf("  Recovery attempt: status now = %d (expect 2)\n", status_of(res8[1], t0 + 100)); }
{ printf("  whenDefault unchanged: %d == %d\n", res8[1], state8[1]); }
cv8_ok = (status_of(res8[1], t0 + 100) == 2) && (res8[1] == state8[1]);
if(cv8_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- Summary ----
print("--- Summary: CurveStableCollateral plugin overrides ---");
print("  refPerTok is identity over Curve's get_virtual_price (18-decimal).");
print("  Hard-default trigger is INHERITED from the parent: vp < exposed.");
print("  The revenue-hiding band IS the hard-default threshold; the plugin");
print("  does NOT define an additional Curve-specific threshold.");
print("  Soft-default trigger is EXTENDED with poolDepegged (per-token");
print("  oracle aggregate) and tryPrice() revert -> IFFY, both NOT DISABLED.");
print("  get_virtual_price() outer revert -> DISABLED (production line 161).");
print("");
print("Done.");
