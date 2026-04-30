\\ draft_rate_evolution.gp
\\
\\ CAS-side validation of StRSR's [draftRate] under the production-
\\ faithful D18{qDrafts/qRSR} model. Whereas the prior simulation
\\ collapsed [draftRate = FIX_ONE] (eagerly era-resetting on any
\\ seizure that broke the implied rate), the simulation now tracks
\\ [draftRate] in storage and only era-resets when it would exceed
\\ [MAX_DRAFT_RATE]. This script probes the new behaviour.
\\
\\ Invariants checked:
\\   - Conservation:    draftRSR * draftRate >= totalDrafts * FIX_ONE
\\   - Range:           FIX_ONE <= draftRate <= MAX_DRAFT_RATE
\\   - Genesis:         beginDraftEra resets draftRate to FIX_ONE
\\   - Stake/unstake:   unstake leaves draftRate unchanged (CEIL on the
\\                      draft mint side); only seizeRSR moves draftRate.
\\   - Seizure:         after a proportional seize, draftRate is
\\                      ceil(totalDrafts * FIX_ONE / draftRSR') and
\\                      stays in [FIX_ONE, MAX_DRAFT_RATE] unless the
\\                      cap is crossed (then era reset fires).
\\
\\ Reference: protocol/contracts/p1/StRSR.sol#73-90 (draftRate, struct
\\ CumulativeDraft) and #L119-L123 (the [draft-rate] invariant).
\\
\\ Constants:
\\   FIX_ONE             = 1e18
\\   MAX_DRAFT_RATE      = 1e9 * FIX_ONE

print("=== StRSR draft_rate_evolution -- CAS validation ===");
print("");

FIX_ONE = 10^18;
MAX_DRAFT_RATE = 10^9 * FIX_ONE;

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ Per-entry draft amount produced by an unstake of rsrAmount qRSR
\\ at the current draftRate:
\\   drafts = ceil(rsrAmount * draftRate / FIX_ONE)
\\ This mirrors production's pushDraft logic at draftRate semantics
\\ (see StRSR.sol#L257 and Phase 1 of unstake).
draftsFromRSR(rsrAmount, draftRate) = ceil_div(rsrAmount * draftRate, FIX_ONE);

\\ rsrAmount paid out when popping `drafts` draft-tokens at the
\\ current draftRate:
\\   rsrPaid = drafts * FIX_ONE / draftRate (FLOOR)
\\ Mirrors production's withdraw arithmetic (StRSR.sol#L334).
rsrFromDrafts(drafts, draftRate) = (drafts * FIX_ONE) \ draftRate;

\\ Recompute draftRate after a seizure that updated draftRSR:
\\   draftRate' = ceil(totalDrafts * FIX_ONE / draftRSR')   when nonzero
\\   else FIX_ONE (era reset).
recomputeDraftRate(totalDrafts, draftRSR) = if(draftRSR == 0 || totalDrafts == 0, FIX_ONE, ceil_div(totalDrafts * FIX_ONE, draftRSR));

\\ Production-faithful seizure on the draft side (Phase 1 + Phase 2 cap test).
\\ Returns ["era-reset", post_draftRSR, post_totalDrafts, post_draftRate]
\\ or ["ok", post_draftRSR, post_totalDrafts, post_draftRate].
\\ Inputs: draftRSR_pre, totalDrafts_pre, rsrAmount, totalRSR_pre.
seize_draft_phase(draftRSR, totalDrafts, draftRate, rsrAmount, totalRSR) = { my(taken, newRSR, newRate); if(totalRSR == 0, return(["era-reset", 0, 0, FIX_ONE])); taken = ceil_div(draftRSR * rsrAmount, totalRSR); newRSR = draftRSR - taken; if(newRSR == 0 || totalDrafts == 0, return(["era-reset", 0, 0, FIX_ONE])); newRate = ceil_div(totalDrafts * FIX_ONE, newRSR); if(newRate > MAX_DRAFT_RATE, return(["era-reset", 0, 0, FIX_ONE])); ["ok", newRSR, totalDrafts, newRate]; }

report_invariant(draftRSR, draftRate, totalDrafts) = if(draftRSR * draftRate >= totalDrafts * FIX_ONE, print("  OK: draftRSR * draftRate >= totalDrafts * FIX_ONE"), print("  FAIL: invariant violated"));

report_range(draftRate) = if(FIX_ONE <= draftRate && draftRate <= MAX_DRAFT_RATE, print("  OK: FIX_ONE <= draftRate <= MAX_DRAFT_RATE"), report_range_fail(draftRate));
report_range_fail(rate) = printf("  FAIL: draftRate=%d (range [%d, %d])\n", rate, FIX_ONE, MAX_DRAFT_RATE);

\\ ---------- (1) Genesis state ----------
print("--- (1) Genesis state: draftRate = FIX_ONE, queue empty ---");
g_draftRSR    = 0;
g_totalDrafts = 0;
g_draftRate   = FIX_ONE;
{ printf("  draftRSR=%d, totalDrafts=%d, draftRate=%d\n", g_draftRSR, g_totalDrafts, g_draftRate); }
report_range(g_draftRate);
\\ Conservation degenerates with both sides zero.
if(g_draftRSR * g_draftRate >= g_totalDrafts * FIX_ONE, print("  OK: conservation holds at genesis"), print("  FAIL"));
print("");

\\ ---------- (2) Unstake leaves draftRate unchanged ----------
print("--- (2) Unstake on a draftRate=FIX_ONE pool leaves draftRate unchanged ---");
\\ Initial: draftRSR=0, totalDrafts=0, draftRate=FIX_ONE; unstake moves
\\ 1M qRSR into the draft pool.
u_rsrAmt = 10^6 * FIX_ONE;
u_drafts = draftsFromRSR(u_rsrAmt, g_draftRate);
u_draftRSR = g_draftRSR + u_rsrAmt;
u_totalDrafts = g_totalDrafts + u_drafts;
u_draftRate = g_draftRate;  \\ unchanged
{ printf("  unstake of rsrAmount=%d at draftRate=%d -> drafts=%d\n", u_rsrAmt, g_draftRate, u_drafts); }
{ printf("  post: draftRSR=%d, totalDrafts=%d, draftRate=%d\n", u_draftRSR, u_totalDrafts, u_draftRate); }
report_invariant(u_draftRSR, u_draftRate, u_totalDrafts);
report_range(u_draftRate);
if(u_drafts == u_rsrAmt, print("  OK: at FIX_ONE rate, drafts = rsrAmount"), print("  FAIL: drafts != rsrAmount at FIX_ONE"));
print("");

report_seize_3_ok(res, totalDrafts) = { my(post_RSR, post_drafts, post_rate); post_RSR = res[2]; post_drafts = res[3]; post_rate = res[4]; printf("  post: draftRSR=%d, totalDrafts=%d, draftRate=%d\n", post_RSR, post_drafts, post_rate); report_invariant(post_RSR, post_rate, post_drafts); report_range(post_rate); if(post_rate >= FIX_ONE, print("  OK: rate >= FIX_ONE post-seize (rate-up direction)"), print("  FAIL: rate dropped below FIX_ONE")); }

\\ ---------- (3) Mild seize keeps draftRate within bounds ----------
print("--- (3) Mild seize: draftRate stays in [FIX_ONE, MAX_DRAFT_RATE] ---");
\\ Setup: 100M stake-side RSR + 1M draft-side RSR (the post-(2) state).
\\ Seize 1% of the stake-side pool. The proportional split removes a
\\ small slice from the draft side too, but draftRate only grows
\\ slightly above FIX_ONE.
stakeRSR_3   = 10^8 * FIX_ONE;
totalRSR_3   = stakeRSR_3 + u_draftRSR;
seize_3      = totalRSR_3 \ 100;  \\ 1% of total
res_3 = seize_draft_phase(u_draftRSR, u_totalDrafts, u_draftRate, seize_3, totalRSR_3);
{ printf("  seize=%d on totalRSR=%d, result tag: %s\n", seize_3, totalRSR_3, res_3[1]); }
if(res_3[1] == "ok", report_seize_3_ok(res_3, u_totalDrafts), print("  FAIL: unexpected era reset"));
print("");

\\ ---------- (4) Heavy seize triggers era reset ----------
print("--- (4) Heavy seize: post-seize draftRate would exceed MAX_DRAFT_RATE ---");
\\ Push draftRSR to a tiny residual after seizing nearly the whole pool.
\\ With totalDrafts ~ FIX_ONE and draftRSR' = 1 wei, the implied rate
\\ would be ~ totalDrafts * FIX_ONE = 1e36, well above MAX_DRAFT_RATE = 1e27.
\\ Build the seize amount that leaves draftRSR' just below the threshold.
heavy_init_RSR    = u_draftRSR;
heavy_init_drafts = u_totalDrafts;
\\ MAX_DRAFT_RATE crossing: newRSR < ceil(totalDrafts * FIX_ONE / MAX_DRAFT_RATE)
\\                        = totalDrafts / 1e9 (since MAX_DRAFT_RATE = 1e9 * FIX_ONE).
heavy_threshold = ceil_div(heavy_init_drafts * FIX_ONE, MAX_DRAFT_RATE);
{ printf("  Era-reset boundary: draftRSR' < %d triggers reset\n", heavy_threshold); }
\\ Pick a seize amount that nearly empties the draft pool (leaves 1 wei).
heavy_total = stakeRSR_3 + heavy_init_RSR;
heavy_seize = ((heavy_init_RSR - 1) * heavy_total) \ heavy_init_RSR + 1;
res_4 = seize_draft_phase(heavy_init_RSR, heavy_init_drafts, u_draftRate, heavy_seize, heavy_total);
{ printf("  seize=%d, result tag: %s\n", heavy_seize, res_4[1]); }
if(res_4[1] == "era-reset", print("  OK: triggered era reset (rate would saturate)"), print("  FAIL: expected era reset"));
print("");

\\ ---------- (5) draftRate cannot drop below FIX_ONE under seizure ----------
print("--- (5) draftRate is non-decreasing under seizure (rate-up only) ---");
\\ After a seizure, totalDrafts is unchanged (the draft tokens don't
\\ vanish, only the RSR backing them shrinks); draftRSR can only
\\ shrink (or stay equal). Therefore the implied rate
\\   ceil(totalDrafts * FIX_ONE / draftRSR')
\\ can only INCREASE relative to ceil(totalDrafts * FIX_ONE / draftRSR).
\\ Probe several seize amounts and check the monotonicity.
init_RSR_5    = u_draftRSR;
init_drafts_5 = u_totalDrafts;
init_rate_5   = u_draftRate;
total_5       = stakeRSR_3 + init_RSR_5;

monotonicity_holds = 1;
for(pct = 1, 50, my(seize_amt, res, post_rate); seize_amt = total_5 * pct \ 1000; res = seize_draft_phase(init_RSR_5, init_drafts_5, init_rate_5, seize_amt, total_5); if(res[1] == "ok", post_rate = res[4]; if(post_rate < init_rate_5, monotonicity_holds = 0)));
if(monotonicity_holds, print("  OK: across 50 mild-seize probes, draftRate >= initial"), print("  FAIL: a seize lowered draftRate"));
print("");

\\ ---------- (6) Withdraw decrements draftRSR and totalDrafts proportionally ----------
print("--- (6) Withdraw: drafts pop -> rsrPaid; draftRate unchanged ---");
\\ From the (2) post-state, withdraw all the drafts in one go.
w_init_RSR    = u_draftRSR;
w_init_drafts = u_totalDrafts;
w_init_rate   = u_draftRate;
w_pop_drafts  = w_init_drafts;
w_rsrPaid     = rsrFromDrafts(w_pop_drafts, w_init_rate);
w_post_RSR    = w_init_RSR - w_rsrPaid;
w_post_drafts = w_init_drafts - w_pop_drafts;
w_post_rate   = w_init_rate;  \\ unchanged
{ printf("  Pop drafts=%d at draftRate=%d -> rsrPaid=%d\n", w_pop_drafts, w_init_rate, w_rsrPaid); }
{ printf("  post: draftRSR=%d, totalDrafts=%d, draftRate=%d\n", w_post_RSR, w_post_drafts, w_post_rate); }
if(w_post_RSR == 0 && w_post_drafts == 0, print("  OK: full withdraw drains pool exactly at FIX_ONE rate"), print("  FAIL: residual after full withdraw"));
report_range(w_post_rate);
print("");

print("Done.");
