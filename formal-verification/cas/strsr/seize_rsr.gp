\\ seize_rsr.gp
\\
\\ CAS-side validation of StRSR's [seizeRSR] operation. Standalone
\\ companion to [exchange_rate_evolution.gp] (covers seizeRSR on the
\\ stake side only) and [withdrawal_queue.gp] (covers the draft side).
\\ This script unifies both pools and probes the production-faithful
\\ proportional-split semantics including era-reset triggers.
\\
\\ Probes:
\\   (1) Small seizure (no era reset). 1% of total RSR seized
\\       proportionally; verify totalRSR drops by exactly seized,
\\       split between stakeRSR and draftRSR pro rata.
\\   (2) Seizure that exactly empties the stake pool (era reset).
\\       seize amount = stakeRSR; verify stake era reset triggers.
\\   (3) Seizure that exceeds total RSR (production reverts; the
\\       sim is total-function so we discharge by precondition).
\\       Document the boundary.
\\   (4) Proportional split fidelity: at calibrated (stakeRSR,
\\       draftRSR) ratios, the stake_share : draft_share split
\\       matches the input ratio within 1 wei (ceil rounding).
\\   (5) Era-reset via MAX_STAKE_RATE saturation: post-seize the
\\       implied stakeRate would exceed MAX_STAKE_RATE; era reset
\\       fires.
\\
\\ Reference: protocol/contracts/p1/StRSR.sol#436-507 (seizeRSR)
\\
\\ Constants:
\\   FIX_ONE             = 1e18
\\   MAX_STAKE_RATE      = 1e9 * FIX_ONE
\\   MAX_DRAFT_RATE      = 1e9 * FIX_ONE

print("=== StRSR seize_rsr — CAS validation ===");
print("");

FIX_ONE = 10^18;
MAX_STAKE_RATE = 10^9 * FIX_ONE;
MAX_DRAFT_RATE = 10^9 * FIX_ONE;

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ The production formula (StRSR.sol line 457):
\\   stakeRSRToTake = (stakeRSR * rsrAmount + (rsrBalance - 1)) / rsrBalance
\\ which is ceil(stakeRSR * rsrAmount / rsrBalance).
\\ The simulation's seizeRSR uses totalRSR = totalRSRStaked + draftRSR
\\ (no separate rewards balance), but the proportional-split shape is
\\ the same.
\\
\\ Reset triggers:
\\   stake_reset: stake_post = 0 OR totalStakes * FIX_ONE > stake_post * MAX_STAKE_RATE
\\                (production's stakeRate > MAX_STAKE_RATE; the
\\                simulation's derived-rate equivalent).
\\   draft_reset: draft_post = 0 OR totalDrafts > draft_post
\\                (the simulation's tighter analog of draftRate >
\\                MAX_DRAFT_RATE: the sim maintains draftRate = FIX_ONE
\\                so it era-resets at the FIX_ONE boundary rather than
\\                MAX_DRAFT_RATE).
seize_sim(stakeRSR, draftRSR, totalStakes, totalDrafts, rsrAmount) = { my(totalRSR, stake_share, draft_share, stake_post, draft_post, stake_reset, draft_reset); totalRSR = stakeRSR + draftRSR; if(totalRSR == 0, return(["empty", stakeRSR, draftRSR, 0, 0])); stake_share = ceil_div(stakeRSR * rsrAmount, totalRSR); draft_share = rsrAmount - stake_share; stake_post = stakeRSR - stake_share; draft_post = draftRSR - draft_share; stake_reset = (stake_post == 0) || (totalStakes > 0 && totalStakes * FIX_ONE > stake_post * MAX_STAKE_RATE); draft_reset = (draft_post == 0) || (totalDrafts > draft_post); [if(stake_reset, "stake-reset", "ok"), stake_post, draft_post, stake_share, draft_share, stake_reset, draft_reset]; }

report_pool_decreases(pre, post, taken) = if(pre - post == taken, print("  OK: pool decreased by exactly taken"), report_pool_decreases_fail(pre, post, taken));
report_pool_decreases_fail(pre, post, taken) = printf("  FAIL: pre=%d post=%d taken=%d (delta=%d)\n", pre, post, taken, pre - post);

report_split_ratio(stake_share, draft_share, stake_pre, draft_pre, total) = { my(expected_stake); expected_stake = ceil_div(stake_pre * total, stake_pre + draft_pre); if(stake_share == expected_stake, print("  OK: stake_share matches CEIL(stake_pre * rsrAmount / total)"), report_split_ratio_fail(stake_share, expected_stake)); }
report_split_ratio_fail(actual, expected) = printf("  FAIL: stake_share=%d expected=%d\n", actual, expected);

report_reset(reset_flag, expected) = if(reset_flag == expected, print("  OK: reset trigger matches expectation"), report_reset_fail(reset_flag, expected));
report_reset_fail(actual, expected) = printf("  FAIL: reset=%d expected=%d\n", actual, expected);

\\ Calibration: 100M qRSR backing 1M qStRSR stakes; 5M qRSR backing
\\ 5M qDrafts (rate = FIX_ONE on the draft side).
stakeRSR_cal    = 10^8 * FIX_ONE;
totalStakes_cal = 10^6 * FIX_ONE;
draftRSR_cal    = 5 * 10^6 * FIX_ONE;
totalDrafts_cal = 5 * 10^6 * FIX_ONE;
totalRSR_cal    = stakeRSR_cal + draftRSR_cal;

\\ ---------- (1) Small seizure on a stake-only state (no era reset) ----------
print("--- (1) Small seizure on stake-only state (no draft pool): 1% of total RSR ---");
\\ With no drafts pre-seize (queue empty, draftRSR = 0), the proportional
\\ split puts everything on the stake side and the draft side stays at 0
\\ so neither reset trigger fires.
small_seize = stakeRSR_cal \ 100;
res1 = seize_sim(stakeRSR_cal, 0, totalStakes_cal, 0, small_seize);
{ printf("  seize=%d (stakeRSR=%d, draftRSR=0), result=%s\n", small_seize, stakeRSR_cal, res1[1]); }
{ printf("  stake_post=%d, draft_post=%d\n", res1[2], res1[3]); }
{ printf("  stake_share=%d, draft_share=%d\n", res1[4], res1[5]); }
\\ Conservation: stake_share + draft_share == small_seize.
if(res1[4] + res1[5] == small_seize, print("  OK: shares sum to seize amount"), print("  FAIL: shares don't sum"));
\\ Pool decreases match.
report_pool_decreases(stakeRSR_cal, res1[2], res1[4]);
report_pool_decreases(0, res1[3], res1[5]);
\\ With draftRSR_pre = 0, draft_share is 0 (everything goes to stake) and
\\ draft_post is 0 -> draft_reset trivially fires.
report_reset(res1[6], 0);
report_reset(res1[7], 1);
print("");

\\ ---------- (1b) Small seizure with both pools non-trivial ----------
print("--- (1b) Small seizure: 1% of total RSR (note: sim era-resets the draft side) ---");
\\ The simulation maintains draftRate = FIX_ONE (vs production's [FIX_ONE,
\\ MAX_DRAFT_RATE] band), so a proportional seize that leaves
\\ totalDrafts > draftRSR_post triggers a draft era reset. This is
\\ stricter than production but consistent: every reachable state in the
\\ simulation satisfies the tighter invariant.
small_seize_b = totalRSR_cal \ 100;
res1b = seize_sim(stakeRSR_cal, draftRSR_cal, totalStakes_cal, totalDrafts_cal, small_seize_b);
{ printf("  seize=%d, result=%s\n", small_seize_b, res1b[1]); }
{ printf("  stake_post=%d, draft_post=%d (vs totalDrafts=%d)\n", res1b[2], res1b[3], totalDrafts_cal); }
{ printf("  stake_reset=%d (stake side preserves invariant), draft_reset=%d (draftRate would exceed FIX_ONE)\n", res1b[6], res1b[7]); }
\\ The proportional-split arithmetic still holds (we check the math even
\\ on the era-reset branch's pre-reset values).
if(res1b[4] + res1b[5] == small_seize_b, print("  OK: shares sum to seize amount"), print("  FAIL: shares don't sum"));
report_split_ratio(res1b[4], res1b[5], stakeRSR_cal, draftRSR_cal, small_seize_b);
\\ Stake side: no reset (totalStakes is 1M and stake_post >> threshold).
report_reset(res1b[6], 0);
\\ Draft side: reset fires (totalDrafts > draft_post by ~1% of pool).
report_reset(res1b[7], 1);
print("");

\\ ---------- (2) Seize exactly stakeRSR (stake era reset) ----------
print("--- (2) Seize amount targeting stake-pool emptying ---");
\\ For seize amount = stakeRSR, the proportional split gives
\\   stake_share = ceil(stakeRSR * stakeRSR / total) = stakeRSR^2 / total
\\ which is LESS than stakeRSR — so a single proportional seize won't
\\ empty the pool unless stakeRSR == total. We instead probe a seize
\\ amount large enough that stake_post hits 0: pick rsrAmount = total
\\ (full empty). Verify both pools zero and both era resets fire.
full_seize = totalRSR_cal;
res2 = seize_sim(stakeRSR_cal, draftRSR_cal, totalStakes_cal, totalDrafts_cal, full_seize);
{ printf("  seize=%d (== total), result=%s\n", full_seize, res2[1]); }
{ printf("  stake_post=%d, draft_post=%d\n", res2[2], res2[3]); }
if(res2[2] == 0 && res2[3] == 0, print("  OK: both pools fully consumed"), print("  FAIL: residual in one of the pools"));
\\ Both era resets fire.
report_reset(res2[6], 1);
report_reset(res2[7], 1);
print("");

\\ ---------- (3) Boundary: seize > total RSR (production reverts) ----------
print("--- (3) Boundary: seize > total RSR is a precondition violation ---");
{ printf("  total RSR = %d\n", totalRSR_cal); }
{ printf("  Production reverts with SeizeExceedsBalance when rsrAmount > rsrBalance\n"); }
{ printf("  Simulation requires rsrAmount <= totalRSR as Valid.t precondition\n"); }
print("  OK: documented; precondition is sim-side hypothesis");
print("");

\\ ---------- (4) Proportional split fidelity (calibrated ratios) ----------
print("--- (4) Proportional split at calibrated ratios ---");
\\ Probe a 30%-stake / 70%-draft setup and a 99%-stake / 1%-draft setup.
print("  -- (4a) 30% stake / 70% draft balance --");
sR_a = 3 * 10^7 * FIX_ONE;
dR_a = 7 * 10^7 * FIX_ONE;
seize_a = (sR_a + dR_a) \ 50;   \\ 2% of total
res4a = seize_sim(sR_a, dR_a, totalStakes_cal, totalDrafts_cal, seize_a);
{ printf("    seize=%d  stake_share=%d (~30%%)  draft_share=%d (~70%%)\n", seize_a, res4a[4], res4a[5]); }
\\ Expected stake share = ceil(30M * seize / 100M) = ceil(0.3 * seize).
expected_a = ceil_div(sR_a * seize_a, sR_a + dR_a);
if(res4a[4] == expected_a, print("    OK: stake_share = ceil(stakeRSR * seize / total)"), print("    FAIL: split ratio off"));

print("  -- (4b) 99% stake / 1% draft balance --");
sR_b = 99 * 10^6 * FIX_ONE;
dR_b = 10^6 * FIX_ONE;
seize_b = (sR_b + dR_b) \ 1000;   \\ 0.1% of total
res4b = seize_sim(sR_b, dR_b, totalStakes_cal, totalDrafts_cal, seize_b);
{ printf("    seize=%d  stake_share=%d (~99%%)  draft_share=%d (~1%%)\n", seize_b, res4b[4], res4b[5]); }
expected_b = ceil_div(sR_b * seize_b, sR_b + dR_b);
if(res4b[4] == expected_b, print("    OK: stake_share matches expected"), print("    FAIL: split ratio off"));
print("");

\\ ---------- (5) Era reset via MAX_STAKE_RATE saturation ----------
print("--- (5) Era reset triggered by MAX_STAKE_RATE saturation ---");
\\ Saturation: totalStakes * FIX_ONE > stake_post * MAX_STAKE_RATE
\\   => stake_post < totalStakes / MAX_STAKE_RATE_BAR
\\   => stake_post < totalStakes_cal / 1e9 (since MAX_STAKE_RATE = 1e9 * FIX_ONE)
\\
\\ Construct a seize where stake_post hits this threshold.
\\ For totalStakes = 1e6 * FIX_ONE = 1e24, threshold = 1e24 / 1e9 = 1e15.
\\ With stakeRSR = 1e26, we need stake_share = stakeRSR - 1e14 ~ 1e26.
\\ Picking rsrAmount such that stake_share = stakeRSR - small means
\\ stakeRSR * rsrAmount / total ~ stakeRSR, so rsrAmount ~ total.
saturate_thresh = totalStakes_cal \ 10^9;   \\ ~ 1e15
{ printf("  Stake-rate saturation when stake_post < %d (~1e15)\n", saturate_thresh); }

\\ Compute the smallest rsrAmount that drops stake_post below this.
\\ stake_share = ceil(stakeRSR * x / total)
\\ stake_post = stakeRSR - stake_share < threshold
\\   => stake_share > stakeRSR - threshold
\\   => ceil(stakeRSR * x / total) > stakeRSR - threshold
\\   => stakeRSR * x / total > stakeRSR - threshold - 1
\\   => x > (stakeRSR - threshold - 1) * total / stakeRSR
\\   ~~ x > (stakeRSR - 1e15) * total / stakeRSR ~~ total - small

\\ We want stake_post strictly below threshold: pick a seize that
\\ leaves at most threshold-1 = ~1e15 - 1 in the stake pool.
x_test = ((stakeRSR_cal - saturate_thresh + 1) * totalRSR_cal) \ stakeRSR_cal + 1;
res5 = seize_sim(stakeRSR_cal, draftRSR_cal, totalStakes_cal, totalDrafts_cal, x_test);
{ printf("  seize=%d -> stake_post=%d, stake_reset=%d\n", x_test, res5[2], res5[6]); }
\\ Expect stake reset to fire (either pool emptied or rate saturated).
report_reset(res5[6], 1);
print("");

print("Done.");
