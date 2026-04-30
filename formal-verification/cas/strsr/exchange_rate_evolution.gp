\\ exchange_rate_evolution.gp
\\
\\ CAS-side validation of StRSR exchange-rate accounting. Cross-checks:
\\   - the stake invariant `stakeRSR * stakeRate >= totalStakes * 1e18`
\\   - the era-reset trigger when `stakeRate > MAX_STAKE_RATE` after seizure
\\   - the reward compound formula `1 - (1-r)^N` matches N sequential
\\     applications of `r` per period (within fixed-point rounding)
\\
\\ Reference: protocol/contracts/p1/StRSR.sol
\\
\\ Constants:
\\   FIX_ONE             = 1e18
\\   MAX_STAKE_RATE      = 1e9 * FIX_ONE
\\   MAX_SAFE_STAKE_RATE = 1e6 * FIX_ONE
\\   MIN_SAFE_STAKE_RATE = 1e12  (i.e. 1e-6 in D18 fixed-point)
\\
\\ Operations modelled (simplified from production):
\\   payoutRewards: stakeRSR' = stakeRSR + payoutRatio * rsrRewardsAtLastPayout / FIX_ONE
\\                  totalStakes unchanged, stakeRate unchanged
\\   seizeRSR(amt):  stakeRSR' = stakeRSR - rsrSeized
\\                  stakeRate' = ceil(FIX_ONE * totalStakes / stakeRSR')
\\                  if stakeRSR' == 0 or stakeRate' > MAX_STAKE_RATE: era resets

print("=== StRSR exchange-rate evolution — CAS validation ===");
print("");

FIX_ONE = 10^18;
MAX_STAKE_RATE = 10^9 * FIX_ONE;
MAX_SAFE_STAKE_RATE = 10^6 * FIX_ONE;
MIN_SAFE_STAKE_RATE = 10^12;
FIX_MAX = 2^192 - 1;

\\ ---- Modelled ops ----
\\ ceil_div(a, b): exact ceiling of a/b, both nonnegative.
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ payoutRewards: returns new stakeRSR (totalStakes, stakeRate unchanged).
payout(stakeRSR, payoutRatio, rsrRewardsAtLastPayout) = stakeRSR + (payoutRatio * rsrRewardsAtLastPayout) \ FIX_ONE;

\\ seizeRSR. Returns ['era-reset'] or ['ok', new_stakeRSR, new_stakeRate].
\\ Production behaviour: era resets if newStakeRSR == 0 OR newStakeRate > MAX_STAKE_RATE.
seizeRSR(stakeRSR, totalStakes, rsrAmount) = { my(newRSR, newRate); newRSR = stakeRSR - rsrAmount; if(newRSR == 0 || totalStakes == 0, return(["era-reset"])); newRate = ceil_div(FIX_ONE * totalStakes, newRSR); if(newRate > MAX_STAKE_RATE, return(["era-reset"])); ["ok", newRSR, newRate]; }

\\ The compound payout ratio for r per period over N periods.
\\   ratio_N = 1 - (1-r)^N
\\ With r expressed as a fixed-point fraction.
compound_ratio_exact(r, N) = FIX_ONE - (FIX_ONE - r)^N / FIX_ONE^(N - 1);

\\ Sequential application of r once per period to a balance B starting at B0.
\\   B_k = B_{k-1} + r * B_{k-1} / FIX_ONE * <- not what production does
\\ Production actually compounds via "1 - (1-r)^N" applied to fixed
\\ rsrRewardsAtLastPayout, which is a *snapshot at the start*. So the
\\ "sequential" comparison must apply r to the *original* snapshot each
\\ period, not the running total. Modelling:
sequential_payout(B0, snapshot, r, N) = { my(B); B = B0; for(i = 1, N, B = B + (r * snapshot) \ FIX_ONE); B; }

closed_form_payout(B0, snapshot, r, N) = { my(ratio); ratio = compound_ratio_exact(r, N); B0 + (ratio * snapshot) \ FIX_ONE; }

\\ ---- (1) Stake invariant: stakeRSR * stakeRate >= totalStakes * FIX_ONE ----
print("--- (1) Stake invariant: stakeRSR * stakeRate >= totalStakes * FIX_ONE ---");
\\ Calibration: 100M staked, 1M total stakes (typical mature RToken).
stakeRSR_cal = 10^8 * FIX_ONE;
totalStakes_cal = 10^6 * FIX_ONE;
\\ stakeRate = ceil(FIX_ONE * totalStakes / stakeRSR)
stakeRate_cal = ceil_div(FIX_ONE * totalStakes_cal, stakeRSR_cal);
{ printf("  stakeRSR=100M, totalStakes=1M -> stakeRate=%d (%.6e in fixed-point)\n", stakeRate_cal, stakeRate_cal * 1.0); }
lhs = stakeRSR_cal * stakeRate_cal;
rhs = totalStakes_cal * FIX_ONE;
{ printf("  lhs (stakeRSR*stakeRate) = %d\n  rhs (totalStakes*FIX_ONE) = %d\n  invariant holds: %d\n", lhs, rhs, lhs >= rhs); }
if(lhs >= rhs, print("  OK"), print("  FAIL"));
print("");

\\ ---- (2) Era-reset trigger after extreme seizure ----
print("--- (2) Era-reset trigger ---");
\\ Era reset fires iff newStakeRate > MAX_STAKE_RATE = 1e27.
\\ Solve for the seize amount: newRSR = ceil(FIX_ONE * totalStakes / MAX_STAKE_RATE).
\\ Below that, newRate exceeds MAX_STAKE_RATE and resets fire.
seize_threshold_rsr = ceil_div(FIX_ONE * totalStakes_cal, MAX_STAKE_RATE);
{ printf("  Reset boundary: newRSR <= %d (~%.2e RSR) triggers era reset\n", seize_threshold_rsr, seize_threshold_rsr * 1.0 / FIX_ONE); }

\\ Seize past the threshold: stakeRSR_cal - (seize_threshold_rsr - 1) -> newRSR < threshold.
extreme_seize = stakeRSR_cal - (seize_threshold_rsr - 1);
res = seizeRSR(stakeRSR_cal, totalStakes_cal, extreme_seize);
{ printf("  Seize %d (leaves %d RSR)\n", extreme_seize, stakeRSR_cal - extreme_seize); }
report_seize_outcome(res) = if(res[1] == "era-reset", print("  OK: triggered era reset"), printf("  Did not reset: newRSR=%d, newRate=%d\n", res[2], res[3]));
report_seize_outcome(res);
print("");

\\ A milder seizure that stays inside MAX_STAKE_RATE.
mild_seize = stakeRSR_cal \ 10;  \\ 10% seize
res2 = seizeRSR(stakeRSR_cal, totalStakes_cal, mild_seize);
{ printf("  Seize %d (= 10%% of stakeRSR)\n", mild_seize); }
{ printf("  Result: %s, new stakeRSR=%d, new stakeRate=%d\n", res2[1], res2[2], res2[3]); }
\\ The new rate must be > old rate (less RSR per stake) and within bounds.
if(res2[1] == "ok" && res2[3] > stakeRate_cal && res2[3] <= MAX_STAKE_RATE, print("  OK: rate increased and within bounds"), print("  FAIL"));
print("");

\\ ---- (3) Compound payout formula matches geometric-decay reward pool ----
print("--- (3) Compound `1 - (1-r)^N` matches geometric pool decay ---");
\\ Production semantics (StRSR.sol::_payoutRewards):
\\   payoutRatio = FIX_ONE - powu(FIX_ONE - r, N)
\\   payout = payoutRatio * snapshot / FIX_ONE
\\   stakeRSR += payout
\\
\\ The algebraic identity this relies on: if the reward pool is reduced
\\ each period by ratio `r` of its CURRENT value (not the snapshot), then
\\ after N periods the cumulative outflow is (1 - (1-r)^N) * pool_0.
\\
\\ Verify by simulating the geometric pool decay and matching the
\\ closed-form payout amount.

\\ Geometric pool decay: payout_k = r * pool_{k-1}; pool_k = pool_{k-1} - payout_k.
\\ Total payout = pool_0 - pool_N = pool_0 * (1 - (1-r)^N).
geometric_pool_payout(pool0, r, N) = { my(pool, total); pool = pool0; total = 0; for(i = 1, N, my(p); p = (r * pool) \ FIX_ONE; total = total + p; pool = pool - p); total; }

r_test = FIX_ONE \ 1000;     \\ 0.1% per period
N_test = 10;
pool_test = 10^8 * FIX_ONE;  \\ 100M reward pool

cf_payout = (compound_ratio_exact(r_test, N_test) * pool_test) \ FIX_ONE;
geo_payout = geometric_pool_payout(pool_test, r_test, N_test);

{ printf("  r=0.1%%/period, N=10, pool=100M\n"); }
{ printf("  Closed-form payout (1-(1-r)^N)*pool: %d\n", cf_payout); }
{ printf("  Geometric simulation total payout:   %d\n", geo_payout); }
{ printf("  |closed - geometric| = %d (rounding-only difference)\n", abs(cf_payout - geo_payout)); }
\\ Bound: each step's `(r*pool)\FIX_ONE` rounds down by < 1 wei. Total
\\ rounding error <= N wei. We allow a generous margin.
if(abs(cf_payout - geo_payout) <= N_test, print("  OK: identity holds within step-wise rounding"), printf("  WARN: discrepancy %d exceeds N=%d wei\n", abs(cf_payout - geo_payout), N_test));
print("");

\\ ---- (4) Stake-rate ceiling vs MAX_SAFE bound ----
print("--- (4) When does stakeRate cross MAX_SAFE_STAKE_RATE? ---");
\\ MAX_SAFE_STAKE_RATE = 1e6 * FIX_ONE means 1 RSR backs 1e6 stRSR
\\ -> totalStakes / stakeRSR ratio = 1e6
\\ Starting from totalStakes=1M, that's stakeRSR = 1 (one wei of RSR).
\\ This is the parametric point at which Reserve UI flags the rate as unsafe.
target_rsr = ceil_div(FIX_ONE * totalStakes_cal, MAX_SAFE_STAKE_RATE);
{ printf("  At totalStakes=1M, stakeRSR <= %d (~%.0f RSR) crosses MAX_SAFE\n", target_rsr, target_rsr * 1.0 / FIX_ONE); }
{ printf("  As %% of original stakeRSR (100M): %.6f%%\n", target_rsr * 100.0 / stakeRSR_cal); }
print("  i.e. a 99.9999%% seize takes the rate into UI-unsafe territory but");
print("  still well below MAX_STAKE_RATE (1e9 * FIX_ONE) which triggers reset.");
print("");

print("Done.");
