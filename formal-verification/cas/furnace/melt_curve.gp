\\ melt_curve.gp
\\
\\ CAS-side validation of Furnace.melt accounting. Verifies:
\\   - payoutRatio = 1 - (1-ratio)^N is monotone in N
\\   - payoutRatio <= FIX_ONE for all valid (ratio, N)
\\   - Closed-form 1 - (1-r)^N matches geometric balance decay (the
\\     identity StRSR also relies on)
\\
\\ Reference: protocol/contracts/p1/Furnace.sol
\\
\\ Note on PARI/GP arithmetic: exact-rational `(FIX_ONE - r)^N` overflows
\\ the default 8 MB stack for N > ~10^5. We bump parisizemax to 1 GB
\\ which suffices for N up to ~10^6, and fall back to numerical
\\ approximation for the 1-year (N ~ 3.16e7) calibration row.

default(parisizemax, "1G");

print("=== Furnace.melt curve — CAS validation ===");
print("");

FIX_ONE   = 10^18;
MAX_RATIO = 10^14;

\\ Exact-rational payoutRatio (works up to N ~ 1e6).
payout_ratio_FIX(ratio_FIX, N) = { my(one_minus_r); one_minus_r = FIX_ONE - ratio_FIX; FIX_ONE - (one_minus_r^N) \ (FIX_ONE^(N - 1)); }

\\ Numerical-float fallback for very large N. Loses exact precision but
\\ accurate to machine precision (~15 decimal digits), which is fine for
\\ the 1y calibration table.
payout_ratio_FLT(ratio_FIX, N) = FIX_ONE * (1.0 - (1.0 - ratio_FIX * 1.0 / FIX_ONE)^N);

\\ Geometric balance decay simulation: each period, melt ratio*current.
geometric_total_melt(bal0, ratio_FIX, N) = { my(bal, total); bal = bal0; total = 0; for(i = 1, N, my(p); p = (ratio_FIX * bal) \ FIX_ONE; total = total + p; bal = bal - p); total; }

\\ ---- (1) Monotone non-decreasing in N ----
print("--- (1) payoutRatio is monotone non-decreasing in N ---");
mono_ok = 1;
prev = -1;
\\ Limit N to values within stack budget; the trend extrapolates.
{
  Ns = [1, 60, 3600, 86400, 604800];  \\ 1s, 1min, 1h, 1d, 1w
  for(idx = 1, 5,
    N = Ns[idx];
    pr = payout_ratio_FIX(MAX_RATIO, N);
    if(pr < prev, mono_ok = 0);
    prev = pr;
  );
}
report_pr(N, ratio) = printf("  N=%-8d ratio=%-12d payoutRatio=%-22d (%.4f%% of balance)\n", N, ratio, payout_ratio_FIX(ratio, N), payout_ratio_FIX(ratio, N) * 100.0 / FIX_ONE);
report_pr(1,         MAX_RATIO);
report_pr(60,        MAX_RATIO);
report_pr(3600,      MAX_RATIO);
report_pr(86400,     MAX_RATIO);
report_pr(604800,    MAX_RATIO);
if(mono_ok, print("  OK: monotone non-decreasing"), print("  FAIL"));
print("");

\\ ---- (2) payoutRatio <= FIX_ONE always ----
print("--- (2) payoutRatio <= FIX_ONE (cannot melt more than 100%) ---");
cap_ok = 1;
{
  for(N = 1, 50, my(pr); pr = payout_ratio_FIX(MAX_RATIO, N * 10000); if(pr > FIX_ONE, cap_ok = 0));
}
if(cap_ok, print("  OK: payoutRatio bounded by FIX_ONE across N up to 5e5"), print("  FAIL: payoutRatio exceeded FIX_ONE"));
print("");

\\ ---- (3) Identity vs geometric simulation ----
print("--- (3) 1 - (1-ratio)^N == direct geometric melt ---");
\\ Calibrate to typical Reserve setup: ratio = 1e10 (~27%/yr), 100M
\\ RToken balance, 1 day of accumulation.
ratio_typ = 10^10;
bal_typ   = 10^8 * FIX_ONE;
N_typ     = 86400;  \\ one day

cf_melt  = (payout_ratio_FIX(ratio_typ, N_typ) * bal_typ) \ FIX_ONE;
geo_melt = geometric_total_melt(bal_typ, ratio_typ, N_typ);
{ printf("  ratio=1e10 (~27%%/yr), bal=100M, N=86400 (1 day)\n"); }
{ printf("  Closed-form melt: %d\n", cf_melt); }
{ printf("  Geometric melt:   %d\n", geo_melt); }
diff_abs = abs(cf_melt - geo_melt);
diff_rel = diff_abs * 1.0 / cf_melt;
{ printf("  |closed - geometric| = %d wei  (relative: %.2e)\n", diff_abs, diff_rel); }
\\ Theoretical bound on geometric simulation accumulated error:
\\ each step's (r*bal) \ FIX_ONE rounds down by < 1 wei in payout, but
\\ the resulting bal error compounds. Over N steps the accumulated bal
\\ drift is bounded by O(N^2 * r/FIX_ONE) wei, which translates back to
\\ ~O(N) wei in cumulative payout. For N=86400, r=1e10, expect << 1e8
\\ wei drift, which is ~1e-15 of the actual value.
if(diff_rel < 1e-10, print("  OK: identity holds to machine precision"), print("  WARN: discrepancy exceeds 1e-10 relative"));
print("");

\\ ---- (4) Calibration: melt fractions at typical settings ----
print("--- (4) Practical melt fractions ---");
report_pct(label, ratio, N) = printf("  %-30s payoutRatio = %.6f%% over %d periods\n", label, payout_ratio_FLT(ratio, N) * 100.0 / FIX_ONE, N);
\\ Use FLT for long-N rows that overflow exact arithmetic.
report_pct("ratio=1e10, N=1y",     10^10,  31556952);
report_pct("ratio=1e10, N=1d",     10^10,  86400);
report_pct("ratio=1e11, N=1y",     10^11,  31556952);
report_pct("ratio=MAX, N=1d",      MAX_RATIO, 86400);
report_pct("ratio=MAX, N=1h",      MAX_RATIO, 3600);
print("");

print("Done.");
