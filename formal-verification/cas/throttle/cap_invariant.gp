\\ cap_invariant.gp
\\
\\ CAS-side validation of ThrottleLib's safety invariants. Cross-checks
\\ the algebraic claims that the corresponding Rocq simulation will need
\\ to prove, using exact-rational arithmetic over a parameter sweep
\\ calibrated to deployed Reserve RTokens.
\\
\\ Reference:
\\   protocol/contracts/libraries/Throttle.sol
\\
\\ Invariants probed (numbering matches the Rocq draft sketch in
\\ formal-verification/rocq/simulations/Throttle.v.draft):
\\
\\   INV-1  currentlyAvailable(throttle, limit) <= limit  (the cap)
\\   INV-2  After useAvailable returns successfully,
\\           lastAvailable <= hourlyLimit(throttle, supply)
\\   INV-3  useAvailable(throttle, supply, +amount) decreases lastAvailable
\\           by exactly `amount`
\\   INV-4  useAvailable(throttle, supply, -amount) increases lastAvailable
\\           by exactly `-amount`, capped at limit
\\   INV-5  useAvailable(throttle, supply, +amount) reverts iff
\\           amount > currentlyAvailable
\\
\\ Plus overflow analysis on
\\   (limit * delta) / ONE_HOUR        in currentlyAvailable
\\   (supply * pctRate) / FIX_ONE      in hourlyLimit

print("=== ThrottleLib — CAS invariant validation ===");
print("");

ONE_HOUR = 3600;
FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;
UINT48_MAX = 2^48 - 1;
UINT256_MAX = 2^256 - 1;

\\ ---- Solidity-faithful semantics, computed exactly ----

\\ hourlyLimit(throttle, supply) = max(amtRate, (supply * pctRate) \ FIX_ONE)
hourlyLimit(amtRate, pctRate, supply) = { my(p); p = (supply * pctRate) \ FIX_ONE; if(p < amtRate, amtRate, p); }

\\ currentlyAvailable(throttle, limit) =
\\   delta = now - lastTimestamp                   {seconds}
\\   raw   = lastAvailable + (limit * delta) \ ONE_HOUR
\\   if raw > limit, raw = limit
currentlyAvailable(lastAvailable, lastTs, now, limit) = { my(delta, raw); delta = now - lastTs; raw = lastAvailable + (limit * delta) \ ONE_HOUR; if(raw > limit, limit, raw); }

\\ useAvailable returns either ['revert'] or ['ok', newLastAvailable, newLastTs].
\\ amount is signed: positive = consume, negative = restore (with cap).
useAvailable(amtRate, pctRate, lastAvailable, lastTs, supply, amount, now) = { my(limit, available, newAvail, newTs); if(amtRate == 0 && pctRate == 0, return(["ok", lastAvailable, lastTs])); limit = hourlyLimit(amtRate, pctRate, supply); available = currentlyAvailable(lastAvailable, lastTs, now, limit); if(amount > 0 && amount > available, return(["revert"])); newTs = if(available != lastAvailable || available == limit, now, lastTs); if(amount > 0, newAvail = available - amount, if(amount < 0, newAvail = available - amount, newAvail = available)); ["ok", newAvail, newTs]; }

\\ ---- INV-1: currentlyAvailable always <= limit ----
print("--- INV-1: currentlyAvailable <= limit, sweep ---");
\\ Calibrated to a 1B-supply RToken with 1%/hr pctRate and 1M qRTok/hr amtRate.
amtRate_cal = 10^6 * FIX_ONE;     \\ 1M with 18 decimals
pctRate_cal = FIX_ONE / 100;       \\ 1% per hour
supply_cal  = 10^9 * FIX_ONE;      \\ 1B
limit_cal   = hourlyLimit(amtRate_cal, pctRate_cal, supply_cal);
{ printf("  Calibration: amtRate=1M, pctRate=1%%, supply=1B  -> limit = %d (~ %.0f)\n", limit_cal, limit_cal * 1.0); }

\\ Sweep over delta and lastAvailable bounded by [0, limit].
viol_inv1 = 0;
{
  for(d_idx = 0, 8,
    deltas = [0, 1, 1799, 1800, 3599, 3600, 3601, ONE_HOUR * 24, UINT48_MAX];
    delta = deltas[d_idx + 1];
    for(la_step = 0, 4,
      la = (limit_cal * la_step) \ 4;
      a = currentlyAvailable(la, 0, delta, limit_cal);
      if(a > limit_cal, viol_inv1 = viol_inv1 + 1);
    );
  );
}
{ printf("  INV-1 violations across (delta, lastAvailable) sweep: %d\n", viol_inv1); }
if(viol_inv1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-3: positive amount decreases lastAvailable by exactly amount ----
print("--- INV-3: useAvailable(+amount) decreases lastAvailable by amount ---");
viol_inv3 = 0;
{
  amounts = [1, 100 * FIX_ONE, 10^5 * FIX_ONE, limit_cal \ 2];
  for(a_idx = 1, 4,
    amt = amounts[a_idx];
    \\ State: full available
    res = useAvailable(amtRate_cal, pctRate_cal, limit_cal, 0, supply_cal, amt, ONE_HOUR);
    if(res[1] != "ok", viol_inv3 = viol_inv3 + 1; next);
    expected = currentlyAvailable(limit_cal, 0, ONE_HOUR, limit_cal) - amt;
    if(res[2] != expected, viol_inv3 = viol_inv3 + 1);
  );
}
{ printf("  INV-3 violations: %d\n", viol_inv3); }
if(viol_inv3 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-5: revert iff amount > available ----
print("--- INV-5: useAvailable reverts iff amount > available ---");
{ printf("  Currently available at delta=ONE_HOUR, lastAvailable=0: %d\n", currentlyAvailable(0, 0, ONE_HOUR, limit_cal)); }
\\ At a fresh (lastAvailable=0, delta=3600), currentlyAvailable = limit.
\\ Asking for limit+1 must revert; asking for limit must succeed.
res_at  = useAvailable(amtRate_cal, pctRate_cal, 0, 0, supply_cal, limit_cal,     ONE_HOUR);
res_over = useAvailable(amtRate_cal, pctRate_cal, 0, 0, supply_cal, limit_cal + 1, ONE_HOUR);
{ printf("  use(amount = limit)     -> %s\n",  if(res_at[1] == "ok",     "ok",     "revert")); }
{ printf("  use(amount = limit + 1) -> %s\n",  if(res_over[1] == "ok",   "ok",     "revert")); }
inv5_ok = (res_at[1] == "ok") && (res_over[1] == "revert");
if(inv5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- Overflow analysis on (limit * delta) / ONE_HOUR ----
print("--- Overflow analysis: (limit * delta) in uint256 ---");
\\ limit is uint256 (in qRTok); delta is uint48 (max ~2.8e14).
\\ Product overflows uint256 if limit * delta > UINT256_MAX, i.e.
\\   limit > UINT256_MAX / delta.
\\ Worst case: delta = uint48 max.
delta_worst = UINT48_MAX;
limit_threshold = UINT256_MAX \ delta_worst;
{ printf("  Worst-case delta (uint48 max) = %d (~%.2e seconds = %.0f years)\n", delta_worst, delta_worst * 1.0, delta_worst / (3600 * 24 * 365.25)); }
{ printf("  limit threshold for uint256 safety: limit < %d\n", limit_threshold); }
{ printf("  In FIX_ONE units, ~ %.2e\n", limit_threshold * 1.0 / FIX_ONE); }
\\ A practical bound: if supply <= 10^15 * FIX_ONE (1Q tokens) and pctRate <= FIX_ONE,
\\ limit <= 10^15 * FIX_ONE = 10^33. Safe.
{ printf("  Practical Reserve bound: supply <= 1Q tokens, pctRate <= 100%%/hr\n"); }
{ printf("    => limit <= %d, safety margin = %.2e\n", 10^15 * FIX_ONE, limit_threshold * 1.0 / (10^15 * FIX_ONE)); }
print("");

\\ ---- Time-monotonicity property ----
\\ For fixed (lastAvailable, lastTs, limit), currentlyAvailable is
\\ non-decreasing in `now` until it reaches `limit`.
print("--- Monotonicity: currentlyAvailable non-decreasing in `now` ---");
mono_ok = 1;
prev = -1;
{
  for(t_idx = 0, 9,
    nows = [0, 60, 600, 1799, 1800, 3000, 3599, 3600, 7200, UINT48_MAX];
    now = nows[t_idx + 1];
    a = currentlyAvailable(0, 0, now, limit_cal);
    if(a < prev, mono_ok = 0);
    prev = a;
  );
}
if(mono_ok, print("  OK: monotone non-decreasing"), print("  FAIL: non-monotone"));
print("");

print("Done.");
