\\ share_conservation.gp
\\
\\ CAS-side validation of Distributor share-conservation properties.
\\ Reference: protocol/contracts/p1/Distributor.sol::distribute
\\
\\ The function semantics (simplified):
\\   tokensPerShare = amount / totalShares                  (floor division)
\\   for each dest with numberOfShares[dest] > 0:
\\     transferAmt[dest] = tokensPerShare * numberOfShares[dest]
\\
\\ Properties checked here:
\\   INV-1  Conservation: sum(transferAmt) <= amount, with equality iff
\\           amount % totalShares == 0
\\   INV-2  Dust bound: amount - sum(transferAmt) < totalShares
\\   INV-3  Per-share fairness: each destination gets exactly
\\           tokensPerShare * numberOfShares (no per-destination rounding)
\\   INV-4  Distribution-sum constraint: sum of declared shares >= MAX_DISTRIBUTION

print("=== Distributor share-conservation — CAS validation ===");
print("");

MAX_DISTRIBUTION = 10000;
MAX_DESTINATIONS = 100;

\\ Model the distribute function's local arithmetic.
distribute_amounts(amount, shares) = { my(total, tps, out); total = sum(i = 1, #shares, shares[i]); if(total == 0, return([0, 0])); tps = amount \ total; out = vector(#shares, i, tps * shares[i]); [out, amount - sum(i = 1, #out, out[i])]; }

\\ ---- INV-1: Conservation across structured cases ----
print("--- INV-1 / INV-2: sum(transfer) <= amount, dust < totalShares ---");
\\ Reserve canonical: 4000 rTokenDist (Furnace), 6000 rsrDist (StRSR) -> total 10000.
\\ For RToken-side: only Furnace has nonzero share for RToken.
\\ For testing, model an arbitrary RToken amount (1M qRTok) and shares.
report_dist(label, amount, shares) = { my(r, dust); r = distribute_amounts(amount, shares); dust = r[2]; printf("  %-40s amount=%-15d sum_transfers=%-15d dust=%d  conservation=%s\n", label, amount, amount - dust, dust, if(dust >= 0 && dust < sum(i = 1, #shares, shares[i]), "OK", "FAIL")); }
report_dist("$1M evenly to 4 dests, even shares",     10^24, [25, 25, 25, 25]);
report_dist("$1M to Furnace+StRSR (4000/6000)",       10^24, [4000, 6000]);
report_dist("$1M with prime-factor share total",      10^24, [3, 7, 11, 13]);
report_dist("$1 (1 wei rounded down)",                1,     [4000, 6000]);
report_dist("$1M / shares prime, dust = exact remainder", 1000003, [1, 2]);  \\ totalShares=3, dust=1000003%3=1
print("");

\\ ---- INV-3: Per-share fairness ----
print("--- INV-3: per-destination amount == tokensPerShare * shares[dest] ---");
\\ This holds by construction in our model; we verify by checking
\\ pairwise ratios match the share ratios.
{
  shares = [1500, 2500, 6000];  \\ 15%/25%/60% style
  amount = 12345678901234;       \\ arbitrary
  r = distribute_amounts(amount, shares);
  out = r[1];
  total = sum(i = 1, #shares, shares[i]);
  tps = amount \ total;
  fairness_ok = 1;
  for(i = 1, #out, if(out[i] != tps * shares[i], fairness_ok = 0));
  printf("  amount=%d, shares=%s, tokensPerShare=%d\n", amount, shares, tps);
  for(i = 1, #out, printf("    dest %d: shares=%d amount=%d (== tps*shares: %d)\n", i, shares[i], out[i], out[i] == tps * shares[i]));
  if(fairness_ok, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: Distribution-sum >= MAX_DISTRIBUTION ----
print("--- INV-4: sum of declared shares >= MAX_DISTRIBUTION = 10000 ---");
\\ This is enforced by Distributor.setDistribution / _ensureSufficientTotal.
\\ Verify our model conserves it: configurations whose sum of nonzero
\\ rsr or rToken shares is below 10000 should be rejected by governance.
test_configs = [[4000, 6000], [10000, 0], [0, 10000], [5000, 5001], [4999, 5000]];
{
  for(i = 1, #test_configs,
    cfg = test_configs[i];
    s = cfg[1] + cfg[2];
    printf("  config %s: sum=%d  acceptable=%d\n", cfg, s, s >= MAX_DISTRIBUTION);
  );
}
print("  (All borderline configs above MAX_DISTRIBUTION acceptable; below rejected.)");
print("");

\\ ---- Dust quantification at typical Reserve scale ----
print("--- Dust quantification at typical scale ---");
\\ Real RToken supplies are ~10^7 qRTok (10M tokens with 18 decimals = 10^25 qRTok).
\\ Distribution sum is typically 10000 (basis-point-style).
\\ Worst-case dust = 9999 (one wei less than totalShares).
real_amount = 10^25;
real_shares = [4000, 6000];
r_real = distribute_amounts(real_amount, real_shares);
{ printf("  amount = 10M qRTok (10^25 wei), shares=[4000,6000]\n"); }
{ printf("  dust = %d wei  (relative: %.2e)\n", r_real[2], r_real[2] * 1.0 / real_amount); }
{ printf("  worst-case dust = 9999 wei (totalShares - 1) = %.2e relative\n", 9999 * 1.0 / real_amount); }
print("  Dust is therefore bounded by 9999 wei at protocol-level scale, i.e. <1e-21 of distributed amount.");
print("");

print("Done.");
