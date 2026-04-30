\\ forward_revenue_iter.gp
\\
\\ CAS-side validation of BackingManager.forwardRevenue's multi-asset
\\ iteration. The single-asset surplus split is already covered in
\\ forward_revenue_conservation.gp; this script lifts the conservation
\\ invariant to a list of assets:
\\
\\   For each asset i in the registry:
\\     req_i  = needed * quantity_i (CEIL)
\\     delta_i = shiftl_toUint(bal_i - req_i, decimals_i) when bal_i > req_i
\\               else 0
\\     tps_i  = delta_i / (rTokenTotal + rsrTotal)
\\     rsrShare_i  = tps_i * rsrTotal
\\     rTokShare_i = tps_i * rTokenTotal
\\     dust_i      = delta_i - (rsrShare_i + rTokShare_i)
\\
\\   Aggregates:
\\     rsrSum  = sum_i rsrShare_i
\\     rTokSum = sum_i rTokShare_i
\\     dustSum = sum_i dust_i
\\
\\ Properties checked:
\\   ITER-1  Per-asset conservation: rsr_i + rTok_i + dust_i = delta_i
\\   ITER-2  Aggregate conservation: rsrSum + rTokSum + dustSum = sum_i delta_i
\\   ITER-3  Aggregate fairness: rsrSum / rTokSum == rsrTotal / rTokenTotal
\\           (modulo per-asset dust)
\\   ITER-4  Order-independence: permuting the asset list does not change
\\           the aggregate sums (the per-asset splits are independent).
\\   ITER-5  Empty asset list: all aggregates are zero.
\\   ITER-6  bal <= req for all assets: all aggregates are zero.

print("=== BackingManager.forwardRevenue multi-asset iteration — CAS validation ===");
print("");

\\ ---- FixLib constants ----
FIX_ONE  = 10^18;
FIX_MAX  = 2^192 - 1;

ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);
fix_mul_ceil(x, y)  = ceil_div(x * y, FIX_ONE);

\\ shiftl_toUint(x, decimals) for non-negative decimals.
shiftl_toUint(x, dec) = x * 10^dec;

\\ Per-asset surplus split. Returns [rsr, rTok, dust, delta].
asset_split(needed, quantity, bal, decimals, rTokenTotal, rsrTotal) =
{
  my(req, delta, totalShares, tps, rsr, rtok, dust);
  req = fix_mul_ceil(needed, quantity);
  if(bal <= req,
    return([0, 0, 0, 0]);
  );
  delta = shiftl_toUint(bal - req, decimals);
  totalShares = rTokenTotal + rsrTotal;
  if(totalShares == 0,
    return([-1, -1, -1, -1]);  \\ Revert path; surfaced as -1
  );
  tps = delta \ totalShares;
  if(tps == 0,
    return([0, 0, delta, delta]);
  );
  rsr = tps * rsrTotal;
  rtok = tps * rTokenTotal;
  dust = delta - (rsr + rtok);
  return([rsr, rtok, dust, delta]);
}

\\ Iterate over a list of assets. Each row: [quantity, bal, decimals].
\\ Returns [rsrSum, rTokSum, dustSum, deltaSum].
forward_iter(needed, assets, rTokenTotal, rsrTotal) =
{
  my(rsrSum, rTokSum, dustSum, deltaSum, n, row, sp);
  rsrSum = 0; rTokSum = 0; dustSum = 0; deltaSum = 0;
  n = #assets;
  for(i = 1, n,
    row = assets[i];
    sp = asset_split(needed, row[1], row[2], row[3], rTokenTotal, rsrTotal);
    if(sp[1] == -1, return([-1, -1, -1, -1]));
    rsrSum  = rsrSum  + sp[1];
    rTokSum = rTokSum + sp[2];
    dustSum = dustSum + sp[3];
    deltaSum = deltaSum + sp[4];
  );
  return([rsrSum, rTokSum, dustSum, deltaSum]);
}

\\ ---- Calibration ----
NEEDED       = 1010000000000000000000000;     \\ 1.01M BU (post 1% buffer)
RTOKEN_TOTAL = 4000;
RSR_TOTAL    = 6000;

print("Calibration: needed=1.01M BU, totals=(rTok=4000, rsr=6000)");
print("");

\\ ============================================================
\\ ITER-1: Per-asset conservation
\\ ============================================================
print("--- ITER-1: per-asset conservation rsr + rTok + dust = delta ---");
{
  bad = 0;
  rows = [
    [10^17, 2 * 10^24, 18],     \\ 0.1 quantity, 2M qTok bal, 18 decimals
    [10^16, 5 * 10^22, 18],     \\ 0.01 quantity, 50k qTok bal
    [10^15, 10^25,     18],     \\ 0.001 quantity, 10M qTok bal
    [10^17, 10^9,       6],     \\ USDC-shape: 6 decimals, 10^9 qTok bal
    [10^15, 10^11,      8]      \\ wBTC-shape: 8 decimals, 10^11 qTok bal
  ];
  for(i = 1, #rows,
    row = rows[i];
    sp = asset_split(NEEDED, row[1], row[2], row[3], RTOKEN_TOTAL, RSR_TOTAL);
    if(sp[1] == -1, bad = bad + 1; next());
    if(sp[1] + sp[2] + sp[3] != sp[4], bad = bad + 1);
    printf("  row %d: q=%d, bal=%d, dec=%d -> rsr=%d, rTok=%d, dust=%d, delta=%d\n",
      i, row[1], row[2], row[3], sp[1], sp[2], sp[3], sp[4]);
  );
  if(bad == 0, print("  OK: per-asset conservation holds for every row."), printf("  FAIL: %d row(s) violated conservation.\n", bad));
}
print("");

\\ ============================================================
\\ ITER-2: Aggregate conservation
\\ ============================================================
print("--- ITER-2: aggregate rsrSum + rTokSum + dustSum = deltaSum ---");
{
  assets = [
    [10^17, 2 * 10^24, 18],
    [10^16, 5 * 10^22, 18],
    [10^15, 10^25,     18],
    [10^17, 10^9,       6],
    [10^15, 10^11,      8]
  ];
  agg = forward_iter(NEEDED, assets, RTOKEN_TOTAL, RSR_TOTAL);
  printf("  rsrSum  = %d\n", agg[1]);
  printf("  rTokSum = %d\n", agg[2]);
  printf("  dustSum = %d\n", agg[3]);
  printf("  deltaSum= %d\n", agg[4]);
  if(agg[1] + agg[2] + agg[3] == agg[4],
    print("  OK: aggregate conservation holds across the asset list."),
    print("  FAIL: aggregate conservation broken."));
}
print("");

\\ ============================================================
\\ ITER-3: Aggregate fairness (rsrSum/rTokSum == rsrTotal/rTokenTotal)
\\ ============================================================
print("--- ITER-3: aggregate fairness (per-share ratio) ---");
\\ Within each asset, rsrShare/rTokShare = rsrTotal/rTokenTotal exactly
\\ (as both are tps * total, with the same tps). Across assets, this
\\ ratio is preserved.
{
  assets = [
    [10^17, 2 * 10^24, 18],
    [10^16, 5 * 10^22, 18],
    [10^15, 10^25,     18]
  ];
  agg = forward_iter(NEEDED, assets, RTOKEN_TOTAL, RSR_TOTAL);
  \\ rsrSum * rTokenTotal == rTokSum * rsrTotal
  ratio_ok = (agg[1] * RTOKEN_TOTAL == agg[2] * RSR_TOTAL);
  printf("  rsrSum * rTokenTotal = %d\n", agg[1] * RTOKEN_TOTAL);
  printf("  rTokSum * rsrTotal   = %d\n", agg[2] * RSR_TOTAL);
  if(ratio_ok, print("  OK: aggregate split preserves Distributor totals ratio."),
               print("  FAIL: aggregate split skews from Distributor totals."));
}
print("");

\\ ============================================================
\\ ITER-4: Order-independence under permutation
\\ ============================================================
print("--- ITER-4: aggregate sums are order-independent ---");
{
  assets_a = [
    [10^17, 2 * 10^24, 18],
    [10^16, 5 * 10^22, 18],
    [10^15, 10^25,     18],
    [10^17, 10^9,       6]
  ];
  assets_b = [
    [10^17, 10^9,       6],
    [10^15, 10^25,     18],
    [10^17, 2 * 10^24, 18],
    [10^16, 5 * 10^22, 18]
  ];
  agg_a = forward_iter(NEEDED, assets_a, RTOKEN_TOTAL, RSR_TOTAL);
  agg_b = forward_iter(NEEDED, assets_b, RTOKEN_TOTAL, RSR_TOTAL);
  if(agg_a[1] == agg_b[1] && agg_a[2] == agg_b[2] && agg_a[3] == agg_b[3] && agg_a[4] == agg_b[4],
    print("  OK: aggregate sums identical under asset-list permutation."),
    print("  FAIL: aggregate sums depend on asset order."));
}
print("");

\\ ============================================================
\\ ITER-5: Empty asset list
\\ ============================================================
print("--- ITER-5: empty asset list -> all-zero aggregates ---");
{
  agg = forward_iter(NEEDED, [], RTOKEN_TOTAL, RSR_TOTAL);
  if(agg[1] == 0 && agg[2] == 0 && agg[3] == 0 && agg[4] == 0,
    print("  OK: empty list yields zero aggregates."),
    print("  FAIL: empty list has non-zero aggregates."));
}
print("");

\\ ============================================================
\\ ITER-6: bal <= req for all assets -> aggregates are zero
\\ ============================================================
print("--- ITER-6: all assets at-or-below req -> zero aggregates ---");
{
  \\ With needed = 1.01e24 and quantity = FIX_ONE = 1e18, req = 1.01e24
  \\ (or req = 1.01e24 + 1 due to CEIL on exact multiples — not exact here).
  \\ Set bal = 1 (well below req in each row).
  assets = [
    [FIX_ONE, 1, 18],
    [FIX_ONE, 1, 6],
    [FIX_ONE, 0, 18]
  ];
  agg = forward_iter(NEEDED, assets, RTOKEN_TOTAL, RSR_TOTAL);
  if(agg[1] == 0 && agg[2] == 0 && agg[3] == 0 && agg[4] == 0,
    print("  OK: under-collateralized rows produce zero aggregates."),
    print("  FAIL: under-collateralized rows produced nonzero aggregates."));
}
print("");

\\ ============================================================
\\ ITER-7: Random sweep on conservation
\\ ============================================================
print("--- ITER-7: random sweep on aggregate conservation ---");
setrand(20260430);
{
  N = 1000;
  bad = 0;
  for(i = 1, N,
    \\ random asset list of length 1..6
    n = 1 + random(6);
    assets = vector(n);
    for(j = 1, n,
      \\ quantity in [10^14, 10^18], bal in [10^9, 10^28], dec in [6, 18]
      q = 10^14 + random(10^18 - 10^14);
      bal = random(10^28);
      dec = 6 + random(13);
      assets[j] = [q, bal, dec];
    );
    agg = forward_iter(NEEDED, assets, RTOKEN_TOTAL, RSR_TOTAL);
    if(agg[1] == -1, next());
    if(agg[1] + agg[2] + agg[3] != agg[4], bad = bad + 1);
  );
  printf("  N=%d random sweeps; bad: %d\n", N, bad);
  if(bad == 0,
    print("  OK: aggregate conservation holds across all random samples."),
    print("  FAIL: aggregate conservation broken on some samples."));
}
print("");

print("Done. Run with `gp -q < forward_revenue_iter.gp`.");
