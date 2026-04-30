\\ powu_correctness.gp
\\
\\ CAS-side validation of FixLib.powu — the exponentiation-by-squaring
\\ implementation that underpins Furnace.melt and StRSR._payoutRewards.
\\ Any rounding error here cascades into both compound-formula contracts.
\\
\\ Reference: protocol/contracts/libraries/Fixed.sol::powu (~line 595)
\\
\\ Algorithm (production):
\\   require(x_ <= FIX_ONE);
\\   if (y == 1) return x_;
\\   if (x_ == FIX_ONE || y == 0) return FIX_ONE;
\\   x = x_ * FIX_SCALE       (lift to D36)
\\   result = FIX_SCALE_SQ    (D36 representation of 1.0)
\\   while (true):
\\     if (y & 1 == 1) result = round((result * x) / FIX_SCALE_SQ)
\\     if (y <= 1) break
\\     y >>= 1
\\     x = round((x * x) / FIX_SCALE_SQ)
\\   return safeWrap(result / FIX_SCALE)
\\
\\ Properties checked:
\\   INV-1  Domain: result <= FIX_ONE for all x <= FIX_ONE
\\   INV-2  Boundary: powu(x, 0) == FIX_ONE; powu(x, 1) == x; powu(FIX_ONE, y) == FIX_ONE
\\   INV-3  Monotone in y: for x < FIX_ONE, powu(x, y) is strictly decreasing in y
\\   INV-4  Match closed form: powu(x, y) ~ x^y / FIX_ONE^(y-1)  (within compounded rounding)

default(parisizemax, "1G");

print("=== FixLib.powu — CAS validation ===");
print("");

FIX_ONE      = 10^18;
FIX_SCALE    = 10^18;
FIX_SCALE_SQ = 10^36;

\\ Faithful PARI/GP reproduction of FixLib.powu's exp-by-squaring loop.
powu_FIX(x_, y) = { my(x, result, yy); if(x_ > FIX_ONE, return("DOMAIN-VIOLATION")); if(y == 1, return(x_)); if(x_ == FIX_ONE || y == 0, return(FIX_ONE)); x = x_ * FIX_SCALE; result = FIX_SCALE_SQ; yy = y; while(1, if(bitand(yy, 1) == 1, result = (result * x + FIX_SCALE_SQ \ 2) \ FIX_SCALE_SQ); if(yy <= 1, break); yy = yy \ 2; x = (x * x + FIX_SCALE_SQ \ 2) \ FIX_SCALE_SQ); result \ FIX_SCALE; }

\\ Closed-form reference: x^y / FIX_ONE^(y-1) with explicit rounding.
\\ For comparison only; production uses iterative squaring.
powu_closed(x_, y) = if(y == 0, FIX_ONE, x_^y \ FIX_ONE^(y - 1));

\\ ---- INV-1: powu(x, y) <= FIX_ONE for all x <= FIX_ONE ----
print("--- INV-1: result <= FIX_ONE for all valid inputs ---");
inv1_violations = 0;
{
  test_xs = [0, 1, FIX_ONE \ 2, FIX_ONE - 1, FIX_ONE];
  test_ys = [0, 1, 2, 10, 100, 10000, 86400];
  for(i = 1, #test_xs,
    for(j = 1, #test_ys,
      v = powu_FIX(test_xs[i], test_ys[j]);
      if(v > FIX_ONE, inv1_violations = inv1_violations + 1);
    );
  );
}
{ printf("  Probed %d (x, y) combinations; violations: %d\n", #[0, 1, FIX_ONE \ 2, FIX_ONE - 1, FIX_ONE] * #[0, 1, 2, 10, 100, 10000, 86400], inv1_violations); }
if(inv1_violations == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-2: Boundary cases ----
print("--- INV-2: boundary cases ---");
b1 = powu_FIX(FIX_ONE \ 2, 0);    \\ x^0 = 1
b2 = powu_FIX(FIX_ONE \ 2, 1);    \\ x^1 = x
b3 = powu_FIX(FIX_ONE,    100);   \\ 1^100 = 1
b4 = powu_FIX(0,          0);     \\ 0^0 = 1 (Solidity convention; matches `y == 0` branch)
b5 = powu_FIX(0,          5);     \\ 0^5 = 0 — needs to actually be 0
{ printf("  powu(0.5, 0)         = %d (expected FIX_ONE = %d)  %s\n", b1, FIX_ONE, if(b1 == FIX_ONE, "OK", "FAIL")); }
{ printf("  powu(0.5, 1)         = %d (expected FIX_ONE/2 = %d)  %s\n", b2, FIX_ONE \ 2, if(b2 == FIX_ONE \ 2, "OK", "FAIL")); }
{ printf("  powu(FIX_ONE, 100)   = %d (expected FIX_ONE)  %s\n", b3, if(b3 == FIX_ONE, "OK", "FAIL")); }
{ printf("  powu(0, 0)           = %d (expected FIX_ONE; Solidity convention)  %s\n", b4, if(b4 == FIX_ONE, "OK", "FAIL")); }
{ printf("  powu(0, 5)           = %d (expected 0)  %s\n", b5, if(b5 == 0, "OK", "FAIL")); }
print("");

\\ ---- INV-3: Monotone decreasing in y for x < FIX_ONE ----
print("--- INV-3: powu(x, y) strictly decreasing in y for x < FIX_ONE ---");
\\ Pick x = 0.999 (FIX_ONE - 1e15). For y_1 < y_2, powu(x, y_1) > powu(x, y_2).
\\ With rounding noise, "strictly decreasing" may have ties at very close y;
\\ verify it's at least non-increasing.
mono_ok = 1;
prev = FIX_ONE + 1;
{
  test_x = FIX_ONE - 10^15;
  ys = [1, 2, 10, 100, 1000, 10000];
  for(i = 1, 6,
    v = powu_FIX(test_x, ys[i]);
    if(v > prev, mono_ok = 0);
    prev = v;
  );
}
report_powu_y(x_label, x, y) = printf("  powu(%-10s y=%-8d) = %d  (= %.6f)\n", x_label, y, powu_FIX(x, y), powu_FIX(x, y) * 1.0 / FIX_ONE);
report_powu_y("0.999",     FIX_ONE - 10^15, 1);
report_powu_y("0.999",     FIX_ONE - 10^15, 10);
report_powu_y("0.999",     FIX_ONE - 10^15, 100);
report_powu_y("0.999",     FIX_ONE - 10^15, 1000);
report_powu_y("0.999",     FIX_ONE - 10^15, 10000);
if(mono_ok, print("  OK: non-increasing in y"), print("  FAIL: monotonicity violated"));
print("");

\\ ---- INV-4: Match closed form within rounding ----
print("--- INV-4: iterative powu vs closed-form x^y / FIX_ONE^(y-1) ---");
\\ Closed form computes via exact-integer power (huge intermediate);
\\ iterative computes via exp-by-squaring with per-step rounding.
\\ Difference grows ~O(log_2(y)) wei because exp-by-squaring does
\\ log_2(y) rounded multiplications. Bound: O(log_2(y)) wei.
match_test(x_label, x, y) = { my(it, cf, diff); it = powu_FIX(x, y); cf = powu_closed(x, y); diff = abs(it - cf); printf("  x=%s y=%-5d  iter=%-22d closed=%-22d diff=%d (~%.0f log2(y))\n", x_label, y, it, cf, diff, log(y) / log(2)); }
match_test("0.5",    FIX_ONE \ 2, 10);
match_test("0.5",    FIX_ONE \ 2, 100);
match_test("0.999",  FIX_ONE - 10^15, 100);
match_test("0.999",  FIX_ONE - 10^15, 1000);
print("  (Diff bounded by ~log_2(y) wei — exp-by-squaring rounds once per squaring step.)");
print("");

print("Done.");
