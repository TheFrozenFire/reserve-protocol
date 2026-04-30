\\ refresh_basket.gp
\\
\\ CAS-side validation of BasketHandlerP1.refreshBasket() / _switchBasket() /
\\ BasketLibP1.nextBasket() — the per-target backup-collateral selection.
\\
\\ Reference:
\\   protocol/contracts/p1/BasketHandler.sol :: refreshBasket / _switchBasket
\\   protocol/contracts/p1/mixins/BasketLib.sol :: nextBasket
\\
\\ The production logic (BasketLib.sol L164-283) iterates the prime config
\\ and, for each target name with DISABLED prime collateral, picks up to
\\ `backup.max` available backups and distributes the unsoundPrimeWt
\\ uniformly across them.  If no backup is available for a target with
\\ DISABLED prime weight, _switchBasket leaves disabled = true.
\\
\\ Properties probed:
\\
\\   INV-RB1  No-op when all primes SOUND: the next basket equals the
\\            prime basket; disabled = false.
\\
\\   INV-RB2  All-DISABLED primes for one target with backup available:
\\            backup is selected; new basket has the backup erc20.
\\
\\   INV-RB3  No backup available -> disabled = true: when a target has
\\            DISABLED prime weight and zero available backups in its
\\            BackupConfig, the resulting basket is disabled.
\\
\\   INV-RB4  Backup max-cap: only `backup.max` backups are taken even
\\            if more are available.
\\
\\   INV-RB5  Per-target weight conservation: for every target name,
\\            sum(targetAmts of new basket entries for that target)
\\            equals sum(targetAmts of prime entries for that target),
\\            modulo the floor-division rounding budget (loss <= size - 1
\\            wei per target).
\\
\\   INV-RB6  Even-distribution invariant: when N > 0 backups are
\\            selected for a target with unsound weight W, each backup
\\            receives floor(W / N).

print("=== BasketHandler.refreshBasket — CAS validation ===");
print("");

FIX_ONE = 10^18;

\\ ---- Mock infrastructure ----

lookup_status(e, status_keys, status_vals) = { my(n, i, r); n = length(status_keys); r = 0; for(i = 1, n, if(status_keys[i] == e, r = status_vals[i])); r; };

select_backups(backups, mx, status_keys, status_vals) = { my(out, i, count); out = []; count = 0; for(i = 1, length(backups), if(count < mx && lookup_status(backups[i], status_keys, status_vals) == 1, out = concat(out, [backups[i]]); count = count + 1)); out; };

unsound_weight(target, prime_e, prime_a, prime_t, status_keys, status_vals) = { my(n, i, sm); n = length(prime_e); sm = 0; for(i = 1, n, if(prime_t[i] == target && lookup_status(prime_e[i], status_keys, status_vals) == 0, sm = sm + prime_a[i])); sm; };

total_prime_weight(target, prime_e, prime_a, prime_t) = { my(n, i, sm); n = length(prime_e); sm = 0; for(i = 1, n, if(prime_t[i] == target, sm = sm + prime_a[i])); sm; };

\\ Find the index of `target` in vector `v`; returns 0 if not found.
find_idx(target, v) = { my(n, i, r); n = length(v); r = 0; for(i = 1, n, if(v[i] == target, r = i)); r; };

\\ refreshBasket simulator: returns [disabled, [new_erc20s, new_refAmts]].
refresh_basket(prime_e, prime_a, prime_t, backup_t, backup_lists, backup_maxes, status_keys, status_vals) = { my(n_primes, i, j, target, need, avail, sz, per, new_e, new_a, names_seen, name_idx); n_primes = length(prime_e); new_e = []; new_a = []; for(i = 1, n_primes, if(lookup_status(prime_e[i], status_keys, status_vals) == 1, new_e = concat(new_e, [prime_e[i]]); new_a = concat(new_a, [prime_a[i]]))); names_seen = []; for(i = 1, n_primes, name_idx = find_idx(prime_t[i], names_seen); if(name_idx == 0, names_seen = concat(names_seen, [prime_t[i]]))); for(i = 1, length(names_seen), target = names_seen[i]; need = unsound_weight(target, prime_e, prime_a, prime_t, status_keys, status_vals); if(need > 0, name_idx = find_idx(target, backup_t); if(name_idx == 0, return([1, [[], []]])); avail = select_backups(backup_lists[name_idx], backup_maxes[name_idx], status_keys, status_vals); sz = length(avail); if(sz == 0, return([1, [[], []]])); per = need \ sz; for(j = 1, sz, new_e = concat(new_e, [avail[j]]); new_a = concat(new_a, [per])))); if(length(new_e) == 0, return([1, [[], []]])); [0, [new_e, new_a]]; };

\\ ============================================================
\\ INV-RB1: All primes SOUND -> next basket = prime basket; disabled = false.
\\ ============================================================
print("--- INV-RB1: no-op refresh when all primes SOUND ---");
prime_e_1 = [101, 102, 103];
prime_a_1 = [FIX_ONE \ 3, FIX_ONE \ 3, FIX_ONE \ 3];
prime_t_1 = [1, 1, 1];
backup_t_1 = [1];
backup_lists_1 = [[201, 202]];
backup_maxes_1 = [2];
status_keys_1 = [101, 102, 103];
status_vals_1 = [1, 1, 1];

result_1 = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_1, backup_lists_1, backup_maxes_1, status_keys_1, status_vals_1);
disabled_1 = result_1[1];
new_e_1 = result_1[2][1];
new_a_1 = result_1[2][2];
{ printf("  disabled = %d (expect 0)\n", disabled_1); }
{ printf("  new basket: %d entries (expect 3)\n", length(new_e_1)); }
inv_rb1_ok = (disabled_1 == 0) && (length(new_e_1) == 3) && (new_e_1 == [101, 102, 103]);
if(inv_rb1_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RB2: All primes DISABLED for one target -> backups selected.
\\ ============================================================
print("--- INV-RB2: backup selection when all primes DISABLED ---");
status_keys_2 = [101, 102, 103, 201, 202];
status_vals_2 = [0, 0, 0, 1, 1];

result_2 = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_1, backup_lists_1, backup_maxes_1, status_keys_2, status_vals_2);
disabled_2 = result_2[1];
new_e_2 = result_2[2][1];
new_a_2 = result_2[2][2];
{ printf("  disabled = %d (expect 0)\n", disabled_2); }
{ printf("  new basket erc20s: %s (expect [201, 202])\n", new_e_2); }
expected_unsound = (FIX_ONE \ 3) * 3;
expected_per_backup = expected_unsound \ 2;
{ printf("  expected unsound = %d, per_backup = %d\n", expected_unsound, expected_per_backup); }
{ printf("  realised per_backup = %d\n", new_a_2[1]); }
inv_rb2_ok = (disabled_2 == 0) && (new_e_2 == [201, 202]) && (new_a_2[1] == expected_per_backup);
if(inv_rb2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RB3: No backup available -> disabled = true.
\\ ============================================================
print("--- INV-RB3: no available backup -> disabled ---");
status_keys_3 = [101, 102, 103, 201, 202];
status_vals_3 = [0, 0, 0, 0, 0];

result_3 = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_1, backup_lists_1, backup_maxes_1, status_keys_3, status_vals_3);
disabled_3 = result_3[1];
{ printf("  disabled = %d (expect 1)\n", disabled_3); }
inv_rb3_ok = (disabled_3 == 1);
if(inv_rb3_ok, print("  OK"), print("  FAIL"));
print("");

\\ Sub-witness: backup config missing entirely.
print("--- INV-RB3a: missing backup config -> disabled ---");
backup_t_missing = [];
backup_lists_missing = [];
backup_maxes_missing = [];
result_3a = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_missing, backup_lists_missing, backup_maxes_missing, status_keys_2, status_vals_2);
disabled_3a = result_3a[1];
{ printf("  disabled = %d (expect 1)\n", disabled_3a); }
inv_rb3a_ok = (disabled_3a == 1);
if(inv_rb3a_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RB4: backup max-cap honoured.
\\ ============================================================
print("--- INV-RB4: backup max-cap honoured ---");
backup_t_4 = [1];
backup_lists_4 = [[201, 202, 203, 204, 205]];
backup_maxes_4 = [2];
status_keys_4 = [101, 102, 103, 201, 202, 203, 204, 205];
status_vals_4 = [0, 0, 0, 1, 1, 1, 1, 1];

result_4 = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_4, backup_lists_4, backup_maxes_4, status_keys_4, status_vals_4);
new_e_4 = result_4[2][1];
{ printf("  selected backups: %s (expect first 2: [201, 202])\n", new_e_4); }
inv_rb4_ok = (new_e_4 == [201, 202]) && (length(new_e_4) == 2);
if(inv_rb4_ok, print("  OK"), print("  FAIL"));
print("");

\\ Sub-witness: max = 3 with mixed statuses.
print("--- INV-RB4a: backup max-cap with mixed statuses ---");
backup_lists_4a = [[201, 202, 203]];
backup_maxes_4a = [3];
status_keys_4a = [101, 102, 103, 201, 202, 203];
status_vals_4a = [0, 0, 0, 0, 1, 1];

result_4a = refresh_basket(prime_e_1, prime_a_1, prime_t_1, backup_t_4, backup_lists_4a, backup_maxes_4a, status_keys_4a, status_vals_4a);
new_e_4a = result_4a[2][1];
{ printf("  selected backups: %s (expect [202, 203])\n", new_e_4a); }
inv_rb4a_ok = (new_e_4a == [202, 203]);
if(inv_rb4a_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RB5: Per-target weight conservation (within rounding budget).
\\ ============================================================
print("--- INV-RB5: per-target weight conservation (within rounding budget) ---");
sum_new_a = 0;
{ for(i = 1, length(new_a_2), sum_new_a = sum_new_a + new_a_2[i]); }
sum_prime_a = 0;
{ for(i = 1, length(prime_a_1), sum_prime_a = sum_prime_a + prime_a_1[i]); }
loss = sum_prime_a - sum_new_a;
{ printf("  prime weight (target USD): %d\n", sum_prime_a); }
{ printf("  new   weight (target USD): %d\n", sum_new_a); }
{ printf("  rounding loss            : %d wei (expect <= 1 wei * (size - 1))\n", loss); }
inv_rb5_ok = (loss >= 0) && (loss <= 1);
if(inv_rb5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ============================================================
\\ INV-RB6: even-distribution invariant.
\\ ============================================================
print("--- INV-RB6: even distribution across surviving backups ---");
unsound_val = (FIX_ONE \ 3) * 3;
size_val = 2;
expected_per = unsound_val \ size_val;
all_equal = 1;
{ for(i = 1, length(result_4[2][2]), if(result_4[2][2][i] != expected_per, all_equal = 0)); }
{ printf("  expected per_backup = %d\n", expected_per); }
{ printf("  realised refAmts    = %s\n", result_4[2][2]); }
{ printf("  all equal to expected? %d\n", all_equal); }
inv_rb6_ok = (all_equal == 1);
if(inv_rb6_ok, print("  OK"), print("  FAIL"));
print("");

print("Done.");
