\\ cancel_unstake.gp
\\
\\ CAS-side validation of StRSR's [cancelUnstake] operation. Companion
\\ to [withdrawal_queue.gp] (probe 5 covers cancel-unstake reversibility
\\ along the stake -> draft -> stake round-trip; this script focuses on
\\ the operation's edge cases as a standalone unit).
\\
\\ Probes:
\\   (1) Round-trip exactness at rate = FIX_ONE: unstake -> cancel
\\       restores totalStakes and stakeRSR EXACTLY (both sides hit
\\       the round-trip bound at zero wei drift).
\\   (2) Lossy recovery at rate = 2 * FIX_ONE: unstake -> cancel
\\       returns less stRSR than the original because the rate
\\       changed; quantify the gap.
\\   (3) FIFO-then-LIFO mismatch: with two unstakes (a then b), the
\\       cancel order is LIFO (cancel rolls back the LATEST entry).
\\       Show that cancelling once removes b's draft, leaving a's
\\       draft intact -- contrast with withdraw which is FIFO.
\\
\\ Reference: protocol/contracts/p1/StRSR.sol#356-400 (cancelUnstake)
\\
\\ Constants:
\\   FIX_ONE             = 1e18
\\   MAX_STAKE_RATE      = 1e9 * FIX_ONE

print("=== StRSR cancel_unstake — CAS validation ===");
print("");

FIX_ONE = 10^18;
MAX_STAKE_RATE = 10^9 * FIX_ONE;

\\ ---- Helpers (mirror withdrawal_queue.gp / exchange_rate_evolution.gp) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ unstake at the simulation's collapsed-rate model:
\\   rate         = exchange_rate(s) -- in this script we drive the rate
\\                  via fixed (totalStakes, stakeRSR, rewards) inputs.
\\   rsrAmount    = floor(amount * rate / FIX_ONE)
\\   totalStakes' = totalStakes - amount
\\   stakeRSR'    = stakeRSR - rsrAmount
\\   draftRSR'    = draftRSR + rsrAmount
\\   queue'       = queue ++ [rsrAmount]
\\ Returns [totalStakes', stakeRSR', draftRSR', rsrAmount, newQueue].
exchange_rate(totalStakes, stakeRSR, rewards) = if(totalStakes == 0, FIX_ONE, ((stakeRSR + rewards) * FIX_ONE) \ totalStakes);

unstake_sim(totalStakes, stakeRSR, rewards, draftRSR, queue, amount) = { my(rate, rsrAmt); rate = exchange_rate(totalStakes, stakeRSR, rewards); rsrAmt = (amount * rate) \ FIX_ONE; [totalStakes - amount, stakeRSR - rsrAmt, draftRSR + rsrAmt, rsrAmt, concat(queue, [rsrAmt])]; }

\\ cancelUnstake_last: pops the LATEST entry from the queue and re-stakes
\\ it at the CURRENT rate (not the unstake-time rate). Production line
\\ 388-399 mirrors mintStakes which uses the present stakeRate.
\\   rsrAmount      = queue[end].rsrAmount
\\   queue'         = queue[0..end-1]
\\   draftRSR'      = draftRSR - rsrAmount
\\   stakeRSR'      = stakeRSR + rsrAmount
\\   if totalStakes == 0:
\\     minted = rsrAmount   (genesis branch)
\\   else:
\\     rate'        = exchange_rate(totalStakes, stakeRSR, rewards)
\\                    -- snapshot BEFORE re-staking
\\     minted       = floor(rsrAmount * FIX_ONE / rate')
\\   totalStakes'   = totalStakes + minted
cancel_last_sim(totalStakes, stakeRSR, rewards, draftRSR, queue) = { my(n, last_rsr, qFront, rate, minted); n = #queue; if(n == 0, return([totalStakes, stakeRSR, draftRSR, 0, [], 0])); last_rsr = queue[n]; qFront = vector(n - 1, i, queue[i]); if(totalStakes == 0, minted = last_rsr, rate = exchange_rate(totalStakes, stakeRSR, rewards); minted = (last_rsr * FIX_ONE) \ rate); [totalStakes + minted, stakeRSR + last_rsr, draftRSR - last_rsr, last_rsr, qFront, minted]; }

report_round_trip_exact(orig_stakes, orig_stakeRSR, post_stakes, post_stakeRSR) = if(orig_stakes == post_stakes && orig_stakeRSR == post_stakeRSR, print("  OK: exact wei-level round-trip"), print("  FAIL: round-trip drift"));

report_round_trip_within(orig, post, tol) = if(abs(orig - post) <= tol, print("  OK: within tolerance"), report_round_trip_within_fail(orig, post, tol));
report_round_trip_within_fail(o, p, t) = printf("  FAIL: drift=%d (tolerance=%d)\n", abs(o - p), t);

\\ ---------- (1) Round-trip exactness at rate = FIX_ONE ----------
print("--- (1) Round-trip exactness at rate = FIX_ONE ---");
\\ Setup: totalStakes = stakeRSR = 1e6 * FIX_ONE, rewards = 0
\\        rate = (stakeRSR + rewards) * FIX_ONE / totalStakes = FIX_ONE
totalStakes_init = 10^6 * FIX_ONE;
stakeRSR_init    = 10^6 * FIX_ONE;
rewards_init     = 0;
draftRSR_init    = 0;
queue_init       = [];
unstake_amt      = totalStakes_init \ 20;   \\ 5%

\\ Step 1: unstake
res_un = unstake_sim(totalStakes_init, stakeRSR_init, rewards_init, draftRSR_init, queue_init, unstake_amt);
mid_stakes = res_un[1]; mid_stakeRSR = res_un[2]; mid_draftRSR = res_un[3]; mid_rsr = res_un[4]; mid_queue = res_un[5];
{ printf("  unstake: amount=%d, rsrAmount=%d, draftRSR=%d, queue=%d entries\n", unstake_amt, mid_rsr, mid_draftRSR, #mid_queue); }

\\ Step 2: cancel_last
res_cu = cancel_last_sim(mid_stakes, mid_stakeRSR, rewards_init, mid_draftRSR, mid_queue);
post_stakes = res_cu[1]; post_stakeRSR = res_cu[2]; post_draftRSR = res_cu[3]; post_rsr = res_cu[4]; post_queue = res_cu[5]; minted = res_cu[6];
{ printf("  cancel:  rsrAmount popped=%d, minted=%d, draftRSR'=%d, queue=%d entries\n", post_rsr, minted, post_draftRSR, #post_queue); }
{ printf("  delta totalStakes=%d, delta stakeRSR=%d\n", post_stakes - totalStakes_init, post_stakeRSR - stakeRSR_init); }

report_round_trip_exact(totalStakes_init, stakeRSR_init, post_stakes, post_stakeRSR);
print("");

\\ ---------- (2) Lossy recovery at rate = 2 * FIX_ONE ----------
print("--- (2) Lossy recovery at rate = 2 * FIX_ONE ---");
\\ Setup: totalStakes = 1e6 * FIX_ONE, stakeRSR = 2e6 * FIX_ONE, rewards = 0
\\        rate = 2e6 * FIX_ONE * FIX_ONE / 1e6 * FIX_ONE = 2 * FIX_ONE
totalStakes_2 = 10^6 * FIX_ONE;
stakeRSR_2    = 2 * 10^6 * FIX_ONE;
rewards_2     = 0;
draftRSR_2    = 0;
queue_2       = [];
unstake_amt_2 = 100000 * FIX_ONE;   \\ 100k qStRSR
init_rate_2   = exchange_rate(totalStakes_2, stakeRSR_2, rewards_2);
{ printf("  initial rate (D18) = %d (= %.3f * FIX_ONE)\n", init_rate_2, init_rate_2 * 1.0 / FIX_ONE); }

res_un2 = unstake_sim(totalStakes_2, stakeRSR_2, rewards_2, draftRSR_2, queue_2, unstake_amt_2);
mid_stakes_2 = res_un2[1]; mid_stakeRSR_2 = res_un2[2]; mid_draftRSR_2 = res_un2[3]; mid_rsr_2 = res_un2[4]; mid_queue_2 = res_un2[5];
{ printf("  unstake: amount=%d -> rsrAmount=%d (rate*amount/FIX_ONE)\n", unstake_amt_2, mid_rsr_2); }

\\ Cancel: re-stake the popped rsrAmount at the rate AFTER unstake.
\\ The post-unstake rate is exchange_rate(mid_stakes, mid_stakeRSR, 0).
post_unstake_rate = exchange_rate(mid_stakes_2, mid_stakeRSR_2, rewards_2);
{ printf("  post-unstake rate (D18) = %d\n", post_unstake_rate); }

res_cu2 = cancel_last_sim(mid_stakes_2, mid_stakeRSR_2, rewards_2, mid_draftRSR_2, mid_queue_2);
post_stakes_2 = res_cu2[1]; post_stakeRSR_2 = res_cu2[2]; post_draftRSR_2 = res_cu2[3]; minted_2 = res_cu2[6];
{ printf("  cancel:  minted=%d (vs original unstake_amt=%d)\n", minted_2, unstake_amt_2); }
{ printf("  delta totalStakes = %d (lossy recovery)\n", post_stakes_2 - totalStakes_2); }
{ printf("  delta stakeRSR    = %d (RSR side conserved)\n", post_stakeRSR_2 - stakeRSR_2); }

\\ stakeRSR side is exactly conserved (RSR moves draft -> stake one-for-one).
if(post_stakeRSR_2 == stakeRSR_2, print("  OK: stakeRSR conservation (no RSR drift)"), print("  FAIL: stakeRSR drift"));

\\ totalStakes side is at most one wei smaller (one ceil/floor pair).
\\ With rate = 2*FIX_ONE and integer bookkeeping the round-trip is
\\ EXACT here too because both divisions hit aligned divisors. Verify
\\ the gap is at most 1 wei.
report_round_trip_within(totalStakes_2, post_stakes_2, 1);
print("");

\\ ---------- (3) FIFO-then-LIFO mismatch ----------
print("--- (3) FIFO-then-LIFO: cancel pops the LATEST entry ---");
\\ Setup: same calibration as (1) but two unstakes back-to-back.
res_a = unstake_sim(totalStakes_init, stakeRSR_init, rewards_init, draftRSR_init, queue_init, 1000 * FIX_ONE);
mid_a_stakes = res_a[1]; mid_a_stakeRSR = res_a[2]; mid_a_draftRSR = res_a[3]; mid_a_rsr = res_a[4]; mid_a_queue = res_a[5];

res_b = unstake_sim(mid_a_stakes, mid_a_stakeRSR, rewards_init, mid_a_draftRSR, mid_a_queue, 2000 * FIX_ONE);
mid_b_stakes = res_b[1]; mid_b_stakeRSR = res_b[2]; mid_b_draftRSR = res_b[3]; mid_b_rsr = res_b[4]; mid_b_queue = res_b[5];

{ printf("  After two unstakes: queue = [%d, %d] (a then b)\n", mid_b_queue[1], mid_b_queue[2]); }

\\ cancel_last: pops the back -> b's entry
res_cancel = cancel_last_sim(mid_b_stakes, mid_b_stakeRSR, rewards_init, mid_b_draftRSR, mid_b_queue);
post_queue_3 = res_cancel[5]; popped_rsr = res_cancel[4];
{ printf("  cancel pops rsrAmount = %d (b's entry: expected %d)\n", popped_rsr, mid_b_rsr); }
{ printf("  Residual queue: %d entries (expected 1, holding a)\n", #post_queue_3); }
if(#post_queue_3 == 1 && post_queue_3[1] == mid_a_rsr, print("  OK: cancel pops LIFO; a's entry remains"), print("  FAIL: queue layout post-cancel"));
print("");

print("Done.");
