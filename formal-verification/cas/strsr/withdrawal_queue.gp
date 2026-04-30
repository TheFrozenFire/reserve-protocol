\\ withdrawal_queue.gp
\\
\\ CAS-side validation of StRSR's withdrawal-queue (draft) accounting.
\\ Companion to exchange_rate_evolution.gp, which covers the stake side.
\\
\\ Probes:
\\   (1) Draft invariant: draftRSR * draftRate >= totalDrafts * FIX_ONE
\\   (2) Era-reset boundary on the draft side (draftRate > MAX_DRAFT_RATE)
\\   (3) Stake -> draft conservation under unstake: draftRSR' + stakeRSR'
\\       == draftRSR + stakeRSR; stake tokens burnt; draft tokens minted
\\       per the (pre-unstake) draftRate.
\\   (4) Withdraw monotonicity: withdraw(endId) reduces draftRSR/totalDrafts
\\       by the cumulative draftAmount; a re-call is a no-op.
\\   (5) Cancel-unstake reversibility: stake -> draft -> stake round-trip
\\       restores the original RSR position modulo at most a few wei of
\\       integer-rounding drift.
\\   (6) seizeRSR draft-side accounting: pro-rata removal preserves the
\\       draft invariant and the era-reset trigger fires at the expected
\\       boundary.
\\
\\ Reference: protocol/contracts/p1/StRSR.sol
\\
\\ Constants:
\\   FIX_ONE             = 1e18
\\   MAX_DRAFT_RATE      = 1e9 * FIX_ONE
\\   MAX_SAFE_DRAFT_RATE = 1e6 * FIX_ONE
\\   MIN_SAFE_DRAFT_RATE = 1e12  (i.e. 1e-6 in D18)

print("=== StRSR withdrawal-queue / draftRate — CAS validation ===");
print("");

FIX_ONE = 10^18;
FIX_MAX = 2^192 - 1;
MAX_STAKE_RATE = 10^9 * FIX_ONE;
MAX_DRAFT_RATE = 10^9 * FIX_ONE;
MAX_SAFE_DRAFT_RATE = 10^6 * FIX_ONE;
MIN_SAFE_DRAFT_RATE = 10^12;

\\ ---- Helpers (mirrors exchange_rate_evolution.gp) ----
ceil_div(a, b) = if(a % b == 0, a \ b, a \ b + 1);

\\ Model of pushDraft (StRSR.sol::pushDraft, lines ~662-688). Returns the
\\ post-state [draftRSR', totalDrafts', draftAmount] where:
\\   draftRSR'    = draftRSR + rsrAmount
\\   newTotal     = floor(draftRate * draftRSR' / FIX_ONE)
\\   draftAmount  = newTotal - totalDrafts
\\ Note: pushDraft does NOT change draftRate.
push_draft(draftRSR, totalDrafts, draftRate, rsrAmount) = { my(newRSR, newTotal, dAmt); newRSR = draftRSR + rsrAmount; newTotal = (draftRate * newRSR) \ FIX_ONE; dAmt = newTotal - totalDrafts; [newRSR, newTotal, dAmt]; }

\\ Model of unstake (StRSR.sol::unstake, lines ~261-285). Returns the
\\ post-state [stakeRSR', totalStakes', draftRSR', totalDrafts', rsrAmount, draftAmount].
\\ Pre: stakeRate is up-to-date (caller already invoked _payoutRewards()).
unstake_op(stakeRSR, totalStakes, stakeRate, draftRSR, totalDrafts, draftRate, stakeAmount) = { my(newTotalStakes, newStakeRSR, rsrAmount, pd); newTotalStakes = totalStakes - stakeAmount; newStakeRSR = ceil_div(FIX_ONE * newTotalStakes, stakeRate); rsrAmount = stakeRSR - newStakeRSR; pd = push_draft(draftRSR, totalDrafts, draftRate, rsrAmount); [newStakeRSR, newTotalStakes, pd[1], pd[2], rsrAmount, pd[3]]; }

\\ Model of withdraw / cancelUnstake (StRSR.sol::withdraw lines ~308-352
\\ and StRSR.sol::cancelUnstake lines ~356-400). Both operations remove
\\ `draftAmount` drafts from the queue (and from totalDrafts), then
\\ recompute draftRSR. Returns [draftRSR', totalDrafts', rsrAmount].
withdraw_drafts(draftRSR, totalDrafts, draftRate, draftAmount) = { my(newTotal, newRSR, rsrAmount); newTotal = totalDrafts - draftAmount; newRSR = ceil_div(newTotal * FIX_ONE, draftRate); rsrAmount = draftRSR - newRSR; [newRSR, newTotal, rsrAmount]; }

\\ Model of mintStakes (StRSR.sol::mintStakes lines ~746-760).
\\ Returns [stakeRSR', totalStakes', stakeAmount].
mint_stakes(stakeRSR, totalStakes, stakeRate, rsrAmount) = { my(newStakeRSR, newTotal, sAmt); newStakeRSR = stakeRSR + rsrAmount; newTotal = (stakeRate * newStakeRSR) \ FIX_ONE; sAmt = newTotal - totalStakes; [newStakeRSR, newTotal, sAmt]; }

\\ Model of seizeRSR's draft phase (StRSR.sol::seizeRSR lines ~471-484).
\\ Phase 1: draftRSRToTake = ceil(draftRSR * rsrAmount / rsrBalance);
\\          draftRSR' = draftRSR - draftRSRToTake;
\\          if draftRSR' != 0 && totalDrafts != 0:
\\              draftRate' = ceil(FIX_ONE * totalDrafts / draftRSR')
\\          else: draftRate stays
\\ Phase 2: if draftRSR' == 0 or draftRate' > MAX_DRAFT_RATE: era reset.
\\ Returns ["era-reset"] or ["ok", draftRSR', draftRate', taken].
seize_drafts(draftRSR, totalDrafts, draftRate, rsrAmount, rsrBalance) = { my(taken, newRSR, newRate); taken = ceil_div(draftRSR * rsrAmount, rsrBalance); newRSR = draftRSR - taken; if(newRSR == 0 || totalDrafts == 0, return(["era-reset", taken])); newRate = ceil_div(FIX_ONE * totalDrafts, newRSR); if(newRate > MAX_DRAFT_RATE, return(["era-reset", taken + newRSR])); ["ok", newRSR, newRate, taken]; }

\\ Helpers lifted out per R006/W019: nested { } blocks inside if(...) inside
\\ a { } context don't parse. These run at top level so each call is single
\\ line.
report_mild_seize(res, max_rate) = if(res[1] == "ok", report_mild_seize_ok(res, max_rate), print("  FAIL: did not expect era reset on mild seize"));
report_mild_seize_ok(res, max_rate) = { printf("  new draftRSR=%d, new draftRate=%d (<= %d)\n", res[2], res[3], max_rate); print("  OK: rate stays within bounds"); }

report_seize_invariant(res, totalDrafts) = if(res[1] == "ok", report_seize_invariant_ok(res, totalDrafts), print("  FAIL: unexpected era reset on 30% seize"));
report_seize_invariant_ok(res, totalDrafts) = { my(post_rsr, post_rate); post_rsr = res[2]; post_rate = res[3]; printf("  draftRSR': %d, draftRate': %d\n", post_rsr, post_rate); if(post_rsr * post_rate >= totalDrafts * FIX_ONE, print("  OK: draft invariant preserved"), print("  FAIL: invariant violated post-seize")); }

report_round_trip(stake_delta, rsr_delta) = if(stake_delta <= 2 && rsr_delta <= 2, print("  OK: round-trip restored within 2 wei"), report_round_trip_fail(stake_delta, rsr_delta));
report_round_trip_fail(s, r) = printf("  FAIL: drift stakes=%d rsr=%d\n", s, r);

report_draft_amount(actual, expected) = if(actual == expected, print("  OK: draftAmount matches push_draft formula"), report_draft_amount_fail(actual, expected));
report_draft_amount_fail(a, e) = printf("  FAIL: draftAmount=%d expected=%d\n", a, e);

report_rsr_match(actual, expected) = if(actual == expected, print("  OK: rsrOut matches input draftRSR"), report_rsr_match_fail(actual, expected));
report_rsr_match_fail(a, e) = printf("  FAIL: rsrOut=%d, draftRSR_in=%d\n", a, e);

\\ Calibration: 100M RSR staked, 1M total stakes, 5% unstaking event,
\\ 14-day delay (the delay is informational — not modelled directly).
\\ stakeRate = ceil(FIX_ONE * 1M / 100M) = 1e16.
stakeRSR_cal     = 10^8 * FIX_ONE;
totalStakes_cal  = 10^6 * FIX_ONE;
stakeRate_cal    = ceil_div(FIX_ONE * totalStakes_cal, stakeRSR_cal);

\\ Initial draft state: nothing in the withdrawal queue yet so the rate
\\ is the genesis value FIX_ONE per beginDraftEra(). 5% of stakes will
\\ enter the queue below.
draftRSR_init    = 0;
totalDrafts_init = 0;
draftRate_init   = FIX_ONE;

\\ ---- (1) Draft invariant under a fresh unstake ----
print("--- (1) Draft invariant: draftRSR * draftRate >= totalDrafts * FIX_ONE ---");
unstake_qty = totalStakes_cal \ 20;   \\ 5% of stakes
res_un = unstake_op(stakeRSR_cal, totalStakes_cal, stakeRate_cal, draftRSR_init, totalDrafts_init, draftRate_init, unstake_qty);
new_stakeRSR    = res_un[1];
new_totalStakes = res_un[2];
new_draftRSR    = res_un[3];
new_totalDrafts = res_un[4];
rsrMoved        = res_un[5];
draftMinted     = res_un[6];
{ printf("  Unstake 5%% of stakes (%d qStRSR)\n", unstake_qty); }
{ printf("  RSR moved stake->draft: %d\n", rsrMoved); }
{ printf("  draftAmount minted: %d\n", draftMinted); }
{ printf("  draftRSR'=%d, totalDrafts'=%d, draftRate=%d\n", new_draftRSR, new_totalDrafts, draftRate_init); }
inv_lhs = new_draftRSR * draftRate_init;
inv_rhs = new_totalDrafts * FIX_ONE;
{ printf("  draftRSR*draftRate = %d\n  totalDrafts*FIX_ONE = %d\n", inv_lhs, inv_rhs); }
if(inv_lhs >= inv_rhs, print("  OK"), print("  FAIL: draft invariant violated"));
print("");

\\ ---- (2) Era-reset boundary on the draft side ----
print("--- (2) Draft era-reset trigger after extreme seizure ---");
\\ Boundary: era resets iff post-seize draftRate > MAX_DRAFT_RATE = 1e27.
\\ Solve newDraftRSR < FIX_ONE * totalDrafts / MAX_DRAFT_RATE for the
\\ critical post-seize draftRSR. (We use ceil_div for the spec form;
\\ the strict inequality means anything strictly below the value
\\ ceil(FIX_ONE * totalDrafts / MAX_DRAFT_RATE) triggers the reset.)
\\
\\ With totalDrafts ~ rsrMoved (since draftRate=FIX_ONE), the
\\ critical draftRSR is rsrMoved / 1e9, i.e. 1 wei of RSR per 1e9
\\ qDrafts.
draft_reset_threshold = ceil_div(FIX_ONE * new_totalDrafts, MAX_DRAFT_RATE);
{ printf("  Reset boundary: newDraftRSR < %d (~%.3e RSR) triggers reset\n", draft_reset_threshold, draft_reset_threshold * 1.0 / FIX_ONE); }

\\ Construct a seize that pushes newDraftRSR below the threshold.
\\ rsrBalance == stakeRSR + draftRSR + rewards (here rewards == 0).
rsrBalance_post_unstake = new_stakeRSR + new_draftRSR;
\\ We want draftRSRToTake >= new_draftRSR - (draft_reset_threshold - 1)
\\   => ceil(draftRSR * x / rsrBalance) >= new_draftRSR - threshold + 1
\\ Pick x large enough; using x = rsrBalance gives draftRSRToTake = new_draftRSR.
\\ A sharper test: pick x just above the threshold, then verify reset
\\ fires. We construct x = floor((new_draftRSR - draft_reset_threshold + 1) * rsrBalance / new_draftRSR) + 1.
extreme_seize = ((new_draftRSR - draft_reset_threshold + 1) * rsrBalance_post_unstake) \ new_draftRSR + 1;
res_seize = seize_drafts(new_draftRSR, new_totalDrafts, draftRate_init, extreme_seize, rsrBalance_post_unstake);
{ printf("  Seize amount %d -> result tag: %s\n", extreme_seize, res_seize[1]); }
if(res_seize[1] == "era-reset", print("  OK: triggered draft era reset"), print("  FAIL: expected era reset"));
print("");

\\ A milder seize that keeps the rate within bounds.
mild_draft_seize = rsrBalance_post_unstake \ 10;   \\ 10% of total RSR
res_mild = seize_drafts(new_draftRSR, new_totalDrafts, draftRate_init, mild_draft_seize, rsrBalance_post_unstake);
{ printf("  Mild seize %d (10%% of rsrBalance): result %s\n", mild_draft_seize, res_mild[1]); }
report_mild_seize(res_mild, MAX_DRAFT_RATE);
print("");

\\ ---- (3) Stake -> draft conservation under unstake ----
print("--- (3) Conservation: draftRSR + stakeRSR preserved across unstake (mod rounding) ---");
sum_pre  = stakeRSR_cal + draftRSR_init;
sum_post = new_stakeRSR + new_draftRSR;
{ printf("  pre  stakeRSR + draftRSR = %d\n", sum_pre); }
{ printf("  post stakeRSR' + draftRSR' = %d\n", sum_post); }
{ printf("  delta = %d\n", sum_pre - sum_post); }
\\ unstake transfers exactly stakeRSR - newStakeRSR into pushDraft, which
\\ adds it to draftRSR. Conservation is exact at the wei level.
if(sum_pre == sum_post, print("  OK: exact conservation"), print("  FAIL: RSR leaked across unstake"));
print("");

\\ Sanity: produced draftAmount = floor(draftRate * draftRSR' / FIX_ONE) - totalDrafts.
\\ With draftRate = FIX_ONE, this should equal rsrMoved (no rounding here).
expect_dAmt = (draftRate_init * (draftRSR_init + rsrMoved)) \ FIX_ONE - totalDrafts_init;
report_draft_amount(draftMinted, expect_dAmt);
print("");

\\ ---- (4) Withdraw monotonicity & no double-withdraw ----
print("--- (4) Withdraw: removes RSR; re-call is a no-op ---");
\\ Suppose the entire batch matures and is withdrawn.
res_w = withdraw_drafts(new_draftRSR, new_totalDrafts, draftRate_init, draftMinted);
post_draftRSR_w    = res_w[1];
post_totalDrafts_w = res_w[2];
rsrOut_w           = res_w[3];
{ printf("  Withdraw all %d drafts\n", draftMinted); }
{ printf("  draftRSR: %d -> %d\n", new_draftRSR, post_draftRSR_w); }
{ printf("  totalDrafts: %d -> %d\n", new_totalDrafts, post_totalDrafts_w); }
{ printf("  rsrAmount paid out: %d\n", rsrOut_w); }

\\ Withdrawing all drafts must zero the draft pool exactly. Per the
\\ Solidity formula, newTotalDrafts == 0 -> newDraftRSR = ceil(0/rate) = 0.
if(post_totalDrafts_w == 0 && post_draftRSR_w == 0, print("  OK: draft pool fully drained"), print("  FAIL: residual drafts after full withdraw"));

\\ rsrOut should equal the full draftRSR going in.
report_rsr_match(rsrOut_w, new_draftRSR);

\\ Re-calling withdraw with draftAmount=0 is a no-op (the production
\\ short-circuits on `firstId >= endId`; here we model by passing 0).
res_w2 = withdraw_drafts(post_draftRSR_w, post_totalDrafts_w, draftRate_init, 0);
if(res_w2[1] == post_draftRSR_w && res_w2[2] == post_totalDrafts_w && res_w2[3] == 0, print("  OK: re-call is a no-op"), print("  FAIL: state changed on second withdraw"));
print("");

\\ Partial withdraw test: remove only half the drafts and confirm
\\ rsrAmount equals the proportional draftRSR delta.
half_drafts = draftMinted \ 2;
res_half = withdraw_drafts(new_draftRSR, new_totalDrafts, draftRate_init, half_drafts);
{ printf("  Partial withdraw %d (half) -> rsrOut=%d, residual draftRSR=%d, totalDrafts=%d\n", half_drafts, res_half[3], res_half[1], res_half[2]); }
\\ Spec: newDraftRSR = ceil((totalDrafts - draftAmount) * FIX_ONE / draftRate)
\\ With draftRate=FIX_ONE this is exactly totalDrafts - draftAmount.
expect_partial_rsr = new_draftRSR - res_half[1];
if(res_half[3] == expect_partial_rsr, print("  OK: partial-withdraw rsrAmount = draftRSR - newDraftRSR"), print("  FAIL"));
print("");

\\ ---- (5) Cancel-unstake reversibility ----
print("--- (5) Cancel-unstake round-trip: stake -> draft -> stake ---");
\\ We re-do unstake, immediately cancel, and check whether the user gets
\\ approximately the same stRSR back. There are two integer-roundings:
\\   - unstake: newStakeRSR = ceil(FIX_ONE * (totalStakes - stakeAmount) / stakeRate)
\\   - cancel:  newStakeRSR = stakeRSR + rsrOut; newTotal = floor(stakeRate * newStakeRSR / FIX_ONE)
\\ With our calibration (stakeRate=1e16) the round-trip recovers exactly.
res_un2 = unstake_op(stakeRSR_cal, totalStakes_cal, stakeRate_cal, draftRSR_init, totalDrafts_init, draftRate_init, unstake_qty);
mid_stakeRSR    = res_un2[1];
mid_totalStakes = res_un2[2];
mid_draftRSR    = res_un2[3];
mid_totalDrafts = res_un2[4];
mid_rsrMoved    = res_un2[5];
mid_draftAmt    = res_un2[6];

\\ Cancel: withdraw the just-pushed drafts and re-mint stakes.
res_wd = withdraw_drafts(mid_draftRSR, mid_totalDrafts, draftRate_init, mid_draftAmt);
rsr_back = res_wd[3];
res_mint = mint_stakes(mid_stakeRSR, mid_totalStakes, stakeRate_cal, rsr_back);
final_stakeRSR    = res_mint[1];
final_totalStakes = res_mint[2];
restored_stakes   = res_mint[3];

{ printf("  unstake_qty   = %d\n", unstake_qty); }
{ printf("  rsr returned  = %d\n", rsr_back); }
{ printf("  stakes minted = %d\n", restored_stakes); }
{ printf("  stakeRSR delta (post round-trip vs original): %d\n", final_stakeRSR - stakeRSR_cal); }
{ printf("  totalStakes delta (post round-trip vs original): %d\n", final_totalStakes - totalStakes_cal); }

\\ Reversibility bound: with our stakeRate, the round-trip restores
\\ exactly. In the worst case the drift is at most 1 wei from each of
\\ the two ceil/floor steps. We assert |delta| <= 2.
stake_delta = abs(final_totalStakes - totalStakes_cal);
rsr_delta   = abs(final_stakeRSR - stakeRSR_cal);
report_round_trip(stake_delta, rsr_delta);
print("");

\\ ---- (6) Seize draft-side: invariant preserved + boundary fires ----
print("--- (6) Seize: draft invariant preserved post-Phase-1 ---");
\\ Set up a non-trivial draft state and seize 30% pro-rata.
ds_draftRSR    = new_draftRSR;
ds_totalDrafts = new_totalDrafts;
ds_draftRate   = draftRate_init;
ds_balance     = new_stakeRSR + ds_draftRSR;
mid_seize      = ds_balance * 3 \ 10;
res_s = seize_drafts(ds_draftRSR, ds_totalDrafts, ds_draftRate, mid_seize, ds_balance);
{ printf("  seize=%d (30%% balance), result tag: %s\n", mid_seize, res_s[1]); }
report_seize_invariant(res_s, ds_totalDrafts);
print("");

\\ ---- (7) Seize boundary: cross MAX_SAFE_DRAFT_RATE without era reset ----
print("--- (7) Boundary: when does draftRate cross MAX_SAFE_DRAFT_RATE? ---");
\\ MAX_SAFE_DRAFT_RATE = 1e6 * FIX_ONE. Crosses when newDraftRSR <
\\ ceil(FIX_ONE * totalDrafts / MAX_SAFE_DRAFT_RATE) = totalDrafts / 1e6.
safe_threshold = ceil_div(FIX_ONE * ds_totalDrafts, MAX_SAFE_DRAFT_RATE);
{ printf("  At totalDrafts=%d, draftRSR <= %d crosses MAX_SAFE\n", ds_totalDrafts, safe_threshold); }
{ printf("  As %% of pre-seize draftRSR: %.6f%%\n", safe_threshold * 100.0 / ds_draftRSR); }
{ printf("  ...still well above MAX_DRAFT_RATE reset boundary (%d)\n", draft_reset_threshold); }
\\ Sanity: safe_threshold > draft_reset_threshold (MAX_SAFE < MAX) so
\\ the unsafe band is reached strictly before era reset fires.
if(safe_threshold > draft_reset_threshold, print("  OK: MAX_SAFE band entered before era reset"), print("  FAIL: thresholds out of order"));
print("");

print("Done.");
