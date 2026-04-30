\\ status_state_machine.gp
\\
\\ CAS-side validation of the CollateralStatus state machine implemented in
\\ FiatCollateral / AppreciatingFiatCollateral. Probes:
\\
\\   SM-1  status() decoding from _whenDefault is correct at the
\\         block.timestamp == _whenDefault boundary (DISABLED, not IFFY)
\\   SM-2  DISABLED is terminal: markStatus(SOUND|IFFY) after default is no-op
\\   SM-3  markStatus(IFFY) is monotone in the deadline: a second IFFY mark
\\         cannot push _whenDefault later than the first
\\   SM-4  markStatus(SOUND) from IFFY clears the deadline (recovery path)
\\   SM-5  markStatus(DISABLED) is instantaneous: status flips on this block
\\   SM-6  Soft-default trigger: pegPrice strictly outside [pegBottom, pegTop]
\\         marks IFFY; pegPrice == pegBottom and pegPrice == pegTop are SOUND
\\   SM-7  No SOUND -> DISABLED transition skipping IFFY for soft default;
\\         the only direct SOUND -> DISABLED is hard default
\\   SM-8  Soft-default cure cycle: IFFY at t0 + recovered price at
\\         t0 + delayUntilDefault - 1 -> SOUND, deadline cleared
\\   SM-9  Soft default elapses at exactly t0 + delayUntilDefault: DISABLED
\\
\\ References:
\\   protocol/contracts/plugins/assets/FiatCollateral.sol
\\     status()                  L168-176  (boundary: > vs <=)
\\     markStatus()              L180-199
\\   protocol/contracts/plugins/assets/AppreciatingFiatCollateral.sol
\\     refresh()                 L79-136

print("=== CollateralStatus state machine — CAS validation ===");
print("");

FIX_ONE     = 10^18;
FIX_MAX     = 2^192 - 1;
UINT48_MAX  = 2^48 - 1;          \\ NEVER sentinel
NEVER       = UINT48_MAX;

\\ ---- Calibration: Aave V3 USDC-style appreciating collateral ----
\\ delayUntilDefault = 24h, defaultThreshold = 5%, targetPerRef = 1.
delayUntilDefault = 86400;       \\ {s} 24h
defaultThreshold  = FIX_ONE / 20;\\ {1} 5%
targetPerRef      = FIX_ONE;     \\ {target/ref} = 1
\\ pegBottom/pegTop computed as in FiatCollateral constructor (L88-93).
peg_delta = (targetPerRef * defaultThreshold) \ FIX_ONE;
pegBottom = targetPerRef - peg_delta;
pegTop    = targetPerRef + peg_delta;

t0 = 1700000000;                 \\ arbitrary anchor block.timestamp

\\ ---- Solidity-faithful semantics ----

\\ status_of(_whenDefault, now) replicates FiatCollateral.status():
\\   _whenDefault == NEVER         -> SOUND
\\   _whenDefault > now            -> IFFY
\\   _whenDefault <= now           -> DISABLED
\\ Encoded as 0=SOUND, 1=IFFY, 2=DISABLED to match the enum.
status_of(wd, now) = if(wd == NEVER, 0, if(wd > now, 1, 2));

\\ markStatus(state, status_, now): returns new _whenDefault per L180-199.
\\ - if currently DISABLED (_whenDefault <= now), no-op (terminal).
\\ - SOUND  -> _whenDefault = NEVER
\\ - IFFY   -> sum = now + delayUntilDefault; if sum >= NEVER, NEVER;
\\             else if sum < _whenDefault, sum; else no change
\\ - DISABLED -> _whenDefault = now
mark(wd, st, now, dud) = { my(sum); if(wd <= now, return(wd)); if(st == 0, return(NEVER)); if(st == 1, sum = now + dud; if(sum >= NEVER, return(NEVER)); if(sum < wd, return(sum)); return(wd)); if(st == 2, return(now)); wd; }

\\ Soft-default decision used by both refresh() implementations:
\\   pegPrice < pegBottom || pegPrice > pegTop || low == 0 -> IFFY else SOUND.
soft_default_status(pegPrice, low) = if(pegPrice < pegBottom || pegPrice > pegTop || low == 0, 1, 0);

\\ ---- SM-1: boundary at block.timestamp == _whenDefault ----
print("--- SM-1: status() boundary at now == _whenDefault ---");
wd_test = t0 + delayUntilDefault;
s_before = status_of(wd_test, wd_test - 1);
s_at     = status_of(wd_test, wd_test);
s_after  = status_of(wd_test, wd_test + 1);
{ printf("  now = wd - 1 -> status = %d (expect 1=IFFY)\n", s_before); }
{ printf("  now = wd     -> status = %d (expect 2=DISABLED)\n", s_at); }
{ printf("  now = wd + 1 -> status = %d (expect 2=DISABLED)\n", s_after); }
sm1_ok = (s_before == 1) && (s_at == 2) && (s_after == 2);
if(sm1_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-2: DISABLED is terminal ----
print("--- SM-2: DISABLED is terminal (markStatus is no-op once defaulted) ---");
\\ Default at t0; try to recover via markStatus(SOUND/IFFY) at t0 + 1s.
wd_disabled = mark(NEVER, 2, t0, delayUntilDefault);  \\ DISABLED at t0
wd_try_sound = mark(wd_disabled, 0, t0 + 1, delayUntilDefault);
wd_try_iffy  = mark(wd_disabled, 1, t0 + 1, delayUntilDefault);
{ printf("  After DISABLED at t0:           _whenDefault = %d\n", wd_disabled); }
{ printf("  After markStatus(SOUND) at t0+1: _whenDefault = %d (expect unchanged)\n", wd_try_sound); }
{ printf("  After markStatus(IFFY)  at t0+1: _whenDefault = %d (expect unchanged)\n", wd_try_iffy); }
sm2_ok = (wd_try_sound == wd_disabled) && (wd_try_iffy == wd_disabled);
if(sm2_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-3: markStatus(IFFY) deadline is monotone (cannot extend) ----
print("--- SM-3: markStatus(IFFY) cannot push _whenDefault later ---");
\\ First IFFY at t0 -> deadline t0 + dud.
wd_a = mark(NEVER, 1, t0, delayUntilDefault);
\\ Second IFFY at t0 + 100 -> sum = t0 + 100 + dud > wd_a; should NOT update.
wd_b = mark(wd_a, 1, t0 + 100, delayUntilDefault);
\\ Third IFFY at t0 - 100 (going back in simulated time) -> sum < wd_a; should update.
wd_c = mark(wd_a, 1, t0 - 100, delayUntilDefault);
{ printf("  IFFY at t0:        _whenDefault = %d (= t0 + dud = %d)\n", wd_a, t0 + delayUntilDefault); }
{ printf("  IFFY at t0+100:    _whenDefault = %d (expect unchanged)\n", wd_b); }
{ printf("  IFFY at t0-100:    _whenDefault = %d (expect = t0-100+dud = %d)\n", wd_c, t0 - 100 + delayUntilDefault); }
sm3_ok = (wd_a == t0 + delayUntilDefault) && (wd_b == wd_a) && (wd_c == t0 - 100 + delayUntilDefault);
if(sm3_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-4: IFFY -> SOUND clears deadline ----
print("--- SM-4: markStatus(SOUND) clears IFFY deadline (recovery) ---");
wd_iffy = mark(NEVER, 1, t0, delayUntilDefault);
wd_recovered = mark(wd_iffy, 0, t0 + 1, delayUntilDefault);
s_recovered = status_of(wd_recovered, t0 + 2);
{ printf("  IFFY -> SOUND: _whenDefault = %d (expect NEVER = %d)\n", wd_recovered, NEVER); }
{ printf("  status() after recovery = %d (expect 0=SOUND)\n", s_recovered); }
sm4_ok = (wd_recovered == NEVER) && (s_recovered == 0);
if(sm4_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-5: hard default is instantaneous ----
print("--- SM-5: markStatus(DISABLED) flips status this block ---");
wd_hard = mark(NEVER, 2, t0, delayUntilDefault);
s_hard = status_of(wd_hard, t0);
{ printf("  markStatus(DISABLED) at t0: _whenDefault = %d, status = %d\n", wd_hard, s_hard); }
sm5_ok = (wd_hard == t0) && (s_hard == 2);
if(sm5_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-6: peg deviation boundary ----
print("--- SM-6: pegPrice deviation -> IFFY at strict boundary ---");
\\ Soft-default decision is on strict comparison: pegPrice < pegBottom triggers,
\\ pegPrice == pegBottom does not. Same for pegTop.
low_ok = FIX_ONE / 2;            \\ any nonzero
s_below_strict = soft_default_status(pegBottom - 1, low_ok);
s_at_bottom    = soft_default_status(pegBottom,     low_ok);
s_at_top       = soft_default_status(pegTop,        low_ok);
s_above_strict = soft_default_status(pegTop + 1,    low_ok);
s_low_zero     = soft_default_status(targetPerRef,  0);
{ printf("  pegBottom = %d, pegTop = %d (5%% of FIX_ONE)\n", pegBottom, pegTop); }
{ printf("  pegPrice = pegBottom - 1 -> %d (expect 1=IFFY)\n", s_below_strict); }
{ printf("  pegPrice = pegBottom     -> %d (expect 0=SOUND, boundary inclusive)\n", s_at_bottom); }
{ printf("  pegPrice = pegTop        -> %d (expect 0=SOUND, boundary inclusive)\n", s_at_top); }
{ printf("  pegPrice = pegTop + 1    -> %d (expect 1=IFFY)\n", s_above_strict); }
{ printf("  low = 0 inside band      -> %d (expect 1=IFFY, unpriced low)\n", s_low_zero); }
sm6_ok = (s_below_strict == 1) && (s_at_bottom == 0) && (s_at_top == 0) && (s_above_strict == 1) && (s_low_zero == 1);
if(sm6_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-7: no SOUND -> DISABLED skipping IFFY for soft default ----
print("--- SM-7: soft default cannot skip IFFY ---");
\\ A single refresh() with pegPrice outside threshold calls markStatus(IFFY),
\\ which yields _whenDefault = now + dud > now, i.e. status() = IFFY this block.
\\ Verify across a sweep of (pegDeviation, now) inputs.
sm7_violations = 0;
{
  pegs = [pegBottom - 10^15, pegBottom - 1, pegTop + 1, pegTop + 10^15];
  ts   = [t0, t0 + 60, t0 + 3600, t0 + delayUntilDefault \ 2];
  for(p_idx = 1, 4,
    pp = pegs[p_idx];
    for(t_idx = 1, 4,
      now = ts[t_idx];
      \\ Start SOUND, run one refresh-equivalent.
      s_pre = soft_default_status(pp, low_ok);
      wd_after = mark(NEVER, s_pre, now, delayUntilDefault);
      s_after  = status_of(wd_after, now);
      \\ Soft default must produce IFFY (1), never DISABLED (2) on this block.
      if(s_after == 2, sm7_violations = sm7_violations + 1);
      if(s_pre == 1 && s_after != 1, sm7_violations = sm7_violations + 1);
    );
  );
}
{ printf("  Soft-default sweep violations (would skip IFFY): %d\n", sm7_violations); }
if(sm7_violations == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-8: soft-default cure cycle ----
print("--- SM-8: IFFY at t0 then SOUND price before deadline -> recovery ---");
\\ Step 1: soft default at t0.
wd_step1 = mark(NEVER, 1, t0, delayUntilDefault);
\\ Step 2: at t0 + dud - 1, peg is back in band -> SOUND.
t_recover = t0 + delayUntilDefault - 1;
s_decision = soft_default_status(targetPerRef, low_ok);
wd_step2 = mark(wd_step1, s_decision, t_recover, delayUntilDefault);
s_after_recover = status_of(wd_step2, t_recover);
{ printf("  After soft default at t0:                       _whenDefault = %d\n", wd_step1); }
{ printf("  Recovery decision at t0+dud-1: status_ = %d (expect 0)\n", s_decision); }
{ printf("  After recovery markStatus:                       _whenDefault = %d (expect NEVER)\n", wd_step2); }
{ printf("  status() at t_recover = %d (expect 0=SOUND)\n", s_after_recover); }
sm8_ok = (s_decision == 0) && (wd_step2 == NEVER) && (s_after_recover == 0);
if(sm8_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- SM-9: soft-default deadline at exactly t0 + delayUntilDefault ----
print("--- SM-9: soft default elapses at now == t0 + delayUntilDefault ---");
wd_soft = mark(NEVER, 1, t0, delayUntilDefault);
s_just_before = status_of(wd_soft, t0 + delayUntilDefault - 1);
s_at_deadline = status_of(wd_soft, t0 + delayUntilDefault);
s_after_dead  = status_of(wd_soft, t0 + delayUntilDefault + 1);
{ printf("  _whenDefault = %d (= t0 + dud)\n", wd_soft); }
{ printf("  now = wd - 1 -> status = %d (expect 1=IFFY)\n", s_just_before); }
{ printf("  now = wd     -> status = %d (expect 2=DISABLED, boundary flip)\n", s_at_deadline); }
{ printf("  now = wd + 1 -> status = %d (expect 2=DISABLED)\n", s_after_dead); }
sm9_ok = (s_just_before == 1) && (s_at_deadline == 2) && (s_after_dead == 2);
if(sm9_ok, print("  OK"), print("  FAIL"));
print("");

\\ ---- Sanity: MAX_DELAY_UNTIL_DEFAULT (2 weeks) does not overflow uint48 ----
print("--- Sanity: now + MAX_DELAY_UNTIL_DEFAULT fits in uint48 ---");
MAX_DUD = 1209600;               \\ 2 weeks per L10 of FiatCollateral.sol
\\ Worst case: now near uint48 max. The contract guards via `if (sum >= NEVER)`.
sum_at_extreme = (UINT48_MAX - 1) + MAX_DUD;
{ printf("  sum at now = NEVER-1 = %d (overflows uint48: %d)\n", sum_at_extreme, sum_at_extreme >= NEVER); }
\\ Verify mark() pins to NEVER (the guard at L191).
wd_guarded = mark(NEVER, 1, NEVER - 1, MAX_DUD);
{ printf("  mark(NEVER, IFFY, NEVER-1, MAX_DUD) = %d (expect NEVER = %d)\n", wd_guarded, NEVER); }
sanity_ok = (wd_guarded == NEVER);
if(sanity_ok, print("  OK"), print("  FAIL"));
print("");

print("Done.");
