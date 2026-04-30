(** CTokenFiatCollateral plugin-specific simulation.

    Mirrors protocol/contracts/plugins/assets/compoundv2/CTokenFiatCollateral.sol
    on top of the abstract base simulation in [Reserve.simulations.Collateral].

    --------------------------------------------------------------- *)

(** WHAT THIS SIM CAPTURES (vs the abstract base in [Collateral.v])

    The abstract base models the shared collateral state machine:
    [Status] / [statusOf] / [markStatus] / [softDefaultStatus] /
    [updateExposed] / [refresh]. The plugin layer adds plugin-specific
    [refPerTok] semantics and [refresh] overrides; this file captures the
    CTokenFiatCollateral overrides.

    CTokenFiatCollateral overrides two pieces of the parent
    AppreciatingFiatCollateral surface:

    1. [underlyingRefPerTok()] (CTokenFiatCollateral.sol#L66-L70).
       Replaces the FIX_ONE default with the cToken-specific
       [exchangeRateStored() << (8 - referenceERC20Decimals - 18)].
       The shift goes through [shiftl_toFix], which is itself
       [shiftl] with an implicit [+18] decimals adjustment, so the
       net shift on the raw [rate] is
       [(8 - referenceERC20Decimals - 18) + 18 = 8 - referenceERC20Decimals].
       For cUSDC (USDC has 6 decimals): shift = +2  -> multiply by 100.
       For cDAI  (DAI has 18 decimals): shift = -10 -> divide by 10^10.

    2. [refresh()] (CTokenFiatCollateral.sol#L44-L63).
       Wraps the parent [refresh()] with a try/catch around
       [exchangeRateCurrent()]. If [exchangeRateCurrent()] reverts
       (typically due to Compound governance pausing accrual), the
       plugin marks DISABLED before delegating to [super.refresh()].
       The [super.refresh()] tail still runs in either branch — it
       handles all hard-default and soft-default checks via the
       parent state machine. *)

(** PRODUCTION DIVERGENCES (also encoded as comments in the lemmas
    that pin them):

    a. The Compound v2 invariant "[exchangeRateStored] is monotone-up"
       is a Compound-Protocol-level property, NOT a CTokenFiatCollateral
       guarantee. The plugin DOES NOT enforce monotonicity; if the
       cToken's exchange rate were to decrease (e.g. via a
       hypothetical exploit on [accrueInterest]), the plugin's
       [underlyingRefPerTok] WOULD report the lower value, the
       parent's [updateExposed] WOULD see [underlying < exposed], and
       the plugin WOULD hard-default. This is the production-faithful
       behaviour: the parent's hard-default branch is itself the
       defense.

    b. The [exchangeRateCurrent()] call in [refresh] is what turns a
       passive [exchangeRateStored()] read into an "accrue-then-read"
       chain. The simulation models the post-accrual rate as the
       single input [rate]; an attacker who manipulates accrual
       (artificially advances the supply rate / borrow rate without
       advancing block.timestamp) would surface as an unusually
       high [rate], which appreciates [exposedReferencePrice] but
       does not default. Whether the manipulation is profitable is
       a Compound-system question, NOT a Reserve plugin question.

    c. The [referenceERC20Decimals == 0] check in the constructor
       (CTokenFiatCollateral.sol#L37) IS modeled here as a [Valid.t]
       precondition — the simulation refuses to instantiate a state
       with [refDecimals = 0]. *)

(** BOUNDARIES — IN scope:
      - Plugin-specific [refPerTok] arithmetic (shift on rate value)
      - Plugin-specific [refresh] override (DISABLED on accrual revert)
      - [Valid.t] extension for the per-plugin storage fields
      - Composition with the abstract Collateral state machine

    BOUNDARIES — OUT of scope (do NOT model):
      - Asset-registry indirection: [erc20] ID is opaque
      - Underlying ERC20 interactions: [rate] taken as input
      - Oracle aggregation: [pegPrice] / [low] direct inputs
      - Reentrancy / access control modifiers
      - Specific token ABI quirks (uint vs int, decimals != 18)
        beyond what the production [referenceERC20Decimals] handles
      - [comp] reward token, [comptroller], [claimRewards]

    Revert coverage:
      Modeled: accrual revert -> DISABLED branch (the [exchangeRateCurrent()]
                catch path).
      Deferred to [Valid.t]: [refDecimals != 0], [rate] in uint256.
      Not modeled: out-of-gas in the cToken call,
                   underlying-token decimals being > 18 (production
                   shiftl_toFix would still work but produce 0),
                   the COMP reward path. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Module CTokenFiatCollateral.

Import FixLib.
Import Collateral.

(** ===== Plugin-specific storage extension =====

    CTokenFiatCollateral adds two effectively-immutable parameters
    on top of the parent [Collateral.State.t]:

      [refDecimals]   — production [referenceERC20Decimals], an integer
                        in [1, 30]. Constructor rejects 0.
      [rateScale]     — derived constant; the divisor that converts
                        [exchangeRateStored()] (whose own scale is
                        [10^(refDecimals + 10)]) into a FIX_ONE-scale
                        ref-per-tok value.
                        Shifted positively when [refDecimals < 8]
                        (multiply), negatively when [refDecimals > 8]
                        (divide).

    Production stores [referenceERC20Decimals] as an [immutable] uint8;
    [rateScale] is computed at refresh time from it. We pre-compute
    [rateScale] here as a derived constant to keep the math closed-form
    and avoid carrying [shiftl] inside every refresh. *)
Module CTokenState.
  Record t : Set := {
    base         : State.t;        (** parent Collateral.State *)
    refDecimals  : Z;              (** uint8: 1..30, !=0 *)
    rateSnapshot : Z;              (** last [exchangeRateStored()] read;
                                       used by witnesses and for an
                                       optional monotonicity claim
                                       across consecutive refreshes. *)
  }.
End CTokenState.

(** Lift the abstract [refresh] preconditions onto the CToken state. *)
Definition base_state (s : CTokenState.t) : State.t := s.(CTokenState.base).

(** ===== Plugin-specific [refPerTok] math =====

    Production: [shiftl_toFix(rate, 8 - refDecimals - 18, FLOOR)],
    which is [shiftl(rate, 8 - refDecimals, FLOOR)] in our
    [+18-stripped] convention.

    Equivalently:
      - if  refDecimals <= 8: rate * 10^(8 - refDecimals)
      - if  refDecimals >  8: rate / 10^(refDecimals - 8) (FLOOR)

    For the sim we expose a closed-form, total-on-Z helper
    [refPerTok_of_rate]; the [shiftl] revert path on
    [refDecimals == 0] is preempted by [Valid.t] (see below). *)
Definition refPerTok_of_rate (rate refDecimals : Z) : Z :=
  if refDecimals <=? 8 then
    rate * (10 ^ (8 - refDecimals))
  else
    rate / (10 ^ (refDecimals - 8)).

(** Headline plugin operation: [underlyingRefPerTok()].

    Pure projection: read the [rate] argument and apply the shift. The
    value of [rate] comes from [ICToken(erc20).exchangeRateStored()]
    on chain; we take it as input. *)
Definition underlyingRefPerTok (s : CTokenState.t) (rate : Z) : Z :=
  refPerTok_of_rate rate s.(CTokenState.refDecimals).

(** ===== Plugin-specific [refresh] override =====

    Production logic (CTokenFiatCollateral.sol#L44-L63):
      try ICToken(erc20).exchangeRateCurrent() {
        // happy path: just call super.refresh()
      } catch {
        markStatus(DISABLED);
        super.refresh();
      }

    The [accrued] flag is the modelled boundary between the two
    paths: [accrued = true] means [exchangeRateCurrent()] succeeded,
    [accrued = false] means it reverted. *)
Definition refresh
    (s : CTokenState.t)
    (rate pegPrice low now : Z)  (** rate = post-accrual exchangeRateStored *)
    (accrued : bool)              (** false if exchangeRateCurrent() reverted *)
    : CTokenState.t :=
  let underlying := refPerTok_of_rate rate s.(CTokenState.refDecimals) in
  (** If accrual reverted, the plugin marks DISABLED *first*, then runs
      super.refresh(). The DISABLED mark sets _whenDefault = now; super's
      refresh re-applies markStatus on the same _whenDefault, but DISABLED
      is terminal so the second mark is a no-op. The composed effect is
      equivalent to: walk the abstract refresh with the natural arguments
      AND additionally apply markStatus(DISABLED) at the end of the chain. *)
  let base_after :=
    Collateral.refresh s.(CTokenState.base) underlying pegPrice low now in
  let base_after_accrual :=
    if accrued then base_after
    else
      {| State.whenDefault           :=
           Collateral.markStatus
             base_after.(State.whenDefault)
             Status.DISABLED now
             base_after.(State.delayUntilDefault);
         State.exposedReferencePrice :=
           base_after.(State.exposedReferencePrice);
         State.delayUntilDefault     :=
           base_after.(State.delayUntilDefault);
         State.revenueShowing        :=
           base_after.(State.revenueShowing);
         State.pegBottom             := base_after.(State.pegBottom);
         State.pegTop                := base_after.(State.pegTop); |} in
  {| CTokenState.base         := base_after_accrual;
     CTokenState.refDecimals  := s.(CTokenState.refDecimals);
     CTokenState.rateSnapshot := rate; |}.

(** ===== Plugin-specific [Valid.t] extension =====

    On top of the parent [Collateral.Valid.t], the CToken layer
    requires:
      - [refDecimals] in [1, 30] — production constructor rejects 0
        (line 37) and CTokens with > 30 decimals are unrealistic in
        production (no deployed cToken has > 18).
      - [rateSnapshot] is uint256 — bounded by the EVM type only;
        no plugin-specific tighter bound. *)
Module Valid.
  Record t (s : CTokenState.t) : Prop := {
    base_valid       : Collateral.Valid.t s.(CTokenState.base);
    refDecimals_pos  : 1 <= s.(CTokenState.refDecimals);
    refDecimals_lim  : s.(CTokenState.refDecimals) <= 30;
    rate_uint256     : 0 <= s.(CTokenState.rateSnapshot) <= UINT256_MAX;
  }.
End Valid.

(** ===== Plugin-specific monotonicity flag =====

    The Compound-Protocol-level guarantee is that [exchangeRateStored]
    is non-decreasing across blocks (modulo the revert / pause case).
    We expose this as a separate predicate — NOT enforced by the
    plugin, but available for callers that have proved it about the
    underlying cToken (e.g. via a Compound-system specification).

    A non-monotone rate would surface to the parent as
    [underlying < exposed], which the parent's hard-default branch
    treats correctly. So this predicate is *not* required for
    [Valid.t] preservation; it only sharpens the conclusion to
    "exposed never decreases under a monotone rate". *)
Definition rate_monotone_step (rate_old rate_new : Z) : Prop :=
  rate_old <= rate_new.

End CTokenFiatCollateral.
