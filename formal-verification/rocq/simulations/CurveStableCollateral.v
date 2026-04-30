(** CurveStableCollateral plugin-specific simulation.

    Mirrors protocol/contracts/plugins/assets/curve/CurveStableCollateral.sol
    on top of the abstract base simulation in [Reserve.simulations.Collateral].

    --------------------------------------------------------------- *)

(** WHAT THIS SIM CAPTURES (vs the abstract base in [Collateral.v])

    The abstract base models the shared collateral state machine:
    [Status] / [statusOf] / [markStatus] / [softDefaultStatus] /
    [updateExposed] / [refresh]. The plugin layer adds plugin-specific
    [refPerTok] semantics and [refresh] overrides; this file captures the
    CurveStableCollateral overrides.

    CurveStableCollateral is structurally different from
    AppreciatingFiatCollateral in two important ways:

    1. [underlyingRefPerTok()] (CurveStableCollateral.sol#L184-L186).
       Returns [_safeWrap(curvePool.get_virtual_price())] directly.
       No decimal shift. The Curve LP token is by convention 18-decimal
       and [get_virtual_price] is itself 18-decimal-scaled, so the
       FIX_ONE alignment is already correct.

    2. [refresh()] (CurveStableCollateral.sol#L108-L167).
       Inlines the AppreciatingFiatCollateral.refresh logic instead
       of [super.refresh()]ing into it; adds extra per-token
       depeg checks via [_anyDepeggedInPool] / [_anyDepeggedOutsidePool].

       The hard-default trigger is INHERITED from the parent shape:
       [underlying < exposedReferencePrice] -> DISABLED. There is NO
       additional Curve-specific hard-default threshold; the
       revenue-hiding band IS the threshold.

       The soft-default trigger is EXTENDED: in addition to the
       parent's [pegPrice < pegBottom || pegPrice > pegTop || low == 0],
       Curve has [_anyDepeggedInPool] (any per-token oracle outside
       its own band) and [_anyDepeggedOutsidePool] (overridable for
       metapools). *)

(** PRODUCTION DIVERGENCES that motivated this sim:

    a. Curve [get_virtual_price] is NOT monotonically increasing in
       production. A whale's imbalanced withdrawal can DECREASE the
       virtual price even with no fee anomaly; the StableSwap
       invariant is convex but only globally, not pointwise under
       all withdrawal patterns. The defense mechanism is the parent's
       hard-default branch: any decrease past the revenue-hiding
       band ([underlying < exposedReferencePrice]) flips the plugin
       to DISABLED on the same refresh.

    b. The plugin's [tryPrice] uses spot AMM balances (it admits in
       the comments that this is MEV-manipulable). The pegPrice is
       hard-coded to 0 for stable pools, since there's no "single peg"
       to surface. This means the parent's [pegPrice < pegBottom]
       check is always vacuously true unless [pegBottom > 0]; in
       production the Curve plugin sets pegBottom = pegTop = 0 by
       passing defaultThreshold = 0 — or rather, it DOESN'T,
       because the constructor enforces [defaultThreshold != 0]
       (line 47). So pegBottom > 0 always; the parent's peg check
       always reports IFFY. The Curve plugin works around this by
       ALSO applying the [_anyDepeggedInPool] soft-default trigger,
       which is the actual defense. We model this faithfully.

    c. The [_anyDepeggedInPool] check loops over [nTokens] underlying
       tokens, each with its own [(low_i, high_i)] oracle pair, and
       compares [(low_i + high_i) / 2] against the SHARED
       [pegBottom, pegTop] band. We model this as a single Boolean
       input [poolDepegged], abstracting over nTokens. *)

(** BOUNDARIES — IN scope:
      - Plugin-specific [refPerTok] (passthrough of virtual price).
      - Plugin-specific [refresh] override (inlined from parent +
        per-token depeg check).
      - Plugin Valid.t extension.
      - Composition with the abstract Collateral state machine.

    BOUNDARIES — OUT of scope (do NOT model):
      - The Curve StableSwap invariant itself (D and the
        Newton-iteration Y solver).
      - Per-token oracle aggregation (nTokens, _anyDepeggedInPool's
        for-loop). We take the aggregate Boolean outcome.
      - Metapool extension via [_anyDepeggedOutsidePool] override.
      - Spot vs MEV-resistant pricing. tryPrice math is not modeled
        (only the resulting (low, high, pegPrice = 0) tuple).
      - CRV / CVX reward token surface; gauge wrappers.
      - Reentrancy / access control modifiers.

    Revert coverage:
      Modeled: get_virtual_price() revert -> DISABLED branch
                (the [pricedRevert] flag).
                tryPrice() revert -> IFFY branch.
                Inner-pool oracle revert in _anyDepeggedInPool ->
                  surfaced via [poolDepegged = true] equivalence.
      Deferred to [Valid.t]: virtualPrice in uint192,
                             pegBottom > 0 (constructor enforces).
      Not modeled: gas exhaustion, reentrancy, the Curve pool
                contract's own reverts beyond the boolean
                [pricedRevert] flag. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Local Open Scope Z_scope.

Module CurveStableCollateral.

Import FixLib.
Import Collateral.

(** ===== Plugin-specific storage extension =====

    CurveStableCollateral adds two effectively-immutable parameters
    on top of the parent [Collateral.State.t]:

      [virtualPriceLast] — the last successfully-read virtual price.
                           Not stored on chain (the plugin reads it
                           fresh each call), but tracked here so that
                           the simulation can express "the last refresh
                           saw virtualPrice = v".

      [poolNTokens]     — number of tokens in the Curve pool, in
                           [2, 4]. Not directly used by the closed-form
                           math but a Valid.t precondition because
                           [_anyDepeggedInPool] iterates over [nTokens].

    Production has neither field; the simulation introduces them as
    pure ghost fields to express witness-level claims and chain
    properties. *)
Module CurveState.
  Record t : Set := {
    base             : State.t;
    virtualPriceLast : Z;        (** {ref/tok}; uint192 *)
    poolNTokens      : Z;        (** uint8: 2..4 *)
  }.
End CurveState.

(** ===== Plugin-specific [underlyingRefPerTok] =====

    Production: [_safeWrap(curvePool.get_virtual_price())]. We model
    this as a passthrough taking the price as input.

    The [_safeWrap] revert path is captured by the [pricedRevert]
    flag in [refresh]; here we just expose the value. *)
Definition underlyingRefPerTok (virtualPrice : Z) : Z := virtualPrice.

(** ===== Plugin-specific [refresh] override =====

    Production logic (CurveStableCollateral.sol#L108-L167):
      try this.underlyingRefPerTok() returns (vp) {
        // hard-default check
        if (vp < exposed) { exposed = vp; markStatus(DISABLED); }
        else if (vp * revenueShowing > exposed) { exposed = vp * revShowing; }

        try this.tryPrice() returns (low, high, pegPrice) {
          // soft default check
          if (low == 0 || _anyDepeggedInPool() || _anyDepeggedOutsidePool())
            markStatus(IFFY);
          else
            markStatus(SOUND);
        } catch { markStatus(IFFY); }
      } catch { markStatus(DISABLED); }

    Modelled inputs:
      [virtualPrice]   — the post-call get_virtual_price() value;
                         only consulted when [pricedRevert = false].
      [low]            — passed through to the parent soft-default check.
      [pricedRevert]   — true iff get_virtual_price() reverted on this
                         refresh; mirrors the outer try/catch.
      [pricedRevert_inner] — true iff tryPrice() reverted on this
                         refresh; mirrors the inner try/catch.
      [poolDepegged]   — Boolean: result of [_anyDepeggedInPool() ||
                         _anyDepeggedOutsidePool()]. Aggregates the
                         per-token loop. *)
Definition refresh
    (s : CurveState.t)
    (virtualPrice low now : Z)
    (pricedRevert : bool)        (** outer get_virtual_price() revert *)
    (pricedRevert_inner : bool)  (** inner tryPrice() revert *)
    (poolDepegged : bool)        (** _anyDepeggedInPool() ||
                                     _anyDepeggedOutsidePool() *)
    : CurveState.t :=
  if pricedRevert then
    (** Outer revert -> DISABLED, no inner work performed. *)
    let new_wd :=
      Collateral.markStatus
        s.(CurveState.base).(State.whenDefault)
        Collateral.Status.DISABLED now
        s.(CurveState.base).(State.delayUntilDefault) in
    {| CurveState.base :=
         {| State.whenDefault           := new_wd;
            State.exposedReferencePrice :=
              s.(CurveState.base).(State.exposedReferencePrice);
            State.delayUntilDefault     :=
              s.(CurveState.base).(State.delayUntilDefault);
            State.revenueShowing        :=
              s.(CurveState.base).(State.revenueShowing);
            State.pegBottom             :=
              s.(CurveState.base).(State.pegBottom);
            State.pegTop                :=
              s.(CurveState.base).(State.pegTop); |};
       CurveState.virtualPriceLast := s.(CurveState.virtualPriceLast);
       CurveState.poolNTokens      := s.(CurveState.poolNTokens); |}
  else
    (** Outer success: do the parent's hard-default check; then
        either take the parent's soft-default-on-tryPrice-success
        path (with the extended [poolDepegged] disjunct) or the
        IFFY-on-tryPrice-revert branch. *)
    let underlying := underlyingRefPerTok virtualPrice in
    let '(new_exposed, defaulted) :=
      Collateral.updateExposed
        s.(CurveState.base).(State.exposedReferencePrice)
        underlying s.(CurveState.base).(State.revenueShowing) in
    let wd_after_hard :=
      if defaulted then
        Collateral.markStatus
          s.(CurveState.base).(State.whenDefault)
          Collateral.Status.DISABLED now
          s.(CurveState.base).(State.delayUntilDefault)
      else s.(CurveState.base).(State.whenDefault) in
    let soft_iffy :=
      if pricedRevert_inner then true
      else (low =? 0) || poolDepegged in
    let soft :=
      if soft_iffy then Collateral.Status.IFFY else Collateral.Status.SOUND in
    let wd_after_soft :=
      Collateral.markStatus wd_after_hard soft now
        s.(CurveState.base).(State.delayUntilDefault) in
    {| CurveState.base :=
         {| State.whenDefault           := wd_after_soft;
            State.exposedReferencePrice := new_exposed;
            State.delayUntilDefault     :=
              s.(CurveState.base).(State.delayUntilDefault);
            State.revenueShowing        :=
              s.(CurveState.base).(State.revenueShowing);
            State.pegBottom             :=
              s.(CurveState.base).(State.pegBottom);
            State.pegTop                :=
              s.(CurveState.base).(State.pegTop); |};
       CurveState.virtualPriceLast := virtualPrice;
       CurveState.poolNTokens      := s.(CurveState.poolNTokens); |}.

(** ===== The hard-default boundary as a closed predicate =====

    Convenient witness for the CAS scripts: the plugin hard-defaults
    iff [virtualPrice < exposedReferencePrice]. *)
Definition hardDefaultTriggered
    (s : CurveState.t) (virtualPrice : Z) : bool :=
  virtualPrice <? s.(CurveState.base).(State.exposedReferencePrice).

(** ===== Plugin-specific [Valid.t] extension =====

    On top of the parent [Collateral.Valid.t]:
      - [virtualPriceLast]      uint192 (FIX_MAX bound).
      - [poolNTokens]           in [2, 4]: production Curve stable
        pools have 2-4 tokens.
      - [pegBottom > 0]         constructor enforces defaultThreshold
        != 0 (line 47), so pegBottom > 0 because pegBottom =
        targetPerRef - delta where delta = targetPerRef *
        defaultThreshold / FIX_ONE > 0 implies pegBottom < targetPerRef
        but doesn't directly imply pegBottom > 0 — production sets
        targetPerRef = FIX_ONE for stable pools so pegBottom = FIX_ONE
        - delta. With delta < FIX_ONE we get pegBottom > 0. We require
        this here as an explicit invariant. *)
Module Valid.
  Record t (s : CurveState.t) : Prop := {
    base_valid       : Collateral.Valid.t s.(CurveState.base);
    vpLast_uint192   : 0 <= s.(CurveState.virtualPriceLast) <= FIX_MAX;
    nTokens_min      : 2 <= s.(CurveState.poolNTokens);
    nTokens_max      : s.(CurveState.poolNTokens) <= 4;
    pegBottom_pos    : 0 < s.(CurveState.base).(State.pegBottom);
  }.
End Valid.

End CurveStableCollateral.
