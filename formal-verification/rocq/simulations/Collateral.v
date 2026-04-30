(** Collateral state-machine simulation.

    Mirrors the collateral status state machine implemented in
    protocol/contracts/plugins/assets/FiatCollateral.sol and the hard-default
    [refresh()] update rule from
    protocol/contracts/plugins/assets/AppreciatingFiatCollateral.sol.

    Three pieces:

      [CollateralStatus]       SOUND (0) | IFFY (1) | DISABLED (2)
      [whenDefault]            uint48 sentinel encoding the status:
                                 == NEVER  -> SOUND
                                 >  now    -> IFFY
                                 <= now    -> DISABLED
      [exposedReferencePrice]  cached max ref-per-tok value, monotone-up
                               modulo a single hard-default drop.

    The on-chain function reads [block.timestamp] from the EVM; here we
    pass it as an explicit [now : U256.t] so the simulation is pure.

    [markStatus] follows FiatCollateral.sol#L180-L199 verbatim:
      - if currently DISABLED (whenDefault <= now), no-op (terminal).
      - SOUND     -> whenDefault := NEVER
      - IFFY      -> sum := now + delayUntilDefault
                     if sum >= NEVER -> whenDefault := NEVER
                     else if sum < whenDefault -> whenDefault := sum
                     else no change
      - DISABLED  -> whenDefault := now

    [updateExposed] follows AppreciatingFiatCollateral.sol#L86-L96. It
    returns the new [exposedReferencePrice] paired with a flag indicating
    whether this refresh hard-defaulted. The two outputs are not separable;
    the same comparison ([underlying < exposed]) drives both.

    [refreshHard] composes [updateExposed] with [markStatus(DISABLED)] in
    the hard-default branch; the full refresh() composes [refreshHard] with
    a [refreshSoft] step driven by [pegPrice]. The state machine proofs
    work at the [markStatus]/[updateExposed] level, which is exactly what
    the CAS scripts in cas/collateral/ probe.

    Revert coverage:
      Modeled:  [markStatus] no-ops when already DISABLED ([wd <= now])
                — terminal-state preservation, not a revert.
      Deferred: well-formedness via [Valid.t] (uint48 timestamps,
                uint192 prices, [delayUntilDefault <= 1209600]).
      Not modeled: oracle-staleness reverts, basket-not-set reverts,
                the cross-component reverts on [refresh] from
                BasketHandler / AssetRegistry. Plugin-specific
                overrides in subclasses (CTokenFiatCollateral etc.)
                are entirely out of scope.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module Collateral.

Import FixLib.

Definition NEVER       : Z := 2 ^ 48 - 1.   (* uint48 max sentinel *)
Definition UINT48_MAX  : Z := 2 ^ 48 - 1.

Module Status.
  Inductive t : Set :=
  | SOUND
  | IFFY
  | DISABLED.

  Definition to_Z (s : t) : Z :=
    match s with SOUND => 0 | IFFY => 1 | DISABLED => 2 end.
End Status.

(** [statusOf wd now] decodes the [_whenDefault] sentinel into a status,
    matching FiatCollateral.sol#L168-L176. *)
Definition statusOf (wd now : Z) : Status.t :=
  if wd =? NEVER then Status.SOUND
  else if now <? wd then Status.IFFY
  else Status.DISABLED.

(** [markStatus wd new_status now delayUntilDefault] returns the updated
    [_whenDefault]. Matches FiatCollateral.sol#L180-L199 line-for-line. *)
Definition markStatus
    (wd : Z) (new_status : Status.t) (now delayUntilDefault : Z) : Z :=
  if wd <=? now then wd  (* terminal DISABLED: no-op *)
  else
    match new_status with
    | Status.SOUND => NEVER
    | Status.IFFY =>
        let sum := now + delayUntilDefault in
        if NEVER <=? sum then NEVER
        else if sum <? wd then sum
        else wd
    | Status.DISABLED => now
    end.

(** Soft-default decision (FiatCollateral.sol#L150):
    [pegPrice < pegBottom || pegPrice > pegTop || low == 0] flags IFFY. *)
Definition softDefaultStatus
    (pegPrice low pegBottom pegTop : Z) : Status.t :=
  if orb (orb (pegPrice <? pegBottom) (pegTop <? pegPrice)) (low =? 0) then
    Status.IFFY
  else Status.SOUND.

(** [updateExposed exposed underlying revenueShowing] — the hard-default
    update from AppreciatingFiatCollateral.sol#L86-L96.

    Returns [(new_exposed, defaulted)] where [defaulted] is true iff
    [underlying < exposed] (the hard-default branch). *)
Definition updateExposed
    (exposed underlying revenueShowing : Z) : Z * bool :=
  let hidden := FixLib.mul underlying revenueShowing RoundingMode.FLOOR in
  if underlying <? exposed then
    (underlying, true)
  else if exposed <? hidden then
    (hidden, false)
  else
    (exposed, false).

(** Full collateral state, as the relevant subset of FiatCollateral +
    AppreciatingFiatCollateral storage. *)
Module State.
  Record t : Set := {
    whenDefault            : Z;     (** uint48; NEVER initially *)
    exposedReferencePrice  : Z;     (** {ref/tok}; uint192; 0 initially *)
    delayUntilDefault      : Z;     (** {s} uint48; immutable *)
    revenueShowing         : Z;     (** {1} uint192; FIX_ONE - revenueHiding *)
    pegBottom              : Z;     (** {target/ref}; uint192; immutable *)
    pegTop                 : Z;     (** {target/ref}; uint192; immutable *)
  }.
End State.

(** The composed refresh() function. Splits into the hard-default branch
    (compares underlyingRefPerTok against the cached max) and the soft-default
    branch (compares pegPrice against pegBottom/pegTop). *)
Definition refresh
    (st : State.t) (underlying pegPrice low now : Z) : State.t :=
  let '(new_exposed, defaulted) :=
    updateExposed st.(State.exposedReferencePrice)
                  underlying st.(State.revenueShowing) in
  let wd_after_hard :=
    if defaulted then
      markStatus st.(State.whenDefault) Status.DISABLED now
                 st.(State.delayUntilDefault)
    else st.(State.whenDefault) in
  let soft :=
    softDefaultStatus pegPrice low st.(State.pegBottom) st.(State.pegTop) in
  let wd_after_soft :=
    markStatus wd_after_hard soft now st.(State.delayUntilDefault) in
  {| State.whenDefault           := wd_after_soft;
     State.exposedReferencePrice := new_exposed;
     State.delayUntilDefault     := st.(State.delayUntilDefault);
     State.revenueShowing        := st.(State.revenueShowing);
     State.pegBottom             := st.(State.pegBottom);
     State.pegTop                := st.(State.pegTop); |}.

(** Validity predicate for a collateral state. *)
Module Valid.
  Record t (st : State.t) : Prop := {
    wd_uint48 :
      0 <= st.(State.whenDefault) <= UINT48_MAX;
    exposed_uint192 :
      0 <= st.(State.exposedReferencePrice) <= FIX_MAX;
    delay_uint48 :
      0 <= st.(State.delayUntilDefault) <= 1209600;  (** 2 weeks per L10 *)
    revShow_uint192 :
      0 <= st.(State.revenueShowing) <= FIX_ONE;
  }.
End Valid.

End Collateral.
