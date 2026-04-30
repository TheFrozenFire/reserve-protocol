(** BackingManager simulation.

    Mirrors the math in protocol/contracts/p1/BackingManager.sol —
    specifically the [forwardRevenue] accounting block, lines 218-262.
    Captures the post-#1283 mitigation that switched [needed]'s rounding
    mode from FLOOR (default) to CEIL, so the BackingManager never
    under-charges when forwarding revenue.

    Production exposes [forwardRevenue] as a single state-mutating
    function; for verification we slice it into two pure pieces:

      computeNewBasketsAndNeeded(basketsHeldBottom, basketsNeeded)
        - Returns the new (basketsNeeded, mintAmount, needed) tuple.
        - basketsNeeded' = max(basketsNeeded, basketsHeld_bottom / (1+buf))
        - mintAmount     = basketsNeeded' - basketsNeeded   (>= 0)
        - needed         = CEIL(basketsNeeded' * (1+buf) / FIX_ONE)

      computeSurplusSplit(quantity, bal, decimals, rTokenTotal, rsrTotal)
        - Per-asset split for forward-revenue distribution.
        - When bal <= req, returns (0, 0, 0).
        - Else delta := shiftl_toUint(bal - req, decimals)
              tps   := delta / (rTokenTotal + rsrTotal)
              if tps == 0: dust = delta, both shares = 0
              else: rsrShare = tps * rsrTotal,
                    rTokShare = tps * rTokenTotal,
                    dust = delta - (rsrShare + rTokShare).

    Both functions match the harness in
    formal-verification/contracts/BackingManagerMathHarness.sol exactly.

    Result.t is included for future revert-bearing extensions
    (e.g. totalShares == 0 will revert in production).

    Revert coverage:
      Modeled:  [computeSurplusSplit] returns [Result.Revert] when
                [totalShares = 0] (matches the production
                [require(totalShares > 0)] before the per-asset
                division).
      Deferred: input bounds via [Valid.bufferInputs] (uint192 on
                each scalar, [backingBuffer <= MAX_BACKING_BUFFER]).
      Not modeled: the rest of [forwardRevenue] — auth, RToken
                interactions, basket-not-ready guards, recollateralization
                state-machine transitions. The full [manageTokens] flow
                is also out of scope. This simulation is the math
                kernel only; see ../../notes/simulation_fidelity_audit.md
                for the per-domain summary.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module BackingManager.

Import FixLib.

(** Maximum backing buffer per BackingManager.sol#L34. *)
Definition MAX_BACKING_BUFFER : Z := FIX_ONE.

(** Two-constructor result mirroring the upstream simulation pattern. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Output of [computeNewBasketsAndNeeded]: the updated basket-buffer
    state used by [forwardRevenue] before walking the asset list. *)
Module BasketState.
  Record t : Set := {
    basketsNeeded : U256.t;   (** {BU} new basketsNeeded, uint192 *)
    mintAmount    : U256.t;   (** {qRTok} amount to mint for revenue *)
    needed        : U256.t;   (** {BU} CEIL-rounded buffer-adjusted target *)
  }.
End BasketState.

(** Output of [computeSurplusSplit]: how the per-asset delta is split
    among RSR-side, RToken-side, and dust. *)
Module SurplusSplit.
  Record t : Set := {
    rsrAmount    : U256.t;   (** {qTok} forwarded to rsrTrader *)
    rTokenAmount : U256.t;   (** {qTok} forwarded to rTokenTrader *)
    dust         : U256.t;   (** {qTok} retained as dust *)
  }.
End SurplusSplit.

(** [shiftl_toUint(x, decimals)] for [decimals >= 0]: multiply by 10^decimals.

    Production semantics: positive [decimals] multiplies, negative divides
    with FLOOR rounding by default. The harness only takes positive
    asset decimals (uint8), so we model the positive branch. The full
    bounded version with overflow is in [FixLib.shiftl]; this is the
    pure-Z algebraic kernel. *)
Definition shiftl_toUint (x : Z) (decimals : Z) : Z :=
  if decimals <? 0 then x / (10 ^ (- decimals))
  else x * (10 ^ decimals).

(** [computeNewBasketsAndNeeded(basketsHeldBottom, basketsNeeded, backingBuffer)]
    Source: BackingManager.sol#L218-L225 + harness#L42-L54. *)
Definition computeNewBasketsAndNeeded
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t)
    : BasketState.t :=
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  let basketsNeeded' :=
    if basketsNeeded <? baskets then baskets else basketsNeeded in
  let mintAmount :=
    if basketsNeeded <? baskets then baskets - basketsNeeded else 0 in
  let needed :=
    FixLib.mul basketsNeeded' (FIX_ONE + backingBuffer) RoundingMode.CEIL in
  {| BasketState.basketsNeeded := basketsNeeded';
     BasketState.mintAmount    := mintAmount;
     BasketState.needed        := needed |}.

(** [computeSurplusSplit(quantity, bal, decimals, rTokenTotal, rsrTotal, needed)]
    Source: BackingManager.sol#L240-L262 + harness#L59-L86.

    When [totalShares = 0] production reverts; the harness requires it.
    The pure simulation exposes that as [Result.Revert]. *)
Definition computeSurplusSplit
    (needed quantity bal : U256.t)
    (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    : Result.t SurplusSplit.t :=
  let req := FixLib.mul needed quantity RoundingMode.CEIL in
  if bal <=? req then
    Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 0;
    |}
  else
    let delta := shiftl_toUint (bal - req) decimals in
    let totalShares := rTokenTotal + rsrTotal in
    if totalShares =? 0 then
      Result.Revert 0 32
    else
      let tokensPerShare := delta / totalShares in
      if tokensPerShare =? 0 then
        Result.Success {|
          SurplusSplit.rsrAmount    := 0;
          SurplusSplit.rTokenAmount := 0;
          SurplusSplit.dust         := delta;
        |}
      else
        let rsrAmount    := tokensPerShare * rsrTotal in
        let rTokenAmount := tokensPerShare * rTokenTotal in
        Result.Success {|
          SurplusSplit.rsrAmount    := rsrAmount;
          SurplusSplit.rTokenAmount := rTokenAmount;
          SurplusSplit.dust         := delta - (rsrAmount + rTokenAmount);
        |}.

(** Validity predicate for the inputs to [computeNewBasketsAndNeeded].
    These are the runtime invariants production maintains. *)
Module Valid.
  Record bufferInputs
      (basketsHeldBottom basketsNeeded backingBuffer : U256.t) : Prop := {
    basketsHeldBottom_u192 : uint192_valid basketsHeldBottom;
    basketsNeeded_u192     : uint192_valid basketsNeeded;
    backingBuffer_u192     : uint192_valid backingBuffer;
    backingBuffer_le_max   : backingBuffer <= MAX_BACKING_BUFFER;
  }.
End Valid.

End BackingManager.
