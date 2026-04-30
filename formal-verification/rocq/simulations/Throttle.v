(** ThrottleLib simulation.

    Mirrors protocol/contracts/libraries/Throttle.sol — a usage throttle that
    bounds net issuance / redemption per hour for an RToken.

    Production exposes three internal functions:
      hourlyLimit(throttle, supply)
      currentlyAvailable(throttle, limit)
      useAvailable(throttle, supply, amount)

    [block.timestamp] is read on-chain; here it is passed as an explicit
    [now : U256.t] parameter so the simulation is pure. The on-chain
    function mutates storage; we return a fresh [Throttle.t] (or a
    [Result.Revert] when the supply-change is throttled).

    Sign convention on [amount : Z]:
      amount > 0  consume  (revert iff amount > available)
      amount < 0  restore  (no cap on lastAvailable; the cap is enforced
                            lazily by [currentlyAvailable] on the next call)
      amount = 0  no-op

    Revert coverage:
      Modeled:  [revert_throttled] when amount > available (production
                line 58, "supply change throttled").
      Deferred: none — this library only has the one revert path.
      Not modeled: governance auth on the storage struct (handled at
                the calling contract level, not in ThrottleLib).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module ThrottleLib.

Definition ONE_HOUR    : Z := 3600.
Definition FIX_ONE     : Z := 10 ^ 18.
Definition UINT48_MAX  : Z := 2 ^ 48 - 1.
Definition UINT192_MAX : Z := 2 ^ 192 - 1.

Module Params.
  Record t : Set := {
    amtRate : U256.t;   (** {qRTok/hour}; uint256, must be > 0 in production *)
    pctRate : U256.t;   (** {1/hour}; uint192 fixed-point, may be 0 *)
  }.
End Params.

Module Throttle.
  Record t : Set := {
    params        : Params.t;
    lastTimestamp : U256.t;   (** {seconds}, uint48 *)
    lastAvailable : U256.t;   (** {qRTok}, uint256 *)
  }.
End Throttle.

(** Two-constructor result mirroring the upstream ERC20 simulation, so the
    eventual [run_useAvailable] equivalence lemma can match Yul revert
    offsets directly. The numeric fields are placeholders here; specific
    offsets are pinned during the equivalence proof. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Generic placeholder revert for "supply change throttled".
    Yul offsets get pinned during the equivalence proof. *)
Definition revert_throttled {A : Set} : Result.t A :=
  Result.Revert 0 32.

(** [hourlyLimit(throttle, supply)] = max(amtRate, supply * pctRate / FIX_ONE).
    Source: Throttle.sol#L80-L90. *)
Definition hourlyLimit (t : Throttle.t) (supply : U256.t) : U256.t :=
  let p := t.(Throttle.params) in
  let limit_pct := (supply * p.(Params.pctRate)) / FIX_ONE in
  Z.max p.(Params.amtRate) limit_pct.

(** [currentlyAvailable(throttle, limit, now)]
    = min(limit, lastAvailable + (limit * (now - lastTimestamp)) / ONE_HOUR).
    Source: Throttle.sol#L69-L77. The [Z.min] is the on-chain
    [if (available > limit) available = limit;] clip — what enforces INV-1. *)
Definition currentlyAvailable
    (t : Throttle.t) (limit : U256.t) (now : U256.t) : U256.t :=
  let delta := now - t.(Throttle.lastTimestamp) in
  let raw := t.(Throttle.lastAvailable) + (limit * delta) / ONE_HOUR in
  Z.min limit raw.

(** [useAvailable(throttle, supply, amount, now)]. Source: Throttle.sol#L37-L65. *)
Definition useAvailable
    (t : Throttle.t) (supply : U256.t) (amount : Z) (now : U256.t)
    : Result.t Throttle.t :=
  let p := t.(Throttle.params) in
  if andb (p.(Params.amtRate) =? 0) (p.(Params.pctRate) =? 0) then
    Result.Success t
  else
    let limit := hourlyLimit t supply in
    let available := currentlyAvailable t limit now in
    let new_ts :=
      if orb (negb (available =? t.(Throttle.lastAvailable)))
             (available =? limit)
      then now
      else t.(Throttle.lastTimestamp) in
    let with_ts := t <| Throttle.lastTimestamp := new_ts |> in
    if 0 <? amount then
      if amount <=? available then
        Result.Success
          (with_ts <| Throttle.lastAvailable := available - amount |>)
      else
        revert_throttled
    else if amount <? 0 then
      Result.Success
        (with_ts <| Throttle.lastAvailable := available + (- amount) |>)
    else
      Result.Success
        (with_ts <| Throttle.lastAvailable := available |>).

(** Validity predicate: the type-level invariants the storage layout
    maintains. uint48 timestamp, uint192 pctRate, uint256 everywhere else. *)
Module Valid.
  Record params (p : Params.t) : Prop := {
    amtRate_u256    : U256.Valid.t p.(Params.amtRate);
    pctRate_u256    : U256.Valid.t p.(Params.pctRate);
    pctRate_uint192 : 0 <= p.(Params.pctRate) <= UINT192_MAX;
  }.

  Record throttle (t : Throttle.t) : Prop := {
    p_valid        : params t.(Throttle.params);
    lastTs_uint48  : 0 <= t.(Throttle.lastTimestamp) <= UINT48_MAX;
    lastAvail_u256 : U256.Valid.t t.(Throttle.lastAvailable);
  }.
End Valid.

End ThrottleLib.
