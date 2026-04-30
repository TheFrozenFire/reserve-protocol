(** IssuancePremium simulation.

    Mirrors the issuance-premium computation from
    protocol/contracts/p1/BasketHandler.sol::issuancePremium (PR #1175).

    Production formula:

      issuancePremium(coll) =
        if !enableIssuancePremium || coll.lastSave() != block.timestamp
                                                  -> FIX_ONE
        elif pegPrice == 0                        -> FIX_ONE
        elif pegPrice >= targetPerRef             -> FIX_ONE
        else                                      -> safeDiv(targetPerRef,
                                                             pegPrice, CEIL)

    The CEIL [safeDiv] kernel mirrors FixLib.div(..., CEIL):

      safeDiv_ceil(a, b) =
        if a == 0          -> 0
        elif a == FIX_MAX  -> FIX_MAX                (* saturation *)
        elif b == 0        -> FIX_MAX                (* /0 sentinel *)
        else
          raw = ceil_div(FIX_ONE * a, b)
          if raw >= FIX_MAX -> FIX_MAX
          else              -> raw

    The CAS script in cas/issuance_premium/premium_curve.gp probes the
    invariants (P1..P6) on a 5-token stablecoin basket calibration.

    Revert coverage:
      Modeled:  [safeDiv_ceil] saturates at FIX_MAX on [b = 0] and
                FIX_MAX-input (matches production [FixLib.safeDiv]
                semantics — these are explicit saturation paths, not
                reverts). All other [issuancePremium] paths return
                FIX_ONE for the disabled / no-premium cases.
      Deferred: input bounds via [Valid.input] (uint192 on each
                price scalar).
      Not modeled: any caller-context reverts in [BasketHandler]
                that gate access to [issuancePremium] (lifecycle,
                governance toggle).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module IssuancePremium.

Import FixLib.

(** [safeDiv a b CEIL] — the saturating ceiling divide used by
    BasketHandler.issuancePremium. Matches the CAS [safeDiv_ceil] helper. *)
Definition safeDiv_ceil (a b : Z) : Z :=
  if a =? 0 then 0
  else if a =? FIX_MAX then FIX_MAX
  else if b =? 0 then FIX_MAX
  else
    let raw := FixLib.div a b RoundingMode.CEIL in
    if FIX_MAX <=? raw then FIX_MAX else raw.

(** [issuancePremium] — the BasketHandler.sol#L371-L387 function. *)
Definition issuancePremium
    (enable lastSaveIsNow : bool)
    (pegPrice targetPerRef : Z) : Z :=
  if negb enable then FIX_ONE
  else if negb lastSaveIsNow then FIX_ONE
  else if pegPrice =? 0 then FIX_ONE
  else if targetPerRef <=? pegPrice then FIX_ONE
  else safeDiv_ceil targetPerRef pegPrice.

(** Validity predicates. *)
Module Valid.
  (** Any uint192 input is valid. The premium output is always uint192. *)
  Definition input (x : Z) : Prop := 0 <= x <= FIX_MAX.
End Valid.

End IssuancePremium.
