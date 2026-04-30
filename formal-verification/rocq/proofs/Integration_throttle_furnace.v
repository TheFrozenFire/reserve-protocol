(** Cross-domain integration: Throttle.lastAvailable + Furnace.lastPayoutBal
    fits in 2 * UINT256_MAX.

    Both quantities are uint256 by their respective [Valid] predicates: the
    Throttle's [lastAvailable] via [U256.Valid.t] in [Throttle.Valid.throttle],
    and the Furnace's [lastPayoutBal] via the [<= UINT256_MAX] bound in
    [Furnace.Valid.t]. Their pointwise sum is therefore bounded by twice
    [UINT256_MAX] — a trivial-but-explicit cross-domain consequence that is
    useful when reasoning about combined balance accounting across the two
    storage domains.

    The proof is purely additive composition of the two validity predicates'
    upper bounds. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Throttle.
Require Import Reserve.simulations.Furnace.

Module IntegrationThrottleFurnace.

Import FixLib.
Import ThrottleLib.

Lemma throttle_lastAvailable_plus_furnace_lastPayoutBal_bounded
    (t : Throttle.t) (s : Furnace.Storage.t) :
  Valid.throttle t ->
  Furnace.Valid.t s ->
  t.(Throttle.lastAvailable) + s.(Furnace.Storage.lastPayoutBal)
    <= 2 * UINT256_MAX.
Proof.
  intros [_ _ Hav_u256] [_ _ _ Hlpb].
  unfold U256.Valid.t in Hav_u256.
  unfold UINT256_MAX in *.
  lia.
Qed.

End IntegrationThrottleFurnace.
