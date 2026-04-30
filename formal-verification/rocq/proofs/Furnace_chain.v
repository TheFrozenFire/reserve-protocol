(** Furnace composition lemma.

    Composing [setRatio_preserves_validity] and [melt_preserves_validity]
    from [Furnace_validity]: if [setRatio] succeeds on a valid storage and
    [melt] is then run on the result, the final storage is still valid.

    This is a chain proof: no new arithmetic reasoning, just propagation of
    [Valid.t] through two sequential steps. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.
Require Import Reserve.proofs.Furnace_validity.

Module FurnaceChain.

Import FixLib.
Import Furnace.
Import FurnaceValidity.

Lemma setRatio_then_melt_preserves_validity
    (s s1 s' : Storage.t) (ratio_ now currentBalance amount : U256.t) :
  Valid.t s ->
  0 <= ratio_ ->
  0 <= now <= UINT256_MAX ->
  0 <= currentBalance <= UINT256_MAX ->
  0 <= amount <= currentBalance ->
  setRatio s ratio_ = Some s1 ->
  melt s1 now currentBalance = (s', amount) ->
  Valid.t s'.
Proof.
  intros Hvalid Hnn Hnow Hbal Hamt Hset Hmelt.
  assert (Hvalid1 : Valid.t s1).
  { apply (setRatio_preserves_validity s s1 ratio_ Hvalid Hnn Hset). }
  apply (melt_preserves_validity s1 s' now currentBalance amount
           Hvalid1 Hnow Hbal Hamt Hmelt).
Qed.

End FurnaceChain.
