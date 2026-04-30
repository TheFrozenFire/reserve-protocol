(** Cross-domain integration: linear history of state evolution.

    Headline lemma: applying [Furnace.setRatio] sequentially over a list of
    candidate ratios preserves the [Furnace.Valid.t] storage invariant,
    provided each candidate is non-negative and the chain succeeds at every
    step (no [None]).

    This is the N-ary generalization of
    [FurnaceValidity.setRatio_preserves_validity]: a single-step preservation
    lemma applied repeatedly along a linear history. The proof is induction
    on the list of ratios — base case is the input [Valid.t] hypothesis,
    inductive step appeals to [setRatio_preserves_validity] on the head of
    the list and the IH on the tail.

    The chain is encoded as [fold_left] over an [option Storage.t] that
    short-circuits to [None] as soon as any [setRatio] rejects (i.e. the
    [<= MAX_RATIO] check fails). The final hypothesis [= Some s'] therefore
    forces every intermediate step to have produced a [Some], so each
    invocation of [setRatio_preserves_validity] is justified by a [Some] in
    the trace.

    [setRatio] was chosen over [melt] because its single-step preservation
    lemma takes only a non-negativity precondition on its input, which lifts
    to a list precondition cleanly via [Forall]. The [melt] preservation
    lemma requires a per-step bound on the (computed) [amount] that is not
    expressible as a precondition on inputs alone. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Furnace.
Require Import Reserve.proofs.Furnace_validity.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationLinearHistory.

Import FixLib.
Import Furnace.
Import FurnaceValidity.

(** Step function: thread an [option Storage.t] through one [setRatio] call.
    [None] is absorbing, modeling a chain that has already failed. *)
Definition setRatio_step (os : option Storage.t) (r : U256.t)
    : option Storage.t :=
  match os with
  | None => None
  | Some s => setRatio s r
  end.

(** Sequential application of [setRatio] over a list of candidate ratios. *)
Definition setRatio_chain (s : Storage.t) (rs : list U256.t)
    : option Storage.t :=
  fold_left setRatio_step rs (Some s).

(** Headline lemma: the chain preserves [Valid.t] when every ratio in the
    list is non-negative and the chain succeeds. *)
Lemma setRatio_chain_preserves_validity
    (s s' : Storage.t) (rs : list U256.t) :
  Valid.t s ->
  Forall (fun r => 0 <= r) rs ->
  setRatio_chain s rs = Some s' ->
  Valid.t s'.
Proof.
  revert s s'.
  induction rs as [|r rs IH]; intros s s' Hvalid Hall Hchain.
  - (* Base case: empty list. [fold_left _ [] (Some s) = Some s], so s' = s. *)
    unfold setRatio_chain in Hchain. simpl in Hchain.
    injection Hchain as Heq. subst s'. exact Hvalid.
  - (* Inductive step: head ratio applies [setRatio] to s, producing some
       intermediate s1; the IH then carries [Valid.t] from s1 to s'. *)
    inversion Hall as [|? ? Hr Hrest]; subst.
    unfold setRatio_chain in Hchain. simpl in Hchain.
    destruct (setRatio s r) as [s1|] eqn:Hstep.
    + (* setRatio succeeded on the head. *)
      assert (Hvalid1 : Valid.t s1).
      { apply (setRatio_preserves_validity s s1 r Hvalid Hr Hstep). }
      apply (IH s1 s' Hvalid1 Hrest).
      unfold setRatio_chain. exact Hchain.
    + (* setRatio failed: the [None] is absorbing, so [Hchain] ends in [None],
         contradicting [= Some s']. *)
      exfalso.
      assert (Hnone : fold_left setRatio_step rs None = None).
      { clear. induction rs as [|x xs IHxs]; simpl; [reflexivity|].
        exact IHxs. }
      rewrite Hnone in Hchain. discriminate.
Qed.

End IntegrationLinearHistory.
