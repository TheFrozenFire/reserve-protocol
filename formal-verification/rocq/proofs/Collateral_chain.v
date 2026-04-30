(** Collateral composition lemma.

    Two-step closure of [disabled_is_terminal] from [proofs/Collateral.v]:
    starting from a DISABLED state, two consecutive [refresh] calls leave
    the (decoded) status as DISABLED.

    The on-chain [State.t] does not store [status] directly — it is decoded
    from [whenDefault] at any [now] via [statusOf]. So "starts DISABLED"
    means [statusOf s.(whenDefault) now0 = DISABLED] at some baseline now0,
    and "ends DISABLED" means the same of the final state at the second
    refresh's [now]. Solidity's monotone-clock assumption surfaces as the
    [now0 <= n1 <= n2] hypotheses below. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Collateral.
Require Import Reserve.proofs.Collateral.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module CollateralChain.

Local Open Scope Z_scope.

(** Helper: when [statusOf wd now1 = DISABLED] and [now1 <= now2], any
    [refresh] starting from a state with that [whenDefault] leaves
    [whenDefault] unchanged. The [refresh] body invokes [markStatus] at
    most twice (once on the hard-default branch, once on the soft path);
    [markStatus_terminal_when_disabled] makes both no-ops. *)
Lemma refresh_whenDefault_terminal_when_disabled
    (st : Collateral.State.t)
    (underlying pegPrice low now1 now2 : Z) :
  Collateral.statusOf st.(Collateral.State.whenDefault) now1
    = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  (Collateral.refresh st underlying pegPrice low now2)
    .(Collateral.State.whenDefault)
    = st.(Collateral.State.whenDefault).
Proof.
  intros HD Hmono.
  unfold Collateral.refresh.
  destruct (Collateral.updateExposed
              st.(Collateral.State.exposedReferencePrice)
              underlying st.(Collateral.State.revenueShowing))
    as [new_exposed defaulted] eqn:Hupd.
  set (wd0 := st.(Collateral.State.whenDefault)).
  assert (Hhard :
    (if defaulted
     then Collateral.markStatus wd0 Collateral.Status.DISABLED now2
            st.(Collateral.State.delayUntilDefault)
     else wd0) = wd0).
  { destruct defaulted.
    - apply (CollateralProofs.markStatus_terminal_when_disabled
               wd0 Collateral.Status.DISABLED now1 now2
               st.(Collateral.State.delayUntilDefault) HD Hmono).
    - reflexivity. }
  simpl.
  rewrite Hhard.
  apply (CollateralProofs.markStatus_terminal_when_disabled
           wd0 _ now1 now2
           st.(Collateral.State.delayUntilDefault) HD Hmono).
Qed.

(** Single-step lifting: [refresh] preserves DISABLED status. *)
Lemma refresh_preserves_disabled
    (st : Collateral.State.t)
    (underlying pegPrice low now1 now2 : Z) :
  Collateral.statusOf st.(Collateral.State.whenDefault) now1
    = Collateral.Status.DISABLED ->
  now1 <= now2 ->
  Collateral.statusOf
    (Collateral.refresh st underlying pegPrice low now2)
      .(Collateral.State.whenDefault) now2
    = Collateral.Status.DISABLED.
Proof.
  intros HD Hmono.
  rewrite (refresh_whenDefault_terminal_when_disabled
             st underlying pegPrice low now1 now2 HD Hmono).
  apply CollateralProofs.statusOf_disabled_iff in HD.
  destruct HD as [HN HL].
  apply CollateralProofs.statusOf_disabled_iff.
  split; [exact HN | lia].
Qed.

(** Two-step closure: starting from DISABLED, two consecutive [refresh]
    calls leave the decoded status DISABLED. The chronology hypothesis
    [now0 <= n1 <= n2] is the on-chain monotone-clock assumption. *)
Lemma refresh_disabled_terminal_chain
    (s s1 s2 : Collateral.State.t)
    (u1 p1 l1 n1 u2 p2 l2 n2 now0 : Z) :
  Collateral.statusOf s.(Collateral.State.whenDefault) now0
    = Collateral.Status.DISABLED ->
  now0 <= n1 ->
  n1 <= n2 ->
  Collateral.refresh s  u1 p1 l1 n1 = s1 ->
  Collateral.refresh s1 u2 p2 l2 n2 = s2 ->
  Collateral.statusOf s2.(Collateral.State.whenDefault) n2
    = Collateral.Status.DISABLED.
Proof.
  intros HD H01 H12 Hr1 Hr2.
  assert (HD1 : Collateral.statusOf
                  s1.(Collateral.State.whenDefault) n1
                = Collateral.Status.DISABLED).
  { rewrite <- Hr1.
    apply (refresh_preserves_disabled s u1 p1 l1 now0 n1 HD H01). }
  rewrite <- Hr2.
  apply (refresh_preserves_disabled s1 u2 p2 l2 n1 n2 HD1 H12).
Qed.

End CollateralChain.
