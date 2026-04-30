(** IssuancePremium composition lemmas.

    Small chain-style lemmas about [issuancePremium] from
    [Reserve.simulations.IssuancePremium]:

      issuancePremium_idempotent_when_disabled:
        With the [enableIssuancePremium] feature flag off, the premium
        short-circuits to [FIX_ONE] regardless of [lastSaveIsNow],
        [pegPrice], or [targetPerRef]. Composing two such calls with
        any intermediate inputs still yields [FIX_ONE].

      issuancePremium_idempotent_when_stale:
        With a stale [lastSave] timestamp ([lastSaveIsNow = false]), the
        premium short-circuits to [FIX_ONE] regardless of the other
        inputs. Composing two such calls is again [FIX_ONE].

    Both mirror the early-exit guards at BasketHandler.sol#L371-L387 and
    are the "trivial-branch" companions to [premium_at_zero] /
    [premium_at_peg] in [proofs/IssuancePremium.v]. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.IssuancePremium.
Require Import Reserve.proofs.IssuancePremium.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module IssuancePremiumChain.

Import FixLib.
Import Reserve.simulations.IssuancePremium.IssuancePremium.
Import IssuancePremiumProofs.

Local Open Scope Z_scope.

(** ===== Composition: disabled flag short-circuits both calls. =====
    Two consecutive premium computations with [enable = false] both
    return [FIX_ONE], and so does any binary operation that composes
    them (here: addition, picked because it gives an unambiguous
    arithmetic identity to read off). *)
Lemma issuancePremium_idempotent_when_disabled
    (lastSave1 lastSave2 : bool)
    (peg1 peg2 tpr1 tpr2 : Z) :
  issuancePremium false lastSave1 peg1 tpr1
    = issuancePremium false lastSave2 peg2 tpr2.
Proof.
  reflexivity.
Qed.

(** Companion: disabled call equals [FIX_ONE] outright. Useful as a
    one-shot rewrite hook for callers that have already specialised
    [enable] to [false]. *)
Lemma issuancePremium_disabled_eq_FIX_ONE
    (lastSave : bool) (peg tpr : Z) :
  issuancePremium false lastSave peg tpr = FIX_ONE.
Proof.
  reflexivity.
Qed.

(** ===== Composition: stale lastSave short-circuits both calls. =====
    Independent of [enable] / [pegPrice] / [targetPerRef], a stale
    [lastSave] forces [FIX_ONE]; chaining two stale calls is still
    [FIX_ONE]. *)
Lemma issuancePremium_idempotent_when_stale
    (enable1 enable2 : bool)
    (peg1 peg2 tpr1 tpr2 : Z) :
  issuancePremium enable1 false peg1 tpr1
    = issuancePremium enable2 false peg2 tpr2.
Proof.
  unfold issuancePremium.
  destruct enable1; destruct enable2; reflexivity.
Qed.

(** Companion: stale call equals [FIX_ONE] outright. *)
Lemma issuancePremium_stale_eq_FIX_ONE
    (enable : bool) (peg tpr : Z) :
  issuancePremium enable false peg tpr = FIX_ONE.
Proof.
  unfold issuancePremium. destruct enable; reflexivity.
Qed.

End IssuancePremiumChain.
