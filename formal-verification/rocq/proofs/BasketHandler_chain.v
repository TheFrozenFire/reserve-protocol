(** BasketHandler composition lemmas.

    Two small composition claims layered on top of the core
    [BasketHandler_validity.v] / [BasketHandler.v] lemmas:

      1. [quote_zero_baskets] — quoting any basket with [baskets = 0]
         produces an all-zero per-asset quantity list, regardless of
         rounding mode. Generalises [quote_empty_baskets_zero] over the
         [quoteQuantities] view (the [List.map snd] projection).

      2. [quote_FLOOR_le_quote_CEIL_pointwise] — pointwise version of
         the existing [quote_floor_le_ceil] batch lemma, projected
         through [quoteQuantities] so the comparison is on bare {qTok}
         lists rather than on (asset, qTok) pairs.

    Both lemmas are pure compositions of existing results — no new
    arithmetic content. Companion to [BasketHandler_validity.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Reserve.proofs.BasketHandler.
Require Import Coq.Lists.List.
Import ListNotations.

Module BasketHandlerChain.

Import FixLib.
Import BasketHandler.
Import BasketHandlerProofs.

(** ===== quote_zero_baskets =====
    With [baskets = 0], every per-asset {qTok} amount is 0, regardless
    of rounding mode. Composes [quote_empty_baskets_zero] (which states
    the same for the (asset, qTok) pair list) onto the
    [quoteQuantities = List.map snd ∘ quote] projection. *)
Lemma quote_zero_baskets
    (s : BasketHandler.Storage) (mode : RoundingMode.t) :
  Forall (fun q => q = 0) (BasketHandler.quoteQuantities s 0 mode).
Proof.
  unfold BasketHandler.quoteQuantities.
  pose proof (quote_empty_baskets_zero s mode) as H.
  induction H as [|p rest Hp _ IH]; simpl.
  - apply Forall_nil.
  - apply Forall_cons; [exact Hp | exact IH].
Qed.

(** ===== quote_FLOOR_le_quote_CEIL_pointwise =====
    Pointwise FLOOR <= CEIL on the bare {qTok} lists. Composition of
    the existing [quote_floor_le_ceil] (which states the comparison on
    the paired (asset, qTok) lists) projected through [List.map snd]. *)
Lemma quote_FLOOR_le_quote_CEIL_pointwise
    (s : BasketHandler.Storage) (baskets : U256.t) :
  Forall2 Z.le
          (BasketHandler.quoteQuantities s baskets RoundingMode.FLOOR)
          (BasketHandler.quoteQuantities s baskets RoundingMode.CEIL).
Proof.
  unfold BasketHandler.quoteQuantities.
  induction s as [|e rest IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + apply quote_one_floor_le_ceil.
    + exact IH.
Qed.

End BasketHandlerChain.
