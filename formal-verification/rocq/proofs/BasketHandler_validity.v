(** BasketHandler output-bound (validity) lemmas.

    Narrow output-bound invariants on the [BasketHandler] simulation
    defined in [Reserve.simulations.BasketHandler]:

      1. [quote_one_nonneg] — given non-negative [refAmt] and [baskets],
         the per-asset quote [quote_one refAmt baskets mode] is
         non-negative for any rounding mode.

         This is the kernel non-negativity claim — without it, the
         downstream {qTok} amounts the protocol mints / redeems against
         could be negative, breaking the integer-quantity contract.

      2. [quoteQuantities_nonneg] — pointwise non-negativity of every
         entry in [quoteQuantities s baskets mode], lifted from the
         per-asset claim above.

    The proofs lean on the same FixLib round-direction discipline used
    in the BackingManager validity lemmas: [divrnd] is non-negative
    whenever the numerator is non-negative and the divisor is positive.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Coq.Lists.List.
Import ListNotations.

Module BasketHandlerValidityProofs.

Import FixLib.
Import BasketHandler.

(** Helper: [divrnd n d mode] is non-negative whenever the numerator is
    non-negative and the divisor is positive. (Same shape as the
    BackingManager validity helper — duplicated locally to keep this
    module self-contained.) *)
Lemma divrnd_nonneg (n d : Z) (mode : RoundingMode.t) :
  0 <= n -> 0 < d -> 0 <= divrnd n d mode.
Proof.
  intros Hn Hd.
  unfold divrnd.
  assert (Hq : 0 <= n / d) by (apply Z.div_pos; [exact Hn|exact Hd]).
  destruct mode.
  - exact Hq.
  - destruct (n mod d >? (d - 1) / 2); lia.
  - destruct (n mod d =? 0); lia.
Qed.

(** ===== INV-V1 (kernel): per-asset quote is non-negative. =====
    [quote_one refAmt baskets mode = divrnd (refAmt*baskets) FIX_SCALE mode]
    is >= 0 whenever both inputs are non-negative, because the numerator
    [refAmt * baskets] is then non-negative and [FIX_SCALE > 0]. *)
Lemma quote_one_nonneg
    (refAmt baskets : U256.t) (mode : RoundingMode.t) :
  0 <= refAmt ->
  0 <= baskets ->
  0 <= quote_one refAmt baskets mode.
Proof.
  intros Hr Hb.
  unfold quote_one, FixLib.mulu_toUint.
  apply divrnd_nonneg.
  - apply Z.mul_nonneg_nonneg; assumption.
  - unfold FIX_SCALE; lia.
Qed.

(** ===== INV-V2 (lifted): every per-asset quote in the list is non-negative.

    Given a basket where every [refAmt] is non-negative and a non-negative
    [baskets] input, every {qTok} amount in [quoteQuantities] is non-negative.
    This is the load-bearing "no negative {qTok}" claim. *)
Lemma quoteQuantities_nonneg
    (s : Storage) (baskets : U256.t) (mode : RoundingMode.t) :
  0 <= baskets ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) s ->
  Forall (fun q => 0 <= q) (quoteQuantities s baskets mode).
Proof.
  intros Hb Hval.
  unfold quoteQuantities.
  induction s as [|e rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    apply Forall_cons.
    + simpl. apply quote_one_nonneg; assumption.
    + apply IH. exact Htl.
Qed.

End BasketHandlerValidityProofs.
