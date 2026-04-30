(** BasketHandler simulation invariant proofs.

    Proves the load-bearing safety invariants on the [BasketHandler]
    simulation defined in [Reserve.simulations.BasketHandler].

      INV-Q1   quote_one_floor_le_ceil:
                 per-asset FLOOR quote <= per-asset CEIL quote
                 (lifts FixLib RD-1 through the [quote_one] kernel)

      INV-RT1  quote_one_round_trip_floor:
                 redeeming the FLOOR-quote of [baskets] BUs against the
                 same [refAmt] never recovers more than [baskets] BUs.
                 This is the "user can't extract more than they put in"
                 property — the algebraic core of round-trip safety.

      INV-EMPTY  quote_empty_basket: [quote] on the empty basket is [].

    Each lemma is fully proved, no admits. The round-direction lemma
    is essentially [FixLib.divrnd_floor_le_ceil] threaded through the
    [mulu_toUint] kernel.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.simulations.BasketHandler.
Require Import Coq.Lists.List.
Import ListNotations.

Module BasketHandlerProofs.

Import FixLib.
Import FixLibProofs.
Import BasketHandler.

(** ===== INV-Q1 (kernel): per-asset FLOOR <= CEIL. =====
    Lifts [FixLib.divrnd_floor_le_ceil] through the [mulu_toUint] kernel
    used in [quote_one]. *)
Lemma quote_one_floor_le_ceil (refAmt baskets : U256.t) :
  quote_one refAmt baskets RoundingMode.FLOOR
  <= quote_one refAmt baskets RoundingMode.CEIL.
Proof.
  unfold quote_one, FixLib.mulu_toUint.
  apply divrnd_floor_le_ceil.
  unfold FIX_SCALE. lia.
Qed.

(** ===== INV-Q1 (lifted to the basket-wide list): pointwise FLOOR <= CEIL. ===== *)
Lemma quote_floor_le_ceil
    (s : Storage) (baskets : U256.t) :
  Forall2 (fun pf pc => snd pf <= snd pc)
          (quote s baskets RoundingMode.FLOOR)
          (quote s baskets RoundingMode.CEIL).
Proof.
  induction s as [|e rest IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + simpl. apply quote_one_floor_le_ceil.
    + exact IH.
Qed.

(** ===== INV-EMPTY: quote on the empty basket returns []. ===== *)
Lemma quote_empty_basket (baskets : U256.t) (mode : RoundingMode.t) :
  quote nil baskets mode = nil.
Proof. reflexivity. Qed.

Lemma quoteQuantities_empty (baskets : U256.t) (mode : RoundingMode.t) :
  quoteQuantities nil baskets mode = nil.
Proof. reflexivity. Qed.

(** Stronger empty-basket statement: with a zero-length basket, every
    invocation of [quote] is the empty list — including the all-zeros
    edge case where the call has nothing to do. *)
Lemma quote_empty_baskets_zero (s : Storage) (mode : RoundingMode.t) :
  Forall (fun p => snd p = 0) (quote s 0 mode).
Proof.
  induction s as [|e rest IH]; simpl.
  - apply Forall_nil.
  - apply Forall_cons; [|exact IH].
    simpl. unfold quote_one, FixLib.mulu_toUint, FixLib.divrnd.
    rewrite Z.mul_0_r. simpl.
    destruct mode; reflexivity.
Qed.

(** ===== INV-RT1: round-trip non-extraction (per-asset, FLOOR). =====

    [redeem_one refAmt (quote_one refAmt baskets FLOOR) <= baskets].

    This is the load-bearing user-can't-extract-more-than-they-put-in
    property: starting from [baskets] BUs, FLOOR-quoting to a token
    quantity and FLOOR-inverting back recovers no more than the input.

    Proof shape: [quote_one refAmt baskets FLOOR = (refAmt * baskets) / FIX_ONE],
    so [(qTok * FIX_ONE) / refAmt = ((refAmt * baskets) / FIX_ONE * FIX_ONE) / refAmt
                                  <= ((refAmt * baskets)) / refAmt
                                  = baskets]
    when [refAmt > 0]. The [refAmt = 0] branch returns 0 trivially. *)
Lemma quote_one_round_trip_floor
    (refAmt baskets : U256.t) :
  0 <= baskets ->
  0 <= refAmt ->
  redeem_one refAmt (quote_one refAmt baskets RoundingMode.FLOOR)
  <= baskets.
Proof.
  intros Hb Hr.
  unfold redeem_one, quote_one, FixLib.mulu_toUint, FixLib.divrnd.
  destruct (refAmt =? 0) eqn:Hr0; [exact Hb|].
  apply Z.eqb_neq in Hr0.
  assert (HrPos : 0 < refAmt) by lia.
  assert (HFIX : 0 < FIX_SCALE) by (unfold FIX_SCALE; lia).
  set (q := refAmt * baskets / FIX_SCALE).
  (* Step 1: q * FIX_SCALE <= refAmt * baskets. *)
  assert (Hstep1 : q * FIX_SCALE <= refAmt * baskets).
  { unfold q. rewrite Z.mul_comm.
    apply Z.mul_div_le. exact HFIX. }
  (* Step 2: dividing both sides of Step 1 by refAmt (positive) preserves <=. *)
  assert (Hstep2 : (q * FIX_SCALE) / refAmt <= (refAmt * baskets) / refAmt).
  { apply Z.div_le_mono; [exact HrPos|exact Hstep1]. }
  (* Step 3: (refAmt * baskets) / refAmt = baskets, since refAmt <> 0
     and baskets >= 0. *)
  assert (Hstep3 : (refAmt * baskets) / refAmt = baskets).
  { rewrite Z.mul_comm. apply Z.div_mul. lia. }
  rewrite Hstep3 in Hstep2.
  unfold FIX_ONE. exact Hstep2.
Qed.

(** ===== INV-RT1 lifted: every entry's round-trip recovers <= baskets. =====

    For each (asset, refAmt) entry, the FLOOR-quote followed by FLOOR-redeem
    never exceeds the input [baskets] amount. This is the per-asset
    statement of the round-trip safety property. *)
Lemma quote_round_trip_floor
    (s : Storage) (baskets : U256.t) :
  0 <= baskets ->
  Forall (fun e => 0 <= e.(BasketEntry.refAmt)) s ->
  Forall
    (fun p =>
       redeem_one (fst p) (snd p) <= baskets)
    (List.map
       (fun e =>
          (e.(BasketEntry.refAmt),
           quote_one e.(BasketEntry.refAmt) baskets RoundingMode.FLOOR))
       s).
Proof.
  intros Hb Hval.
  induction s as [|e rest IH]; simpl.
  - apply Forall_nil.
  - inversion Hval as [|? ? Hhd Htl]; subst.
    apply Forall_cons.
    + simpl. apply quote_one_round_trip_floor; assumption.
    + apply IH. exact Htl.
Qed.

End BasketHandlerProofs.
