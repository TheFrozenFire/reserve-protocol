(** DutchTrade composition lemmas.

    Small, clean composition lemmas that lift the per-phase results in
    [proofs/DutchTrade.v] to statements about [bidPrice] over time.

    Lemmas:
      1. [phase4_absorbing] — once progression has reached the phase-4
         range (>= 95%), [bidPrice] equals [worstPrice] for every later
         progression value within range.
      2. [bidPrice_progresses_to_worst] — at progression = FIX_ONE
         (i.e. t = endTime), [bidPrice] equals [worstPrice]. This
         corollary chains [progression_at_endTime] with
         [bidPrice_phase4_constant].

    Discipline: no admits. Re-uses lemmas from [DutchTradeProofs] rather
    than re-proving curve facts.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Reserve.simulations.DutchTrade.
Require Reserve.proofs.DutchTrade.

Module DutchTradeChain.

Import FixLib.
Import Reserve.simulations.DutchTrade.DutchTrade.
Import Reserve.proofs.DutchTrade.DutchTradeProofs.

Opaque FixLib.mul FixLib.divrnd FixLib.powu.

(** ===== phase4 is absorbing in progression. =====

    If two progression values [p1, p2] both lie in the phase-4 range
    [95%, 100%], the [bidPrice] at the corresponding times agrees: both
    are [worstPrice]. The "absorbing" framing: once the auction enters
    phase 4, no later in-range time changes the price. *)
Lemma phase4_absorbing (a : Auction.t) (t1 t2 : U256.t) :
  NINETY_FIVE_PERCENT <= progression a t1 ->
  progression a t1 <= FIX_ONE ->
  NINETY_FIVE_PERCENT <= progression a t2 ->
  progression a t2 <= FIX_ONE ->
  bidPrice a t1 = bidPrice a t2.
Proof.
  intros H1lo H1hi H2lo H2hi.
  rewrite (bidPrice_phase4_constant a t1 H1lo H1hi).
  rewrite (bidPrice_phase4_constant a t2 H2lo H2hi).
  reflexivity.
Qed.

(** ===== bidPrice at endTime = worstPrice. =====

    Already proved as [bidPrice_at_endTime] in [proofs/DutchTrade.v];
    re-stated here as the natural composition of
    [progression_at_endTime] with [bidPrice_phase4_constant], to give
    the chain-of-lemmas form. *)
Lemma bidPrice_progresses_to_worst (a : Auction.t) :
  Valid.t a ->
  bidPrice a a.(Auction.endTime) = a.(Auction.worstPrice).
Proof.
  intros Hv.
  apply bidPrice_phase4_constant.
  - rewrite (progression_at_endTime _ Hv).
    unfold NINETY_FIVE_PERCENT, FIX_ONE, FIX_SCALE. lia.
  - rewrite (progression_at_endTime _ Hv). lia.
Qed.

End DutchTradeChain.
