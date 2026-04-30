(** Furnace simulation.

    Mirrors protocol/contracts/p1/Furnace.sol — the RToken melter.
    Each call to [melt] computes how much of the cached RToken balance
    should have been burned ("melted") since the last call, by applying
    the per-period ratio [r] over [N] elapsed periods. The production
    code uses the algebraic identity:

      payoutAmount = bal_0 * (1 - (1 - r)^N)

    which is what [melt] computes via [FixLib.powu] on [(FIX_ONE - ratio)].

    The on-chain function reads [block.timestamp] and
    [rToken.balanceOf(address(this))]; here we pass them as explicit
    [now] and [currentBalance] parameters so the simulation is pure.

    [setRatio] caps [ratio] at [MAX_RATIO = 10^14] (0.01%/period) before
    storing. The simulation enforces the same cap.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.

Module Furnace.

Import FixLib.

Definition MAX_RATIO : Z := 10^14.  (* 0.01% per period *)

Module Storage.
  Record t : Set := {
    ratio         : U256.t;   (** {1}, uint192 ≤ MAX_RATIO *)
    lastPayout    : U256.t;   (** {seconds}, uint48 *)
    lastPayoutBal : U256.t;   (** {qRTok}, uint256 *)
  }.
End Storage.

(** [melt(s, now, currentBalance)] returns the new storage and the amount
    burned. Mirrors [Furnace.sol#L65-L79]. Returns the updated storage and
    the melted amount.

    The production code:
      - Early-returns (s unchanged) if now < lastPayout + 1.
      - Sets lastPayout' = lastPayout + numPeriods.
      - Sets lastPayoutBal' = currentBalance - amount, where currentBalance
        is rToken.balanceOf(address(this)). *)
Definition melt (s : Storage.t) (now : U256.t) (currentBalance : U256.t)
    : Storage.t * U256.t :=
  if now <? s.(Storage.lastPayout) + 1 then
    (s, 0)
  else
    let numPeriods := now - s.(Storage.lastPayout) in
    let payoutRatio :=
      FixLib.minus FixLib.FIX_ONE
        (FixLib.powu (FixLib.minus FixLib.FIX_ONE s.(Storage.ratio)) numPeriods) in
    let amount := FixLib.mulu_toUint payoutRatio s.(Storage.lastPayoutBal) RoundingMode.FLOOR in
    let s' := {|
      Storage.ratio         := s.(Storage.ratio);
      Storage.lastPayout    := s.(Storage.lastPayout) + numPeriods;
      Storage.lastPayoutBal := currentBalance - amount;
    |} in
    (s', amount).

(** [setRatio]: governance bound check. Returns [None] on invalid ratio. *)
Definition setRatio (s : Storage.t) (ratio_ : U256.t) : option Storage.t :=
  if ratio_ <=? MAX_RATIO then
    Some {|
      Storage.ratio := ratio_;
      Storage.lastPayout := s.(Storage.lastPayout);
      Storage.lastPayoutBal := s.(Storage.lastPayoutBal);
    |}
  else None.

(** Validity predicate. *)
Module Valid.
  Record t (s : Storage.t) : Prop := {
    ratio_le_max     : s.(Storage.ratio) <= MAX_RATIO;
    ratio_nonneg     : 0 <= s.(Storage.ratio);
    lastPayout_uint48 : 0 <= s.(Storage.lastPayout) <= UINT256_MAX;
    lastPayoutBal_u256 : 0 <= s.(Storage.lastPayoutBal) <= UINT256_MAX;
  }.
End Valid.

End Furnace.
