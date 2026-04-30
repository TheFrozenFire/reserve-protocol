(** Distributor simulation.

    Mirrors protocol/contracts/p1/Distributor.sol — the Reserve revenue
    distributor. Production stores destinations as an [EnumerableSet]
    keyed by address, with a side mapping from address to [RevenueShare].
    For the math we care about — [distribute(amount)] — only the flat
    list of (destination, share) pairs matters, so the simulation models
    storage as that list directly.

    The production [distribute(erc20, amount)] computes:

      totalShares    = isRSR ? sum(rsrDist) : sum(rTokenDist)
      tokensPerShare = amount / totalShares           (FLOOR)
      transferAmt[i] = tokensPerShare * shares[i]

    We mirror that arithmetic exactly. The on-chain fee-recipient leg
    (DAOFeeRegistry) is intentionally omitted — its accounting is a
    separate concern and the share-conservation invariant we want to
    prove is over the inner-loop transfer math.

    Companion harness: contracts/DistributorMathHarness.sol.
    Companion CAS witness: cas/distributor/share_conservation.gp.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module Distributor.

Definition MAX_DISTRIBUTION : Z := 10000.
Definition MAX_DESTINATIONS : Z := 100.

Module RevenueShare.
  Record t : Set := {
    rTokenDist : U256.t;   (** uint16 share for RToken-side revenue *)
    rsrDist    : U256.t;   (** uint16 share for RSR-side revenue   *)
  }.
End RevenueShare.

(** Storage = ordered list of (destination address, share). The address is
    a [U256.t] since [Address.t = U256.t]. *)
Definition Storage : Set := list (U256.t * RevenueShare.t).

(** Sum the rTokenDist and rsrDist columns over the destinations list.
    Mirrors [Distributor.totals()] (the inner loop, ignoring DAOFeeRegistry). *)
Fixpoint totals (s : Storage) : U256.t * U256.t :=
  match s with
  | nil => (0, 0)
  | cons (_, share) rest =>
    let pair := totals rest in
    let rTokenTotal := fst pair in
    let rsrTotal    := snd pair in
    (rTokenTotal + share.(RevenueShare.rTokenDist),
     rsrTotal    + share.(RevenueShare.rsrDist))
  end.

(** Pull the per-destination share number for the leg we are distributing. *)
Definition shareOf (isRSR : bool) (share : RevenueShare.t) : U256.t :=
  if isRSR then share.(RevenueShare.rsrDist) else share.(RevenueShare.rTokenDist).

(** [distributeAmounts(s, amount, isRSR)] computes per-destination transfer
    amounts (in [s]'s order) using FLOOR division, and returns the dust
    remaining after paying out.

      tokensPerShare = amount / totalShares
      transferAmt[i] = tokensPerShare * shareOf(isRSR, distribution[i])
      dust           = amount - sum(transferAmt)

    When totalShares = 0 (no destinations or all-zero shares on the
    relevant leg), no math is meaningful — we return ([], amount) so the
    conservation invariant degenerates trivially. The production
    [require(tokensPerShare != 0, ...)] is a runtime check, not a math
    property; we surface it instead as [tokensPerShare_zero_means_zero_paid]. *)
Definition tokensPerShare (s : Storage) (amount : U256.t) (isRSR : bool) : U256.t :=
  let totalShares :=
    if isRSR then snd (totals s) else fst (totals s) in
  if totalShares =? 0 then 0 else amount / totalShares.

Fixpoint transferAmts_aux
    (s : Storage) (tps : U256.t) (isRSR : bool) : list U256.t :=
  match s with
  | nil => nil
  | cons (_, share) rest =>
    cons (tps * shareOf isRSR share) (transferAmts_aux rest tps isRSR)
  end.

Definition distributeAmounts
    (s : Storage) (amount : U256.t) (isRSR : bool)
    : list U256.t * U256.t :=
  let totalShares :=
    if isRSR then snd (totals s) else fst (totals s) in
  if totalShares =? 0 then
    (nil, amount)
  else
    let tps := amount / totalShares in
    let amts := transferAmts_aux s tps isRSR in
    let paidOut := List.fold_right Z.add 0 amts in
    (amts, amount - paidOut).

End Distributor.
