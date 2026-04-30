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

    Revert coverage:
      Modeled:  none. The simulation is a math kernel.
      Deferred: none structurally — sim returns dust where production
                reverts.
      Not modeled: production's [require(tokensPerShare != 0,
                "nothing to distribute")] (line 134) — sim returns
                ([], amount) instead. Production's
                [require(caller == rsrTrader || rTokenTrader)] (line
                124) and [require(erc20 == rsr || rToken)] (line 125)
                — sim has no auth or token-identity checks. The DAO
                fee-leg accounting (production lines 177-190) is
                explicitly out of scope; see
                proofs/CAS_additional_findings.v for the
                governance-conditional gap pinned as a counterexample.
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

(** ===== DAO-fee leg =====

    Production's [distribute()] (Distributor.sol#L177-L190) pays an
    additional fee leg to the [DAOFeeRegistry]'s recipient when configured.
    The fee adjustment is computed inside [totals()] (Distributor.sol#L212-L226)
    and only inflates the [rsrTotal] component of the share totals:

      rsrTotal' = rsrTotal + (feeNumerator * (rTokenTotal + rsrTotal))
                              / (feeDenominator - feeNumerator)

    The fee recipient then receives [tokensPerShare * (totalShares' - paidOutShares)]
    when [paidOutShares < totalShares'], with [paidOutShares] = sum of the
    inner-loop [shareOf] values.

    When [feeNumerator = 0] or the registry is unset, the DAO leg vanishes
    and the math reduces to the basic [distributeAmounts] path above.

    Result module bundling the per-destination amounts, the DAO-fee amount,
    and the residual dust. The conservation invariant is

      sum(amts) + daoFee + dust = amount    (exactly, when totalShares != 0)
*)
Module DistResult.
  Record t : Set := {
    amts    : list U256.t;
    daoFee  : U256.t;
    dust    : U256.t;
  }.
End DistResult.

(** [feeShareInflation rTokenTotal rsrTotal feeNumerator feeDenominator]
    mirrors the production fee-share computation:

      (feeNumerator * (rTokenTotal + rsrTotal)) / (feeDenominator - feeNumerator)

    Returns 0 when [feeNumerator = 0] or [feeDenominator <= feeNumerator]
    (the latter is a malformed configuration; production would revert
    via Solidity's checked subtraction). *)
Definition feeShareInflation
    (rTokenTotal rsrTotal feeNumerator feeDenominator : U256.t) : U256.t :=
  if feeNumerator =? 0 then 0
  else if feeDenominator <=? feeNumerator then 0
  else (feeNumerator * (rTokenTotal + rsrTotal))
         / (feeDenominator - feeNumerator).

(** Sum of the inner-loop share count for the leg being distributed.
    Used to compute [paidOutShares] in [distributeAmounts_with_dao_fee]. *)
Fixpoint paidOutShares (s : Storage) (isRSR : bool) : U256.t :=
  match s with
  | nil => 0
  | cons (_, share) rest =>
    shareOf isRSR share + paidOutShares rest isRSR
  end.

(** [distributeAmounts_with_dao_fee s amount isRSR feeNumerator feeDenominator]
    The DAO-fee-aware distribution.

    - For the rToken leg ([isRSR = false]) the DAO fee inflates only the
      rsr side and so does not affect rTokenTotal — the rToken leg's
      [tokensPerShare] is unchanged from the no-fee case.
    - For the rsr leg ([isRSR = true]) the inflated [rsrTotal] enlarges
      the divisor, lowering [tokensPerShare] and creating a residual
      [(totalShares' - paidOutShares) * tps] that flows to the DAO fee
      recipient.

    Conservation: [sum(amts) + daoFee + dust = amount] when totalShares' > 0.
*)
Definition distributeAmounts_with_dao_fee
    (s : Storage) (amount : U256.t) (isRSR : bool)
    (feeNumerator feeDenominator : U256.t)
    : DistResult.t :=
  let pair := totals s in
  let rTokenTotal := fst pair in
  let rsrTotal    := snd pair in
  let inflation := feeShareInflation rTokenTotal rsrTotal feeNumerator feeDenominator in
  let totalShares :=
    if isRSR then rsrTotal + inflation else rTokenTotal in
  if totalShares =? 0 then
    {| DistResult.amts := nil;
       DistResult.daoFee := 0;
       DistResult.dust := amount; |}
  else
    let tps := amount / totalShares in
    let amts := transferAmts_aux s tps isRSR in
    let paid := paidOutShares s isRSR in
    let daoFee :=
      if isRSR then tps * (totalShares - paid) else 0 in
    let consumed := List.fold_right Z.add 0 amts in
    {| DistResult.amts := amts;
       DistResult.daoFee := daoFee;
       DistResult.dust := amount - consumed - daoFee; |}.

End Distributor.
