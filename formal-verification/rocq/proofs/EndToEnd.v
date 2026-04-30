(** System-level end-to-end joint-bound theorem (initial 3-domain version).

    This file is the **first** of three system-level joint-bound
    theorems in the tree. They form a progression of strengthening
    cross-domain compositions:

      1. [EndToEnd.v]              - 3 storage domains  (this file)
                                     Throttle + Furnace + StRSR ratio
                                     Bound: [<= 5 * UINT256_MAX]

      2. [EndToEnd_strengthened.v] - 8 storage-state domains
                                     Adds Collateral, DutchTrade, Rebalance,
                                     and BackingManager (BasketState +
                                     SurplusSplit), with Furnace and StRSR
                                     contributions widened.
                                     Bound: [<= 34 * UINT256_MAX]

      3. [EndToEnd_complete.v]     - all 13 domains (8 storage + 5 functional)
                                     Adds the call-arg-bounded functional
                                     domains (TradeLib, IssuancePremium,
                                     GnosisTrade, BasketHandler, Distributor)
                                     via explicit envelope hypotheses.
                                     Bound: [<= 43 * UINT256_MAX]

    The [Audit.v] handoff index re-exports [EndToEnd_complete] as the
    headline [audit_endtoend_jointly_bounded] and this file's three
    domains as [audit_endtoend_storage_jointly_bounded]'s strict
    subset. The [_strengthened] variant is the right intermediate
    handle for callers that have storage states but no per-call
    arguments to discharge functional-domain envelopes.

    --------------------------------------------------------------- *)

(** A modest but real cross-domain correctness statement: the headline
    uint256 quantities maintained by three independent storage domains
    — the supply Throttle, the Furnace, and the StRSR module — are
    each individually bounded by their per-domain validity invariants,
    so their pointwise sum is bounded by the matching multiple of
    [UINT256_MAX].

    Concretely, given that
      - the Throttle satisfies [Valid.throttle] (so [lastAvailable] is
        a uint256 and [params.amtRate] is a uint256),
      - the Furnace storage satisfies [Furnace.Valid.t] (so
        [lastPayoutBal] is a uint256 and [lastPayout] is a uint256),
      - the StRSR storage satisfies [StRSR.Valid.t] (which gives
        [0 <= ratio <= FIX_ONE_Z]),
    we conclude that the four-way sum

      throttle.lastAvailable
      + throttle.params.amtRate
      + furnace.lastPayoutBal
      + furnace.lastPayout

    fits in [4 * UINT256_MAX], and additionally that StRSR's [ratio]
    is dominated by [UINT256_MAX] (since [FIX_ONE_Z = 10^18] is many
    orders of magnitude smaller).

    This is the same shape of proof as
    [Integration_throttle_furnace.v], extended across one more domain
    boundary (Furnace's second uint256 field plus an StRSR ratio
    bound). It is purely additive composition of per-domain validity
    upper bounds, which is exactly the pattern the per-domain [Valid]
    records were designed to support. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Throttle.
Require Import Reserve.simulations.Furnace.
Require Import Reserve.simulations.StRSR.

Module EndToEnd.

Import FixLib.
Import ThrottleLib.

(** Joint uint256 bound across Throttle and Furnace headline fields:
    four uint256-bounded quantities sum to at most [4 * UINT256_MAX]. *)
Lemma system_uint256_fields_bounded
    (t : Throttle.t) (f : Furnace.Storage.t) :
  Valid.throttle t ->
  Furnace.Valid.t f ->
  t.(Throttle.lastAvailable)
  + t.(Throttle.params).(Params.amtRate)
  + f.(Furnace.Storage.lastPayoutBal)
  + f.(Furnace.Storage.lastPayout)
    <= 4 * UINT256_MAX.
Proof.
  intros [Hp_valid _ Hav_u256] [_ _ Hlp Hlpb].
  destruct Hp_valid as [Hamt_u256 _ _].
  unfold U256.Valid.t in Hav_u256, Hamt_u256.
  unfold UINT256_MAX in *.
  lia.
Qed.

(** StRSR's [ratio] is many orders of magnitude smaller than
    [UINT256_MAX]: it lives in [0, FIX_ONE_Z] = [0, 10^18], whereas
    [UINT256_MAX = 2^256 - 1 ≈ 1.16 * 10^77]. *)
Lemma stRSR_ratio_le_uint256_max
    (s : StRSR.Storage.t) :
  StRSR.Valid.t s ->
  s.(StRSR.Storage.ratio) <= UINT256_MAX.
Proof.
  intros [_ _ _ Hratio _].
  destruct Hratio as [_ Hratio_hi].
  unfold StRSR.FIX_ONE_Z, FixLib.FIX_ONE, FixLib.FIX_SCALE in Hratio_hi.
  unfold UINT256_MAX.
  (* 10^18 <= 2^256 - 1: the LHS is a tiny constant; trivially true. *)
  assert (Hpow : 10 ^ 18 <= 2 ^ 256 - 1) by (vm_compute; discriminate).
  lia.
Qed.

(** Headline system-level theorem: the four uint256-bounded fields
    across Throttle and Furnace plus StRSR's bounded ratio jointly
    fit in [5 * UINT256_MAX]. This composes the two lemmas above. *)
Theorem system_invariants
    (t : Throttle.t) (f : Furnace.Storage.t) (s : StRSR.Storage.t) :
  Valid.throttle t ->
  Furnace.Valid.t f ->
  StRSR.Valid.t s ->
  t.(Throttle.lastAvailable)
  + t.(Throttle.params).(Params.amtRate)
  + f.(Furnace.Storage.lastPayoutBal)
  + f.(Furnace.Storage.lastPayout)
  + s.(StRSR.Storage.ratio)
    <= 5 * UINT256_MAX.
Proof.
  intros Ht Hf Hs.
  pose proof (system_uint256_fields_bounded t f Ht Hf) as Htf.
  pose proof (stRSR_ratio_le_uint256_max s Hs) as Hr.
  destruct Hs as [_ _ _ Hratio _].
  destruct Hratio as [Hratio_lo _].
  lia.
Qed.

End EndToEnd.
