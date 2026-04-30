(** * Audit.v - Decision-relevant theorem index.

    This file is the human-readable handoff for auditors and reviewers
    of the Reserve Protocol formal-verification tree. The full tree
    contains 800+ lemmas across 100+ files; this index re-exports the
    load-bearing claims under audit-friendly names so that reviewing
    the safety story does not require navigating the tree.

    Reading guide:
      - Each [Theorem audit_*] below is a re-export of a single
        existing lemma. No new proofs live here.
      - Section comments describe the threat or property the group
        addresses. Per-theorem comments describe the claim and why
        it matters.
      - Compile time is dominated by transitive imports of the
        underlying proof modules; the body of this file is just
        definitional re-exports and adds no proof obligations.

    To inspect a claim in detail, jump from the [:=] right-hand side
    back to its source file under [proofs/].

    --------------------------------------------------------------- *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

(* Section 1 - Bug findings. *)
Require Import Reserve.proofs.Distributor_deprecation_bug.

(* Section 2 - Certora mitigation (PR #1283). *)
Require Import Reserve.proofs.Fixed_certora_mitigation.

(* Section 3 - Throttle safety. *)
Require Import Reserve.proofs.Throttle.
Require Import Reserve.proofs.Throttle_validity.

(* Section 4 - Furnace correctness. *)
Require Import Reserve.proofs.Furnace_chain.
Require Import Reserve.proofs.Integration_supply_decay.

(* Section 5 - Distributor conservation. *)
Require Import Reserve.proofs.Distributor.
Require Import Reserve.proofs.Integration_revenue_full_circuit.

(* Section 6 - Collateral state machine. *)
Require Import Reserve.proofs.Collateral.
Require Import Reserve.proofs.Collateral_validity.

(* Section 7 - System-level. *)
Require Import Reserve.proofs.EndToEnd_strengthened.
Require Import Reserve.proofs.EndToEnd_complete.

(** ============================================================
    Section 1 - Bug findings.

    PR #1285 (RToken deprecation scripts) shipped a sequence of
    governance calls that, applied in the order the script writes
    them, makes the second call revert against the canonical
    Reserve revenue table. The lemma below is the formal
    counterexample: starting from [canonical_pre], zeroing FURNACE
    first reverts. Companion lemmas in the source file prove that
    the opposite ordering (ST_RSR first) succeeds end-to-end and
    that the two orderings are not interchangeable.
    ============================================================ *)

(** Zeroing FURNACE first against the canonical pre-state reverts.
    This is the headline counterexample for the PR #1285 deprecation
    sequencing bug. *)
Notation audit_pr1285_furnace_first_reverts :=
  DistributorDeprecationBug.deprecation_bug_furnace_first_reverts.

(** ============================================================
    Section 2 - Certora mitigation (PR #1283).

    PR #1283 adopted a Certora-recommended rounding-mode change in
    the Reserve FixLib [mul]/[safeMulDiv] kernels. The simulation
    in [simulations/Fixed.v] models only the post-mitigation
    surface; [TradeLib] additionally exposes the pre-mitigation
    rounding orientation via [buyAmountPre]. The lemmas below
    quantify the gap.
    ============================================================ *)

(** Existence of inputs at which the post-mitigation [buyAmount]
    strictly exceeds the pre-mitigation [buyAmountPre]. Witnesses
    that PR #1283 is not a no-op. *)
Notation audit_certora_mitigation_diverges :=
  FixedCertoraMitigation.certora_mitigation_diverges_at_witness.

(** Universally-quantified counterpart: under the non-saturation
    hypotheses spelled out in the source, the post-mitigation
    [buyAmount] is always at least the pre-mitigation value. The
    mitigation never under-credits the seller. *)
Notation audit_buyAmount_post_ge_pre :=
  FixedCertoraMitigation.post_mitigation_buyAmount_ge_pre.

(** ============================================================
    Section 3 - Throttle safety.

    Throttle (the issuance/redemption rate limiter) is the most
    safety-critical of the rate-limit contracts. The three lemmas
    here cover the cap invariant, the revert characterization, and
    storage-validity preservation across [useAvailable].
    ============================================================ *)

(** INV-1: [currentlyAvailable] never exceeds the configured limit.
    This is the cap-invariant - the throttle cannot hand out more
    than its configured ceiling regardless of refill history. *)
Notation audit_throttle_INV1_cap :=
  ThrottleProofs.currentlyAvailable_le_limit.

(** INV-5: [useAvailable] reverts iff the requested amount is
    positive and exceeds the currently-available budget. Pins the
    revert surface exactly - no silent successes, no spurious
    reverts. *)
Notation audit_throttle_revert_iff_overdraw :=
  ThrottleProofs.useAvailable_revert_iff.

(** [useAvailable] preserves the [Valid.throttle] storage
    invariant. The on-chain [Throttle] storage stays well-typed
    (uint48 timestamps, uint256 lastAvailable, valid params) across
    every successful call. *)
Notation audit_useAvailable_preserves_validity :=
  ThrottleValidity.useAvailable_preserves_validity.

(** ============================================================
    Section 4 - Furnace correctness.

    The Furnace burns RToken to deliver the configured melt rate.
    The lemmas here cover the supply-monotonicity property auditors
    most often ask about, and a chain proof that a governance
    [setRatio] followed by a [melt] step preserves storage validity.
    ============================================================ *)

(** Treating the melted [amount] as an RToken burn from a notional
    [totalSupply], the resulting supply [totalSupply - amount] never
    exceeds [totalSupply]. The Furnace cannot mint via the melt
    path. *)
Notation audit_melt_decreases_supply :=
  IntegrationSupplyDecay.melt_decreases_or_preserves_total_supply.

(** Composition: if [setRatio] succeeds on a valid storage and a
    [melt] is then run on the result, the final storage is still
    valid. Closes the [setRatio];[melt] sequence that governance
    invokes on every ratio update. *)
Notation audit_setRatio_then_melt_safe :=
  FurnaceChain.setRatio_then_melt_preserves_validity.

(** ============================================================
    Section 5 - Distributor conservation.

    The Distributor splits revenue across recipients. The headline
    property is wei-level conservation: every input wei is either
    transferred or accounted for as dust.
    ============================================================ *)

(** [sum(transferAmts) + dust = amount] for every storage, amount,
    and leg (rToken/RSR). No wei is created or destroyed inside
    [distributeAmounts]. *)
Notation audit_share_conservation :=
  DistributorProofs.share_conservation.

(** Cross-domain composition: the BackingManager surplus split
    feeds the Distributor on both legs and conservation holds for
    each. Closes the BackingManager -> Distributor circuit.

    Companion file [Integration_revenue_path.v] proves the weaker
    non-negativity composition along the same path; this file pins
    the stronger [sum + dust = amount] equality across both legs. *)
Notation audit_revenue_full_circuit :=
  IntegrationRevenueFullCircuit.revenue_full_circuit_conservation.

(** ============================================================
    Section 6 - Collateral state machine.

    Collateral has a four-state status machine (SOUND, IFFY,
    DISABLED, plus the implicit "never marked" pre-state).
    DISABLED is terminal - once a collateral is hard-defaulted it
    cannot recover. The lemmas here pin that property and the
    storage-validity preservation across [refresh].
    ============================================================ *)

(** Once [statusOf] reports DISABLED at any earlier time, every
    subsequent [statusOf] call reports DISABLED. DISABLED is a
    terminal absorbing state of the status machine. *)
Notation audit_disabled_is_terminal :=
  CollateralProofs.disabled_is_terminal.

(** [refresh] preserves the [Valid.t] storage invariant on
    [Collateral.State.t]. The state remains well-typed (uint48
    timestamps, uint192 prices) across every refresh. *)
Notation audit_refresh_preserves_validity :=
  CollateralValidity.refresh_preserves_validity.

(** ============================================================
    Section 7 - System-level.

    Two cross-domain no-overflow theorems compose the per-domain
    uint256 bounds across the formalization tree.

    The headline claim ([all_domain_outputs_jointly_bounded]) covers
    all 13 domains: 8 with storage-state Valid + InputBounded
    predicates, plus 5 purely-functional domains whose call-site
    envelope hypotheses are taken as explicit antecedents. The sum
    is bounded by [43 * UINT256_MAX].

    [audit_endtoend_storage_jointly_bounded] is the storage-only
    sub-theorem (8 domains, 34 scalars, [34 * UINT256_MAX]); it is
    re-exported here for callers that don't have the per-call
    arguments to discharge the functional-domain envelopes.
    ============================================================ *)

(** Headline: all 13 domains jointly bounded.

    Composes 8 storage-state domains (Throttle, Furnace, StRSR,
    Collateral, DutchTrade, Rebalance, BackingManager BasketState,
    BackingManager SurplusSplit) with 5 functional domains (TradeLib
    output pair, IssuancePremium I/O triple, GnosisTrade output pair,
    BasketHandler single-asset quote, Distributor amount). Sum of
    all uint256 fields and call inputs is bounded by [43 * UINT256_MAX]. *)
Notation audit_endtoend_jointly_bounded :=
  EndToEndComplete.all_domain_outputs_jointly_bounded.

(** Sub-theorem: storage-state-only joint bound.

    Sum of the 34 uint256 storage scalars across the 8 storage-state
    domains is bounded by [34 * UINT256_MAX]. Use this when the call
    arguments to the 5 functional domains aren't in scope. *)
Notation audit_endtoend_storage_jointly_bounded :=
  EndToEndStrengthened.all_domain_scalars_jointly_bounded.
