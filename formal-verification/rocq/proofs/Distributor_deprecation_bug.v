(** Distributor deprecation sequencing bug — formal counterexample.

    Background:
      PR #1285 (RToken deprecation scripts) introduced
      [scripts/deprecation/generate-deprecation-proposals.py]. Lines 75-81
      of that script issue two governance calls:

        6a)  setDistribution(FURNACE, RevenueShare(0, 0))
        6b)  setDistribution(ST_RSR,  RevenueShare(0, 10000))

      [Distributor.sol#setDistribution] re-checks the cumulative-share
      floor [_ensureSufficientTotal] AFTER EACH individual call:

        require(uint256(rTokenTotal) + uint256(rsrTotal) >= MAX_DISTRIBUTION)
                                                                 (= 10000)

      For the canonical Reserve table — FURNACE = (4000, 0),
      ST_RSR = (0, 6000) — call 6a zeroes out FURNACE, dropping the
      cumulative total from 10000 to 6000. The post-state fails the
      check and the call reverts.

      The CAS witness [cas/deprecation/rtoken_deprecation.gp #D4] sweeps
      pre-states and emits 5/8 reverts. This Rocq file pins down the
      canonical case as a closed counterexample, plus a "fix witness"
      lemma showing that flipping the call order succeeds.

    What we model:
      A small extension to the [Distributor] simulation: a [setDistribution]
      function that updates the per-destination [RevenueShare] in storage,
      then runs the [_ensureSufficientTotal] gate. Returns [Result.Success
      s'] or [Result.Revert].

    What we do NOT model:
      The other production guards in [_setDistribution] (FURNACE/ST_RSR
      cross-leg restrictions, MAX_DESTINATIONS, etc.). The bug in scope
      is purely about the cumulative-share floor and the order of two
      calls — the other guards never fire on the canonical inputs.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Distributor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorDeprecationBug.

Import Distributor.

(** Two-constructor result mirroring the upstream simulation pattern
    used in [simulations/BackingManager.v]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Magic destinations from [Distributor.sol#L32-L33]. *)
Definition FURNACE_addr : U256.t := 1.
Definition ST_RSR_addr  : U256.t := 2.

(** [setRow s dest share] mirrors [_setDistribution]'s storage write.
    We treat storage as a simple list of [(addr, share)] entries:
    update-in-place if [dest] is present; otherwise append.

    The on-chain version uses an [EnumerableSet] keyed by address; for
    the cumulative-total math (the only thing this lemma cares about)
    the difference is irrelevant — both yield the same [totals]. *)
Fixpoint setRow (s : Storage) (dest : U256.t) (share : RevenueShare.t)
  : Storage :=
  match s with
  | nil => [(dest, share)]
  | cons (a, sh) rest =>
    if a =? dest then cons (dest, share) rest
    else cons (a, sh) (setRow rest dest share)
  end.

(** [setDistribution s dest share] mirrors [Distributor.sol#L61-L71]:
    write the row, then check [_ensureSufficientTotal] on the new totals.
    We omit the precursor [distributeTokenToBuy] sweeps — they are
    independent of the cumulative-floor check. *)
Definition setDistribution
    (s : Storage) (dest : U256.t) (share : RevenueShare.t)
  : Result.t Storage :=
  let s' := setRow s dest share in
  let pair := totals s' in
  let rTokenTotal := fst pair in
  let rsrTotal    := snd pair in
  if rTokenTotal + rsrTotal <? MAX_DISTRIBUTION then
    Result.Revert 0 32
  else
    Result.Success s'.

(** Convenience: post-state [Storage] of a successful call, or [s] if it
    reverted. We never use this on a revert-path lemma. *)
Definition successState (r : Result.t Storage) (fallback : Storage) : Storage :=
  match r with
  | Result.Success s' => s'
  | Result.Revert _ _ => fallback
  end.

(** Canonical Reserve pre-state: FURNACE owns the rToken side at 4000,
    ST_RSR owns the RSR side at 6000. Sum = 10000 = MAX_DISTRIBUTION,
    invariant holds. *)
Definition canonical_pre : Storage :=
  [ (FURNACE_addr, {| RevenueShare.rTokenDist := 4000;
                      RevenueShare.rsrDist    := 0    |});
    (ST_RSR_addr,  {| RevenueShare.rTokenDist := 0;
                      RevenueShare.rsrDist    := 6000 |}) ].

(** Sanity: the canonical pre-state sits exactly at the floor. *)
Lemma canonical_pre_totals :
  totals canonical_pre = (4000, 6000).
Proof. reflexivity. Qed.

Lemma canonical_pre_satisfies_floor :
  fst (totals canonical_pre) + snd (totals canonical_pre) = MAX_DISTRIBUTION.
Proof. reflexivity. Qed.

(** ============================================================
    THEOREM 1 (the bug):
      Starting from the canonical pre-state, calling
        setDistribution(FURNACE, (0,0))
      first — exactly what generate-deprecation-proposals.py does at
      lines 75-81 — REVERTS, because the post-write totals (0, 6000)
      sum to 6000 < 10000 = MAX_DISTRIBUTION.
    ============================================================ *)
Theorem deprecation_bug_furnace_first_reverts :
  setDistribution canonical_pre FURNACE_addr
    {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 0 |}
  = Result.Revert 0 32.
Proof. reflexivity. Qed.

(** A slightly more general statement: for any pre-state where FURNACE
    owns all of the rToken-side total (i.e. [rsrTotal < MAX_DISTRIBUTION]
    pre-write and FURNACE's [rTokenDist] is the full backstop), zeroing
    FURNACE first must revert. We give the canonical-shape version:
    pre = [(FURNACE, (rt, 0)); (ST_RSR, (0, rs))] with rt + rs >= 10000
    but rs < 10000 implies revert. *)
Theorem deprecation_bug_general_furnace_first_reverts :
  forall (rt rs : U256.t),
    rs <? MAX_DISTRIBUTION = true ->
    let pre := [ (FURNACE_addr, {| RevenueShare.rTokenDist := rt;
                                   RevenueShare.rsrDist    := 0  |});
                 (ST_RSR_addr,  {| RevenueShare.rTokenDist := 0;
                                   RevenueShare.rsrDist    := rs |}) ] in
    setDistribution pre FURNACE_addr
      {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 0 |}
    = Result.Revert 0 32.
Proof.
  intros rt rs Hrs.
  unfold setDistribution. simpl setRow.
  change (FURNACE_addr =? FURNACE_addr) with true.
  cbv iota beta.
  simpl totals. simpl fst. simpl snd.
  (* The if-condition simplifies to [(0 + (rs + 0)) <? 10000] which equals
     [rs <? 10000] = [Hrs] = true. *)
  assert (Hrewrite : forall a, ((0 + (a + 0)) <? MAX_DISTRIBUTION) = (a <? MAX_DISTRIBUTION))
    by (intros a; f_equal; lia).
  rewrite Hrewrite, Hrs.
  reflexivity.
Qed.

(** ============================================================
    THEOREM 2 (the fix witness):
      Performing the calls in the OPPOSITE order — ST_RSR first,
      then FURNACE — succeeds end-to-end, landing on the intended
      post-state (0, 10000).
    ============================================================ *)

(** The intended post-state of the deprecation: FURNACE removed (0,0),
    ST_RSR owning the entire 10000-share RSR allocation. We expose it
    so callers can pattern-match on the success value. *)
Definition deprecation_post : Storage :=
  [ (FURNACE_addr, {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 0     |});
    (ST_RSR_addr,  {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 10000 |}) ].

Theorem deprecation_bug_strsr_first_succeeds :
  let r1 := setDistribution canonical_pre ST_RSR_addr
              {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 10000 |} in
  match r1 with
  | Result.Success s1 =>
      setDistribution s1 FURNACE_addr
        {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 0 |}
      = Result.Success deprecation_post
  | Result.Revert _ _ => False
  end.
Proof. reflexivity. Qed.

(** ============================================================
    THEOREM 3: the fix is *necessary*, not merely sufficient. The two
    orderings produce different end-states (Revert vs Success). This
    rules out the naive "well, it reaches the same place either way"
    objection.
    ============================================================ *)
Theorem deprecation_bug_orderings_differ :
  let r_bad :=
    setDistribution canonical_pre FURNACE_addr
      {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 0 |} in
  let r_good_step1 :=
    setDistribution canonical_pre ST_RSR_addr
      {| RevenueShare.rTokenDist := 0; RevenueShare.rsrDist := 10000 |} in
  r_bad = Result.Revert 0 32
  /\ match r_good_step1 with
     | Result.Success _ => True
     | Result.Revert _ _ => False
     end.
Proof. split; reflexivity. Qed.

End DistributorDeprecationBug.
