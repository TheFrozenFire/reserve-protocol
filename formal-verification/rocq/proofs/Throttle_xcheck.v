(** Throttle simulation × CAS witness cross-check.

    Evaluates the [ThrottleLib] simulation on the same calibration inputs
    used by [cas/throttle/cap_invariant.gp] and asserts identical outputs.
    Any divergence between the Rocq simulation and the CAS witness corpus
    fails the build.

    Calibration (matching the CAS script):
      amtRate = 1M  qRTok/hr   = 10^6 * FIX_ONE  = 10^24
      pctRate = 1%/hr           = FIX_ONE / 100  = 10^16
      supply  = 1B  qRTok       = 10^9 * FIX_ONE = 10^27
      => limit = max(10^24, supply * pctRate / FIX_ONE) = 10^25

    The CAS witness corpus reports limit = 10000000000000000000000000;
    the lemmas below verify the simulation produces the same number on
    each probe.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Throttle.

Module ThrottleXCheck.

Import ThrottleLib.

Definition cal_amtRate : U256.t := 10^24.
Definition cal_pctRate : U256.t := 10^16.
Definition cal_supply  : U256.t := 10^27.
Definition cal_limit   : U256.t := 10^25.

Definition cal_params : Params.t := {|
  Params.amtRate := cal_amtRate;
  Params.pctRate := cal_pctRate;
|}.

Definition cal_throttle_fresh : Throttle.t := {|
  Throttle.params        := cal_params;
  Throttle.lastTimestamp := 0;
  Throttle.lastAvailable := 0;
|}.

(** ----- CAS reports: limit = 10^25 (= 10000000000000000000000000). ----- *)
Lemma xcheck_limit :
  hourlyLimit cal_throttle_fresh cal_supply = cal_limit.
Proof. vm_compute. reflexivity. Qed.

(** ----- CAS reports: currentlyAvailable at delta = ONE_HOUR,
        lastAvailable = 0, lastTs = 0  =  limit (= 10^25).
    This is the saturation point: a full hour of refill at rate=limit. ----- *)
Lemma xcheck_currentlyAvailable_at_one_hour :
  currentlyAvailable cal_throttle_fresh cal_limit 3600 = cal_limit.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-3 witness: use(+10^21) at full state decreases by 10^21.
    Calibration uses smaller probes; we re-state the canonical one. ----- *)
Lemma xcheck_use_positive_subtracts :
  match useAvailable cal_throttle_fresh cal_supply (10^21) 3600 with
  | Result.Success t' => t'.(Throttle.lastAvailable) = cal_limit - 10^21
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-5 witness: use(amount = limit) at full state succeeds.
    CAS prints "use(amount = limit) -> ok". ----- *)
Lemma xcheck_use_at_limit_succeeds :
  exists t', useAvailable cal_throttle_fresh cal_supply cal_limit 3600
             = Result.Success t'.
Proof. vm_compute. eexists. reflexivity. Qed.

(** ----- INV-5 witness: use(amount = limit+1) at full state reverts.
    CAS prints "use(amount = limit + 1) -> revert". ----- *)
Lemma xcheck_use_over_limit_reverts :
  exists ps qs,
    useAvailable cal_throttle_fresh cal_supply (cal_limit + 1) 3600
    = Result.Revert ps qs.
Proof. vm_compute. exists 0. exists 32. reflexivity. Qed.

(** ----- Monotonicity probe: currentlyAvailable at now=1799 ≤ at now=3600.
    CAS sweeps {0, 60, 600, 1799, 1800, 3000, 3599, 3600, 7200, UINT48_MAX}. ----- *)
Lemma xcheck_monotone_one_step :
  currentlyAvailable cal_throttle_fresh cal_limit 1799
  <= currentlyAvailable cal_throttle_fresh cal_limit 3600.
Proof. vm_compute. discriminate. Qed.

(** ----- Saturated state: at any [now] >= ONE_HOUR with lastAvailable = 0
    and lastTs = 0, currentlyAvailable saturates at limit. ----- *)
Lemma xcheck_saturated_at_two_hours :
  currentlyAvailable cal_throttle_fresh cal_limit 7200 = cal_limit.
Proof. vm_compute. reflexivity. Qed.

End ThrottleXCheck.
