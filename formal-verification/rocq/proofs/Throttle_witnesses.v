(** Throttle witness corpus.

    Companion to [proofs/Throttle_xcheck.v]: where [Throttle_xcheck] pins the
    seven canonical CAS rows from [cas/throttle/cap_invariant.gp], this file
    nails down additional closed-form witnesses that exercise boundary
    behaviour the xcheck file does not target:

      - [currentlyAvailable] at boundary timestamps:
          * now = lastTimestamp           (delta = 0; no refill)
          * now = lastTimestamp + 1800    (half-hour; partial refill)
          * now = UINT48_MAX              (max uint48; saturates at limit)
      - [useAvailable] success path with positive amount at the exact
        [available] boundary (consume-everything probe at half-hour).
      - [useAvailable] revert path with positive amount = available + 1
        (one-wei-over revert).
      - [useAvailable] with negative amounts at multiple magnitudes
        (-1 wei, -10^21 wei, -limit) starting from a partially-drained
        state, verifying restore-with-no-cap-on-add.
      - Multi-call sequences: [useAvailable] then [useAvailable] from
        the resulting state (positive then positive; positive then
        negative).
      - [hourlyLimit] saturation: when supply * pctRate / FIX_ONE > amtRate,
        the percentage branch dominates (canonical case at supply = 1B,
        pctRate = 1%/hr).

    Every witness is a closed evaluation discharged by [vm_compute] +
    [reflexivity]. No admits.

    Reference:
      - [cas/throttle/cap_invariant.gp] for sweep ranges.
      - [simulations/Throttle.v]: [hourlyLimit], [currentlyAvailable],
        [useAvailable], [Throttle.t], [Params.t].
      - [proofs/Throttle_xcheck.v] for the calibration-row witnesses.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Throttle.

Module ThrottleWitnesses.

Import ThrottleLib.

(** Same calibration as [Throttle_xcheck.v]:
      amtRate = 10^24, pctRate = 10^16, supply = 10^27 ⇒ limit = 10^25. *)
Definition cal_amtRate : U256.t := 10^24.
Definition cal_pctRate : U256.t := 10^16.
Definition cal_supply  : U256.t := 10^27.
Definition cal_limit   : U256.t := 10^25.

Definition cal_params : Params.t := {|
  Params.amtRate := cal_amtRate;
  Params.pctRate := cal_pctRate;
|}.

(** Fresh throttle: lastTs = 0, lastAvailable = 0. *)
Definition cal_throttle_fresh : Throttle.t := {|
  Throttle.params        := cal_params;
  Throttle.lastTimestamp := 0;
  Throttle.lastAvailable := 0;
|}.

(** A "mid-state" throttle: lastTs = 1000, lastAvailable = 5 * 10^24
    (= half of limit). Used to probe boundary timestamps and useAvailable
    chained from a non-trivial state. *)
Definition cal_throttle_mid : Throttle.t := {|
  Throttle.params        := cal_params;
  Throttle.lastTimestamp := 1000;
  Throttle.lastAvailable := 5 * 10^24;
|}.

(** ============================================================
    (1) currentlyAvailable at boundary timestamp now = lastTimestamp:
        delta = 0, no refill ⇒ available = lastAvailable.
    ============================================================ *)
Lemma w_currentlyAvailable_at_lastTs :
  currentlyAvailable cal_throttle_mid cal_limit 1000 = 5 * 10^24.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (2) currentlyAvailable at lastTs + ONE_HOUR/2 = 1000 + 1800 = 2800:
        delta = 1800, refill = limit * 1800 / 3600 = limit / 2.
        Starting at 5e24 (= limit/2), result = limit/2 + limit/2 = limit.
    ============================================================ *)
Lemma w_currentlyAvailable_at_half_hour :
  currentlyAvailable cal_throttle_mid cal_limit 2800 = cal_limit.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (3) currentlyAvailable at now = UINT48_MAX:
        far-future time, lastAvailable = 0, lastTs = 0 ⇒ saturates at limit.
    ============================================================ *)
Lemma w_currentlyAvailable_at_uint48_max :
  currentlyAvailable cal_throttle_fresh cal_limit UINT48_MAX = cal_limit.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (4) useAvailable with positive amount = currentlyAvailable, success.
        At cal_throttle_mid with now = 2800, currentlyAvailable = limit.
        Consuming exactly limit drives lastAvailable to 0.
    ============================================================ *)
Lemma w_useAvailable_consume_all :
  match useAvailable cal_throttle_mid cal_supply cal_limit 2800 with
  | Result.Success t' => t'.(Throttle.lastAvailable) = 0
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (5) useAvailable with positive amount = available + 1: revert.
        At cal_throttle_mid with now = 2800, available = limit;
        asking limit + 1 must revert.
    ============================================================ *)
Lemma w_useAvailable_one_over_reverts :
  exists ps qs,
    useAvailable cal_throttle_mid cal_supply (cal_limit + 1) 2800
    = Result.Revert ps qs.
Proof. vm_compute. exists 0. exists 32. reflexivity. Qed.

(** ============================================================
    (6) useAvailable with amount = -1: restore by 1 wei.
        At fresh state with now = 1800 (half-hour refill),
        currentlyAvailable = limit/2 = 5*10^24.
        Restoring 1 wei ⇒ lastAvailable = 5*10^24 + 1.
    ============================================================ *)
Lemma w_useAvailable_negative_one_wei :
  match useAvailable cal_throttle_fresh cal_supply (-1) 1800 with
  | Result.Success t' => t'.(Throttle.lastAvailable) = 5 * 10^24 + 1
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (7) useAvailable with amount = -10^21: restore mid-magnitude.
        From fresh + half-hour refill (= limit/2 = 5*10^24),
        result = 5*10^24 + 10^21.
    ============================================================ *)
Lemma w_useAvailable_negative_mid :
  match useAvailable cal_throttle_fresh cal_supply (-(10^21)) 1800 with
  | Result.Success t' => t'.(Throttle.lastAvailable) = 5 * 10^24 + 10^21
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (8) useAvailable with amount = -limit: restore by full limit
        (the simulation does not cap on add — cap is enforced lazily by
        currentlyAvailable on the next call).
        From fresh + half-hour refill, lastAvailable becomes
        limit/2 + limit = 1.5 * limit = 15 * 10^24.
    ============================================================ *)
Lemma w_useAvailable_negative_limit :
  match useAvailable cal_throttle_fresh cal_supply (-cal_limit) 1800 with
  | Result.Success t' => t'.(Throttle.lastAvailable) = 15 * 10^24
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (9) Multi-call: useAvailable(+10^21) then useAvailable(+10^21).
        From fresh state at now = 3600 (full hour ⇒ available = limit),
        first call ⇒ lastAvailable = limit - 10^21.
        Second call at the same now (delta = 0) ⇒ available = limit - 10^21,
        consume 10^21 ⇒ lastAvailable = limit - 2*10^21.
    ============================================================ *)
Lemma w_useAvailable_chain_pos_pos :
  match useAvailable cal_throttle_fresh cal_supply (10^21) 3600 with
  | Result.Success t1 =>
      match useAvailable t1 cal_supply (10^21) 3600 with
      | Result.Success t2 =>
          t2.(Throttle.lastAvailable) = cal_limit - 2 * 10^21
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (10) Multi-call: useAvailable(+10^21) then useAvailable(-10^21).
         From fresh state at now = 3600, first call drops lastAvailable
         by 10^21 (= limit - 10^21). Second call (delta = 0) restores
         10^21 ⇒ lastAvailable = limit.
    ============================================================ *)
Lemma w_useAvailable_chain_pos_neg :
  match useAvailable cal_throttle_fresh cal_supply (10^21) 3600 with
  | Result.Success t1 =>
      match useAvailable t1 cal_supply (-(10^21)) 3600 with
      | Result.Success t2 =>
          t2.(Throttle.lastAvailable) = cal_limit
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (11) hourlyLimit pct-saturation: at calibration, the percentage branch
         dominates the amtRate floor.
           supply * pctRate / FIX_ONE = 10^27 * 10^16 / 10^18 = 10^25,
         which is greater than amtRate = 10^24. So hourlyLimit = 10^25.
         (Distinct from the xcheck row only in framing — this isolates
         the max-branch selection at the calibration ratio.)
    ============================================================ *)
Lemma w_hourlyLimit_pct_dominates :
  hourlyLimit cal_throttle_fresh cal_supply = 10^25.
Proof. vm_compute. reflexivity. Qed.

(** ============================================================
    (12) hourlyLimit amtRate-floor: at small supply, the amtRate floor
         dominates the percentage product.
           supply = 10^18, pctRate = 10^16
           ⇒ supply * pctRate / FIX_ONE = 10^18 * 10^16 / 10^18 = 10^16,
         which is less than amtRate = 10^24. So hourlyLimit = 10^24.
    ============================================================ *)
Lemma w_hourlyLimit_amt_floor :
  hourlyLimit cal_throttle_fresh (10^18) = cal_amtRate.
Proof. vm_compute. reflexivity. Qed.

End ThrottleWitnesses.
