(** BasketHandler simulation.

    Mirrors protocol/contracts/p1/BasketHandler.sol. Two layers:

      Layer 1 — Quote math kernel (legacy, unchanged):
        [quote_one], [quote], [quoteQuantities], [redeem_one] convert a
        {BU} basket-units quantity into per-asset {qTok} quantities. The
        algebraic core, modeling
            qTok_i = refAmt_i * baskets / FIX_ONE  (rounded by [mode])
        with refPerTok = FIX_ONE collapsed away (kept out of scope; the
        asset-registry / oracle / decimals layer is intentionally OUT of
        scope here).

      Layer 2 — Basket-state lifecycle (new):
        [setPrimeBasket] and [refreshBasket] govern *what* basket the
        quote functions are invoked against. Production: the
        [BasketConfig] is governance-mutable via [setPrimeBasket]; when
        prime collateral disables, [refreshBasket] swaps in backups via
        [BasketLibP1.nextBasket]. Modeled:
          - Storage record carrying the live basket, the prime config,
            backup configs (per target name), nonce, and the disabled
            flag.
          - [setPrimeBasket] validates target-amount bounds, basket size,
            no-duplicate erc20s, and writes the new prime config.
          - [refreshBasket] consumes a [list (erc20, AssetStatus)] (the
            input collateral statuses) and rebuilds the basket from the
            prime config plus per-target-name backup config; sets
            [disabled = true] if a target has DISABLED prime weight and
            no available backup.
        Excluded by design (see boundaries below).

    Coverage scope and boundaries:
      IN scope:
        - Storage shape: prime/backup config, basket, nonce, disabled.
        - setPrimeBasket validation+write logic.
        - refreshBasket swap logic against an explicit AssetStatus list.
        - targetAmt conservation across refresh.
        - Validity preservation for both lifecycle ops.

      OUT of scope (do NOT model):
        - Asset-registry indirection — sim TAKES the AssetStatus list as
          input; production reads it from [assetRegistry.toColl(_)].
        - Oracle layer — [pegPrice] etc. not consulted in setPrimeBasket
          or refreshBasket directly.
        - Full Collateral status state machine — modeled separately in
          [simulations/Collateral.v]; this sim consumes the boolean
          DISABLED outcome via [AssetStatus.t].
        - Governance modifier — [setPrimeBasket] is governance-gated in
          production; sim models the body, not the gate.
        - Frozen / pause flags.
        - Per-target [requireConstantConfigTargets] check (reweightable
          flag); the sim's [setPrimeBasket] is the unconditional write
          path (post the require check), parameterised over an explicit
          allow list.
        - Warmup period and basket history.
        - The targetPerRef-driven backup weight derivation: production
          divides by [targetPerRef * size]; sim distributes the
          unsoundPrimeWt evenly across surviving backups (the algebraic
          relation that makes per-target conservation auditable).

    Companion CAS witnesses:
      cas/basket_handler/quote_rounding_direction.gp
      cas/basket_handler/quote_round_trip.gp
      cas/basket_handler/set_prime_basket.gp
      cas/basket_handler/refresh_basket.gp

    Revert coverage:
      Modeled:
        - [setPrimeBasket] returns [None] on:
            - len(erc20s) != len(targetAmts), len(erc20s) = 0
              (production "invalid lengths" line 235).
            - any targetAmt outside [MIN_TARGET_AMT, MAX_TARGET_AMT]
              (production "invalid target amount" line 267).
            - duplicate erc20s in the prime list (production
              "contains duplicates" line 699 via requireValidCollArray).
            - basket length exceeds [MAX_BASKET_LENGTH] (sim-side bound;
              production has no explicit cap on prime basket length but
              [MAX_BACKUP_ERC20S = 64] caps backup arrays — we use the
              same constant for the prime list as a defensive bound).
        - [redeem_one] returns 0 on [refAmt = 0] (avoids div-by-zero;
          algebraically vacuous because production doesn't store zero
          refAmts in the basket).
      Deferred:
        - well-formed basket as a precondition on the quote layer
          (covered by [Valid.t]).
      Not modeled:
        - basket-not-set lifecycle reverts at the quote-time entry,
          oracle-failure reverts, asset-registry-mismatch reverts —
          governed upstream of the simulation.
        - Reentrancy / governance gate on [setPrimeBasket].

    Backwards-compatibility note: this file used to define
    [Definition Storage : Set := list BasketEntry.t.]. That same data is
    now [Basket : Set := list BasketEntry.t.]; the new lifecycle
    [Storage.t] is a record carrying the [basket : Basket] field plus
    config, nonce, and disabled flag. Existing proofs that referenced
    [BasketHandler.Storage] are updated in lock-step to use
    [BasketHandler.Basket] (the algebraic kernel they actually want).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module BasketHandler.

Import FixLib.

(** =================================================================
    Layer 1 — Quote math kernel (unchanged behaviour).
    =================================================================
*)

(** A [BasketEntry] is a single (asset id, refAmount) pair. The asset id
    is an opaque token identifier; we model it as [U256.t] (matching
    Address.t = U256.t in the rocq-of-solidity tree). [refAmt] is in
    {ref/BU}, uint192 fixed-point. *)
Module BasketEntry.
  Record t : Set := {
    asset  : U256.t;
    refAmt : U256.t;   (** {ref/BU}, uint192 fixed-point *)
  }.
End BasketEntry.

(** [Basket] = ordered list of basket entries.

    Renamed from the previous [Storage] definition — the new lifecycle
    [Storage.t] (below) is a record carrying [basket : Basket] plus
    config, nonce, and disabled flag. Proofs about quote semantics
    operate on [Basket]; proofs about lifecycle operations operate on
    [Storage.t]. *)
Definition Basket : Set := list BasketEntry.t.

(** Per-asset quote: [refAmt * baskets / FIX_ONE], rounded by [mode].
    Mirrors the algebraic core of [quote()]; see BasketHandler.sol#L487-L517.

    Concretely this is [FixLib.mulu_toUint refAmt baskets mode] specialised
    to "two fixed-point factors, integer result". *)
Definition quote_one
    (refAmt baskets : U256.t) (mode : RoundingMode.t) : U256.t :=
  FixLib.mulu_toUint refAmt baskets mode.

(** [quote(b, baskets, mode)] returns the per-asset {qTok} list, in the
    storage order. The on-chain [quote] also returns the parallel array of
    asset addresses; we keep them paired here so callers can reconstruct
    the (asset, qTok) tuples without an extra zip. *)
Fixpoint quote
    (b : Basket) (baskets : U256.t) (mode : RoundingMode.t)
    : list (U256.t * U256.t) :=
  match b with
  | nil => nil
  | cons e rest =>
    cons (e.(BasketEntry.asset),
          quote_one e.(BasketEntry.refAmt) baskets mode)
         (quote rest baskets mode)
  end.

(** Just the per-asset quantities, dropping the asset id. *)
Definition quoteQuantities
    (b : Basket) (baskets : U256.t) (mode : RoundingMode.t)
    : list U256.t :=
  List.map snd (quote b baskets mode).

(** FLOOR-inverse of [quote_one]: given an actual token quantity [qTok]
    held by the protocol, the maximum number of {BU} that can be
    redeemed against entry [e] without over-paying. This is the
    "user can't extract more than they put in" inverse used in the
    round-trip safety claim. *)
Definition redeem_one
    (refAmt qTok : U256.t) : U256.t :=
  if refAmt =? 0 then 0
  else (qTok * FIX_ONE) / refAmt.

(** =================================================================
    Layer 2 — Basket-state lifecycle.
    =================================================================
*)

(** Production constants (BasketHandler.sol#L31-#L35).

    [MIN_TARGET_AMT = FIX_ONE / 1e6 = 1e12]: minimum permitted
    target-amount weight. [MAX_TARGET_AMT = 1e3 * FIX_ONE = 1e21]:
    maximum permitted target-amount weight.

    [MAX_BASKET_LENGTH = MAX_BACKUP_ERC20S = 64]: production caps the
    backup array at 64 erc20s; we apply the same defensive bound to the
    prime basket length here (production has no explicit prime-basket
    length cap, but the calldata array is implicitly bounded by gas).
*)
Definition MIN_TARGET_AMT  : Z := FIX_ONE / 10^6.   (* 1e12 *)
Definition MAX_TARGET_AMT  : Z := 10^3 * FIX_ONE.   (* 1e21 *)
Definition MAX_BASKET_LENGTH : Z := 64.

(** A [PrimeEntry] is a single (erc20, targetAmt) pair as supplied to
    [setPrimeBasket]. The erc20 is an opaque token identifier. *)
Module PrimeEntry.
  Record t : Set := {
    erc20      : U256.t;
    targetAmt  : U256.t;   (** {target/BU}, uint192 fixed-point *)
    targetName : U256.t;   (** bytes32 target-unit name (e.g. "USD") *)
  }.
End PrimeEntry.

(** A [BackupEntry] is a (targetName, ordered backup erc20s, max) triple:
    if [targetName]'s prime collateral is DISABLED, [refreshBasket] picks
    up to [max] available backups from the [erc20s] list (in order).

    Production stores this as [mapping(bytes32 => BackupConfig)]; we
    flatten to a list keyed by [targetName] for the same content with a
    pure-Coq-friendly shape. *)
Module BackupEntry.
  Record t : Set := {
    targetName : U256.t;
    erc20s     : list U256.t;
    max        : U256.t;   (** maximum number of backups to use *)
  }.
End BackupEntry.

(** [AssetStatus.t]: the boolean [is_good] outcome of the Collateral
    state machine. Mirrors [BasketLibP1.goodCollateral] which returns
    [status() == SOUND && targetPerRef != 0 && refPerTok != 0]. We
    consume the boolean here; the upstream Collateral simulation
    derives it. *)
Module AssetStatus.
  Record t : Set := {
    erc20    : U256.t;
    is_good  : bool;       (** false ↔ DISABLED-or-equivalent *)
  }.
End AssetStatus.

(** Storage record carrying the lifecycle state.

    Production fields modeled (see BasketHandler.sol#L46-#L97):
      - [basket]      = production [basket] (Basket struct)
      - [primeBasket] = production [config.erc20s/targetAmts/targetNames]
      - [backupConfigs] = production [config.backups[targetName]]
      - [nonce]       = production [nonce] (uint48)
      - [disabled]    = production [disabled] (bool)

    Production fields not modeled (and why):
      - [warmupPeriod], [lastStatusTimestamp], [lastStatus]: warmup gate,
        not part of basket arithmetic.
      - [basketHistory]: backwards-compatibility reads, not arithmetic.
      - [reweightable], [enableIssuancePremium]: governance flags
        consumed elsewhere.
      - [lastCollateralized]: set by trackStatus, not setPrimeBasket /
        refreshBasket.
      - [timestamp]: only read by upstream gates (warmup), not consumed
        by quote or refresh logic.
*)
Module Storage.
  Record t : Set := {
    basket        : Basket;                  (** the live basket *)
    primeBasket   : list PrimeEntry.t;       (** governance-set prime *)
    backupConfigs : list BackupEntry.t;      (** per-target backups *)
    nonce         : U256.t;                  (** {basketNonce} *)
    disabled      : bool;                    (** post-refresh disabled *)
  }.
End Storage.

(** Convenience projection: extract the [basket] field. Used at quote
    integration sites that previously took a bare [Basket]. *)
Definition basket_of (s : Storage.t) : Basket :=
  s.(Storage.basket).

(** [Storage] convenience constructor for the empty / freshly-init state. *)
Definition empty_storage : Storage.t := {|
  Storage.basket        := nil;
  Storage.primeBasket   := nil;
  Storage.backupConfigs := nil;
  Storage.nonce         := 0;
  Storage.disabled      := true;   (** init() leaves disabled = true *)
|}.

(** ----- erc20-list duplicate check.

    Mirrors production [ArrayLib.allUnique]. We walk the list and
    require each element absent from the tail. Returns [true] iff all
    elements are pairwise distinct. *)
Fixpoint erc20s_unique (erc20s : list U256.t) : bool :=
  match erc20s with
  | nil => true
  | cons x rest =>
    if existsb (Z.eqb x) rest then false
    else erc20s_unique rest
  end.

(** ----- target-amt validation: every targetAmt within bounds.

    Mirrors production [require(MIN_TARGET_AMT <= targetAmts[i] <=
    MAX_TARGET_AMT, "invalid target amount")] (line 267). *)
Definition targetAmt_valid (a : U256.t) : bool :=
  (MIN_TARGET_AMT <=? a) && (a <=? MAX_TARGET_AMT).

Fixpoint all_targetAmts_valid (entries : list PrimeEntry.t) : bool :=
  match entries with
  | nil => true
  | cons e rest =>
    targetAmt_valid e.(PrimeEntry.targetAmt) && all_targetAmts_valid rest
  end.

(** ----- setPrimeBasket.

    Models the body of production [_setPrimeBasket] (line 229+) after
    governance gating and after the reweightable / target-constancy
    check. We accept a list of [PrimeEntry.t] (erc20, targetAmt,
    targetName) tuples. The [targetName] is precomputed by the caller
    (in production it is read from [assetRegistry.toColl(erc20).
    targetName()]); the simulation takes it as input rather than
    indirecting through a registry, consistent with the asset-registry
    boundary documented above.

    Validation:
      - len(entries) > 0 and len(entries) <= MAX_BASKET_LENGTH.
      - all targetAmts within [MIN_TARGET_AMT, MAX_TARGET_AMT].
      - erc20 list contains no duplicates.

    Effect on the storage:
      - [primeBasket] := entries.
      - [nonce] := nonce + 1.
      - [disabled], [basket], [backupConfigs] left intact (production
        [_setPrimeBasket] only mutates [config]; the live [basket] and
        [disabled] are only changed by [_switchBasket]).

    Returns [None] on validation failure. *)
Definition setPrimeBasket
    (s : Storage.t) (entries : list PrimeEntry.t) : option Storage.t :=
  let len := Z.of_nat (List.length entries) in
  if (len =? 0) || (len >? MAX_BASKET_LENGTH) then None
  else if negb (all_targetAmts_valid entries) then None
  else if negb (erc20s_unique (List.map PrimeEntry.erc20 entries)) then None
  else
    Some {|
      Storage.basket        := s.(Storage.basket);
      Storage.primeBasket   := entries;
      Storage.backupConfigs := s.(Storage.backupConfigs);
      Storage.nonce         := s.(Storage.nonce) + 1;
      Storage.disabled      := s.(Storage.disabled);
    |}.

(** ----- AssetStatus lookup.

    Walks a [list AssetStatus.t] for the entry matching a given erc20.
    Returns [false] (DISABLED-equivalent) if absent — production
    [BasketLibP1.goodCollateral] catches the registry miss and returns
    [false] (line 307). *)
Fixpoint lookup_status (e : U256.t) (statuses : list AssetStatus.t) : bool :=
  match statuses with
  | nil => false
  | cons hd rest =>
    if hd.(AssetStatus.erc20) =? e then hd.(AssetStatus.is_good)
    else lookup_status e rest
  end.

(** ----- refreshBasket helpers.

    [select_backups statuses backups max] walks [backups] in order and
    keeps up to [max] entries that are good (per [statuses]). Returns
    the surviving sublist. Mirrors [BasketLibP1.nextBasket] inner loop
    "j < backup.erc20s.length && size < backup.max" (line 252). *)
Fixpoint select_backups
    (statuses : list AssetStatus.t) (backups : list U256.t) (remaining : nat)
    : list U256.t :=
  match remaining, backups with
  | O, _ => nil
  | _, nil => nil
  | S k, cons e rest =>
    if lookup_status e statuses then
      cons e (select_backups statuses rest k)
    else
      select_backups statuses rest (S k)
  end.

(** [find_backup_config name configs] returns the [BackupEntry.t] for
    [name], or [None] if absent. *)
Fixpoint find_backup_config
    (name : U256.t) (configs : list BackupEntry.t) : option BackupEntry.t :=
  match configs with
  | nil => None
  | cons hd rest =>
    if hd.(BackupEntry.targetName) =? name then Some hd
    else find_backup_config name rest
  end.

(** [unsound_weight name primes statuses] sums the targetAmts of every
    prime entry that targets [name] and whose erc20 is DISABLED in
    [statuses]. This is production [unsoundPrimeWt(tgt)] (BasketLib
    comment line 133). *)
Fixpoint unsound_weight
    (name : U256.t) (primes : list PrimeEntry.t) (statuses : list AssetStatus.t)
    : U256.t :=
  match primes with
  | nil => 0
  | cons e rest =>
    let tail_sum := unsound_weight name rest statuses in
    if (e.(PrimeEntry.targetName) =? name) &&
       negb (lookup_status e.(PrimeEntry.erc20) statuses) then
      e.(PrimeEntry.targetAmt) + tail_sum
    else tail_sum
  end.

(** Build the post-refresh [basket] entry list for the good prime
    collateral. Each surviving prime entry contributes
    [BasketEntry.asset = erc20] and [BasketEntry.refAmt = targetAmt]
    (i.e. we model the "refAmt = targetAmt" calibration where
    targetPerRef = FIX_ONE — the same calibration used by the quote
    layer). Disabled prime entries are dropped. *)
Fixpoint good_prime_entries
    (primes : list PrimeEntry.t) (statuses : list AssetStatus.t)
    : list BasketEntry.t :=
  match primes with
  | nil => nil
  | cons e rest =>
    if lookup_status e.(PrimeEntry.erc20) statuses then
      cons {| BasketEntry.asset := e.(PrimeEntry.erc20);
              BasketEntry.refAmt := e.(PrimeEntry.targetAmt) |}
           (good_prime_entries rest statuses)
    else good_prime_entries rest statuses
  end.

(** [unique_target_names primes] returns the de-duplicated list of
    target names appearing in [primes], preserving first-occurrence
    order. Mirrors production [_targetNames] (BasketHandler.sol#L63)
    populated at line 181 of BasketHandler.sol. *)
Fixpoint unique_target_names_aux
    (primes : list PrimeEntry.t) (acc : list U256.t) : list U256.t :=
  match primes with
  | nil => List.rev acc
  | cons e rest =>
    if existsb (Z.eqb e.(PrimeEntry.targetName)) acc then
      unique_target_names_aux rest acc
    else
      unique_target_names_aux rest (e.(PrimeEntry.targetName) :: acc)
  end.

Definition unique_target_names (primes : list PrimeEntry.t) : list U256.t :=
  unique_target_names_aux primes nil.

(** Per-target processing: for [name], compute the weight that needs
    backup coverage (= [unsound_weight name primes statuses]) and
    distribute it evenly across the surviving backups (production line
    265-268: [unsoundPrimeWt / (targetPerRef * size)]; we set
    targetPerRef = FIX_ONE and divide by [size] alone).

    Returns:
      - [Some new_entries] if the unsound weight is 0 (no backup needed,
        no entries added) or if the unsound weight is positive AND at
        least one backup is available.
      - [None] if the unsound weight is positive and no backup is
        available — in production, this triggers
        [_switchBasket] to leave [disabled = true]. *)
Definition build_backups_for_target
    (name : U256.t) (primes : list PrimeEntry.t)
    (statuses : list AssetStatus.t)
    (configs : list BackupEntry.t)
    : option (list BasketEntry.t) :=
  let need := unsound_weight name primes statuses in
  if need =? 0 then Some nil   (* nothing to backup *)
  else
    match find_backup_config name configs with
    | None => None              (* no backup config registered *)
    | Some bc =>
      let avail := select_backups statuses
                     bc.(BackupEntry.erc20s) (Z.to_nat bc.(BackupEntry.max)) in
      let size := Z.of_nat (List.length avail) in
      if size =? 0 then None    (* unsound weight but no backup available *)
      else
        let per_backup := need / size in
        Some (List.map
                (fun e =>
                   {| BasketEntry.asset := e;
                      BasketEntry.refAmt := per_backup |})
                avail)
    end.

(** Aggregate over all target names. Returns [Some entries] if every
    target's backup leg succeeded; [None] (with the accumulated
    successes discarded) if any target failed.

    The inner accumulator threads [option (list BasketEntry.t)] forward;
    a single [None] in the chain short-circuits. *)
Fixpoint build_all_backups
    (names : list U256.t) (primes : list PrimeEntry.t)
    (statuses : list AssetStatus.t)
    (configs : list BackupEntry.t)
    : option (list BasketEntry.t) :=
  match names with
  | nil => Some nil
  | cons n rest =>
    match build_backups_for_target n primes statuses configs with
    | None => None
    | Some this_target =>
      match build_all_backups rest primes statuses configs with
      | None => None
      | Some others => Some (this_target ++ others)
      end
    end
  end.

(** [refreshBasket s statuses] is a TOTAL function over [Storage.t] —
    no [option] return, mirroring production where [_switchBasket]
    always succeeds in writing *some* state, with [disabled] flipped to
    [true] iff the next-basket selection failed. *)
Definition refreshBasket
    (s : Storage.t) (statuses : list AssetStatus.t) : Storage.t :=
  let primes := s.(Storage.primeBasket) in
  let names  := unique_target_names primes in
  let goods  := good_prime_entries primes statuses in
  match build_all_backups names primes statuses s.(Storage.backupConfigs) with
  | None =>
    (* Failure: keep the basket as-is, set disabled = true. Mirrors
       _switchBasket lines 660-684 where disabled := true is the entry
       point and only flipped back if nextBasket succeeded. *)
    {|
      Storage.basket        := s.(Storage.basket);
      Storage.primeBasket   := primes;
      Storage.backupConfigs := s.(Storage.backupConfigs);
      Storage.nonce         := s.(Storage.nonce);
      Storage.disabled      := true;
    |}
  | Some backups =>
    let new_basket := goods ++ backups in
    if Z.of_nat (List.length new_basket) =? 0 then
      (* Empty basket — unreachable when the prime config is non-empty
         and at least one prime is good or one backup leg fired. We
         still defensively flip disabled to mirror production:
         "newBasket.erc20s.length != 0" gate at line 282. *)
      {|
        Storage.basket        := s.(Storage.basket);
        Storage.primeBasket   := primes;
        Storage.backupConfigs := s.(Storage.backupConfigs);
        Storage.nonce         := s.(Storage.nonce);
        Storage.disabled      := true;
      |}
    else
      {|
        Storage.basket        := new_basket;
        Storage.primeBasket   := primes;
        Storage.backupConfigs := s.(Storage.backupConfigs);
        Storage.nonce         := s.(Storage.nonce) + 1;
        Storage.disabled      := false;
      |}
  end.

(** =================================================================
    Validity predicate.
    =================================================================
*)

Module Valid.
  (** Storage validity:
      - prime basket has size in [0, MAX_BASKET_LENGTH] (allow size 0
        only at init);
      - all prime targetAmts in [MIN_TARGET_AMT, MAX_TARGET_AMT];
      - prime erc20s pairwise distinct;
      - nonce within uint256 range;
      - every refAmt in the live basket is non-negative.

      The live-basket refAmt non-negativity is a structural invariant
      that the quote layer requires. It is preserved by both
      [setPrimeBasket] (which doesn't touch [basket]) and
      [refreshBasket] (which constructs [basket] from non-negative
      targetAmts and non-negative quotients).

      We do not constrain the live [basket] field with prime-style
      tight bounds because [refreshBasket] computes per-backup weights
      as [unsound_weight / size] which can fall below MIN_TARGET_AMT
      for large [size] — this is faithful to production behaviour. *)
  Record t (s : Storage.t) : Prop := {
    prime_size_bound :
      Z.of_nat (List.length s.(Storage.primeBasket)) <= MAX_BASKET_LENGTH;
    prime_targetAmts_valid :
      all_targetAmts_valid s.(Storage.primeBasket) = true;
    prime_unique :
      erc20s_unique
        (List.map PrimeEntry.erc20 s.(Storage.primeBasket)) = true;
    nonce_u256 :
      0 <= s.(Storage.nonce) <= UINT256_MAX;
    basket_refAmts_nonneg :
      List.Forall (fun e => 0 <= e.(BasketEntry.refAmt)) s.(Storage.basket);
  }.
End Valid.

End BasketHandler.
