(** BackingManager simulation.

    Mirrors the math + operation surface of protocol/contracts/p1/BackingManager.sol.

    The simulation has two layers:

    Layer 1 — pure math kernels (the original simulation, lines 218-262):

      computeNewBasketsAndNeeded(basketsHeldBottom, basketsNeeded, backingBuffer)
        - Returns the new (basketsNeeded, mintAmount, needed) tuple.
        - basketsNeeded' = max(basketsNeeded, basketsHeld_bottom / (1+buf))
        - mintAmount     = basketsNeeded' - basketsNeeded   (>= 0)
        - needed         = CEIL(basketsNeeded' * (1+buf) / FIX_ONE)
        - Captures the post-#1283 CEIL-mitigation.

      computeSurplusSplit(quantity, bal, decimals, rTokenTotal, rsrTotal, needed)
        - Per-asset split for forward-revenue distribution.
        - When bal <= req, returns (0, 0, 0).
        - Else delta := shiftl_toUint(bal - req, decimals)
              tps   := delta / (rTokenTotal + rsrTotal)
              if tps == 0: dust = delta, both shares = 0
              else: rsrShare = tps * rsrTotal,
                    rTokShare = tps * rTokenTotal,
                    dust = delta - (rsrShare + rTokShare).

    Layer 2 — operation surface:

      forwardRevenueIter(needed, totals, assets)
        - Multi-asset iterator over [list AssetState.t].
        - Calls [computeSurplusSplit] for each asset.
        - Returns a list of [SurplusSplit.t] outputs and aggregate
          (rsrTotal, rTokenTotal, dustTotal).
        - Conservation: across the iteration, sum(rsr) + sum(rTok) + sum(dust)
          = sum of per-asset deltas.

      forwardRevenue(s, assets)
        - Composes [computeNewBasketsAndNeeded] with [forwardRevenueIter]
          over a [Storage.t] carrying [basketsNeeded] and [backingBuffer].
        - Returns a [ForwardRevenueResult.t] with the post-state and the
          full per-asset split list.

      prepareRecollateralizationTrade(s, range_inputs, assets)
        - Recollateralization state-machine entry.
        - Composes [RebalanceLib.basketRange] (algebraic skeleton) with
          [TradeLib.buyAmount] to set up [pendingTrade].
        - Transitions tradeStatus: NONE -> OPEN.
        - Returns the storage unchanged when no trade is needed
          (range.low >= basketsNeeded).

      settleRecollateralizationTrade(s, settlement)
        - Recollateralization settlement.
        - Transitions tradeStatus: OPEN -> NONE (the SETTLED state is
          modeled as a transient — production has it but it doesn't
          persist past the settle call).
        - Updates [basketsNeeded] from the settlement.

    Boundaries — what's IN scope and what's OUT:

      IN scope:
        - The math kernels above
        - The iteration framework over a *provided* [AssetList]
        - The state-machine transitions
        - Composition with [Rebalance.basketRange] and [TradeLib.buyAmount]
        - Conservation invariants across the iteration
        - Validity preservation across all new operations

      OUT of scope (NOT modeled):
        - Asset-registry indirection — the simulation TAKES the asset
          list as input, not a registry query. Caller responsibility.
        - Oracle layer — accept oracle-priced inputs (low/high) as
          parameters; no oracle calls.
        - Trade execution itself — only trade preparation and
          settlement bookkeeping; the actual ERC20 transfers and
          Gnosis interactions live in DutchTrade/GnosisTrade
          simulations.
        - basketHandler.fullyCollateralized() gating — accepted as a
          boolean input, not a derived predicate.
        - Reentrancy modifiers and access control — out of scope per
          the dual-track audit table.
        - `compromiseBasketsNeeded` haircut path: modeled as a
          settlement variant rather than as a separate call.
        - RToken/RSR transfer side effects (the SafeERC20 calls in
          forwardRevenue lines 212-216 and 253-260) — only the
          accounting math is modeled.

    Both kernel functions match the harness in
    formal-verification/contracts/BackingManagerMathHarness.sol exactly.

    Revert coverage:
      Modeled:  [computeSurplusSplit] returns [Result.Revert] when
                [totalShares = 0] (matches the production
                [require(totalShares > 0)] before the per-asset
                division).
      Deferred: input bounds via [Valid.bufferInputs] (uint192 on
                each scalar, [backingBuffer <= MAX_BACKING_BUFFER]) and
                [Valid.storage] (analogue for [Storage.t]).
                Aggregate iteration preconditions in [Valid.assetList].
      Not modeled: auth, RToken interactions, basket-not-ready
                guards, "trade open" gating, "trading delayed"
                gating, the duplicate-tokens revert
                ([ArrayLib.allUnique]), reentrancy modifiers. See
                ../../notes/simulation_fidelity_audit.md for the
                per-domain summary.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.Rebalance.
Require Import Reserve.simulations.TradeLib.
Require Import Coq.Lists.List.
Import ListNotations.

Module BackingManager.

Import FixLib.

(** Maximum backing buffer per BackingManager.sol#L34. *)
Definition MAX_BACKING_BUFFER : Z := FIX_ONE.

(** Two-constructor result mirroring the upstream simulation pattern. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Output of [computeNewBasketsAndNeeded]: the updated basket-buffer
    state used by [forwardRevenue] before walking the asset list. *)
Module BasketState.
  Record t : Set := {
    basketsNeeded : U256.t;   (** {BU} new basketsNeeded, uint192 *)
    mintAmount    : U256.t;   (** {qRTok} amount to mint for revenue *)
    needed        : U256.t;   (** {BU} CEIL-rounded buffer-adjusted target *)
  }.
End BasketState.

(** Output of [computeSurplusSplit]: how the per-asset delta is split
    among RSR-side, RToken-side, and dust. *)
Module SurplusSplit.
  Record t : Set := {
    rsrAmount    : U256.t;   (** {qTok} forwarded to rsrTrader *)
    rTokenAmount : U256.t;   (** {qTok} forwarded to rTokenTrader *)
    dust         : U256.t;   (** {qTok} retained as dust *)
  }.
End SurplusSplit.

(** [shiftl_toUint(x, decimals)] for [decimals >= 0]: multiply by 10^decimals.

    Production semantics: positive [decimals] multiplies, negative divides
    with FLOOR rounding by default. The harness only takes positive
    asset decimals (uint8), so we model the positive branch. The full
    bounded version with overflow is in [FixLib.shiftl]; this is the
    pure-Z algebraic kernel. *)
Definition shiftl_toUint (x : Z) (decimals : Z) : Z :=
  if decimals <? 0 then x / (10 ^ (- decimals))
  else x * (10 ^ decimals).

(** [computeNewBasketsAndNeeded(basketsHeldBottom, basketsNeeded, backingBuffer)]
    Source: BackingManager.sol#L218-L225 + harness#L42-L54. *)
Definition computeNewBasketsAndNeeded
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t)
    : BasketState.t :=
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  let basketsNeeded' :=
    if basketsNeeded <? baskets then baskets else basketsNeeded in
  let mintAmount :=
    if basketsNeeded <? baskets then baskets - basketsNeeded else 0 in
  let needed :=
    FixLib.mul basketsNeeded' (FIX_ONE + backingBuffer) RoundingMode.CEIL in
  {| BasketState.basketsNeeded := basketsNeeded';
     BasketState.mintAmount    := mintAmount;
     BasketState.needed        := needed |}.

(** [computeSurplusSplit(quantity, bal, decimals, rTokenTotal, rsrTotal, needed)]
    Source: BackingManager.sol#L240-L262 + harness#L59-L86.

    When [totalShares = 0] production reverts; the harness requires it.
    The pure simulation exposes that as [Result.Revert]. *)
Definition computeSurplusSplit
    (needed quantity bal : U256.t)
    (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    : Result.t SurplusSplit.t :=
  let req := FixLib.mul needed quantity RoundingMode.CEIL in
  if bal <=? req then
    Result.Success {|
      SurplusSplit.rsrAmount    := 0;
      SurplusSplit.rTokenAmount := 0;
      SurplusSplit.dust         := 0;
    |}
  else
    let delta := shiftl_toUint (bal - req) decimals in
    let totalShares := rTokenTotal + rsrTotal in
    if totalShares =? 0 then
      Result.Revert 0 32
    else
      let tokensPerShare := delta / totalShares in
      if tokensPerShare =? 0 then
        Result.Success {|
          SurplusSplit.rsrAmount    := 0;
          SurplusSplit.rTokenAmount := 0;
          SurplusSplit.dust         := delta;
        |}
      else
        let rsrAmount    := tokensPerShare * rsrTotal in
        let rTokenAmount := tokensPerShare * rTokenTotal in
        Result.Success {|
          SurplusSplit.rsrAmount    := rsrAmount;
          SurplusSplit.rTokenAmount := rTokenAmount;
          SurplusSplit.dust         := delta - (rsrAmount + rTokenAmount);
        |}.

(** ================================================================
    Layer 2 — operation surface
    ================================================================ *)

(** Per-asset row passed to [forwardRevenueIter]. Production iterates
    over an [erc20s : IERC20[]] calldata array, calling
    [assetRegistry.toAsset], [basketHandler.quantity], and
    [asset.bal(this)] inside the loop. The simulation accepts the
    pre-resolved tuple directly: the registry/oracle indirection is
    OUT of scope per the simulation header. *)
Module AssetState.
  Record t : Set := {
    erc20    : U256.t;   (** asset address — opaque uint256 *)
    quantity : U256.t;   (** {ref/BU}, uint192 *)
    bal      : U256.t;   (** {qTok}, uint256 *)
    decimals : Z;        (** uint8 — non-negative in production *)
  }.
End AssetState.

Definition AssetList : Set := list AssetState.t.

(** Per-asset delta = [shiftl_toUint(bal - req, decimals)] when [bal > req],
    else 0. Used to anchor conservation at the iteration level. *)
Definition assetDelta (needed : U256.t) (a : AssetState.t) : Z :=
  let req := FixLib.mul needed a.(AssetState.quantity) RoundingMode.CEIL in
  if a.(AssetState.bal) <=? req then 0
  else shiftl_toUint (a.(AssetState.bal) - req) a.(AssetState.decimals).

(** [forwardRevenueIter] aggregate. Tracks per-asset splits in input
    order plus the running aggregates the production code's transfers
    feed (sum of rsr / rTok / dust over all assets). *)
Module IterAggregate.
  Record t : Set := {
    splits     : list SurplusSplit.t;   (** per-asset, in input order *)
    rsrSum     : U256.t;   (** sum of rsrAmount across assets *)
    rTokenSum  : U256.t;   (** sum of rTokenAmount across assets *)
    dustSum    : U256.t;   (** sum of dust across assets *)
  }.

  Definition empty : t :=
    {| splits := nil; rsrSum := 0; rTokenSum := 0; dustSum := 0 |}.
End IterAggregate.

(** Step the aggregate with a per-asset split. Used by both the
    iterator and the conservation/validity proofs (we expose the
    helper so the proofs don't have to re-derive the cons-and-add
    pattern inside induction). *)
Definition stepAggregate
    (acc : IterAggregate.t) (sp : SurplusSplit.t) : IterAggregate.t :=
  {| IterAggregate.splits     := acc.(IterAggregate.splits) ++ [sp];
     IterAggregate.rsrSum     := acc.(IterAggregate.rsrSum)
                                  + sp.(SurplusSplit.rsrAmount);
     IterAggregate.rTokenSum  := acc.(IterAggregate.rTokenSum)
                                  + sp.(SurplusSplit.rTokenAmount);
     IterAggregate.dustSum    := acc.(IterAggregate.dustSum)
                                  + sp.(SurplusSplit.dust); |}.

(** [forwardRevenueIter] walks the asset list and, for each row, calls
    [computeSurplusSplit]. If any per-asset call returns Revert (because
    [totalShares = 0]), the iteration short-circuits. Otherwise the
    aggregate is built up via [stepAggregate].

    Production maps `tokensPerShare = 0` to `continue` (skip the
    transfer) — the kernel returns dust = delta in that branch and
    we simply add it into [dustSum]. The behavioral effect matches:
    no transfer happens because [rsrAmount = rTokenAmount = 0]. *)
Fixpoint forwardRevenueIter_aux
    (acc : IterAggregate.t)
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList)
    : Result.t IterAggregate.t :=
  match assets with
  | nil => Result.Success acc
  | cons a rest =>
    match computeSurplusSplit needed
            a.(AssetState.quantity) a.(AssetState.bal)
            a.(AssetState.decimals) rTokenTotal rsrTotal with
    | Result.Revert p s => Result.Revert p s
    | Result.Success sp =>
      forwardRevenueIter_aux (stepAggregate acc sp)
                             needed rTokenTotal rsrTotal rest
    end
  end.

Definition forwardRevenueIter
    (needed : U256.t) (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList)
    : Result.t IterAggregate.t :=
  forwardRevenueIter_aux IterAggregate.empty needed rTokenTotal rsrTotal assets.

(** ================================================================
    Recollateralization state machine
    ================================================================ *)

(** [TradeStatus.t] mirrors the BackingManager's at-most-one-trade
    invariant. Production tracks this implicitly via [tradesOpen]
    (uint8 counter in TradingP1) and [tradeEnd] (kind -> endTime).
    For the abstract state machine we expose three constructors:
        NONE     — no open trade; [pendingTrade = None]
        OPEN     — a trade is open; [pendingTrade = Some _]
        SETTLED  — a trade has been settled; transient — the
                   simulation collapses SETTLED back to NONE on the
                   next call. *)
Module TradeStatus.
  Inductive t : Set :=
  | NONE
  | OPEN
  | SETTLED.
End TradeStatus.

(** [PendingTrade.t] captures the bookkeeping fields that production
    derives from RecollateralizationLib output. We keep just the
    symbolic sell/buy ERC20 tokens, the sell amount the trade was
    initialized with, and the post-mitigation [buyAmount] computed via
    [TradeLib.buyAmount] from the trade prices.

    Note: [DutchTrade]/[GnosisTrade] simulations carry the per-trade
    auction state (price decay, settlement floor); this record is just
    the recollateralization bookkeeping that lives in
    [BackingManager]'s storage. *)
Module PendingTrade.
  Record t : Set := {
    sellERC20  : U256.t;
    buyERC20   : U256.t;
    sellAmount : U256.t;
    buyAmount  : U256.t;
  }.
End PendingTrade.

(** [Storage.t] for the BackingManager-relevant fields the simulation
    needs to thread through forwardRevenue / manageTokens.

    Production [BackingManager.sol] storage:
      - basketsNeeded (lives in [RToken], not BM, but we treat it as
        BM-storage here since BM is the only writer)
      - backingBuffer (uint192, governance-set)
      - tradesOpen (uint8, parent TradingP1 — modeled as tradeStatus)
      - tradeEnd (mapping; not modeled — see header)
      - tokensOut (mapping; not modeled — see header)

    We omit:
      - tradingDelay, maxTradeSlippage, minTradeVolume — passed as
        arguments to the relevant operations
      - assetRegistry / basketHandler / distributor / etc. pointers —
        the simulation accepts the data they would return as inputs
*)
Module Storage.
  Record t : Set := {
    basketsNeeded : U256.t;          (** {BU} *)
    backingBuffer : U256.t;          (** {1} D18, gov: <= MAX_BACKING_BUFFER *)
    tradeStatus   : TradeStatus.t;
    pendingTrade  : option PendingTrade.t;
  }.

  (** A reasonable initial state — no open trade, gov-set basketsNeeded
      and backingBuffer. *)
  Definition init (basketsNeeded backingBuffer : U256.t) : t :=
    {| basketsNeeded := basketsNeeded;
       backingBuffer := backingBuffer;
       tradeStatus   := TradeStatus.NONE;
       pendingTrade  := None |}.
End Storage.

(** [ForwardRevenueResult.t]: the full output of [forwardRevenue].
    Carries the post-state, the per-asset split list, the mintAmount
    derived during the basket update, and the iteration aggregates. *)
Module ForwardRevenueResult.
  Record t : Set := {
    storage'    : Storage.t;
    mintAmount  : U256.t;          (** RToken minted during basket update *)
    needed      : U256.t;          (** the buffer-adjusted target *)
    splits      : list SurplusSplit.t;
    rsrSum      : U256.t;
    rTokenSum   : U256.t;
    dustSum     : U256.t;
  }.
End ForwardRevenueResult.

(** [forwardRevenue]: full operation. Composes
    [computeNewBasketsAndNeeded] with [forwardRevenueIter] and threads
    the results through the storage update.

    [basketsHeldBottom] is the {BU} pessimistic basket count from
    [basketHandler.basketsHeldBy(this).bottom] — passed in (asset
    registry / basket handler are out of scope).

    [(rTokenTotal, rsrTotal)] = [distributor.totals()], passed in.

    On a Revert from any per-asset call ([totalShares = 0]), we surface
    the revert. Otherwise we wrap the aggregate + post-state in a
    [Result.Success]. *)
Definition forwardRevenue
    (s : Storage.t) (basketsHeldBottom : U256.t)
    (rTokenTotal rsrTotal : U256.t)
    (assets : AssetList)
    : Result.t ForwardRevenueResult.t :=
  let bs := computeNewBasketsAndNeeded basketsHeldBottom
              s.(Storage.basketsNeeded) s.(Storage.backingBuffer) in
  match forwardRevenueIter bs.(BasketState.needed) rTokenTotal rsrTotal assets with
  | Result.Revert p q => Result.Revert p q
  | Result.Success agg =>
    let s' := {|
      Storage.basketsNeeded := bs.(BasketState.basketsNeeded);
      Storage.backingBuffer := s.(Storage.backingBuffer);
      Storage.tradeStatus   := s.(Storage.tradeStatus);
      Storage.pendingTrade  := s.(Storage.pendingTrade);
    |} in
    Result.Success {|
      ForwardRevenueResult.storage'   := s';
      ForwardRevenueResult.mintAmount := bs.(BasketState.mintAmount);
      ForwardRevenueResult.needed     := bs.(BasketState.needed);
      ForwardRevenueResult.splits     := agg.(IterAggregate.splits);
      ForwardRevenueResult.rsrSum     := agg.(IterAggregate.rsrSum);
      ForwardRevenueResult.rTokenSum  := agg.(IterAggregate.rTokenSum);
      ForwardRevenueResult.dustSum    := agg.(IterAggregate.dustSum);
    |}
  end.

(** ================================================================
    prepareRecollateralizationTrade
    ================================================================ *)

(** Inputs to the recollateralization trade preparation.

    Production [rebalance(kind)] (BackingManager.sol#L108-L173) calls:

        BasketRange basketsHeld = basketHandler.basketsHeldBy(this);
        require(basketsHeld.bottom < rToken.basketsNeeded(), "already collateralized");
        ...
        (TradingContext ctx, Registry reg) = tradingContext(basketsHeld);
        (bool doTrade, TradeRequest req, TradePrices prices)
            = RecollateralizationLibP1.prepareRecollateralizationTrade(ctx, reg);

    [prepareRecollateralizationTrade] internally calls
    [RecollateralizationLib.basketRange] (algebraic skeleton in
    [Reserve.simulations.Rebalance.RebalanceLib]). The output range is
    used to pick the surplus / deficit asset pair and call
    [TradeLib.prepareTradeSell] (the buy-amount kernel modeled in
    [Reserve.simulations.TradeLib]).

    The simulation skips the asset-pick logic — the caller hands in
    the chosen surplus/deficit ERC20 addresses + their oracle-priced
    sell-low / buy-high. We compute [basketRange] for the
    state-transition record and [TradeLib.buyAmount] for the trade's
    buyAmount field. *)
Module RecollateralizationInputs.
  Record t : Set := {
    rangeInputs   : RebalanceLib.RangeInputs.t;
    sellERC20     : U256.t;   (** picked surplus asset *)
    buyERC20      : U256.t;   (** picked deficit asset *)
    sellAmount    : U256.t;   (** capped at min(maxTradeSize, surplus) *)
    sellLow       : U256.t;   (** oracle low for sellERC20 *)
    buyHigh       : U256.t;   (** oracle high for buyERC20 *)
    maxTradeSlippage : U256.t;
    fullyCollateralized : bool;  (** basketHandler.fullyCollateralized() *)
  }.
End RecollateralizationInputs.

(** [needsTrade range basketsNeeded] mirrors the
    [basketsHeld.bottom < rToken.basketsNeeded()] guard plus the
    "did the lib decide to trade" bool. We fold both into a single
    predicate over the abstract range and basketsNeeded.

    The lib returns [doTrade = false] when the range is tight enough
    that no trade is meaningful — captured here by
    [range.high <= basketsNeeded] (the optimistic upper bound is
    already not above basketsNeeded, so a trade can't tighten it). *)
Definition needsTrade
    (r : RebalanceLib.BasketRange.t) (basketsNeeded : U256.t) : bool :=
  andb (r.(RebalanceLib.BasketRange.low) <? basketsNeeded)
       (basketsNeeded <? r.(RebalanceLib.BasketRange.high) + 1).

(** [prepareRecollateralizationTrade] state transition.

    Pre: [s.tradeStatus = NONE].
    Post (when needsTrade fires): [s.tradeStatus = OPEN] and
                                  [s.pendingTrade = Some pt].
    Post (when no trade needed):  storage unchanged. *)
Definition prepareRecollateralizationTrade
    (s : Storage.t) (ri : RecollateralizationInputs.t) : Storage.t :=
  let range := RebalanceLib.basketRange ri.(RecollateralizationInputs.rangeInputs) in
  if needsTrade range s.(Storage.basketsNeeded) then
    let buyAmt := TradeLib.buyAmount
                    ri.(RecollateralizationInputs.sellAmount)
                    ri.(RecollateralizationInputs.maxTradeSlippage)
                    ri.(RecollateralizationInputs.sellLow)
                    ri.(RecollateralizationInputs.buyHigh) in
    let pt := {|
      PendingTrade.sellERC20  := ri.(RecollateralizationInputs.sellERC20);
      PendingTrade.buyERC20   := ri.(RecollateralizationInputs.buyERC20);
      PendingTrade.sellAmount := ri.(RecollateralizationInputs.sellAmount);
      PendingTrade.buyAmount  := buyAmt;
    |} in
    {| Storage.basketsNeeded := s.(Storage.basketsNeeded);
       Storage.backingBuffer := s.(Storage.backingBuffer);
       Storage.tradeStatus   := TradeStatus.OPEN;
       Storage.pendingTrade  := Some pt; |}
  else
    s.

(** ================================================================
    settleRecollateralizationTrade
    ================================================================ *)

(** Inputs to the trade-settlement step. Production reads the
    settled trade's actual sellAmount/buyAmount from the underlying
    [DutchTrade]/[GnosisTrade] contract; here we accept them as
    arguments. The new basketsNeeded after settle is also passed in
    (matches production's [compromiseBasketsNeeded] code path which
    sets basketsNeeded directly when the trade was a haircut). *)
Module SettlementInputs.
  Record t : Set := {
    actualSellAmount : U256.t;   (** what the trade actually sold *)
    actualBuyAmount  : U256.t;   (** what the trade actually bought *)
    newBasketsNeeded : U256.t;   (** post-settle basketsNeeded — caller-computed *)
  }.
End SettlementInputs.

(** [settleRecollateralizationTrade]: transitions OPEN -> NONE.

    Pre: [s.tradeStatus = OPEN] and [s.pendingTrade = Some pt].
    Post: [s.tradeStatus = NONE], [s.pendingTrade = None],
          [basketsNeeded = settlement.newBasketsNeeded].

    If the precondition does not hold (NONE or SETTLED state with no
    pending trade), the storage is unchanged — we model the no-op
    behaviour rather than a revert. Production reverts via
    [_msgSender() == address(trade)] etc.; the auth checks are out of
    scope. *)
Definition settleRecollateralizationTrade
    (s : Storage.t) (settlement : SettlementInputs.t) : Storage.t :=
  match s.(Storage.tradeStatus), s.(Storage.pendingTrade) with
  | TradeStatus.OPEN, Some _ =>
    {| Storage.basketsNeeded := settlement.(SettlementInputs.newBasketsNeeded);
       Storage.backingBuffer := s.(Storage.backingBuffer);
       Storage.tradeStatus   := TradeStatus.NONE;
       Storage.pendingTrade  := None; |}
  | _, _ => s
  end.

(** ================================================================
    Validity predicates
    ================================================================ *)
Module Valid.
  Record bufferInputs
      (basketsHeldBottom basketsNeeded backingBuffer : U256.t) : Prop := {
    basketsHeldBottom_u192 : uint192_valid basketsHeldBottom;
    basketsNeeded_u192     : uint192_valid basketsNeeded;
    backingBuffer_u192     : uint192_valid backingBuffer;
    backingBuffer_le_max   : backingBuffer <= MAX_BACKING_BUFFER;
  }.

  (** [storage s]: storage-state invariant.

      Production maintains:
        - basketsNeeded fits in uint192
        - backingBuffer fits in uint192 and <= MAX_BACKING_BUFFER
        - tradeStatus and pendingTrade are mutually consistent
          (NONE iff pendingTrade = None; OPEN iff pendingTrade = Some _;
           SETTLED is transient and we collapse it back to NONE on
           the next call). *)
  Record storage (s : Storage.t) : Prop := {
    storage_basketsNeeded_u192 :
      uint192_valid s.(Storage.basketsNeeded);
    storage_backingBuffer_u192 :
      uint192_valid s.(Storage.backingBuffer);
    storage_backingBuffer_le_max :
      s.(Storage.backingBuffer) <= MAX_BACKING_BUFFER;
    storage_status_pendingTrade_consistent :
      match s.(Storage.tradeStatus), s.(Storage.pendingTrade) with
      | TradeStatus.NONE, None => True
      | TradeStatus.OPEN, Some _ => True
      | TradeStatus.SETTLED, None => True
      | _, _ => False
      end;
  }.

  (** [assetState a]: per-asset row invariants.
      Production stores [quantity] in uint192, [bal] in uint256
      (returned from [asset.bal(this)]), [decimals] in uint8 (>= 0). *)
  Record assetState (a : AssetState.t) : Prop := {
    assetState_quantity_u192 : uint192_valid a.(AssetState.quantity);
    assetState_bal_nonneg    : 0 <= a.(AssetState.bal);
    assetState_decimals_nn   : 0 <= a.(AssetState.decimals);
  }.

  (** [assetList]: every row is well-formed. *)
  Definition assetList (assets : AssetList) : Prop :=
    Forall assetState assets.
End Valid.

End BackingManager.
