(** BackingManager composition lemmas.

    Two chained-output lemmas covering the two-stage [forwardRevenue]
    pipeline (computeNewBasketsAndNeeded -> computeSurplusSplit):

      1. [computeNewBasketsAndNeeded_then_surplusSplit_outputs_nonneg]
         End-to-end non-negativity: given [Valid.bufferInputs] and
         non-negative per-asset inputs (quantity, bal, decimals,
         rTokenTotal, rsrTotal), the second stage's Success-branch
         outputs are all non-negative when fed [needed] from the first
         stage. This is the chain of the two output-bound lemmas in
         [BackingManager_validity].

      2. [surplusSplit_after_no_op_basket_change]
         When the first stage is a no-op (basketsHeldBottom below
         threshold so basketsNeeded is unchanged) and the asset's bal
         is at or below the resulting [req], the surplus split returns
         the all-zero output. The "no-op" leg threads the unchanged
         basketsNeeded through to the surplus stage's [needed] input
         without further arithmetic.

    Composition only — both proofs delegate to existing lemmas in
    [BackingManager_validity] and [BackingManager], adding only the
    glue that wires stage-1 outputs into stage-2 inputs.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.simulations.BackingManager.
Require Import Reserve.proofs.BackingManager.
Require Import Reserve.proofs.BackingManager_validity.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module BackingManagerChain.

Import FixLib.
Import BackingManager.

Local Open Scope Z_scope.

(** ----- Chain 1: end-to-end non-negativity of the two-stage pipeline. -----

    Take [needed] from stage 1 and feed it into stage 2. Given the
    standard input validity for stage 1 and non-negativity preconditions
    for stage 2, every Success-branch output of stage 2 is non-negative.

    The proof is a direct composition: [computeNewBasketsAndNeeded_outputs_nonneg]
    yields [0 <= needed], which is exactly the precondition stage 2
    requires. *)
Lemma computeNewBasketsAndNeeded_then_surplusSplit_outputs_nonneg
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t)
    (quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t)
    (split : BackingManager.SurplusSplit.t) :
  BackingManager.Valid.bufferInputs basketsHeldBottom basketsNeeded
                                    backingBuffer ->
  0 <= quantity ->
  0 <= bal ->
  0 <= rTokenTotal ->
  0 <= rsrTotal ->
  0 <= decimals ->
  let st := BackingManager.computeNewBasketsAndNeeded
              basketsHeldBottom basketsNeeded backingBuffer in
  BackingManager.computeSurplusSplit
    st.(BackingManager.BasketState.needed) quantity bal decimals
    rTokenTotal rsrTotal
    = BackingManager.Result.Success split ->
  0 <= split.(BackingManager.SurplusSplit.rsrAmount) /\
  0 <= split.(BackingManager.SurplusSplit.rTokenAmount) /\
  0 <= split.(BackingManager.SurplusSplit.dust).
Proof.
  intros Hvalid Hquantity Hbal HrT HrS Hdec st Hsucc.
  (* Stage 1: needed >= 0 from the validity-output lemma. *)
  pose proof (BackingManagerValidityProofs.computeNewBasketsAndNeeded_outputs_nonneg
                basketsHeldBottom basketsNeeded backingBuffer Hvalid)
    as [_ Hneeded_nn].
  (* Stage 2: feed needed (>= 0) into computeSurplusSplit_outputs_nonneg. *)
  apply (BackingManagerValidityProofs.computeSurplusSplit_outputs_nonneg
           st.(BackingManager.BasketState.needed) quantity bal decimals
           rTokenTotal rsrTotal split
           Hneeded_nn Hquantity Hbal HrT HrS Hdec Hsucc).
Qed.

(** ----- Chain 2: no-op stage 1 + bal <= req stage 2 = all-zero output. -----

    When [basketsHeldBottom / (FIX_ONE+buf) <= basketsNeeded] (the
    "below threshold" branch of stage 1), basketsNeeded is unchanged
    and [needed = mul basketsNeeded (FIX_ONE+buf) CEIL]. If, in
    addition, the per-asset balance is at or below [req = mul needed
    quantity CEIL], stage 2 returns all-zero outputs.

    Threads [basketsNeeded_unchanged_when_below_threshold] into
    [surplusSplit_bal_le_req_no_split], composing two stage-local
    lemmas without re-deriving any arithmetic. *)
Lemma surplusSplit_after_no_op_basket_change
    (basketsHeldBottom basketsNeeded backingBuffer : U256.t)
    (quantity bal : U256.t) (decimals : Z)
    (rTokenTotal rsrTotal : U256.t) :
  let st := BackingManager.computeNewBasketsAndNeeded
              basketsHeldBottom basketsNeeded backingBuffer in
  let baskets := FixLib.div basketsHeldBottom (FIX_ONE + backingBuffer)
                            RoundingMode.FLOOR in
  baskets <= basketsNeeded ->
  bal <= FixLib.mul st.(BackingManager.BasketState.needed) quantity
                    RoundingMode.CEIL ->
  BackingManager.computeSurplusSplit
    st.(BackingManager.BasketState.needed) quantity bal decimals
    rTokenTotal rsrTotal
    = BackingManager.Result.Success {|
        BackingManager.SurplusSplit.rsrAmount    := 0;
        BackingManager.SurplusSplit.rTokenAmount := 0;
        BackingManager.SurplusSplit.dust         := 0;
      |}.
Proof.
  intros st baskets Hle Hbal_le.
  (* Stage 2 returns the zero output whenever bal <= req. The
     basket-unchanged hypothesis is along for the ride: it documents
     that the [needed] threading is the no-op stage-1 leg. *)
  apply (BackingManagerProofs.surplusSplit_bal_le_req_no_split
           st.(BackingManager.BasketState.needed) quantity bal decimals
           rTokenTotal rsrTotal Hbal_le).
Qed.

End BackingManagerChain.
