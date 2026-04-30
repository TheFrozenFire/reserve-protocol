(** GnosisTrade uint256 upper-bound derivation.

    Mirrors [proofs/IssuancePremium_uint256_bounds.v]: GnosisTrade's
    [simulations/GnosisTrade.v] is purely functional (no storage record),
    so the natural "uint256 bounds" claim is on the *output* of the pure
    [worstCasePrice] and [settlement_floor] kernels.

    Production has uint256 ceilings on every storage word and arithmetic
    by EVM semantics; furthermore, on-chain [worstCasePrice] is stored
    in a [uint192] slot via [_safeWrap], which reverts whenever the
    next-state value would overflow [FIX_MAX]. We model that here as
    explicit call-boundary hypotheses on the post-division outputs,
    matching the on-chain revert behaviour: a successful return path is
    exactly the path on which the next-state bound holds.

    Three lemmas:
      - [worstCasePrice_le_UINT256_MAX]: under input envelope on the
        numerator [mba * 10^27 / max(sa,1)], the FLOOR-divided output
        fits in uint256.
      - [settlement_floor_le_UINT256_MAX]: under input envelope on
        [wcp * max(soldAmt,1) / 10^27], the CEIL-divided-minus-1 output
        fits in uint256.
      - [gnosis_trade_outputs_jointly_bounded]: composes the two,
        yielding a [<= 2 * UINT256_MAX] envelope.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Fixed.
Require Import Reserve.proofs.Fixed.
Require Import Reserve.simulations.GnosisTrade.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Module GnosisTradeUint256Bounds.

Import FixLib.
Import FixLibProofs.
Import Reserve.simulations.GnosisTrade.GnosisTrade.

(** ---------- helper: D27_ONE positivity ---------- *)
Lemma D27_ONE_pos : 0 < D27_ONE.
Proof. unfold D27_ONE. vm_compute. reflexivity. Qed.

(** ---------- output bounds: worstCasePrice ----------

    [worstCasePrice mba sa] is [(mba * 10^27) / sa] (FLOOR) when [sa <> 0]
    and [0] otherwise. The natural "didn't revert" envelope is that the
    quotient stays under [UINT256_MAX]. We state this as a hypothesis on
    the [Z.max sa 1]-divided numerator so the [sa = 0] branch is also
    covered uniformly. *)
Lemma worstCasePrice_le_UINT256_MAX
    (mba sa : Z) :
  0 <= mba ->
  0 <= sa ->
  mba * D27_ONE / Z.max sa 1 <= UINT256_MAX ->
  worstCasePrice mba sa <= UINT256_MAX.
Proof.
  intros Hmba Hsa Henv.
  unfold worstCasePrice, shiftl_toFix_d27.
  destruct (sa =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst sa.
    assert (Hmax : Z.max 0 1 = 1) by (vm_compute; reflexivity).
    rewrite Hmax in Henv.
    assert (HU : 0 <= UINT256_MAX) by (unfold UINT256_MAX; vm_compute; discriminate).
    exact HU.
  - apply Z.eqb_neq in Hzero.
    assert (Hsapos : 0 < sa) by lia.
    assert (Hmax : Z.max sa 1 = sa) by (apply Z.max_l; lia).
    rewrite Hmax in Henv.
    rewrite divrnd_floor_eq.
    exact Henv.
Qed.

(** ---------- worstCasePrice non-negativity (re-export-style helper) ---------- *)
Lemma worstCasePrice_nonneg_local
    (mba sa : Z) :
  0 <= mba ->
  0 <= sa ->
  0 <= worstCasePrice mba sa.
Proof.
  intros Hmba Hsa. unfold worstCasePrice.
  destruct (sa =? 0) eqn:Hzero; [lia|].
  apply Z.eqb_neq in Hzero.
  rewrite divrnd_floor_eq.
  apply Z.div_pos.
  - unfold shiftl_toFix_d27. apply Z.mul_nonneg_nonneg; [exact Hmba|]. lia.
  - lia.
Qed.

(** ---------- output bounds: settlement_floor ----------

    [settlement_floor wcp soldAmt] is
      [Z.max (ceil(wcp * max(soldAmt,1) / 10^27) - 1) 0].
    The hypothesis [Henv] captures the EVM revert envelope on the CEIL
    expression itself; the subsequent [-1] and [Z.max _ 0] only
    strengthen the bound. *)
Lemma settlement_floor_le_UINT256_MAX
    (wcp soldAmt : Z) :
  0 <= wcp ->
  divrnd (wcp * Z.max soldAmt 1) D27_ONE RoundingMode.CEIL <= UINT256_MAX ->
  settlement_floor wcp soldAmt <= UINT256_MAX.
Proof.
  intros Hwcp Henv.
  unfold settlement_floor.
  set (adj := Z.max soldAmt 1).
  set (ceilv := divrnd (wcp * adj) D27_ONE RoundingMode.CEIL).
  fold adj in Henv. fold ceilv in Henv.
  assert (HU : 0 <= UINT256_MAX) by (unfold UINT256_MAX; vm_compute; discriminate).
  apply Z.max_lub; lia.
Qed.

(** ---------- settlement_floor non-negativity (re-export-style helper) ---------- *)
Lemma settlement_floor_nonneg_local
    (wcp soldAmt : Z) :
  0 <= settlement_floor wcp soldAmt.
Proof.
  unfold settlement_floor. lia.
Qed.

(** ---------- joint bound ----------

    Sums the two output channels under their respective envelopes. Each
    is bounded by [UINT256_MAX], so the sum is at most [2 * UINT256_MAX]. *)
Lemma gnosis_trade_outputs_jointly_bounded
    (mba sa wcp soldAmt : Z) :
  0 <= mba ->
  0 <= sa ->
  0 <= wcp ->
  mba * D27_ONE / Z.max sa 1 <= UINT256_MAX ->
  divrnd (wcp * Z.max soldAmt 1) D27_ONE RoundingMode.CEIL <= UINT256_MAX ->
  worstCasePrice mba sa + settlement_floor wcp soldAmt <= 2 * UINT256_MAX.
Proof.
  intros Hmba Hsa Hwcp Hwcp_env Hsf_env.
  pose proof (worstCasePrice_le_UINT256_MAX mba sa Hmba Hsa Hwcp_env) as Hwcp_hi.
  pose proof (settlement_floor_le_UINT256_MAX wcp soldAmt Hwcp Hsf_env) as Hsf_hi.
  lia.
Qed.

End GnosisTradeUint256Bounds.
