(** FixLib simulation.

    Mirrors protocol/contracts/libraries/Fixed.sol — Reserve's fixed-point
    arithmetic library on uint192 with a 1e18 scale. Production functions
    revert on uint192 overflow via [_safeWrap]; the simulation models the
    arithmetic in [Z] and exposes a [uint192_valid] predicate for the
    boundedness reasoning. Safety lemmas (in proofs/Fixed.v) state when
    inputs preserve the predicate.

    This matches the CAS-side approach in cas/fixlib/, which computes the
    same arithmetic in PARI/GP's exact rationals and reasons about
    overflow as a separate concern.

    Coverage at this stage:
      - RoundingMode (FLOOR / ROUND / CEIL)
      - _divrnd : the rounding-mode-aware integer division kernel
      - mul / div with rounding modes
      - mulu, plus, minus, comparisons
      - powu : fixed-point exponentiation by squaring (matches Throttle.sol's
              [(1 - ratio)^numPeriods] in Furnace, etc.)
      - shiftl with rounding

    Out of scope here (defer until they're needed downstream):
      - sqrt, divFix, divuu (Reserve uses these less frequently)
      - the full chained-operation surface (mulu_toUint, etc.)

    Revert coverage:
      Modeled:  [_safeWrap] returns [None] on uint192 overflow,
                surfaced via [_opt]-suffixed variants ([mul_opt],
                [div_opt], etc.). This matches production's [_safeWrap]
                revert in [FixLib].
      Deferred: input boundedness via [uint192_valid] (carried as
                hypothesis in proofs/Fixed_safety.v).
      Not modeled: uint256 overflow on the unchecked variants — sim
                works in [Z]. Production reverts via Solidity 0.8's
                checked arithmetic; the [_opt] wrappers cover the
                uint192 boundary, but the inner uint256 multiplication
                (e.g. inside [mulDiv256]) is not separately bounded.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module FixLib.

Definition FIX_SCALE     : Z := 10 ^ 18.
Definition FIX_SCALE_SQ  : Z := 10 ^ 36.
Definition FIX_ONE       : Z := FIX_SCALE.
Definition FIX_MAX       : Z := 2 ^ 192 - 1.
Definition FIX_MAX_INT   : Z := FIX_MAX / FIX_SCALE.
Definition UINT256_MAX   : Z := 2 ^ 256 - 1.
Definition FIX_HALF      : Z := FIX_SCALE / 2.

(** uint192 boundedness — the invariant [_safeWrap] enforces. *)
Definition uint192_valid (x : Z) : Prop :=
  0 <= x <= FIX_MAX.

Module RoundingMode.
  Inductive t : Set :=
  | FLOOR
  | ROUND
  | CEIL.
End RoundingMode.

Definition FLOOR := RoundingMode.FLOOR.
Definition ROUND := RoundingMode.ROUND.
Definition CEIL  := RoundingMode.CEIL.

(** [_divrnd(numerator, divisor, rounding)] — production source lines 155-175.
      FLOOR: n / d
      ROUND: n / d + (1 if n%d > (d-1)/2 else 0)
      CEIL:  n / d + (1 if n%d != 0 else 0) *)
Definition divrnd (n d : Z) (mode : RoundingMode.t) : Z :=
  let q := n / d in
  let r := n mod d in
  match mode with
  | RoundingMode.FLOOR => q
  | RoundingMode.ROUND => if r >? (d - 1) / 2 then q + 1 else q
  | RoundingMode.CEIL  => if r =? 0 then q else q + 1
  end.

(** [_safeWrap] returns [Some] if x fits in uint192, else [None] (revert).
    Plain option is enough — there is no extra information at the boundary. *)
Definition safeWrap (x : Z) : option Z :=
  if x <=? FIX_MAX then Some x else None.

(** mul(x, y, mode) — FixLib.sol#L259-L265 *)
Definition mul_opt (x y : Z) (mode : RoundingMode.t) : option Z :=
  safeWrap (divrnd (x * y) FIX_SCALE mode).

(** Pure-Z variant of mul, ignoring overflow. Useful for stating algebraic
    identities; pair with [mul_safe] from proofs/Fixed.v for boundedness. *)
Definition mul (x y : Z) (mode : RoundingMode.t) : Z :=
  divrnd (x * y) FIX_SCALE mode.

(** div(x, y, mode) — FixLib.sol#L284-L291. Pre-multiplies by FIX_SCALE
    before dividing to preserve precision. *)
Definition div_opt (x y : Z) (mode : RoundingMode.t) : option Z :=
  safeWrap (divrnd (x * FIX_SCALE) y mode).

Definition div (x y : Z) (mode : RoundingMode.t) : Z :=
  divrnd (x * FIX_SCALE) y mode.

(** mulu(x, y) — FixLib.sol#L270-L272. Multiply uint192 by uint256, returning uint192. *)
Definition mulu_opt (x y : Z) : option Z :=
  safeWrap (x * y).

Definition mulu (x y : Z) : Z := x * y.

(** mulu_toUint(x, y, mode) = divrnd(x*y, FIX_SCALE, mode).
    Multiply a fixed-point [x] by a uint [y], returning a plain uint
    (so the FIX_SCALE cancels out). FLOOR by default. *)
Definition mulu_toUint (x y : Z) (mode : RoundingMode.t) : Z :=
  divrnd (x * y) FIX_SCALE mode.

(** plus / minus on uint192. Solidity 0.8 reverts on overflow / underflow. *)
Definition plus_opt (x y : Z) : option Z := safeWrap (x + y).
Definition plus (x y : Z) : Z := x + y.

Definition minus_opt (x y : Z) : option Z :=
  if y <=? x then Some (x - y) else None.
Definition minus (x y : Z) : Z := x - y.

(** Comparisons. *)
Definition lt  (x y : Z) : bool := x <? y.
Definition lte (x y : Z) : bool := x <=? y.
Definition gt  (x y : Z) : bool := y <? x.
Definition gte (x y : Z) : bool := y <=? x.
Definition eq  (x y : Z) : bool := x =? y.
Definition neq (x y : Z) : bool := negb (x =? y).

(** [powu(x, y)] — FixLib.sol#L317-L330. Exponentiation by squaring on
    fixed-point with mid-divisor rounding at the half-step. We use a nat-fueled
    fixpoint since [y : uint48] is bounded; in production [y] enters as a
    uint48, so [Z.to_nat (Z.log2 y) + 1] iterations suffice. *)
Definition halfDiv (n d : Z) : Z := (n + d / 2) / d.

Fixpoint powu_aux (fuel : nat) (x result y : Z) : Z :=
  match fuel with
  | O => result
  | S fuel' =>
    let result' :=
      if Z.odd y then halfDiv (result * x) FIX_SCALE_SQ else result in
    if y <=? 1 then result'
    else powu_aux fuel' (halfDiv (x * x) FIX_SCALE_SQ) result' (y / 2)
  end.

(** Top-level powu. Requires [x <= FIX_ONE] (the production [require] check).
    Conditional order is rearranged from production so each test is
    individually reducible by [simpl] when its discriminating input is a
    closed numeral — this avoids [orb _ true] traps in proofs. *)
Definition powu (x y : Z) : Z :=
  if y =? 0 then FIX_ONE
  else if y =? 1 then x
  else if x =? FIX_ONE then FIX_ONE
  else
    (* x is scaled to D36 (1e36) for intermediate precision *)
    let x_d36 := x * FIX_SCALE in
    let result_d36 :=
      powu_aux (S (Z.to_nat (Z.log2 y))) x_d36 FIX_SCALE_SQ y in
    result_d36 / FIX_SCALE.

(** [shiftl(x, decimals, mode)] — FixLib.sol#L206-L218.
    Decimal shift in base 10. Negative decimals divide with rounding;
    positive decimals multiply.

    Edge cases from production:
      x = 0           => 0
      decimals <= -59 => CEIL? 1 : 0  (10^58 > 2^192)
      decimals >= 58  => revert       (x*10^58 > 2^192 if x != 0)
*)
Definition shiftl (x : Z) (decimals : Z) (mode : RoundingMode.t) : option Z :=
  if x =? 0 then Some 0
  else if decimals <=? -59 then
    Some (match mode with RoundingMode.CEIL => 1 | _ => 0 end)
  else if 58 <=? decimals then None
  else
    let coeff := 10 ^ (Z.abs decimals) in
    let shifted :=
      if 0 <=? decimals then x * coeff
      else divrnd x coeff mode in
    safeWrap shifted.

End FixLib.
