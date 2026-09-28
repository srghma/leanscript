module

@[expose] public section

set_option autoImplicit false

/-!
# A model of the JavaScript that `runtime.js` uses

`runtime.js` holds each Lean integer in one of two JavaScript representations:

* a `BigInt` (the `bigint_nat` / `bigint_int` representations), an arbitrary-precision
  integer, modelled here by `Int`;
* a `number` holding a **safe integer** (the `uint53` / `int53` representations), one of
  absolute value at most `2^53 - 1`, also modelled by `Int` (`IsSafe`).

## What the model assumes about `number`

A `number` is an IEEE double.  On safe integers the operations `runtime.js` uses are modelled
by their exact integer results:

* `a + b`, `a - b`, `a * b` are exact whenever the exact result is safe; when it is not, the
  rounded double is not safe either (rounding is monotone and `2^53` is a double), so
  `Number.isSafeInteger` rejects it exactly when it rejects the exact result.  `$chk53` is
  therefore modelled by `toNum53` of the exact result.
* `Math.floor(a / b)`, `Math.trunc(a / b)`, `a / 2 ** k` (floored), and `x | 0` of a quotient
  (which truncates) are modelled by the exact integer quotients (`Int.fdiv`, `Int.tdiv`).  This
  is the same assumption the rest of `runtime.js` (and the old runtime) already makes for
  `Nat.div` on numbers.
* `a % b` is `Int.tmod` (the sign of `a`), `Math.abs` is `Int.natAbs`.

The 32-bit operators are modelled exactly: `ToInt32(x)` is `BitVec.ofInt 32 x`, the result of
`&`, `|`, `^`, `<<`, `>>` is read back signed (`BitVec.toInt`), the result of `>>>` unsigned
(`BitVec.toNat`), and a shift count is taken modulo 32.

A `BigInt` is exact, `BigInt.asUintN(n, x)` is `x % 2^n` and `BigInt.asIntN(n, x)` is
`x.bmod (2^n)`.  A thrown `RangeError` (integer overflow) is `none`.
-/

namespace RuntimeSpec

/-- The largest safe integer, `Number.MAX_SAFE_INTEGER = 2^53 - 1`. -/
def maxSafe : Int := 2 ^ 53 - 1

/-- A safe integer: what a `uint53` / `int53` `number` holds. -/
def IsSafe (x : Int) : Prop := -maxSafe ≤ x ∧ x ≤ maxSafe

instance (x : Int) : Decidable (IsSafe x) := by unfold IsSafe; infer_instance

/-- `$toNum53` (on a `BigInt`) and `$chk53` (on a `number`, see the module doc): the result
as a safe integer, or the overflow `RangeError` (`none`). -/
def toNum53 (x : Int) : Option Int := if -maxSafe ≤ x ∧ x ≤ maxSafe then some x else none

/-- `ToInt32(x)`, as a 32-bit vector. -/
def toI32 (x : Int) : BitVec 32 := BitVec.ofInt 32 x

/-- The shift count of `<<`, `>>`, `>>>`: `ToUint32(n) & 31`. -/
def shiftCount (n : Int) : Nat := (toI32 n).toNat % 32

/-- `x & y`. -/
def band (x y : Int) : Int := (toI32 x &&& toI32 y).toInt
/-- `x | y`. -/
def bor (x y : Int) : Int := (toI32 x ||| toI32 y).toInt
/-- `x ^ y`. -/
def bxor (x y : Int) : Int := (toI32 x ^^^ toI32 y).toInt
/-- `x << n`. -/
def shl (x n : Int) : Int := (toI32 x <<< shiftCount n).toInt
/-- `x >> n`. -/
def sar (x n : Int) : Int := ((toI32 x).sshiftRight (shiftCount n)).toInt
/-- `x >>> n`. -/
def ushr (x n : Int) : Int := ((toI32 x) >>> shiftCount n).toNat
/-- `Math.clz32(x)`: the leading zero bits of `ToUint32(x)`. -/
def clz32 (x : Int) : Nat :=
  let u := (toI32 x).toNat
  if u = 0 then 32 else 31 - u.log2

/-- `BigInt.asUintN(n, x)`. -/
def asUintN (n : Nat) (x : Int) : Int := x % (2 ^ n : Nat)
/-- `BigInt.asIntN(n, x)`. -/
def asIntN (n : Nat) (x : Int) : Int := x.bmod (2 ^ n)

/-- A JavaScript value holding an integer, as the **old** runtime had to expect it: a
`BigInt` or a `number` (it tested which with `typeof`). -/
inductive JsInt where
  | big (x : Int)
  | num (x : Int)

end RuntimeSpec
