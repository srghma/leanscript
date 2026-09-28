module

public import RuntimeSpec.Model

@[expose] public section

set_option autoImplicit false

/-!
# The refactored functions of `runtime.js`, transcribed

Each definition is the function of the same name in `runtime.js`, transcribed into the model
of `RuntimeSpec.Model` operator by operator (the JavaScript is quoted in each docstring).
A function returning `Option Int` may throw the overflow `RangeError` (`none`); one returning
`Int` cannot throw.

`RuntimeSpec.Old` transcribes the **old** versions of the functions whose shape changed: the
ones that tested `typeof` (on a `JsInt`) and the ones that went through `BigInt` and `$toNum53`.
-/

namespace RuntimeSpec

/-! ## The new runtime -/

namespace New

/-! ### Fixed-width conversions on numbers -/

/-- `uint53__lean_uint16_of_nat = (a) => a & 65535` -/
def uint53__lean_uint16_of_nat (a : Int) : Int := band a 65535
/-- `uint53__lean_uint32_of_nat = (a) => a >>> 0` -/
def uint53__lean_uint32_of_nat (a : Int) : Int := ushr a 0
/-- `uint53__lean_uint8_of_nat = (a) => a & 255` -/
def uint53__lean_uint8_of_nat (a : Int) : Int := band a 255
/-- `int53__lean_int16_of_int = (a) => (a << 16) >> 16` -/
def int53__lean_int16_of_int (a : Int) : Int := sar (shl a 16) 16
/-- `int53__lean_int32_of_int = (a) => a | 0` -/
def int53__lean_int32_of_int (a : Int) : Int := bor a 0
/-- `int53__lean_int8_of_int = (a) => (a << 24) >> 24` -/
def int53__lean_int8_of_int (a : Int) : Int := sar (shl a 24) 24

/-! ### Fixed-width conversions on `BigInt`s (no `typeof`, no `BigInt(a)`) -/

/-- `bigint_int__lean_int16_of_int = (a) => Number(BigInt.asIntN(16, a))` -/
def bigint_int__lean_int16_of_int (a : Int) : Int := asIntN 16 a
/-- `bigint_int__lean_int32_of_int = (a) => Number(BigInt.asIntN(32, a))` -/
def bigint_int__lean_int32_of_int (a : Int) : Int := asIntN 32 a
/-- `bigint_int__lean_int8_of_int = (a) => Number(BigInt.asIntN(8, a))` -/
def bigint_int__lean_int8_of_int (a : Int) : Int := asIntN 8 a
/-- `bigint_nat__lean_uint16_of_nat = (a) => Number(BigInt.asUintN(16, a))` -/
def bigint_nat__lean_uint16_of_nat (a : Int) : Int := asUintN 16 a
/-- `bigint_nat__lean_uint32_of_nat = (a) => Number(BigInt.asUintN(32, a))` -/
def bigint_nat__lean_uint32_of_nat (a : Int) : Int := asUintN 32 a
/-- `bigint_nat__lean_uint8_of_nat = (a) => Number(BigInt.asUintN(8, a))` -/
def bigint_nat__lean_uint8_of_nat (a : Int) : Int := asUintN 8 a

/-! ### Bitwise operations below `2^53`, on the high 21 and the low 32 bits apart -/

/-- `$land53 = (a, b) => (((a / 2^32) | 0) & ((b / 2^32) | 0)) * 2^32 + ((a & b) >>> 0)`
(`uint53__lean_nat_land`, `uint53__lean_uint64_land`) -/
def land53 (a b : Int) : Int :=
  band (bor (a.tdiv (2 ^ 32)) 0) (bor (b.tdiv (2 ^ 32)) 0) * 2 ^ 32 + ushr (band a b) 0
/-- `$lor53` (`uint53__lean_nat_lor`, `uint53__lean_uint64_lor`) -/
def lor53 (a b : Int) : Int :=
  bor (bor (a.tdiv (2 ^ 32)) 0) (bor (b.tdiv (2 ^ 32)) 0) * 2 ^ 32 + ushr (bor a b) 0
/-- `$xor53` (`uint53__lean_nat_lxor`, `uint53__lean_uint64_xor`) -/
def xor53 (a b : Int) : Int :=
  bxor (bor (a.tdiv (2 ^ 32)) 0) (bor (b.tdiv (2 ^ 32)) 0) * 2 ^ 32 + ushr (bxor a b) 0
/-- `$log2_53 = (a) => a < 2^32 ? (a === 0 ? 0 : 31 - Math.clz32(a)) : 63 - Math.clz32(a / 2^32)`
(`uint53__lean_uint64_log2`) -/
def log2_53 (a : Int) : Int :=
  if a < 2 ^ 32 then (if a = 0 then 0 else 31 - (clz32 a : Int))
  else 63 - (clz32 (a.tdiv (2 ^ 32)) : Int)

/-! ### `UInt64` below `2^53` (`uint53`) -/

/-- `uint53__lean_uint64_add = (a, b) => $chk53(a + b)` -/
def uint53__lean_uint64_add (a b : Int) : Option Int := toNum53 (a + b)
/-- `uint53__lean_uint64_sub = (a, b) => a >= b ? a - b : $toNum53(BigInt.asUintN(64, BigInt(a - b)))` -/
def uint53__lean_uint64_sub (a b : Int) : Option Int :=
  if a ≥ b then some (a - b) else toNum53 (asUintN 64 (a - b))
/-- `uint53__lean_uint64_neg = (a) => a === 0 ? 0 : $toNum53(2n ** 64n - BigInt(a))` -/
def uint53__lean_uint64_neg (a : Int) : Option Int :=
  if a = 0 then some 0 else toNum53 (2 ^ 64 - a)
/-- `uint53__lean_uint64_complement = (a) => $toNum53(BigInt.asUintN(64, ~BigInt(a)))` -/
def uint53__lean_uint64_complement (a : Int) : Option Int := toNum53 (asUintN 64 (-a - 1))
/-- `uint53__lean_uint64_mul = (a, b) => $toNum53(BigInt.asUintN(64, BigInt(a) * BigInt(b)))` -/
def uint53__lean_uint64_mul (a b : Int) : Option Int := toNum53 (asUintN 64 (a * b))
/-- `uint53__lean_uint64_div = (a, b) => b === 0 ? 0 : Math.floor(a / b)` -/
def uint53__lean_uint64_div (a b : Int) : Int := if b = 0 then 0 else a.fdiv b
/-- `uint53__lean_uint64_mod = (a, b) => b === 0 ? a : a % b` -/
def uint53__lean_uint64_mod (a b : Int) : Int := if b = 0 then a else a.tmod b
/-- `uint53__lean_uint64_shift_right = (a, b) => Math.floor(a / 2 ** (b % 64))` -/
def uint53__lean_uint64_shift_right (a b : Int) : Int := a.fdiv (2 ^ (b.tmod 64).toNat)
/-- `uint53__lean_uint64_of_nat = (a) => a` (also `…_ofNatLT`) -/
def uint53__lean_uint64_of_nat (a : Int) : Int := a

/-! ### `Int64` of absolute value below `2^53` (`int53`) -/

/-- `int53__lean_int64_of_int = (a) => a` (also `uint53__int53__lean_int64_of_nat`) -/
def int53__lean_int64_of_int (a : Int) : Int := a
/-- `int53__lean_int64_abs = (a) => Math.abs(a)` -/
def int53__lean_int64_abs (a : Int) : Int := a.natAbs
/-- `int53__lean_int64_neg = (a) => 0 - a` -/
def int53__lean_int64_neg (a : Int) : Int := 0 - a
/-- `int53__lean_int64_add = (a, b) => $chk53(a + b)` -/
def int53__lean_int64_add (a b : Int) : Option Int := toNum53 (a + b)
/-- `int53__lean_int64_sub = (a, b) => $chk53(a - b)` -/
def int53__lean_int64_sub (a b : Int) : Option Int := toNum53 (a - b)
/-- `int53__lean_int64_complement = (a) => $chk53(-a - 1)` -/
def int53__lean_int64_complement (a : Int) : Option Int := toNum53 (-a - 1)
/-- `int53__lean_int64_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b)` -/
def int53__lean_int64_div (a b : Int) : Int := if b = 0 then 0 else a.tdiv b
/-- `int53__lean_int64_mod = (a, b) => b === 0 ? a : a % b` -/
def int53__lean_int64_mod (a b : Int) : Int := if b = 0 then a else a.tmod b
/-- `int53__lean_int64_shift_right = (a, b) => Math.floor(a / 2 ** (((b % 64) + 64) % 64))` -/
def int53__lean_int64_shift_right (a b : Int) : Int :=
  a.fdiv (2 ^ ((b.tmod 64 + 64).tmod 64).toNat)

/-! ### `Nat` / `Int` conversions -/

/-- `int53__uint53__lean_nat_abs = (a) => Math.abs(a)` -/
def int53__uint53__lean_nat_abs (a : Int) : Int := a.natAbs
/-- `int53__bigint_nat__lean_nat_abs = (a) => BigInt(Math.abs(a))` -/
def int53__bigint_nat__lean_nat_abs (a : Int) : Int := a.natAbs
/-- `bigint_int__uint53__lean_nat_abs = (a) => $toNum53(a < 0n ? -a : a)` -/
def bigint_int__uint53__lean_nat_abs (a : Int) : Option Int := toNum53 (if a < 0 then -a else a)
/-- `uint53__int53__lean_int_neg_succ_of_nat = (a) => -a - 1` -/
def uint53__int53__lean_int_neg_succ_of_nat (a : Int) : Int := -a - 1
/-- `bigint_nat__int53__lean_int_neg_succ_of_nat = (a) => $toNum53(-a - 1n)` -/
def bigint_nat__int53__lean_int_neg_succ_of_nat (a : Int) : Option Int := toNum53 (-a - 1)

/-! ### Arrays indexed by a `BigInt`

`Number(i)` of a `BigInt` is a double: the model only uses that it is exact on safe integers
and monotone (`num` below). -/

/-- `bigint_nat__lean_array_get = (d, a, i) => { const k = Number(i); return k < a.length ? a[k] : d; }` -/
def bigint_nat__lean_array_get {α : Type} (num : Int → Int) (d : α) (a : List α) (i : Int) : α :=
  let k := num i
  if k < a.length then a.getD k.toNat d else d

/-- `uint53__lean_array_get = (d, a, i) => (i < a.length ? a[i] : d)` -/
def uint53__lean_array_get {α : Type} (d : α) (a : List α) (i : Int) : α :=
  if i < a.length then a.getD i.toNat d else d

end New

/-! ## The old runtime (the functions whose shape changed) -/

namespace Old

/-- `bigint_int__lean_int16_of_int = (a) => typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16`
(shared, through an alias, with `int53__lean_int16_of_int`) -/
def bigint_int__lean_int16_of_int : JsInt → Int
  | .big a => asIntN 16 a
  | .num a => sar (shl a 16) 16

/-- `bigint_nat__lean_uint16_of_nat = (a) => typeof a === "bigint" ? Number(BigInt.asUintN(16, a)) : ((a % 65536) + 65536) % 65536` -/
def bigint_nat__lean_uint16_of_nat : JsInt → Int
  | .big a => asUintN 16 a
  | .num a => ((a.tmod 65536) + 65536).tmod 65536

/-- `bigint_int__uint53__lean_nat_abs = (a) => typeof a === "bigint" ? $toNum53(a < 0n ? -a : a) : a < 0 ? -a : a`
(shared with `int53__uint53__lean_nat_abs`) -/
def bigint_int__uint53__lean_nat_abs : JsInt → Option Int
  | .big a => toNum53 (if a < 0 then -a else a)
  | .num a => some (if a < 0 then -a else a)

/-- `bigint_nat__int53__lean_int_neg_succ_of_nat = (a) => typeof a === "bigint" ? $toNum53(-a - 1n) : -a - 1`
(shared with `uint53__int53__lean_int_neg_succ_of_nat`) -/
def bigint_nat__int53__lean_int_neg_succ_of_nat : JsInt → Option Int
  | .big a => toNum53 (-a - 1)
  | .num a => some (-a - 1)

/-- The old `$idx`: `typeof i === "bigint" ? (i > MAX_SAFE ? Infinity : Number(i)) : i`,
with `Infinity` as `none`. -/
def idx (num : Int → Int) : JsInt → Option Int
  | .big i => if i > maxSafe then none else some (num i)
  | .num i => some i

/-- `bigint_nat__lean_array_get = (d, a, i) => { const k = $idx(i); return k < a.length ? a[k] : d; }` -/
def bigint_nat__lean_array_get {α : Type} (num : Int → Int) (d : α) (a : List α) (i : JsInt) : α :=
  match idx num i with
  | some k => if k < a.length then a.getD k.toNat d else d
  | none => d

/-- The old `uint53` / `int53` `UInt64` / `Int64` operations: `a = BigInt(a); b = BigInt(b);
return $toNum53(…)`, all of them through `BigInt` and all of them checked. -/
def uint53__lean_uint64_div (a b : Int) : Option Int := toNum53 (if b = 0 then 0 else asUintN 64 (a / b))
/-- old `uint53__lean_uint64_mod`: `$toNum53(b === 0n ? a : a % b)` -/
def uint53__lean_uint64_mod (a b : Int) : Option Int := toNum53 (if b = 0 then a else a.tmod b)
/-- old `uint53__lean_uint64_add`: `$toNum53(BigInt.asUintN(64, a + b))` -/
def uint53__lean_uint64_add (a b : Int) : Option Int := toNum53 (asUintN 64 (a + b))
/-- old `uint53__lean_uint64_sub`: `$toNum53(BigInt.asUintN(64, a - b))` -/
def uint53__lean_uint64_sub (a b : Int) : Option Int := toNum53 (asUintN 64 (a - b))
/-- old `uint53__lean_uint64_neg`: `$toNum53(BigInt.asUintN(64, -a))` -/
def uint53__lean_uint64_neg (a : Int) : Option Int := toNum53 (asUintN 64 (-a))
/-- old `uint53__lean_uint64_shift_right`: `$toNum53(a >> (((b % 64n) + 64n) % 64n))` -/
def uint53__lean_uint64_shift_right (a b : Int) : Option Int :=
  toNum53 (a >>> ((b % 64 + 64) % 64).toNat)
/-- old `int53__lean_int64_div`: `$toNum53(b === 0n ? 0n : BigInt.asIntN(64, a / b))` (a
`BigInt` `/` truncates) -/
def int53__lean_int64_div (a b : Int) : Option Int := toNum53 (if b = 0 then 0 else asIntN 64 (a.tdiv b))
/-- old `int53__lean_int64_abs`: `$toNum53(BigInt.asIntN(64, a < 0n ? -a : a))` -/
def int53__lean_int64_abs (a : Int) : Option Int := toNum53 (asIntN 64 (if a < 0 then -a else a))
/-- old `int53__lean_int64_add`: `$toNum53(BigInt.asIntN(64, a + b))` -/
def int53__lean_int64_add (a b : Int) : Option Int := toNum53 (asIntN 64 (a + b))
/-- old `int53__lean_int64_of_int`: `$toNum53(BigInt.asIntN(64, BigInt(a)))` -/
def int53__lean_int64_of_int (a : Int) : Option Int := toNum53 (asIntN 64 a)

end Old

end RuntimeSpec
