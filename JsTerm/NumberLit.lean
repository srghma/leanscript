module

@[expose] public section

set_option autoImplicit false

/-!
# `number` literals

How a JavaScript `number` (an IEEE double) is written in the source the backend prints: a
small integer as itself (`12`, `-3`), the special values as `NaN`, `Infinity`, `-Infinity` and
`-0`, and every other value as the **shortest** decimal that reads back as the same double
(`0.1`, `1e-7`, `5e-324`).

The value is taken apart with the core library's model of IEEE floats,
`Float.Model.UnpackedFloat` (`f.toModel.unpack`): not a number, a signed infinity, a signed
zero, or `± m * 2 ^ e` with `m > 0`.  A `Float32` unpacks to the same shape (`Float32.toModel`),
and its value is a double too, so the two share `UnpackedFloat.form`: the decimal printed for
a `Float32` reads back as that double exactly (a `number` holding a `Float32` is always one
`Math.fround` has rounded, so the literal must not be a shorter decimal that only rounds to the
same `Float32`).
-/

namespace MoreJs

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- The number of decimal digits of `n` (`1` for `0`). -/
def decDigits (n : Nat) : Nat := (toString n).length

/-- The shortest decimal `(digits, exponent)` with `digits * 10 ^ exponent` reading back as
    the double `m * 2 ^ e` (`m > 0`). -/
def shortestDecimal (m : Nat) (e : Int) : Nat × Int :=
  -- the exact value as `D * 10 ^ (-K)`
  let (D, K) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 0) else (m * 5 ^ e.natAbs, e.natAbs)
  let exact : Float := Float.ofScientific D true K
  let L := decDigits D
  let rec go (fuel k : Nat) : Nat × Int :=
    match fuel with
    | 0 => (D, -(K : Int))
    | fuel + 1 =>
      if k ≥ L then (D, -(K : Int)) else
      let drop := L - k
      let q := D / 10 ^ drop
      let r := D % 10 ^ drop
      let q := if 2 * r ≥ 10 ^ drop then q + 1 else q
      let ex : Int := (drop : Int) - K
      let f : Float := if ex ≥ 0 then Float.ofScientific q false ex.toNat
        else Float.ofScientific q true ex.natAbs
      if f.toBits == exact.toBits then (q, ex) else go fuel (k + 1)
  go 20 1

/-- How a `number` is written in JavaScript source. -/
inductive NumberForm where
  /-- `NaN`. -/
  | nan
  /-- `Infinity` or `-Infinity`. -/
  | infinity (neg : Bool)
  /-- `-0`. -/
  | negZero
  /-- An integer of absolute value at most `2 ^ 53`, written as itself. -/
  | int (n : Int)
  /-- `(neg ? "-" : "") digits e exponent`, the shortest such decimal. -/
  | decimal (neg : Bool) (digits : Nat) (exponent : Int)
  deriving Inhabited, Repr, BEq, DecidableEq

/-- Is the sign negative? -/
def signIsNeg : Sign → Bool
  | .negative => true
  | .positive => false

namespace NumberForm

/-- The value `m * 2 ^ e` as a natural number, when it is an integer of at most `2 ^ 53`. -/
def smallNat? (m : Nat) (e : Int) : Option Nat :=
  let v? : Option Nat :=
    if e ≥ 0 then some (m * 2 ^ e.toNat)
    else if m % 2 ^ e.natAbs == 0 then some (m / 2 ^ e.natAbs) else none
  match v? with
  | some v => if v ≤ 2 ^ 53 then some v else none
  | none => none

/-- The form of an unpacked float. -/
def ofUnpacked : UnpackedFloat → NumberForm
  | .notANumber => .nan
  | .infinity s => .infinity (signIsNeg s)
  | .zero s => if signIsNeg s then .negZero else .int 0
  | .finite s m e _ =>
    match smallNat? m e with
    | some v => .int (if signIsNeg s then -(v : Int) else v)
    | none =>
      let (d, ex) := stripZeros (shortestDecimal m e)
      .decimal (signIsNeg s) d ex
where
  /-- `(d, ex)` without the trailing zeros of `d` (rounding up can leave one: `10e-7`). -/
  stripZeros (p : Nat × Int) : Nat × Int :=
    let rec go (fuel : Nat) (d : Nat) (ex : Int) : Nat × Int :=
      match fuel with
      | 0 => (d, ex)
      | fuel + 1 => if d != 0 && d % 10 == 0 then go fuel (d / 10) (ex + 1) else (d, ex)
    go 400 p.1 p.2

/-- The form of a double. -/
def ofFloat (f : Float) : NumberForm := ofUnpacked f.toModel.unpack

/-- The form of a `Float32`, as the double that holds it. -/
def ofFloat32 (f : Float32) : NumberForm := ofUnpacked f.toModel.unpack

/-- The decimal `digits * 10 ^ exponent` (`digits > 0`) as JavaScript's `Number.prototype.
    toString` writes it: positional when the decimal point falls at most 21 digits to the right
    and 6 zeros to the left of the digits, scientific (`1.5e-7`, `1e+21`) otherwise. -/
def decimalString (digits : Nat) (exponent : Int) : String :=
  let s := toString digits
  let k : Int := s.length
  -- the position of the decimal point, counted from the left of the digits
  let n : Int := exponent + k
  if k ≤ n ∧ n ≤ 21 then s ++ String.ofList (List.replicate (n - k).toNat '0')
  else if 0 < n ∧ n ≤ 21 then
    String.ofList (s.toList.take n.toNat) ++ "." ++ String.ofList (s.toList.drop n.toNat)
  else if -6 < n ∧ n ≤ 0 then "0." ++ String.ofList (List.replicate n.natAbs '0') ++ s
  else
    let mant := match s.toList with
      | [] => s
      | [c] => String.singleton c
      | c :: cs => String.singleton c ++ "." ++ String.ofList cs
    let e := n - 1
    mant ++ "e" ++ (if e ≥ 0 then "+" else "-") ++ toString e.natAbs

/-- The form as JavaScript source, spelled as `String(x)` spells the number in JavaScript. -/
def source : NumberForm → String
  | .nan => "NaN"
  | .infinity neg => if neg then "-Infinity" else "Infinity"
  | .negZero => "-0"
  | .int n => toString n
  | .decimal neg d ex => (if neg then "-" else "") ++ decimalString d ex

end NumberForm

/-- A `number`, as JavaScript source. -/
def numberSource (f : Float) : String := (NumberForm.ofFloat f).source

/-- A `Float32` (a `number` rounded by `Math.fround`), as JavaScript source. -/
def float32Source (f : Float32) : String := (NumberForm.ofFloat32 f).source

end MoreJs

end
