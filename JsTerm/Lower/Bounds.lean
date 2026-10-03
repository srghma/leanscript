module

public import JsTerm.Lower.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Accesses to arrays known to be in bounds, and sizes compared as numbers

Two rewrites of the conversion from `Term` (`JsTerm.Lower.FromTerm`), both about the size of an
array, both local to the expression being converted:

* **Accesses in bounds.**  `a[i]!` (`lean_array_get d a i`, `Array.get!Internal`) reads the
  default `d` when `i` is out of bounds, so it is a call of the runtime
  (`uint53__lean_array_get(d, a, i)`).  Under a test that proves `i < a.size`, it is the plain
  access `a[i]` (`JsExpr.index`).  The conversion collects what the enclosing tests say of the
  sizes of the arrays held in variables (`BoundFacts`, carried by `Names.bounds`):

  | test | then | else |
  | --- | --- | --- |
  | `a.size == k` | `a.size ≥ k` | `a.size ≥ 1` when `k = 0` |
  | `k < a.size` | `a.size ≥ k + 1` | |
  | `a.size < k` | | `a.size ≥ k` |
  | `k ≤ a.size` | `a.size ≥ k` | |
  | `a.size ≤ k` | | `a.size ≥ k + 1` |
  | `i < a.size` | `i < a.size` | |
  | `a.size ≤ i` | | `i < a.size` |
  | `i < k` | `i < k` | |
  | `i ≤ k`, `i == k` | `i < k + 1` | |
  | `k ≤ i` | | `i < k` |
  | `k < i` | | `i < k + 1` |

  (`a`, `i` variables, `k` a literal).  An index `i < k` is in bounds of an array of at least
  `k` elements, and of an array literal of at least `k` elements (`#[1, 2, 3][i]` under
  `if i < 3`, the shape of `xs[i]?` once `xs` is inlined).  This is the shape Lean compiles a match on array
  literals to (`| #[_, 2] => …` is `if a.size = 2 then if a[1]! = 2 then …`), and the shape of
  `if h : i < a.size then a[i] else …`.  A variable is named by its de Bruijn level, which
  does not change under binders, and keeps the value the test saw everywhere below the test: a
  constant is never reassigned, and a mutable variable of a loop is only assigned at the end of
  an iteration, from values computed before any assignment (`loopNext`).  An array updated in
  place is never read again (`Own.updateInPlace`).  The default is
  only dropped when it is computed by no operation at all (`JsExpr.movable`).
* **Sizes compared as numbers.**  At the `BigInt` representation of `Nat`, the size of an array
  is `BigInt(a.length)`; a comparison of sizes and literals that fit in a safe integer is done
  on the numbers themselves: `BigInt(a.length) === 2n` is `a.length === 2` (a length is below
  `2 ^ 32`, so both comparisons agree).

Neither can be done on `Term`: the language has no access without a default (the proof of
bounds is erased, `Array.getInternal` is translated as `Array.get!Internal`), and its
naturals have no representation to change.
-/

namespace MoreJs

variable {S : JsSig}

open LeanScript

/-! ## Views of `Term` -/

/-- A natural number as the tests on sizes see it: a variable, a literal, or the size of the
    array held in a variable (`lean_array_get_size`). -/
inductive NatAtom where
  | const (x : VarKey)
  | lit (k : Nat)
  | size (x : VarKey)
  deriving Inhabited, BEq

/-- The comparisons of naturals the tests on sizes read. -/
inductive NatCmp where
  | eq
  | lt
  | le
  deriving Inhabited, BEq

/-- The variable a variable of `Term` lives in, if it lives in one. -/
def Ref.varKey? : Ref → Option VarKey
  | .c l => some (false, l)
  | .m l => some (true, l)
  | _ => Option.none

section
variable {ks : List Nat} {Δ : DSig ks}

/-- The JavaScript variable a pure expression is, if it is a variable living in one. -/
def pexprConst? {Φ : KCtx ks} {Γ : UCtx ks} (n : Names) : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → Option VarKey
  | _, _, .neu (.var x) => (n.u.getD x.index .none).varKey?
  | _, _, .kvar k => (n.k.getD k.index .none).varKey?
  | _, _, _ => none

/-- A pure expression as a `NatAtom`, if it is one. -/
def pexprAtom? {Φ : KCtx ks} {Γ : UCtx ks} (n : Names) : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → Option NatAtom
  | _, _, .lit p v =>
    match p, v with
    | .nat, v => some (.lit v)
    | _, _ => none
  | _, _, .neu (Neu.extern ex (.cons a .nil) _) =>
    if externName ex == "lean_array_get_size" then (pexprConst? n a).map .size else none
  | _, _, e => (pexprConst? n e).map .const

/-- The comparison of naturals a condition is, if it is one of `NatCmp` on two `NatAtom`s. -/
def condCmp? {Φ : KCtx ks} {Γ : UCtx ks} (n : Names) : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Option (NatCmp × NatAtom × NatAtom)
  | _, _, Neu.extern ex (.cons a (.cons b .nil)) _ => do
    let op ← match externName ex with
      | "lean_nat_dec_eq__Nat_decEq" | "lean_nat_dec_eq__Nat_beq" => some NatCmp.eq
      | "lean_nat_dec_lt" => some .lt
      | "lean_nat_dec_le__Nat_ble" | "lean_nat_dec_le__Nat_decLe" => some .le
      | _ => none
    return (op, ← pexprAtom? n a, ← pexprAtom? n b)
  | _, _, _ => none

end

/-! ## The facts -/

namespace BoundFacts

/-- The array in `a` has at least `k` elements. -/
def addMin (f : BoundFacts) (a : VarKey) (k : Nat) : BoundFacts := { f with minSize := (a, k) :: f.minSize }

/-- The natural in `i` is smaller than the size of the array in `a`. -/
def addIdx (f : BoundFacts) (i a : VarKey) : BoundFacts := { f with idxLt := (i, a) :: f.idxLt }

/-- The natural in `i` is smaller than the literal `k`. -/
def addIdxLit (f : BoundFacts) (i : VarKey) (k : Nat) : BoundFacts :=
  { f with idxLtLit := (i, k) :: f.idxLtLit }

/-- The facts below a test, in its two branches (the table of the module documentation). -/
def split (f : BoundFacts) : NatCmp × NatAtom × NatAtom → BoundFacts × BoundFacts
  | (.eq, .size a, .lit k) | (.eq, .lit k, .size a) =>
    (f.addMin a k, if k == 0 then f.addMin a 1 else f)
  | (.lt, .lit k, .size a) => (f.addMin a (k + 1), f)
  | (.lt, .size a, .lit k) => (f, f.addMin a k)
  | (.le, .lit k, .size a) => (f.addMin a k, f)
  | (.le, .size a, .lit k) => (f, f.addMin a (k + 1))
  | (.lt, .const i, .size a) => (f.addIdx i a, f)
  | (.le, .size a, .const i) => (f, f.addIdx i a)
  | (.lt, .const i, .lit k) => (f.addIdxLit i k, f)
  | (.le, .const i, .lit k) => (f.addIdxLit i (k + 1), f)
  | (.lt, .lit k, .const i) => (f, f.addIdxLit i (k + 1))
  | (.le, .lit k, .const i) => (f, f.addIdxLit i k)
  | (.eq, .const i, .lit k) | (.eq, .lit k, .const i) => (f.addIdxLit i (k + 1), f)
  | _ => (f, f)

/-- Is the index `i` known to be smaller than the size of the array in `a`? -/
def inBounds (f : BoundFacts) (a : VarKey) : NatAtom → Bool
  | .lit k => f.minSize.any fun (a', m) => a' == a && k < m
  | .const i => f.idxLt.any (fun (i', a') => i' == i && a' == a) ||
      f.idxLtLit.any fun (i', k) => i' == i && f.minSize.any fun (a', m) => a' == a && k ≤ m
  | .size _ => false

/-- Is the index `i` known to be smaller than `n`, the length of an array literal? -/
def inBoundsLit (f : BoundFacts) (n : Nat) : NatAtom → Bool
  | .lit k => k < n
  | .const i => f.idxLtLit.any fun (i', k) => i' == i && k ≤ n
  | .size _ => false

end BoundFacts

/-- The facts of the two branches of a test on the condition `c`. -/
def Names.splitOn {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {ℓ : Nat} (n : Names) (c : Neu Δ Φ Γ τ ℓ) : Names × Names :=
  match condCmp? n c with
  | some v => let (t, e) := n.bounds.split v; ({ n with bounds := t }, { n with bounds := e })
  | none => (n, n)

/-- The number of elements of an array or list literal. -/
def elemsLength {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} :
    {o : Lvl} → Elems Δ Φ Γ t o → Nat
  | _, .nil => 0
  | _, .cons _ es => elemsLength es + 1

/-- Is the call of `lean_array_get` (or `lean_array_get_borrowed`) on the arguments `args`
    (the default, the array, the index) known to be in bounds? -/
def Names.getInBounds {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}
    {σs : List (Ty ks)} {o : Lvl} (n : Names) : Args Δ Φ Γ σs o → Bool
  | .cons _ (.cons a (.cons i .nil)) =>
    match a, pexprAtom? n i with
    | .array_mk es, some i => n.bounds.inBoundsLit (elemsLength es) i
    | _, some i =>
      match pexprConst? n a with
      | some a => n.bounds.inBounds a i
      | none => false
    | _, _ => false
  | _ => false

/-! ## The rewrites of the JavaScript -/

/-- `uint53__lean_array_get(d, a, i)` (or its `BigInt` version) as the access `a[i]`, when the
    default `d` is computed by no operation (so that dropping it drops nothing).  The caller
    knows that the access is in bounds. -/
def JsExpr.uncheckedGet? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option (JsExpr S C M τ)
  | .imported (.uint53__lean_array_get l) (.cons d (.cons a (.cons i .nil))) =>
    if d.movable then some (.index l .uint53 a i) else none
  | .imported (.bigint_nat__lean_array_get l) (.cons d (.cons a (.cons i .nil))) =>
    if d.movable then some (.index l .bigint_nat a i) else none
  | _ => none

/-- A `BigInt` natural as a `number`, when it is the size of an array (`BigInt(a.length)` is
    `a.length`, the flag `true`) or a literal that fits in a safe integer (the flag `false`). -/
def JsExpr.narrowNat? {C M : List JsTy} :
    JsExpr S C M (.terminal .bigint_nat) → Option (JsExpr S C M (.terminal .uint53) × Bool)
  | .inlined (.bigint_nat__lean_array_get_size l) args =>
    some (.inlined (.uint53__lean_array_get_size l) args, true)
  | .lit (.bigint_nat k) => if h : k ≤ maxSafe then some (.lit (.uint53 k h), false) else none
  | _ => none

/-- The comparison `op` of two `BigInt` naturals done on `number`s, when both narrow
    (`JsExpr.narrowNat?`) and one of them is the size of an array. -/
def narrowCmp2 {C M : List JsTy}
    (op : JsOpInlinable .pure .doesntThrow [.terminal .uint53, .terminal .uint53] (.terminal .bool))
    (a b : JsExpr S C M (.terminal .bigint_nat)) : Option (JsExpr S C M (.terminal .bool)) := do
  let (a', sa) ← a.narrowNat?
  let (b', sb) ← b.narrowNat?
  if sa || sb then some (.inlined op (.cons a' (.cons b' .nil))) else none

/-- `BigInt(a.length) === 2n` as `a.length === 2` (and `<`, `<=`): a comparison of `BigInt`
    naturals of which one is the size of an array and the other the size of an array or a
    literal that fits in a safe integer, done on `number`s. -/
def JsExpr.narrowCmp? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option (JsExpr S C M τ)
  | .inlined .bigint_nat__lean_nat_dec_eq__Nat_decEq (.cons a (.cons b .nil)) =>
    narrowCmp2 .uint53__lean_nat_dec_eq__Nat_decEq a b
  | .inlined .bigint_nat__lean_nat_dec_eq__Nat_beq (.cons a (.cons b .nil)) =>
    narrowCmp2 .uint53__lean_nat_dec_eq__Nat_beq a b
  | .inlined .bigint_nat__lean_nat_dec_lt (.cons a (.cons b .nil)) =>
    narrowCmp2 .uint53__lean_nat_dec_lt a b
  | .inlined .bigint_nat__lean_nat_dec_le__Nat_ble (.cons a (.cons b .nil)) =>
    narrowCmp2 .uint53__lean_nat_dec_le__Nat_ble a b
  | .inlined .bigint_nat__lean_nat_dec_le__Nat_decLe (.cons a (.cons b .nil)) =>
    narrowCmp2 .uint53__lean_nat_dec_le__Nat_decLe a b
  | _ => none

end MoreJs

end
