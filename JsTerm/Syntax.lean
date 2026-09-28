module

public import JsTerm.OpsLookup

@[expose] public section

set_option autoImplicit false

/-!
# `JsTerm`: the JavaScript grammar, simply typed

`LeanScript.Term` models Lean code: intrinsically typed, de Bruijn indexed, every redex that
could be computed computed.  The grammar here models the **JavaScript** the backend prints:
a simply typed subset of JavaScript, split into expressions (`JsExpr`) and blocks of
statements (`JsBlock`), with `return`, loops with a mutable accumulator, calls of the
runtime, and join points.  It is intrinsically typed too: an expression of type `τ` is a
`JsExpr C M τ`, and a block a `JsBlock C M J k`, so the printer never meets an ill-typed
term, and every pass of the backend is type-preserving by construction.

`JsTerm.PrintMini` maps the grammar onto the full JavaScript syntax tree of
`LanguageJavascriptMini`, whose printer writes the `.js` file.

## Variables: three de Bruijn contexts

A local variable is not named: it is a **de Bruijn index** (`JsMem Γ τ`, a typed position in
a context `Γ`) into one of three separate contexts, so that no pass of the backend ever has to
invent a fresh name or worry about capture (the printer chooses the names):

* the **constants** `C` (`JsExpr.cvar`): the variables that are never reassigned — the
  parameters of the functions, `const x = e;`, the fields a pattern binds, the element of a
  `for … of` loop, the counter of a counting loop, and the value a join point receives;
* the **mutable variables** `M` (`JsExpr.mvar`): the variables declared by `let x = e;`,
  which `x = e;` (`JsBlock.assign`) reassigns (the accumulators of the loops);
* the **join points** `J` (`JsBlock.jump`): the enclosing `join` blocks, each by the type of
  the value a jump to it passes.

Index `0` is the innermost variable of its context.  A binder binds its variables for the
statements that follow it in its block; the variables of a pattern are bound in order, the
last one innermost (`pushAll`).  An arrow function binds its parameter as a constant on top of
the constants around it, keeps the mutable variables around it, and starts with no join point
(a jump never leaves a function); so does the body of a loop.  Every binder keeps a *hint*,
the name the printer starts from (`x`, `acc`, a parameter's Lean name); hints carry no
meaning.

## Operations

There are no generic operators: every operation is typed, and is named by the JavaScript
representation of its signature and the extern it implements (`bigint_nat__lean_nat_div :
[bigint_nat, bigint_nat] → bigint_nat`, `uint53__lean_nat_land : [uint53, uint53] →
uint53`).  An operation either calls a function of the runtime of the same name
(`JsOpImported`, `JsTerm.OpsImported`) or is written inline as a JavaScript operator or
conversion (`JsOpInlined`, `JsTerm.OpsInlined`).  An extern without an operation at the
representation of its arguments is `JsExpr.unimplemented`, a call that throws.

## Blocks

A block ends in `return e` (`JsBlock.ret`, in a function: `k = .ret τ`), in the end of an
iteration (`JsBlock.next`, in the body of a loop: `k = .loop`), in a jump to an enclosing join
point, or in a `throw`.  A join point `join x block rest` is the labelled block `L: { block }`
whose statements may jump to it (join point `0` inside `block`), passing a value that `rest`
reads as its innermost constant `x`.
-/

namespace MoreJs

/-! ## Contexts -/

/-- A typed position in a context: a de Bruijn index (`zero` is the innermost). -/
inductive JsMem {α : Type} : List α → α → Type where
  | zero {x : α} {xs : List α} : JsMem (x :: xs) x
  | succ {x y : α} {xs : List α} : JsMem xs x → JsMem (y :: xs) x
  deriving Repr

namespace JsMem

variable {α : Type}

/-- The de Bruijn index of a position. -/
def index {xs : List α} {x : α} : JsMem xs x → Nat
  | .zero => 0
  | .succ m => m.index + 1

/-- The position of index `i` in `xs`, if it holds `x`. -/
def ofIndex? [DecidableEq α] : (xs : List α) → Nat → (x : α) → Option (JsMem xs x)
  | [], _, _ => none
  | y :: _, 0, x => if h : y = x then some (h ▸ .zero) else none
  | _ :: ys, i + 1, x => (ofIndex? ys i x).map .succ

end JsMem

/-- `pushAll us C`: the context `C` after binding the variables of the types `us` in order,
    the last one innermost. -/
def pushAll {α : Type} : List α → List α → List α
  | [], c => c
  | u :: us, c => pushAll us (u :: c)

/-- Which fields of a record (or of a constructor of a union) a pattern binds, with their
    hints: `JsSel ts us` keeps the fields `us` of the fields `ts`. -/
inductive JsSel : List JsTy → List JsTy → Type where
  | nil : JsSel [] []
  | keep {t : JsTy} {ts us : List JsTy} (hint : String) : JsSel ts us → JsSel (t :: ts) (t :: us)
  | skip {t : JsTy} {ts us : List JsTy} : JsSel ts us → JsSel (t :: ts) us
  deriving Repr

/-- The pattern that binds no field. -/
def JsSel.none : (ts : List JsTy) → JsSel ts []
  | [] => .nil
  | _ :: ts => .skip (JsSel.none ts)

/-- The hints of the fields a pattern binds, with their positions (from `0`). -/
def JsSel.binds {ts us : List JsTy} : JsSel ts us → List (Nat × String) :=
  go 0
where
  go {ts us : List JsTy} (i : Nat) : JsSel ts us → List (Nat × String)
    | .nil => []
    | .keep h s => (i, h) :: go (i + 1) s
    | .skip s => go (i + 1) s

/-- How a block ends: by returning a value of type `τ` (a function body), or by ending the
    iteration (a loop body). -/
inductive JsEnd where
  | ret (τ : JsTy)
  | loop
  deriving Repr, DecidableEq

/-! ## Literals -/

/-- The largest safe integer of a `number`. -/
def maxSafe : Nat := 2 ^ 53 - 1

/-- A literal of a leaf type.  A literal at a `number` representation of an unbounded type
    carries the proof that it fits. -/
inductive JsLit : JsTerminalTy → Type where
  | bool (b : Bool) : JsLit .bool
  | bigint_nat (n : Nat) : JsLit .bigint_nat
  | uint53 (n : Nat) (h : n ≤ maxSafe) : JsLit .uint53
  | bigint_int (n : Int) : JsLit .bigint_int
  | int53 (n : Int) (h : n.natAbs ≤ maxSafe) : JsLit .int53
  | bitvec_small {n : Nat} {h₁ : n ≤ 53} {h₂ : 2 ≤ n} (v : Nat) : JsLit (.bitvec_small n h₁ h₂)
  | bigint_bitvec_big {n : Nat} {h : 53 < n} (v : Nat) : JsLit (.bigint_bitvec_big n h)
  | int53_bitvec_big {n : Nat} {h : 53 < n} (v : Nat) (hv : v ≤ maxSafe) :
      JsLit (.int53_bitvec_big n h)
  | uint8 (v : UInt8) : JsLit .uint8
  | uint16 (v : UInt16) : JsLit .uint16
  | uint32 (v : UInt32) : JsLit .uint32
  | int8 (v : Int8) : JsLit .int8
  | int16 (v : Int16) : JsLit .int16
  | int32 (v : Int32) : JsLit .int32
  | float (f : Float) : JsLit .float
  | float32 (f : Float32) : JsLit .float32
  | string (s : String) : JsLit .string
  /-- `[str, startPos, stopPos]`. -/
  | substring (s : String) (start stop : Nat) : JsLit .substring
  /-- `[str, startPos, stopPos]`. -/
  | stringSlice (s : String) (start stop : Nat) : JsLit .stringSlice

/-- The shape of a double: `NaN`, an infinity, or `± m * 2 ^ e` exactly. -/
inductive FloatParts where
  | nan
  | inf (neg : Bool)
  /-- `(neg ? -1 : 1) * m * 2 ^ e` (`m = 0` for the zeros). -/
  | finite (neg : Bool) (m : Nat) (e : Int)
  deriving Inhabited, Repr, BEq

/-- The shape of a double, read off its IEEE bits. -/
def floatParts (f : Float) : FloatParts :=
  let bits : Nat := f.toBits.toNat
  let neg : Bool := (bits / 2 ^ 63) % 2 == 1
  let ex : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let frac : Nat := bits % 2 ^ 52
  if ex == 2047 then
    if frac != 0 then .nan else .inf neg
  else if ex == 0 then .finite neg frac (-1074)
  else .finite neg (frac + 2 ^ 52) ((ex : Int) - 1075)

/-- The integer a finite double stands for, when it is one of absolute value `≤ 2^53`. -/
def floatSmallInt? (f : Float) : Option Int :=
  match floatParts f with
  | .finite neg m e =>
    let v? : Option Nat :=
      if e ≥ 0 then some (m * 2 ^ e.toNat)
      else if m % 2 ^ e.natAbs == 0 then some (m / 2 ^ e.natAbs) else none
    match v? with
    | some v => if v ≤ 2 ^ 53 then some (if neg then -(v : Int) else v) else none
    | none => none
  | _ => none

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

/-- A `number`, as JavaScript source: an integer when it is a small one, otherwise the
    shortest decimal that reads back as the same double (`NaN`, `Infinity`, `-Infinity`,
    `-0` for the special values). -/
def numberSource (f : Float) : String :=
  match floatSmallInt? f, floatParts f with
  | some 0, .finite true _ _ => "-0"
  | some n, _ => toString n
  | none, .nan => "NaN"
  | none, .inf neg => if neg then "-Infinity" else "Infinity"
  | none, .finite neg m e =>
    let (d, ex) := shortestDecimal m e
    (if neg then "-" else "") ++ toString d ++ (if ex == 0 then "" else s!"e{ex}")

/-- How a literal is written in JavaScript: a boolean, a `number`, a `BigInt`, a string, or
    an array of those (`[str, start, stop]`). -/
inductive JsLitShape where
  | bool (b : Bool)
  | number (f : Float)
  | bigint (n : Int)
  | str (s : String)
  | array (es : List JsLitShape)

namespace JsLit

/-- How the literal is written in JavaScript. -/
def shape {t : JsTerminalTy} : JsLit t → JsLitShape
  | .bool b => .bool b
  | .bigint_nat n => .bigint n
  | .uint53 n _ => .number (Float.ofNat n)
  | .bigint_int n => .bigint n
  | .int53 n _ => .number (Float.ofInt n)
  | .bitvec_small v => .number (Float.ofNat v)
  | .bigint_bitvec_big v => .bigint v
  | .int53_bitvec_big v _ => .number (Float.ofNat v)
  | .uint8 v => .number (Float.ofNat v.toNat)
  | .uint16 v => .number (Float.ofNat v.toNat)
  | .uint32 v => .number (Float.ofNat v.toNat)
  | .int8 v => .number (Float.ofInt v.toInt)
  | .int16 v => .number (Float.ofInt v.toInt)
  | .int32 v => .number (Float.ofInt v.toInt)
  | .float f => .number f
  | .float32 f => .number f.toFloat
  | .string s => .str s
  | .substring s a b => .array [.str s, .number (Float.ofNat a), .number (Float.ofNat b)]
  | .stringSlice s a b => .array [.str s, .number (Float.ofNat a), .number (Float.ofNat b)]

end JsLit

/-- The literal, as JavaScript source. -/
partial def JsLitShape.pretty : JsLitShape → String
  | .bool b => toString b
  | .number f => numberSource f
  | .bigint n => toString n ++ "n"
  | .str s => s.quote
  | .array es => "[" ++ ", ".intercalate (es.map JsLitShape.pretty) ++ "]"

/-! ## Expressions and blocks -/

mutual
/-- Expressions of type `τ`, over the constants `C` and the mutable variables `M`. -/
inductive JsExpr : List JsTy → List JsTy → JsTy → Type where
  /-- A constant (a parameter, a `const`, …), by its de Bruijn index among the constants. -/
  | cvar {C M : List JsTy} {τ : JsTy} (x : JsMem C τ) : JsExpr C M τ
  /-- A mutable variable (a `let`), by its de Bruijn index among the mutable variables. -/
  | mvar {C M : List JsTy} {τ : JsTy} (x : JsMem M τ) : JsExpr C M τ
  /-- A constant the module shares (`$tag0`, `$k1`), of type `τ`. -/
  | global {C M : List JsTy} (name : String) (τ : JsTy) : JsExpr C M τ
  /-- A literal. -/
  | lit {C M : List JsTy} {t : JsTerminalTy} (l : JsLit t) : JsExpr C M (.terminal t)
  /-- A call of an operation of the runtime, `name(args)`. -/
  | imported {C M σs : List JsTy} {τ : JsTy} (op : JsOpImported σs τ) (args : JsArgs C M σs) :
      JsExpr C M τ
  /-- An operation written inline (`a & b`, `BigInt(a)`, …). -/
  | inlined {C M σs : List JsTy} {τ : JsTy} (op : JsOpInlined σs τ) (args : JsArgs C M σs) :
      JsExpr C M τ
  /-- A call of an extern that has no operation at this representation: it throws when it is
      evaluated (`lean_extern_unimplemented("name")`). -/
  | unimplemented {C M : List JsTy} (name : String) (τ : JsTy) : JsExpr C M τ
  /-- `f(a)`. -/
  | app {C M : List JsTy} {σ τ : JsTy} (f : JsExpr C M (.fn σ τ)) (a : JsExpr C M σ) :
      JsExpr C M τ
  /-- `(x) => { body }`: the parameter is the innermost constant of the body. -/
  | lam {C M : List JsTy} {σ τ : JsTy} (hint : String) (body : JsBlock (σ :: C) M [] (.ret τ)) :
      JsExpr C M (.fn σ τ)
  /-- `() => { body }`. -/
  | lazy_mk {C M : List JsTy} {τ : JsTy} (body : JsBlock C M [] (.ret τ)) : JsExpr C M (.lazy τ)
  /-- `e()`. -/
  | lazy_force {C M : List JsTy} {τ : JsTy} (e : JsExpr C M (.lazy τ)) : JsExpr C M τ
  /-- `{ _1: f₁, _2: f₂, … }`. -/
  | record_mk {C M ts : List JsTy} (fs : JsArgs C M ts) : JsExpr C M (.record ts)
  /-- `{ tag: i, _1: f₁, … }`, `i` the position of the constructor `ix`. -/
  | union_mk {C M : List JsTy} {cs : List (List JsTy)} {fs : List JsTy} (ix : JsMem cs fs)
      (args : JsArgs C M fs) : JsExpr C M (.union cs)
  /-- The number `shift + i`. -/
  | enum_mk {C M : List JsTy} (n : Nat) (shift : Int) (i : Fin n) : JsExpr C M (.enum n shift)
  /-- `[e₀, ...a, e₂]` (a generic array) or `Uint8Array.of(e₀, ...a)` (a typed array). -/
  | array_mk {C M : List JsTy} {A E : JsTy} (l : JsArrayLayout A E) (parts : JsParts C M A E) :
      JsExpr C M A
  /-- `[e₀, ...xs, e₂]`: a list. -/
  | list_mk {C M : List JsTy} {α : JsTy} (parts : JsParts C M (.list α) α) : JsExpr C M (.list α)
  /-- `c ? a : b`. -/
  | cond {C M : List JsTy} {τ : JsTy} (c : JsExpr C M (.terminal .bool)) (a b : JsExpr C M τ) :
      JsExpr C M τ

/-- The arguments of an operation or the fields of a record. -/
inductive JsArgs : List JsTy → List JsTy → List JsTy → Type where
  | nil {C M : List JsTy} : JsArgs C M []
  | cons {C M : List JsTy} {σ : JsTy} {σs : List JsTy} (a : JsExpr C M σ) (as : JsArgs C M σs) :
      JsArgs C M (σ :: σs)

/-- The parts of an array literal of type `A` (of elements `E`): elements, and spreads of
    arrays of the same type. -/
inductive JsParts : List JsTy → List JsTy → JsTy → JsTy → Type where
  | nil {C M : List JsTy} {A E : JsTy} : JsParts C M A E
  | elem {C M : List JsTy} {A E : JsTy} (e : JsExpr C M E) (rest : JsParts C M A E) :
      JsParts C M A E
  | spread {C M : List JsTy} {A E : JsTy} (a : JsExpr C M A) (rest : JsParts C M A E) :
      JsParts C M A E

/-- Blocks of statements, over the constants `C`, the mutable variables `M` and the join points
    `J`, ending as `k` says. -/
inductive JsBlock : List JsTy → List JsTy → List JsTy → JsEnd → Type where
  /-- `return e;` -/
  | ret {C M J : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : JsBlock C M J (.ret τ)
  /-- The end of an iteration of a loop (`continue;`, or nothing at the end of the body). -/
  | next {C M J : List JsTy} : JsBlock C M J .loop
  /-- `x = e; break L;`, `L` and `x` the label and the variable of the join point `j`. -/
  | jump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (j : JsMem J τ) (e : JsExpr C M τ) :
      JsBlock C M J k
  /-- `throw new Error(msg);` -/
  | throw {C M J : List JsTy} {k : JsEnd} (msg : String) : JsBlock C M J k
  /-- `const x = e;` and the rest, which reads `x` as its innermost constant. -/
  | const {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (e : JsExpr C M τ)
      (rest : JsBlock (τ :: C) M J k) : JsBlock C M J k
  /-- `let x = e;` and the rest, which reads and assigns `x` as its innermost mutable
      variable. -/
  | letMut {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (e : JsExpr C M τ)
      (rest : JsBlock C (τ :: M) J k) : JsBlock C M J k
  /-- `x = e;` and the rest. -/
  | assign {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (x : JsMem M τ) (e : JsExpr C M τ)
      (rest : JsBlock C M J k) : JsBlock C M J k
  /-- `const { _1: f₁, _3: f₃ } = e;` and the rest, which reads the fields `sel` keeps as
      constants (the last one innermost). -/
  | destructure {C M J ts us : List JsTy} {k : JsEnd} (e : JsExpr C M (.record ts))
      (sel : JsSel ts us) (rest : JsBlock (pushAll us C) M J k) : JsBlock C M J k
  /-- `if (c) { t } else { e }`. -/
  | ite {C M J : List JsTy} {k : JsEnd} (c : JsExpr C M (.terminal .bool)) (t e : JsBlock C M J k) :
      JsBlock C M J k
  /-- A case analysis on an enum: `if (e === shift) { … } else if (e === shift + 1) …`. -/
  | enumCases {C M J : List JsTy} {k : JsEnd} {n : Nat} {shift : Int} (e : JsExpr C M (.enum n shift))
      (arms : JsEnumArms C M J k n) : JsBlock C M J k
  /-- A case analysis on a union: `if (e.tag === 0) { const { _1: f } = e; … } else …`. -/
  | unionCases {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (e : JsExpr C M (.union cs))
      (arms : JsUnionArms C M J k cs) : JsBlock C M J k
  /-- A join point: `let x; L: { block }` and the rest, which reads the value the jumps of
      `block` to it (join point `0`) pass as its innermost constant `x`. -/
  | join {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (block : JsBlock C M (τ :: J) k)
      (rest : JsBlock (τ :: C) M J k) : JsBlock C M J k
  /-- `for (let i = 0; i < n; i++) { body }` (`0n` for a `BigInt` counter) and the rest; the
      body reads the counter as its innermost constant. -/
  | forRange {C M J : List JsTy} {N : JsTy} {k : JsEnd} (hint : String) (nt : JsNatTy N)
      (n : JsExpr C M N) (body : JsBlock (N :: C) M [] .loop) (rest : JsBlock C M J k) :
      JsBlock C M J k
  /-- The last iteration of a counting loop only, `if (0 < n) { const i = n - 1; body }`, and
      the rest. -/
  | lastIter {C M J : List JsTy} {N : JsTy} {k : JsEnd} (hint : String) (nt : JsNatTy N)
      (n : JsExpr C M N) (body : JsBlock (N :: C) M [] .loop) (rest : JsBlock C M J k) :
      JsBlock C M J k
  /-- `for (const x of xs) { body }` and the rest; the body reads the element as its innermost
      constant. -/
  | forOf {C M J : List JsTy} {A E : JsTy} {k : JsEnd} (hint : String) (l : JsArrayLayout A E)
      (xs : JsExpr C M A) (body : JsBlock (E :: C) M [] .loop) (rest : JsBlock C M J k) :
      JsBlock C M J k

/-- The arms of a case analysis on an enum of `n` constructors, in order. -/
inductive JsEnumArms : List JsTy → List JsTy → List JsTy → JsEnd → Nat → Type where
  | nil {C M J : List JsTy} {k : JsEnd} : JsEnumArms C M J k 0
  | cons {C M J : List JsTy} {k : JsEnd} {n : Nat} (b : JsBlock C M J k)
      (rest : JsEnumArms C M J k n) : JsEnumArms C M J k (n + 1)

/-- The arms of a case analysis on a union of constructors `cs`, in order: each binds the
    fields its pattern keeps. -/
inductive JsUnionArms : List JsTy → List JsTy → List JsTy → JsEnd → List (List JsTy) → Type where
  | nil {C M J : List JsTy} {k : JsEnd} : JsUnionArms C M J k []
  | cons {C M J : List JsTy} {k : JsEnd} {fs us : List JsTy} {cs : List (List JsTy)}
      (sel : JsSel fs us) (b : JsBlock (pushAll us C) M J k) (rest : JsUnionArms C M J k cs) :
      JsUnionArms C M J k (fs :: cs)
end

instance {C M : List JsTy} {τ : JsTy} : Inhabited (JsExpr C M τ) := ⟨.unimplemented "unreachable" τ⟩
instance {C M J : List JsTy} {k : JsEnd} : Inhabited (JsBlock C M J k) := ⟨.throw "unreachable"⟩
instance {C M : List JsTy} {A E : JsTy} : Inhabited (JsParts C M A E) := ⟨.nil⟩

/-- Arguments that throw (the default of a traversal). -/
def JsArgs.default {C M : List JsTy} : (σs : List JsTy) → JsArgs C M σs
  | [] => .nil
  | σ :: σs => .cons (.unimplemented "unreachable" σ) (JsArgs.default σs)

instance {C M σs : List JsTy} : Inhabited (JsArgs C M σs) := ⟨JsArgs.default σs⟩

/-- Arms that throw (the default of a traversal). -/
def JsEnumArms.default {C M J : List JsTy} {k : JsEnd} : (n : Nat) → JsEnumArms C M J k n
  | 0 => .nil
  | n + 1 => .cons (.throw "unreachable") (JsEnumArms.default n)

instance {C M J : List JsTy} {k : JsEnd} {n : Nat} : Inhabited (JsEnumArms C M J k n) :=
  ⟨JsEnumArms.default n⟩

/-- Arms that throw (the default of a traversal). -/
def JsUnionArms.default {C M J : List JsTy} {k : JsEnd} :
    (cs : List (List JsTy)) → JsUnionArms C M J k cs
  | [] => .nil
  | fs :: cs => .cons (JsSel.none fs) (.throw "unreachable") (JsUnionArms.default cs)

instance {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    Inhabited (JsUnionArms C M J k cs) := ⟨JsUnionArms.default cs⟩

/-- The integer literal `n` at a natural-number representation, if it fits. -/
def JsNatTy.lit? {C M : List JsTy} {N : JsTy} (nt : JsNatTy N) (n : Nat) : Option (JsExpr C M N) :=
  match nt with
  | .bigint_nat => some (.lit (.bigint_nat n))
  | .uint53 => if h : n ≤ maxSafe then some (.lit (.uint53 n h)) else none

/-! ## Functions and modules -/

/-- A top-level function: `export const name = (params) => { body };`. -/
structure JsFun where
  /-- The JavaScript name of the function. -/
  name : String
  /-- The Lean definition it was translated from. -/
  leanName : String
  /-- The parameters (zero or more), as the names they are printed with and their types; the
      body reads them as its outermost constants (the last one innermost). -/
  params : List (String × JsTy)
  /-- The type of the result. -/
  ret : JsTy
  /-- The body; every path ends in a `return` (or a `throw`). -/
  body : JsBlock (pushAll (params.map (·.2)) []) [] [] (.ret ret)

/-- A constant shared by the functions of a module: `const name = e;`. -/
structure JsConst where
  name : String
  ty : JsTy
  e : JsExpr [] [] ty

/-- A whole module: the operations of the runtime it imports, the constants it computes once
    (at the top of the module, `const name = e;`), and its exported functions. -/
structure JsModule where
  /-- The configuration it was generated with. -/
  config : JsConfig
  /-- The names of the functions of `runtime.js` it calls, each once, in order of first use. -/
  imports : List String
  /-- The constants shared by its functions, each defined before it is used. -/
  consts : List JsConst := []
  /-- The exported functions. -/
  funs : List JsFun

/-- The name of the runtime function a call of an extern without an operation calls. -/
def unimplementedFnName : String := "lean_extern_unimplemented"

/-! ## The dump (`-JsTerm-*.txt`) -/

/-- The name of field `i` (from `0`) of a record or a constructor: `_1`, `_2`, …. -/
def fieldKey (i : Nat) : String := s!"_{i + 1}"

mutual
/-- An expression, on one line (arrows break lines).  The variables are shown as their de
    Bruijn indices: `c0` the innermost constant, `m0` the innermost mutable variable (the
    binders show their hints); an operation by its name (an inlined one marked `inline:`). -/
partial def JsExpr.pretty {C M : List JsTy} {τ : JsTy} (ind : String) : JsExpr C M τ → String
  | .cvar i => s!"c{i.index}"
  | .mvar i => s!"m{i.index}"
  | .global x _ => x
  | .lit l => l.shape.pretty
  | .imported op args => op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .inlined op args => "inline:" ++ op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .unimplemented n _ => s!"{unimplementedFnName}({n.quote})"
  | .app f a => s!"{f.pretty ind}({a.pretty ind})"
  | .lam x body => s!"({x}) => \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}"
  | .lazy_mk body => "() => {\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}"
  | .lazy_force e => s!"{e.pretty ind}()"
  | .record_mk fs =>
    let es := fs.pretty ind
    if es.isEmpty then "{}" else
    "{ " ++ ", ".intercalate (es.zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}") ++ " }"
  | .union_mk ix args =>
    "{ " ++ ", ".intercalate (s!"tag: {ix.index}" ::
      ((args.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}")) ++ " }"
  | .enum_mk _ shift i => toString (shift + i.val)
  | .array_mk (.generic _) ps => "[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .array_mk (.typed k _) ps => k.ctorName ++ ".of(" ++ ", ".intercalate (ps.pretty ind) ++ ")"
  | .list_mk ps => "list[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .cond c a b => s!"({c.pretty ind} ? {a.pretty ind} : {b.pretty ind})"

/-- Arguments. -/
partial def JsArgs.pretty {C M σs : List JsTy} (ind : String) : JsArgs C M σs → List String
  | .nil => []
  | .cons a as => a.pretty ind :: as.pretty ind

/-- The parts of an array literal. -/
partial def JsParts.pretty {C M : List JsTy} {A E : JsTy} (ind : String) :
    JsParts C M A E → List String
  | .nil => []
  | .elem e rest => e.pretty ind :: rest.pretty ind
  | .spread a rest => ("..." ++ a.pretty ind) :: rest.pretty ind

/-- A block, each statement indented by `ind` and ending in a new line. -/
partial def JsBlock.pretty {C M J : List JsTy} {k : JsEnd} (ind : String) :
    JsBlock C M J k → String
  | .ret e => s!"{ind}return {e.pretty ind};\n"
  | .next => s!"{ind}next;\n"
  | .jump j e => s!"{ind}jump {j.index} {e.pretty ind};\n"
  | .throw msg => s!"{ind}throw new Error({msg.quote});\n"
  | .const x e rest => s!"{ind}const {x} = {e.pretty ind};\n" ++ rest.pretty ind
  | .letMut x e rest => s!"{ind}let {x} = {e.pretty ind};\n" ++ rest.pretty ind
  | .assign x e rest => s!"{ind}m{x.index} = {e.pretty ind};\n" ++ rest.pretty ind
  | .destructure e sel rest =>
    let b := sel.binds.map fun (i, x) => s!"{fieldKey i}: {x}"
    s!"{ind}const \{ {", ".intercalate b} } = {e.pretty ind};\n" ++ rest.pretty ind
  | .ite c t e =>
    s!"{ind}if ({c.pretty ind}) \{\n{t.pretty (ind ++ "  ")}{ind}} else \{\n" ++
      e.pretty (ind ++ "  ") ++ ind ++ "}\n"
  | .enumCases e arms =>
    s!"{ind}switch ({e.pretty ind}) \{\n" ++ arms.pretty ind 0 ++ ind ++ "}\n"
  | .unionCases e arms =>
    s!"{ind}switch ({e.pretty ind}.tag) \{\n" ++ arms.pretty ind 0 ++ ind ++ "}\n"
  | .join x block rest =>
    s!"{ind}join {x} \{\n" ++ block.pretty (ind ++ "  ") ++ ind ++ "}\n" ++ rest.pretty ind
  | .forRange i _ n body rest =>
    s!"{ind}for ({i} < {n.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind
  | .lastIter i _ n body rest =>
    s!"{ind}last ({i} < {n.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind
  | .forOf x _ xs body rest =>
    s!"{ind}for ({x} of {xs.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind

/-- The arms of a case analysis on an enum. -/
partial def JsEnumArms.pretty {C M J : List JsTy} {k : JsEnd} {n : Nat} (ind : String) (i : Nat) :
    JsEnumArms C M J k n → String
  | .nil => ""
  | .cons b rest => s!"{ind}case {i}:\n" ++ b.pretty (ind ++ "  ") ++ rest.pretty ind (i + 1)

/-- The arms of a case analysis on a union. -/
partial def JsUnionArms.pretty {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (ind : String) (i : Nat) : JsUnionArms C M J k cs → String
  | .nil => ""
  | .cons sel b rest =>
    let bs := sel.binds.map fun (j, x) => s!"{fieldKey j}: {x}"
    s!"{ind}case {i} \{ {", ".intercalate bs} }:\n" ++ b.pretty (ind ++ "  ") ++
      rest.pretty ind (i + 1)
end

/-- A function, for the dump (its parameters are its outermost constants). -/
def JsFun.pretty (f : JsFun) : String :=
  let ps := f.params.map fun (x, t) => s!"{x} : {t}"
  s!"// {f.leanName}\nexport const {f.name} = ({", ".intercalate ps}) : {f.ret} => \{\n" ++
    f.body.pretty "  " ++ "};\n"

/-- A module, for the dump. -/
def JsModule.pretty (m : JsModule) : String :=
  (if m.imports.isEmpty then "" else
    s!"import \{ {", ".intercalate m.imports} } from \"runtime.js\";\n\n") ++
  String.join (m.consts.map fun c => s!"const {c.name} : {c.ty} = {c.e.pretty ""};\n") ++
  (if m.consts.isEmpty then "" else "\n") ++
  "\n".intercalate (m.funs.map JsFun.pretty)

end MoreJs

end
