module

public import JsTerm.Ty.Config
public import JsTerm.Ops.Imported
public import JsTerm.Ops.Template
public import JsTerm.Syntax.NumberLit

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

`JsTerm.Print.Mini` maps the grammar onto the full JavaScript syntax tree of
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
last one innermost (`pushAll`).  An arrow function binds its parameters as constants on top of
the constants around it, keeps the mutable variables around it, and starts with no join point
(a jump never leaves a function); so does the body of a loop.  Every binder keeps a *hint*,
the name the printer starts from (`x`, `acc`, a parameter's Lean name); hints carry no
meaning.

## Operations

There are no generic operators: every operation is typed, and is named by the JavaScript
representation of its signature and the extern it implements (`bigint_nat__lean_nat_div :
[bigint_nat, bigint_nat] → bigint_nat`, `uint53__lean_nat_land : [uint53, uint53] →
uint53`).  An operation either calls a function of the runtime named as it
(`JsOpImported`, `JsTerm.Ops.Imported`) or is written inline as a JavaScript operator or
conversion (`JsOpInlinable`, `JsTerm.Ops.Inlinable`); both are indexed by their effects
(`Effectfulness`, `MayThrow`).  Every extern has an operation at every representation, so the
conversion never needs a placeholder for a missing one.

## Functions

Functions are **uncurried**: a function type is `JsTy.fn doms cod`, of any number of
parameters (none for a delayed computation, `Thunk`'s argument, `() => …`), and the lowering of
a Lean arrow `A → B → C` is the function of two parameters `(a, b) => …`.  A call passes all
the parameters at once (`JsExpr.app`).

## Blocks

A block ends in `return e` (`JsBlock.ret`, in a function: `k = .ret τ`), in the end of an
iteration (`JsBlock.next`, in the body of a loop: `k = .loop`), in a jump to an enclosing join
point, or in a `throw`.  A join point `join x block rest` is the labelled block `L: { block }`
whose statements may jump to it (join point `0` inside `block`), passing a value that `rest`
reads as its innermost constant `x`.

The dump of the grammar (`-JsTerm-*.txt`) is in `JsTerm.Syntax.Pretty`.
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

/-- How a literal is written in JavaScript: a boolean, a `number`, a `BigInt`, a string, or
    an array of those (`[str, start, stop]`). -/
inductive JsLitShape where
  | bool (b : Bool)
  | number (f : NumberForm)
  | bigint (n : Int)
  | str (s : String)
  | array (es : List JsLitShape)

namespace JsLit

/-- How the literal is written in JavaScript. -/
def shape {t : JsTerminalTy} : JsLit t → JsLitShape
  | .bool b => .bool b
  | .bigint_nat n => .bigint n
  | .uint53 n _ => .number (.int n)
  | .bigint_int n => .bigint n
  | .int53 n _ => .number (.int n)
  | .bitvec_small v => .number (.int v)
  | .bigint_bitvec_big v => .bigint v
  | .int53_bitvec_big v _ => .number (.int v)
  | .uint8 v => .number (.int v.toNat)
  | .uint16 v => .number (.int v.toNat)
  | .uint32 v => .number (.int v.toNat)
  | .int8 v => .number (.int v.toInt)
  | .int16 v => .number (.int v.toInt)
  | .int32 v => .number (.int v.toInt)
  | .float f => .number (.ofFloat f)
  | .float32 f => .number (.ofFloat32 f)
  | .string s => .str s
  | .substring s a b => .array [.str s, .number (.int a), .number (.int b)]
  | .stringSlice s a b => .array [.str s, .number (.int a), .number (.int b)]

end JsLit

/-- The literal, as JavaScript source. -/
partial def JsLitShape.pretty : JsLitShape → String
  | .bool b => toString b
  | .number f => f.source
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
  | imported {C M σs : List JsTy} {τ : JsTy} {e : Effectfulness} {t : MayThrow}
      (op : JsOpImported e t σs τ) (args : JsArgs C M σs) : JsExpr C M τ
  /-- An operation written inline (`a & b`, `BigInt(a)`, …). -/
  | inlined {C M σs : List JsTy} {τ : JsTy} {e : Effectfulness} {t : MayThrow}
      (op : JsOpInlinable e t σs τ) (args : JsArgs C M σs) : JsExpr C M τ
  /-- A value that is never read (a field annotated unused, the default of a traversal):
      `undefined`. -/
  | unreachable {C M : List JsTy} (τ : JsTy) : JsExpr C M τ
  /-- `f(a₁, …, aₙ)`: a call passing all the parameters. -/
  | app {C M σs : List JsTy} {τ : JsTy} (f : JsExpr C M (.fn σs τ)) (args : JsArgs C M σs) :
      JsExpr C M τ
  /-- `(x₁, …, xₙ) => { body }`: the parameters are the innermost constants of the body (the
      last one innermost); `hints` are their preferred names. -/
  | lam {C M σs : List JsTy} {τ : JsTy} (hints : List String)
      (body : JsBlock (pushAll σs C) M [] (.ret τ)) : JsExpr C M (.fn σs τ)
  /-- `{ _1: f₁, _2: f₂, … }` (two fields or more). -/
  | record_mk {C M : List JsTy} {f₁ f₂ : JsTy} {fs : List JsTy} (args : JsArgs C M (f₁ :: f₂ :: fs)) :
      JsExpr C M (.record f₁ f₂ fs)
  /-- `{ tag: i, _1: f₁, … }`, `i` the position of the constructor `ix`. -/
  | union_mk {C M : List JsTy} {c₀ c₁ : List JsTy} {cs : List (List JsTy)} {fs : List JsTy}
      (ix : JsMem (c₀ :: c₁ :: cs) fs) (args : JsArgs C M fs) : JsExpr C M (.union c₀ c₁ cs)
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
  | destructure {C M J : List JsTy} {f₁ f₂ : JsTy} {fs us : List JsTy} {k : JsEnd}
      (e : JsExpr C M (.record f₁ f₂ fs)) (sel : JsSel (f₁ :: f₂ :: fs) us)
      (rest : JsBlock (pushAll us C) M J k) : JsBlock C M J k
  /-- `if (c) { t } else { e }`. -/
  | ite {C M J : List JsTy} {k : JsEnd} (c : JsExpr C M (.terminal .bool)) (t e : JsBlock C M J k) :
      JsBlock C M J k
  /-- A case analysis on an enum: `if (e === shift) { … } else if (e === shift + 1) …`. -/
  | enumCases {C M J : List JsTy} {k : JsEnd} {n : Nat} {shift : Int} (e : JsExpr C M (.enum n shift))
      (arms : JsEnumArms C M J k n) : JsBlock C M J k
  /-- A case analysis on a union: `if (e.tag === 0) { const { _1: f } = e; … } else …`. -/
  | unionCases {C M J : List JsTy} {k : JsEnd} {c₀ c₁ : List JsTy} {cs : List (List JsTy)}
      (e : JsExpr C M (.union c₀ c₁ cs)) (arms : JsUnionArms C M J k (c₀ :: c₁ :: cs)) :
      JsBlock C M J k
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

instance {C M : List JsTy} {τ : JsTy} : Inhabited (JsExpr C M τ) := ⟨.unreachable τ⟩
instance {C M J : List JsTy} {k : JsEnd} : Inhabited (JsBlock C M J k) := ⟨.throw "unreachable"⟩
instance {C M : List JsTy} {A E : JsTy} : Inhabited (JsParts C M A E) := ⟨.nil⟩

/-- Arguments that throw (the default of a traversal). -/
def JsArgs.default {C M : List JsTy} : (σs : List JsTy) → JsArgs C M σs
  | [] => .nil
  | σ :: σs => .cons (.unreachable σ) (JsArgs.default σs)

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

/-- The name of field `i` (from `0`) of a record or a constructor: `_1`, `_2`, …. -/
def fieldKey (i : Nat) : String := s!"_{i + 1}"

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
  /-- Another exported function of the module, defined before this one, that is the same
      function (the same type and body), or the function of the runtime this one only passes
      its parameters to: this one is then written `export const name = other;`
      (`JsModule.shareFuns`). -/
  alias : Option String := none

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

end MoreJs

end
