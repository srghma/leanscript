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
`JsExpr S C M τ`, and a block a `JsBlock S C M J k`, so the printer never meets an ill-typed
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

## Objects: one set of forms, at nominal types

Every object — a record, a tagged union, a cons cell, a value of a declared datatype — has a
nominal type `obj id args` (`JsTy.obj`), and its layout is read from the declaration: the
grammar is parameterised by the signature `S : JsSig` of the function (its declared
datatypes), and `record_mk` / `destructure` are indexed by the fields `S.fieldsOf id args`,
`union_mk` / `unionCases` by the constructors `S.ctorsOf id args`.  So the constructor a
`union_mk` builds and the arms of a `unionCases` on it are indexed by the **same** list, for
anonymous unions, cons cells and declared datatypes alike.  One layer of a declared datatype
in and out are the casts `fold` / `unfold` (nothing at run time).

The dump of the grammar (`-JsTerm-*.txt`) is in `JsTerm.Syntax.Pretty`.
-/

namespace MoreJs

variable {S : JsSig}

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

/-! ## Conversions between representations -/

/-- The conversions between two representations of the same values, functions of the runtime
    (proposal S of `proposals/TypedDataProposals3.md`: two representations are two types, and a
    change of representation is one of these, never implicit).

    * The two layouts of a list: tagged cons cells (`JsTy.consList`, the layout of `List` under
      `ListRepr.taggedUnion`, the prelude's declaration `consList`) and the array layout
      (`JsTy.list`).  The externs of the catalogue that take or answer a list are written for
      the array layout; at the tagged layout their arguments and result are converted
      (`MoreJs.lowerExtern`).  The cells themselves are built and taken apart as any object
      (`union_mk`, `unionCases`).
    * The two representations of a union (`JsRepr`): every constructor an object (`cells`, what
      the externs of the catalogue take and answer), or the constructors without fields as
      numbers (`smallIntNullary`). -/
inductive JsListOp : List JsTy → JsTy → Type where
  /-- The cons cells of the elements of an array: `consList__of_array(a)`. -/
  | ofArray (α : JsTy) : JsListOp [.list α] (.consList α)
  /-- The array of the elements of cons cells: `consList__to_array(l)`. -/
  | toArray (α : JsTy) : JsListOp [.consList α] (.list α)
  /-- A union whose constructors are objects, with its constructors without fields as numbers:
      `obj__nullary_to_int(u)` (`{ tag: i }` is `i`). -/
  | nullaryToInt (ar : List Nat) (args : List JsTy) :
      JsListOp [.obj (.union ar .cells) args] (.obj (.union ar .smallIntNullary) args)
  /-- A union whose constructors without fields are numbers, with every constructor an object:
      `obj__nullary_to_cells(u)` (`i` is `{ tag: i }`). -/
  | nullaryToCells (ar : List Nat) (args : List JsTy) :
      JsListOp [.obj (.union ar .smallIntNullary) args] (.obj (.union ar .cells) args)
  deriving Repr

namespace JsListOp

/-- The function of `runtime.js` the operation calls. -/
def runtimeName {σs : List JsTy} {τ : JsTy} : JsListOp σs τ → String
  | .ofArray _ => "consList__of_array"
  | .toArray _ => "consList__to_array"
  | .nullaryToInt _ _ => "obj__nullary_to_int"
  | .nullaryToCells _ _ => "obj__nullary_to_cells"

/-- The functions of `runtime.js` the conversions call. -/
def runtimeNames : List String :=
  ["consList__of_array", "consList__to_array", "obj__nullary_to_int", "obj__nullary_to_cells"]

end JsListOp

/-! ## Expressions and blocks -/

mutual
/-- Expressions of type `τ`, over the constants `C` and the mutable variables `M`. -/
inductive JsExpr (S : JsSig) : List JsTy → List JsTy → JsTy → Type where
  /-- A constant (a parameter, a `const`, …), by its de Bruijn index among the constants. -/
  | cvar {C M : List JsTy} {τ : JsTy} (x : JsMem C τ) : JsExpr S C M τ
  /-- A mutable variable (a `let`), by its de Bruijn index among the mutable variables. -/
  | mvar {C M : List JsTy} {τ : JsTy} (x : JsMem M τ) : JsExpr S C M τ
  /-- A literal. -/
  | lit {C M : List JsTy} {t : JsTerminalTy} (l : JsLit t) : JsExpr S C M (.terminal t)
  /-- A call of an operation of the runtime, `name(args)`. -/
  | imported {C M σs : List JsTy} {τ : JsTy} {e : Effectfulness} {t : MayThrow}
      (op : JsOpImported e t σs τ) (args : JsArgs S C M σs) : JsExpr S C M τ
  /-- An operation written inline (`a & b`, `BigInt(a)`, …). -/
  | inlined {C M σs : List JsTy} {τ : JsTy} {e : Effectfulness} {t : MayThrow}
      (op : JsOpInlinable e t σs τ) (args : JsArgs S C M σs) : JsExpr S C M τ
  /-- A value that is never read (a field annotated unused, the default of a traversal):
      `undefined`. -/
  | unreachable {C M : List JsTy} (τ : JsTy) : JsExpr S C M τ
  /-- `f(a₁, …, aₙ)`: a call passing all the parameters. -/
  | app {C M σs : List JsTy} {τ : JsTy} (f : JsExpr S C M (.fn σs τ)) (args : JsArgs S C M σs) :
      JsExpr S C M τ
  /-- `(x₁, …, xₙ) => { body }`: the parameters are the innermost constants of the body (the
      last one innermost); `hints` are their preferred names. -/
  | lam {C M σs : List JsTy} {τ : JsTy} (hints : List String)
      (body : JsBlock S (pushAll σs C) M [] (.ret τ)) : JsExpr S C M (.fn σs τ)
  /-- `{ _1: f₁, _2: f₂, … }`: a record of the declaration `id` (its fields
      `S.fieldsOf id args`). -/
  | record_mk {C M : List JsTy} {id : JsObjId} {args : List JsTy}
      (fs : JsArgs S C M (S.fieldsOf id args)) : JsExpr S C M (.obj id args)
  /-- `{ tag: i, _1: f₁, … }`: constructor `ix` (at position `i`) of the declaration `id` (its
      constructors `S.ctorsOf id args`). -/
  | union_mk {C M : List JsTy} {id : JsObjId} {args fs : List JsTy}
      (ix : JsMem (S.ctorsOf id args) fs) (as : JsArgs S C M fs) : JsExpr S C M (.obj id args)
  /-- One layer into declaration `i`: a value of its body is a value of the datatype (nothing
      at run time: the value is laid out as its body). -/
  | fold {C M : List JsTy} (i : Nat) (e : JsExpr S C M (S.body i)) : JsExpr S C M (.obj (.decl i) [])
  /-- One layer out of declaration `i` (nothing at run time). -/
  | unfold {C M : List JsTy} (i : Nat) (e : JsExpr S C M (.obj (.decl i) [])) : JsExpr S C M (S.body i)
  /-- The number `shift + i`. -/
  | enum_mk {C M : List JsTy} (n : Nat) (shift : Int) (i : Fin n) : JsExpr S C M (.enum n shift)
  /-- The position `i` of the constructor `shift + i` of an enum, as a natural number of the
      representation `nt`: `e - shift` (just `e` when `shift = 0`), `BigInt(e - shift)` for a
      `BigInt`.  (Lean's `toCtorIdx`, which a derived `BEq`/`DecidableEq`/`Ord` compares.) -/
  | enumIndex {C M : List JsTy} {n : Nat} {shift : Int} {N : JsTy} (nt : JsNatTy N)
      (e : JsExpr S C M (.enum n shift)) : JsExpr S C M N
  /-- `a === b` on two constructors of the same enum. -/
  | enumEq {C M : List JsTy} {n : Nat} {shift : Int} (a b : JsExpr S C M (.enum n shift)) :
      JsExpr S C M (.terminal .bool)
  /-- `[e₀, ...a, e₂]` (a generic array) or `Uint8Array.of(e₀, ...a)` (a typed array). -/
  | array_mk {C M : List JsTy} {A E : JsTy} (l : JsArrayLayout A E) (parts : JsParts S C M A E) :
      JsExpr S C M A
  /-- `[e₀, ...xs, e₂]`: a list. -/
  | list_mk {C M : List JsTy} {α : JsTy} (parts : JsParts S C M (.list α) α) : JsExpr S C M (.list α)
  /-- `c ? a : b`. -/
  | cond {C M : List JsTy} {τ : JsTy} (c : JsExpr S C M (.terminal .bool)) (a b : JsExpr S C M τ) :
      JsExpr S C M τ
  /-- A conversion of a list from or to cons cells (`JsListOp`). -/
  | listOp {C M σs : List JsTy} {τ : JsTy} (op : JsListOp σs τ) (args : JsArgs S C M σs) :
      JsExpr S C M τ

/-- The arguments of an operation or the fields of a record. -/
inductive JsArgs (S : JsSig) : List JsTy → List JsTy → List JsTy → Type where
  | nil {C M : List JsTy} : JsArgs S C M []
  | cons {C M : List JsTy} {σ : JsTy} {σs : List JsTy} (a : JsExpr S C M σ) (as : JsArgs S C M σs) :
      JsArgs S C M (σ :: σs)

/-- The parts of an array literal of type `A` (of elements `E`): elements, and spreads of
    arrays of the same type. -/
inductive JsParts (S : JsSig) : List JsTy → List JsTy → JsTy → JsTy → Type where
  | nil {C M : List JsTy} {A E : JsTy} : JsParts S C M A E
  | elem {C M : List JsTy} {A E : JsTy} (e : JsExpr S C M E) (rest : JsParts S C M A E) :
      JsParts S C M A E
  | spread {C M : List JsTy} {A E : JsTy} (a : JsExpr S C M A) (rest : JsParts S C M A E) :
      JsParts S C M A E

/-- Blocks of statements, over the constants `C`, the mutable variables `M` and the join points
    `J`, ending as `k` says. -/
inductive JsBlock (S : JsSig) : List JsTy → List JsTy → List JsTy → JsEnd → Type where
  /-- `return e;` -/
  | ret {C M J : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) : JsBlock S C M J (.ret τ)
  /-- The end of an iteration of a loop (`continue;`, or nothing at the end of the body). -/
  | next {C M J : List JsTy} : JsBlock S C M J .loop
  /-- `x = e; break L;`, `L` and `x` the label and the variable of the join point `j`. -/
  | jump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (j : JsMem J τ) (e : JsExpr S C M τ) :
      JsBlock S C M J k
  /-- `throw new Error(msg);` -/
  | throw {C M J : List JsTy} {k : JsEnd} (msg : String) : JsBlock S C M J k
  /-- `const x = e;` and the rest, which reads `x` as its innermost constant. -/
  | const {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (e : JsExpr S C M τ)
      (rest : JsBlock S (τ :: C) M J k) : JsBlock S C M J k
  /-- `let x = e;` and the rest, which reads and assigns `x` as its innermost mutable
      variable. -/
  | letMut {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (e : JsExpr S C M τ)
      (rest : JsBlock S C (τ :: M) J k) : JsBlock S C M J k
  /-- `x = e;` and the rest. -/
  | assign {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (x : JsMem M τ) (e : JsExpr S C M τ)
      (rest : JsBlock S C M J k) : JsBlock S C M J k
  /-- `const { _1: f₁, _3: f₃ } = e;` and the rest, which reads the fields `sel` keeps as
      constants (the last one innermost). -/
  | destructure {C M J : List JsTy} {id : JsObjId} {args us : List JsTy} {k : JsEnd}
      (e : JsExpr S C M (.obj id args)) (sel : JsSel (S.fieldsOf id args) us)
      (rest : JsBlock S (pushAll us C) M J k) : JsBlock S C M J k
  /-- `if (c) { t } else { e }`. -/
  | ite {C M J : List JsTy} {k : JsEnd} (c : JsExpr S C M (.terminal .bool)) (t e : JsBlock S C M J k) :
      JsBlock S C M J k
  /-- A case analysis on an enum: `if (e === shift) { … } else if (e === shift + 1) …`. -/
  | enumCases {C M J : List JsTy} {k : JsEnd} {n : Nat} {shift : Int} (e : JsExpr S C M (.enum n shift))
      (arms : JsEnumArms S C M J k n) : JsBlock S C M J k
  /-- A case analysis on a union: `if (e.tag === 0) { const { _1: f } = e; … } else …`. -/
  | unionCases {C M J : List JsTy} {k : JsEnd} {id : JsObjId} {args : List JsTy}
      (e : JsExpr S C M (.obj id args)) (arms : JsUnionArms S C M J k (S.ctorsOf id args)) :
      JsBlock S C M J k
  /-- A join point: `let x; L: { block }` and the rest, which reads the value the jumps of
      `block` to it (join point `0`) pass as its innermost constant `x`. -/
  | join {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String) (block : JsBlock S C M (τ :: J) k)
      (rest : JsBlock S (τ :: C) M J k) : JsBlock S C M J k
  /-- `for (let i = 0; i < n; i++) { body }` (`0n` for a `BigInt` counter) and the rest; the
      body reads the counter as its innermost constant. -/
  | forRange {C M J : List JsTy} {N : JsTy} {k : JsEnd} (hint : String) (nt : JsNatTy N)
      (n : JsExpr S C M N) (body : JsBlock S (N :: C) M [] .loop) (rest : JsBlock S C M J k) :
      JsBlock S C M J k
  /-- `for (const x of xs) { body }` and the rest; the body reads the element as its innermost
      constant. -/
  | forOf {C M J : List JsTy} {A E : JsTy} {k : JsEnd} (hint : String) (l : JsArrayLayout A E)
      (xs : JsExpr S C M A) (body : JsBlock S (E :: C) M [] .loop) (rest : JsBlock S C M J k) :
      JsBlock S C M J k
  /-- A counting-down loop with an exit: `let j = n; L: while (true) { if (j === 0) { base }
      j--; step }` and the rest.  `base` and `step` read and assign the counter `j` as their
      innermost mutable variable (in `step`, already decremented); an iteration ends by going on
      (`next`, `continue;`) or by jumping to the join point `0`, which ends the loop and passes a
      value that `rest` reads as its innermost constant.  (A tail-recursive fold,
      `JsTerm.Lower.FromTerm`: the loop runs at most `n + 1` times.) -/
  | countdown {C M J : List JsTy} {N τ : JsTy} {k : JsEnd} (hint : String) (nt : JsNatTy N)
      (n : JsExpr S C M N) (base step : JsBlock S C (N :: M) [τ] .loop)
      (rest : JsBlock S (τ :: C) M J k) : JsBlock S C M J k
  /-- Mutually recursive local functions: `const f₀ = e₀; const f₁ = e₁; …` and the rest.  Every
      definition `eᵢ` (an arrow function, so that it reads the others only when it is called)
      and the rest read all the `fᵢ` as constants (the last one innermost). -/
  | funs {C M J : List JsTy} {τs : List JsTy} {k : JsEnd} (hints : List String)
      (defs : JsArgs S (pushAll τs C) M τs) (rest : JsBlock S (pushAll τs C) M J k) :
      JsBlock S C M J k

/-- The arms of a case analysis on an enum of `n` constructors, in order. -/
inductive JsEnumArms (S : JsSig) : List JsTy → List JsTy → List JsTy → JsEnd → Nat → Type where
  | nil {C M J : List JsTy} {k : JsEnd} : JsEnumArms S C M J k 0
  | cons {C M J : List JsTy} {k : JsEnd} {n : Nat} (b : JsBlock S C M J k)
      (rest : JsEnumArms S C M J k n) : JsEnumArms S C M J k (n + 1)

/-- The arms of a case analysis on a union of constructors `cs`, in order: each binds the
    fields its pattern keeps. -/
inductive JsUnionArms (S : JsSig) : List JsTy → List JsTy → List JsTy → JsEnd → List (List JsTy) → Type where
  | nil {C M J : List JsTy} {k : JsEnd} : JsUnionArms S C M J k []
  | cons {C M J : List JsTy} {k : JsEnd} {fs us : List JsTy} {cs : List (List JsTy)}
      (sel : JsSel fs us) (b : JsBlock S (pushAll us C) M J k) (rest : JsUnionArms S C M J k cs) :
      JsUnionArms S C M J k (fs :: cs)
end

instance {C M : List JsTy} {τ : JsTy} : Inhabited (JsExpr S C M τ) := ⟨.unreachable τ⟩
instance {C M J : List JsTy} {k : JsEnd} : Inhabited (JsBlock S C M J k) := ⟨.throw "unreachable"⟩
instance {C M : List JsTy} {A E : JsTy} : Inhabited (JsParts S C M A E) := ⟨.nil⟩

/-- Arguments that throw (the default of a traversal). -/
def JsArgs.default {C M : List JsTy} : (σs : List JsTy) → JsArgs S C M σs
  | [] => .nil
  | σ :: σs => .cons (.unreachable σ) (JsArgs.default σs)

instance {C M σs : List JsTy} : Inhabited (JsArgs S C M σs) := ⟨JsArgs.default σs⟩

/-- Arms that throw (the default of a traversal). -/
def JsEnumArms.default {C M J : List JsTy} {k : JsEnd} : (n : Nat) → JsEnumArms S C M J k n
  | 0 => .nil
  | n + 1 => .cons (.throw "unreachable") (JsEnumArms.default n)

instance {C M J : List JsTy} {k : JsEnd} {n : Nat} : Inhabited (JsEnumArms S C M J k n) :=
  ⟨JsEnumArms.default n⟩

/-- Arms that throw (the default of a traversal). -/
def JsUnionArms.default {C M J : List JsTy} {k : JsEnd} :
    (cs : List (List JsTy)) → JsUnionArms S C M J k cs
  | [] => .nil
  | fs :: cs => .cons (JsSel.none fs) (.throw "unreachable") (JsUnionArms.default cs)

instance {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    Inhabited (JsUnionArms S C M J k cs) := ⟨JsUnionArms.default cs⟩

/-- The integer literal `n` at a natural-number representation, if it fits. -/
def JsNatTy.lit? {C M : List JsTy} {N : JsTy} (nt : JsNatTy N) (n : Nat) : Option (JsExpr S C M N) :=
  match nt with
  | .bigint_nat => some (.lit (.bigint_nat n))
  | .uint53 => if h : n ≤ maxSafe then some (.lit (.uint53 n h)) else none

/-! ## Lists of cons cells: builders -/

/-- `[]` as cons cells: `{ tag: 0 }`, constructor `0` of the prelude's `consList`. -/
def JsExpr.consNil {C M : List JsTy} {α : JsTy} : JsExpr S C M (.consList α) :=
  .union_mk (id := .consList) (args := [α]) .zero .nil

/-- `h :: t` as cons cells: `{ tag: 1, _1: h, _2: t }`, constructor `1` of `consList`. -/
def JsExpr.consCons {C M : List JsTy} {α : JsTy} (h : JsExpr S C M α)
    (t : JsExpr S C M (.consList α)) : JsExpr S C M (.consList α) :=
  .union_mk (id := .consList) (args := [α]) (.succ .zero) (.cons h (.cons t .nil))

/-- The cons cells of an array list `xs`: `consList__of_array(xs)`. -/
def JsExpr.ofArrayList {C M : List JsTy} {α : JsTy} (xs : JsExpr S C M (.list α)) :
    JsExpr S C M (.consList α) :=
  .listOp (.ofArray α) (.cons xs .nil)

/-- The array list of the cons cells `l`: `consList__to_array(l)`. -/
def JsExpr.toArrayList {C M : List JsTy} {α : JsTy} (l : JsExpr S C M (.consList α)) :
    JsExpr S C M (.list α) :=
  .listOp (.toArray α) (.cons l .nil)

/-- The elements of the parts of a list literal, when there is no spread. -/
def JsParts.elems? {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → Option (List (JsExpr S C M E))
  | .nil => some []
  | .elem e ps => (e :: ·) <$> ps.elems?
  | .spread _ _ => none

/-- The parts of a list literal as cons cells: `{ tag: 1, _1: e₀, _2: … { tag: 0 } }`, the cells
    of the elements in order (the cells of the array literal, `consList__of_array([…])`, when
    it has a spread). -/
def JsParts.toConsList {C M : List JsTy} {α : JsTy} (ps : JsParts S C M (.list α) α) :
    JsExpr S C M (.consList α) :=
  match ps.elems? with
  | some es => es.foldr JsExpr.consCons JsExpr.consNil
  | none => JsExpr.ofArrayList (.list_mk ps)

/-- The name of field `i` (from `0`) of a record or a constructor: `_1`, `_2`, …. -/
def fieldKey (i : Nat) : String := s!"_{i + 1}"

/-! ## Functions and modules -/

/-- A top-level function: `export const name = (params) => { body };`. -/
structure JsFun where
  /-- The JavaScript name of the function. -/
  name : String
  /-- The Lean definition it was translated from. -/
  leanName : String
  /-- More lines of its documentation comment (which parameters a version owns, …). -/
  notes : List String := []
  /-- The declared datatypes its types name (`JsObjId.decl`). -/
  sig : JsSig := {}
  /-- The parameters (zero or more), as the names they are printed with and their types; the
      body reads them as its outermost constants (the last one innermost). -/
  params : List (String × JsTy)
  /-- The type of the result. -/
  ret : JsTy
  /-- The body; every path ends in a `return` (or a `throw`). -/
  body : JsBlock sig (pushAll (params.map (·.2)) []) [] [] (.ret ret)
  /-- Exported (`export const name = …;`), or private to the module (`const name = …;`: a
      worker shared by other functions, `JsTerm.Print.Share`). -/
  exported : Bool := true
  /-- Written as a call of another function of the module, the name of that function and the
      literal it passes first: `(params) => worker(lit, params)` (`JsTerm.Print.Share`); the
      body, which computes the same, is then not printed. -/
  delegate? : Option (String × JsLitShape) := none

/-- A top-level definition without parameters (its type is not a function, `termToJs`) is a
    constant: it is exported as the value its body computes, `export const name = value;`,
    not as a function of no arguments (the translated programs are pure and total, so the
    value is the same whenever it is computed).  The value is shared by every reader: like a
    borrowed argument, it must not be given to a version of a function that owns (and may
    update in place) its parameter. -/
def JsFun.isConst (f : JsFun) : Bool := f.params.isEmpty

/-- A whole module: the operations of the runtime it imports, and its exported functions. -/
structure JsModule where
  /-- The configuration it was generated with. -/
  config : JsConfig
  /-- The names of the functions of `runtime.js` it calls, each once, in order of first use. -/
  imports : List String
  /-- The operations it calls that it defines itself instead of importing them
      (`localHelper?`: the operations over the cons cells of `List`), each once. -/
  locals : List String := []
  /-- The exported functions. -/
  funs : List JsFun

end MoreJs

end
