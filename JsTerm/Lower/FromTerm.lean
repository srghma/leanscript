module

public import JsTerm.Lower.DataRec
public import JsTerm.Lower.Bounds

@[expose] public section

set_option autoImplicit false

/-!
# From `Term` to the JavaScript grammar

`termToJs cfg t` converts a closed normal-form statement (`LeanScript.Term`) into a
JavaScript function (`MoreJs.JsFun`), at the configuration `cfg`.  The conversion is
syntax-directed and type-directed: a `Term` of type `τ` becomes a `JsTerm` of type
`lowerTy cfg τ`, and each construct of `Term` has one JavaScript shape:

| `Term` | JavaScript |
| --- | --- |
| an unknown, a known value (de Bruijn) | a constant (`const`, a parameter, a field) or a mutable variable (the accumulator of a loop), by its de Bruijn index in its own context; join points stay de Bruijn indexed |
| `PExpr.lit` | a literal at the configured representation (`12n` or `12`); a literal that does not fit in a `number` is refused |
| `record_mk`, `union_mk ix`, `array_mk`, `list_mk` | `{ _1: f₁, … }`, `{ tag: ix, _1: f₁, … }`, `[e₀, …]` or `Uint8Array.of(…)`, `[e₀, …]` (`listRepr = stdListToJsArray`) or `{ tag: 1, _1: e₀, _2: … { tag: 0 } }` (`listRepr = taggedUnion`) |
| `enum_mk i` | the number `shift + i` |
| `Neu.cond` | `c ? a : b` |
| `Neu.extern` | the operation of the extern at these types (`MoreJs.lowerExtern`); `a[i]!` known in bounds by the enclosing tests is `a[i]`, and a comparison of sizes of arrays at `BigInt` is done on the numbers (`JsTerm.Lower.Bounds`) |
| `Val.lam` | `(x, y) => { … }`, of all the parameters of its type (uncurried) |
| `Val.thunk_mk`, `Val.lazy_mk` | `thunk__lean_mk_thunk(() => { … })`, `() => { … }` |
| `Term.ret`, `Term.jump j v` | `return e;`, a jump to the join point `j`; `throw new Error(msg);` when the value is a panic, `lean_panic_fn(d, msg)`, or an arm of a conditional is one (`JsBlock.retOrRaise`) |
| `Term.letV`, `Term.letE` | `const k = v;`, `const x = c;` |
| `Term.record_casesOn` | `const { _1: f₁, _3: f₃ } = r;` (unused fields skipped) |
| `Branch.ite`, `enum_casesOn`, `union_casesOn` | `if`/`else`, and case analyses |
| `Branch.join` | a join point (`JsBlock.join`); a join point whose body takes its parameter apart at once is written at each jump passing a constructor literal (of a constructor no other jump passes), on the fields of the literal (`JoinInl`), and disappears when every jump is one of those |
| `Comp.app f a`, `Comp.share n` | `f(a, b)` once every parameter is passed (a partial application is a closure), `n` |
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }` |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }`; a fold pushing every element (`Array.append z a`) on generic arrays is `[...z, ...a]` |
| `Comp.thunk_force`, `Comp.lazy_force` | `thunk__lean_thunk_get_own(t)`, `t()` |
| `PExpr.data_in`, `Neu.data_out` | the value itself (`JsExpr.fold`, `JsExpr.unfold`) |
| `Comp.data_rec` | `const go0 = (v) => { …; return branch₀; }; …; const x = go_j(e);` |

An extern with no operation at the types of a call is an error of the conversion
(`lowerExtern`).

A literal of an unbounded type at a `number` representation (a `Nat` as a `uint53`) that does
not fit in a safe integer is an error of the conversion: `leanscript` reports it and exits.

## Functions are uncurried

The layout of a Lean arrow `A → B → C` is the JavaScript function of two parameters
(`lowerTy`: `JsTy.fn [A, B] C`), wherever it appears: an exported function, a closure, a
parameter or a field of function type.  So:

* a lambda takes **all** the parameters of its type at once: the chain `fun x => (val k :=
  fun y => b; ret k)` is `(x, y) => b`; when the body of a lambda is not the next lambda of the
  chain (it computes the function first), it is applied to the remaining parameters
  (`(x, y) => { …; const f = …; return f(y); }`) — the parameters are passed later than the
  Lean code passes them, which changes nothing, since the conversion of a computation never has
  an effect but a throw;
* a call passes all the parameters at once.  A call of fewer (`let g := f a; let r := g b`)
  is not a call yet: the conversion remembers the function and the arguments passed so far
  (`Ref.pap`, all of them constants), and the call `f(a, b)` happens once the last parameter
  is passed; a partial application used as a value (passed, returned, stored) is the closure
  `(y) => f(a, y)`;
* the exported function takes all the parameters of its type, named by the Lean binders.

## Declared datatypes

A value of a declared datatype has the type `obj (decl i) []` (its stable number, `refIndex`):
`data_in` and `data_out` are the casts `JsExpr.fold` and `JsExpr.unfold` (nothing at run time).
The fold `data_rec` (and the course-of-values fold `data_brec` at depth `0`, the same fold) is
one local function per member of the block, mutually recursive (`JsBlock.funs`), each mapping
one layer and running the member's branch on it (`JsTerm.Lower.DataRec`).  A course-of-values
fold of depth `1` or more is not converted yet: a term using one is refused with an error.

The literals, the conversion monad and the builders of the shapes are in `JsTerm.Lower.Basic`.
-/

namespace MoreJs

variable {S : JsSig}

open LeanScript

/-- Does the statement start with a case analysis of its innermost unknown (`case x of …`), and
    read it nowhere else? -/
def _root_.LeanScript.Term.casesOnHead {ks : List Nat} {Δ : DSig ks} {d : Nat} {Φ : KCtx ks}
    {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} : Term Δ d Φ Γ τ js o → Bool
  | t@(.branch (.union_casesOn (.var x) _)) => x.index == 0 && (Own.Term.occ (.u 0) t).n == 1
  | _ => false

/-- The constructor of a union a pure expression is a literal of (`some` its position), if it is
    one. -/
def _root_.LeanScript.PExpr.ctorTag? {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}
    {σ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ σ o → Option Nat
  | .union_mk ix _ => some (ctorIxIndex ix)
  | _ => none

/-- The position of the constructor and the fields of a constructor literal of a union. -/
def _root_.LeanScript.PExpr.ctorArgs? {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}
    {σ : Ty ks} {o : Lvl} :
    PExpr Δ Φ Γ σ o → Option (Nat × (σs : List (Ty ks)) × (o' : Lvl) × Args Δ Φ Γ σs o')
  | .union_mk ix args => some (ctorIxIndex ix, ⟨_, _, args⟩)
  | _ => none

mutual
/-- What the jumps of a statement to the join point of index `j` pass: `some` the position of the
    constructor for a constructor literal of a union, `none` for any other value; one entry per
    jump. -/
partial def _root_.LeanScript.Term.jumpCtors {ks : List Nat} {Δ : DSig ks} {d : Nat}
    {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (j : Nat) :
    Term Δ d Φ Γ τ js o → List (Option Nat)
  | .ret _ => []
  | .letV _ _ t => t.jumpCtors j
  | .letE _ _ t => t.jumpCtors j
  | .record_casesOn _ _ t => t.jumpCtors j
  | .branch b => b.jumpCtors j
  | .jump x p => if x.index == j then [p.ctorTag?] else []

/-- `Term.jumpCtors` of a branch. -/
partial def _root_.LeanScript.Branch.jumpCtors {ks : List Nat} {Δ : DSig ks} {d : Nat}
    {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} (j : Nat) :
    Branch Δ d Φ Γ τ js ℓ → List (Option Nat)
  | .ite _ a b => a.jumpCtors j ++ b.jumpCtors j
  | .enum_casesOn (s := s) _ bs =>
    (List.range s.nOfConstructors).flatMap fun i =>
      if h : i < s.nOfConstructors then (bs ⟨i, h⟩).jumpCtors j else []
  | .union_casesOn _ brs => brs.jumpCtors j
  | .join _ _ _ body br => body.jumpCtors j ++ br.jumpCtors (j + 1)

/-- `Term.jumpCtors` of the arms of a case analysis. -/
partial def _root_.LeanScript.Branches.jumpCtors {ks : List Nat} {Δ : DSig ks} {d : Nat}
    {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (j : Nat) : Branches Δ d Φ Γ cs τ js o → List (Option Nat)
  | .two _ _ a b => a.jumpCtors j ++ b.jumpCtors j
  | .cons _ a rest => a.jumpCtors j ++ rest.jumpCtors j
end

/-- The join points seen under one more join point, which is the join point `0` of `J`. -/
def jmapPush (m : Nat → Nat) : Nat → Nat := fun i => if i == 0 then 0 else m (i - 1) + 1

/-- The join points seen under one more join point that has no join point in `J` (every jump to
    it is written at the jump, `JoinInl`). -/
def jmapSkip (m : Nat → Nat) : Nat → Nat := fun i => if i == 0 then 0 else m (i - 1)

/-- Does the body (of one parameter) start with a case analysis of its parameter? -/
def _root_.LeanScript.Body.casesOnParam {ks : List Nat} {Δ : DSig ks} {d : Nat} {Φ : KCtx ks}
    {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} : Body Δ d Φ Γ bs τ o → Bool
  | .closed t => t.casesOnHead
  | .opened t _ => t.casesOnHead

/-- The constant of the version of the local function `fi` a call giving up the arguments `off`
    calls (`Own.FnOwn.chosen`), when it is generated. -/
def fnVersionRef? (n : Names) (fi : Own.FnOwn) (off : List Bool) : Option Ref :=
  match (n.fns.lookup fi.id).bind (·[(fi.chosen off).1]?) with
  | some r@(.c _) => some r
  | _ => none

/-- The values of `Ref`s as arguments, those `copies` says copied (`[...a]`). -/
def refArgsCopy {C M : List JsTy} :
    (as : List (Ref × JsTy)) → List Bool → ConvM (JsArgs S C M (as.map (·.2)))
  | [], _ => pure .nil
  | (r, t) :: as, cs => do
    let e ← r.get t
    let e ← if cs.headD false then
        match e.copyArray? with
        | some e' => pure e'
        | none => throw "internal: a copy of an argument that is not an array"
      else pure e
    return .cons e (← refArgsCopy as cs.tail)

/-- The change of the environment of the body of a loop whose accumulator (the parameter `idx`)
    is an owning closure (`Own.AccMode.ownFn`, `Own.Env.withAccFn`). -/
def accEnv {ks : List Nat} (mode : Own.AccMode) (idx fid : Nat) (ρ : Ty ks) : Own.Env → Own.Env :=
  match mode with
  | .ownFn m r => Own.Env.withAccFn idx (Own.mustFn fid ρ m r) m r
  | _ => fun e => e

/-! ## Records kept in one variable per field

The variables of a tail loop (`cTailLoop`) that hold a record of leaves (numbers, booleans,
strings, enums) that the step only takes apart, and rebuilds as a literal for the next
iteration, are kept as one variable per field (`Ref.fields`): the loop then builds no record
per iteration and takes none apart (`let p$2 = b._1, p$3 = b._2; … p$2 = f(p$3); …`). -/

/-- The fields of a record type whose fields are all leaves (the records a loop may keep in
    one variable per field). -/
def scalarRecordFields? : JsTy → Option (List JsTy)
  | .obj (.record _) ts =>
    if ts.all (fun | .terminal _ => true | .enum _ _ => true | _ => false) then some ts else none
  | _ => none

/-- Is the expression a record literal? -/
def JsExpr.isRecordMk {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .record_mk _ => true
  | _ => false

/-- The pattern that binds every field. -/
def JsSel.all : (ts : List JsTy) → JsSel ts ts
  | [] => .nil
  | _ :: ts => .keep "f" (JsSel.all ts)

/-- The renaming of the constants `C` into `pushAll us C` (under the variables of a
    pattern). -/
def wkAllRen {C : List JsTy} : (us : List JsTy) → JsRenM Id C (pushAll us C)
  | [] => fun x => x
  | _ :: us => fun x => wkAllRen us (JsMem.succ x)

/-- The initial values of the variables of a loop keeping the parameters `flat` says in one
    variable per field (`cTailLoop`): the values `todo`, the fields of a record literal given
    for such a parameter, and for another value of such a parameter (a variable) its fields,
    taken apart first (`const { _1: f₁, … } = e;`, in front of the loop).  `k` builds the rest
    from the constants then in scope and the flattened values. -/
partial def flattenInit {C M J : List JsTy} {k : JsEnd}
    (done : List ((σ : JsTy) × JsExpr S C M σ))
    (todo : List (((σ : JsTy) × JsExpr S C M σ) × Bool))
    (kont : (C' : List JsTy) → List ((σ : JsTy) × JsExpr S C' M σ) → ConvM (JsBlock S C' M J k)) :
    ConvM (JsBlock S C M J k) :=
  match todo with
  | [] => kont C done.reverse
  | (a, false) :: rest => flattenInit (a :: done) rest kont
  | (⟨_, .record_mk fs⟩, true) :: rest => flattenInit (fs.toList.reverse ++ done) rest kont
  | (⟨.obj id args, e⟩, true) :: rest => do
    let ts := S.fieldsOf id args
    let ren : JsRenM Id C (pushAll ts C) := wkAllRen ts
    let wk : ((σ : JsTy) × JsExpr S C M σ) → ((σ : JsTy) × JsExpr S (pushAll ts C) M σ) :=
      fun ⟨σ, e⟩ => ⟨σ, Id.run (e.renameM ren JsRen.id)⟩
    let fieldEs ← (paramRefs C ts).mapM fun (r, t) => do
      let fe : JsExpr S (pushAll ts C) M t ← r.get t
      return (⟨t, fe⟩ : (σ : JsTy) × JsExpr S (pushAll ts C) M σ)
    return .destructure e (JsSel.all ts) (← flattenInit (fieldEs.reverse ++ done.map wk)
      (rest.map fun (a, b) => (wk a, b)) kont)
  | (_, true) :: _ => throw "internal: a record kept in variables that is not a record"

section
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

/-- The operands of a chain of `List.append`s (`lean_list_append`), whatever its nesting, in
    order: `(a ++ b) ++ (c ++ d)` has the operands `a, b, c, d`. -/
partial def listAppendLeaves {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → List ((τ' : Ty ks) × (o' : Lvl) × PExpr Δ Φ Γ τ' o')
  | _, _, p@(.neu (Neu.extern e (.cons a (.cons b .nil)) _)) =>
    if externName e == "lean_list_append" then listAppendLeaves a ++ listAppendLeaves b
    else [⟨_, _, p⟩]
  | _, _, p => [⟨_, _, p⟩]

/-- The enum constructor `shift + k` of an enum of `n` constructors, when `k < n`. -/
def enumCtorOf? {C M : List JsTy} (n : Nat) (shift : Int) (k : Nat) :
    Option (JsExpr S C M (.enum n shift)) :=
  if h : k < n then some (.enum_mk n shift ⟨k, h⟩) else none

/-- `x === k` for the position `x` of the constructor of `e` (`JsExpr.enumIndex`) and a literal
    `k`: `e === shift + k`, or `false` when the enum has no constructor `k`. -/
def enumIndexEqLit {C M : List JsTy} {n : Nat} {shift : Int} (e : JsExpr S C M (.enum n shift))
    (k : Nat) : JsExpr S C M (.terminal .bool) :=
  match enumCtorOf? n shift k with
  | some c => .enumEq e c
  | none => .lit (.bool false)

/-- `Nat.decEq` of the positions of two constructors of the same enum (`JsExpr.enumIndex`, what a
    derived `BEq` or `DecidableEq` compares) is `a === b` on the enum itself, and of the position
    of a constructor and a literal `k` is `a === shift + k`: no conversion to a number or a
    `BigInt` is written.  `none` for any other arguments. -/
def enumIndexEq? {C M σs : List JsTy} (as : JsArgs S C M σs) :
    Option (JsExpr S C M (.terminal .bool)) :=
  match as with
  | .cons a (.cons b .nil) =>
    match a, b with
    | .enumIndex (n := n) (shift := sh) _ x, .enumIndex (n := n') (shift := sh') _ y =>
      if h : n' = n ∧ sh' = sh then some (.enumEq x (h.1 ▸ h.2 ▸ y)) else none
    | .enumIndex _ x, b => b.natLit?.map (enumIndexEqLit x)
    | a, .enumIndex _ y => a.natLit?.map (enumIndexEqLit y)
    | _, _ => none
  | _ => none

/-! ## Values known from a case analysis

In the arm of `case x of | cᵢ(f₁, …) => …`, the constructor expression `cᵢ(f₁, …)` (on the very
fields the arm binds) is the value of `x` itself: Lean's `match` builds it again when a later
pattern names the whole value (`| x => … x …`), and the conversion writes `x` instead
(`CtorFact`, `knownCtorLvl?`), as purescript-backend-optimizer does.  Only for values that
hold no array (`JsTy.hasMutable`): nothing can then tell the value built again from the one
taken apart. -/

mutual
/-- The level of the constant holding the value of a pure expression, when it is a variable held
    in a constant, or a constructor expression of a value known from a case analysis. -/
partial def pexprLvl? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) : Option Nat :=
  match e with
  | .neu (.var y) => match n.u.getD y.index .none with
    | .c l => some l
    | _ => none
  | .kvar k => match n.k.getD k.index .none with
    | .c l => some l
    | _ => none
  | .union_mk .. => ctorLvl? e (lowerTy cfg τ) n
  | .data_in _ _ e' => ctorLvl? e' (lowerTy cfg τ) n
  | _ => none
/-- The level of the constant holding the value of a constructor expression `e` (of a union),
    whose value has the JavaScript type `ty` (the union, or the datatype it is the layer of). -/
partial def ctorLvl? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (ty : JsTy) (n : Names) (nullary : Bool := true) : Option Nat :=
  match e with
  | .union_mk ix args =>
    knownCtorLvl? (S := S) n.ctors n.bools (ctorIxIndex ix) (argsLvls args n) ty nullary
  | _ => none
/-- `pexprLvl?` of each argument (a boolean literal as itself). -/
partial def argsLvls {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) : List ArgKey :=
  match as with
  | .nil => []
  | .cons (.lit .bool b) as => .bool b :: argsLvls as n
  | .cons a as => ((pexprLvl? a n).map ArgKey.lvl).getD .none :: argsLvls as n
end

/-- The level of the constant holding the value of a constructor built again on the fields of a
    value known from a case analysis (`ctorLvl?`). -/
def valCtorLvl? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ σ o) (n : Names) : Option Nat :=
  match v with
  | Val.union_mk ix args =>
    knownCtorLvl? (S := S) n.ctors n.bools (ctorIxIndex ix) (argsLvls (S := S) cfg args n)
      (lowerTy cfg σ)
  | Val.data_in _ _ e => ctorLvl? (S := S) cfg e (lowerTy cfg σ) n
  | _ => none

/-- The unknown a case analysis takes apart, when it is one (or one layer out of one). -/
def _root_.LeanScript.Neu.scrutVar? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ Γ τ ℓ → Option Nat
  | .var x => some x.index
  | .data_out _ _ (.var x) => some x.index
  | _ => none

/-- The constant of level `l`, when the constructor expression is known to be its value. -/
def knownGet? {C M : List JsTy} (l? : Option Nat) (τ : JsTy) : ConvM (Option (JsExpr S C M τ)) :=
  match l? with
  | some l => do return some (← (Ref.c l).get τ)
  | none => pure none

/-- Is the statement `jump j i`, `j` the innermost join point and `i` the literal `Nat` `k`? -/
def isJumpNatLit {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (k : Nat) : Term Δ d Φ Γ τ js o → Bool
  | .jump j (.lit .nat v) => j.index == 0 && v == k
  | _ => false

/-- Is the case analysis on an enum `case e of | c₀ => jump j 0 | c₁ => jump j 1 | …`, every
    arm jumping to the innermost join point with the position of its constructor as a `Nat` (the
    shape of Lean's `toCtorIdx e`, which a derived `BEq`, `DecidableEq` or `Ord` compares)? -/
def isCtorIdxCases {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
    Branch Δ d Φ Γ τ js ℓ → Bool
  | .enum_casesOn (s := s) _ bs =>
    (List.finRange s.nOfConstructors).all fun i => isJumpNatLit i.val (bs i)
  | _ => false

mutual

/-- A neutral expression. -/
partial def cNeu {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (e : Neu Δ Φ Γ τ ℓ) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .var x => (n.u.getD x.index .none).get _
  | Neu.data_out b j e => do unfoldE (← cNeu e n C M) (lowerTy cfg ((Δ.block b).unfold j))
  | .cond c a b => do
    let ce ← castE (← cNeu c n C M) (.terminal .bool)
    let (nt, ne) := n.splitOn c
    return .cond ce (← cPExpr a nt C M) (← cPExpr b ne C M)
  | Neu.extern (σs := σs) (τ := τ) e args h => do
    let nm := externName e
    -- `l ++ l'` on cons cells: the whole chain of appends, built from its end (`cConsAppend`)
    if nm == "lean_list_append" && (lowerTy cfg τ).isConsList then
      return ← cConsAppend (listAppendLeaves (.neu (Neu.extern e args h))) n C M _
    let as ← cArgs args n C M
    if nm == "lean_nat_dec_eq__Nat_decEq" || nm == "lean_nat_dec_eq__Nat_beq" then
      if let some r := enumIndexEq? as then return ← castE r _
    let r ← match stringPosArg? σs with
      | some s => lowerExtern nm (.cons (.lit (.string s)) as)
      | none => lowerExtern nm as
    -- an access known to be in bounds is `a[i]`, and a comparison of sizes of arrays at the
    -- `BigInt` representation is done on the numbers (`JsTerm.Lower.Bounds`)
    if (nm == "lean_array_get" || nm == "lean_array_get_borrowed") && n.getInBounds args then
      if let some r' := r.uncheckedGet? then return r'
    if let some r' := r.narrowCmp? then return r'
    -- an update of an array nothing else refers to is done in place; `set!` and
    -- `swapIfInBounds` otherwise update a copy in place (their answer is then always new).
    -- An append onto an array literal is better written as one literal (below).
    if Own.updateInPlace n.cx nm args && !(nm == "lean_array_append" && as.firstIsArrayLit) then
      return r.inPlace
    else if Own.copyThenUpdate nm then
      match r.updateOnCopy? with
      | some r' => return r'
      | none => throw s!"internal: the update {nm} on a copy"
    -- `a ++ b` on arrays (and on lists at the array layout) is the literal `[...a, ...b]`, in
    -- which the literal operands, and the appends already written as literals, are spliced
    else if nm == "lean_array_append" || nm == "lean_list_append" then
      return (← appendLit? as).getD r
    else return r

/-- A chain of appends of lists of cons cells (`ListRepr.taggedUnion`), given by its operands
    (`listAppendLeaves`), at the type `L`: built from its end, so that the last operand is shared,
    not copied, a literal operand is its cells put in front of the rest
    (`{ tag: 1, _1: "a", _2: rest }`), and any other operand is copied in front of the rest
    (`consList__lean_list_append(xs, rest)`).  `(a ++ b) ++ c` is written `a ++ (b ++ c)`, which
    copies the cells of `a` once instead of twice (`List.append` is associative). -/
partial def cConsAppend {Φ : KCtx ks} {Γ : UCtx ks}
    (leaves : List ((τ' : Ty ks) × (o' : Lvl) × PExpr Δ Φ Γ τ' o')) (n : Names)
    (C M : List JsTy) (L : JsTy) : ConvM (JsExpr S C M L) := do
  match L with
  | .obj .consList [α] =>
    match leaves.reverse with
    | [] => throw "internal: an append of no list"
    | ⟨_, _, last⟩ :: before =>
      let mut acc : JsExpr S C M (.consList α) ← castE (← cPExpr last n C M) _
      for ⟨_, _, leaf⟩ in before do
        let whole : ConvM (JsExpr S C M (.consList α)) := do
          let e ← castE (← cPExpr leaf n C M) (.consList α)
          lowerExtern "lean_list_append" (.cons e (.cons acc .nil))
        acc ← match ← cConsLitFront? leaf n C M α acc with
          | some r => pure r
          | none => whole
      castE acc L
  | L => throw s!"internal: an append of lists of type {L}"

/-- A list literal put in front of `rest` as its cells (`{ tag: 1, _1: e₀, _2: rest }`); `none`
    when the expression is not a list literal of plain elements. -/
partial def cConsLitFront? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) (α : JsTy)
    (rest : JsExpr S C M (.consList α)) : ConvM (Option (JsExpr S C M (.consList α))) :=
  match e with
  | PExpr.list_mk (t := t) es => do
    let ps : JsParts S C M (.list (lowerTy cfg t)) (lowerTy cfg t) ← cElems es n C M
    match ps.elems? with
    | some xs => do
      let xs ← xs.mapM (castE · α)
      pure (some (xs.foldr JsExpr.consCons rest))
    | none => pure none
  | _ => pure none

/-- A pure expression. -/
partial def cPExpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .neu e => cNeu e n C M
  | .kvar k => (n.k.getD k.index .none).get _
  | .lit p v => do
    let ⟨_, l⟩ ← primLit cfg p v
    castE (.lit l) _
  | .enum_mk s i => pure (.enum_mk s.nOfConstructors s.shift i)
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do
    if let some v ← knownGet? (ctorLvl? (S := S) cfg e (lowerTy cfg τ) n (nullary := false)) _ then return v
    unionLit cs c ix (← cArgs args n C M)
  | PExpr.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | PExpr.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
  | PExpr.data_in b j e' => do
    if let some v ← knownGet? (ctorLvl? (S := S) cfg e' (lowerTy cfg τ) n (nullary := false)) _ then return v
    foldE (← cPExpr e' n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))

/-- A pure expression whose value is made owned by copying arrays (`Own.PExpr.copyable`): its
    owned parts as they are, each other array copied (`[...a]`). -/
partial def cPExprOwned {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  if Own.PExpr.owned n.cx e then cPExpr e n C M else
  match e with
  | .record_mk args => do recordLit (← cArgsOwned args n C M) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgsOwned args n C M)
  | PExpr.data_in b j e => do
    foldE (← cPExprOwned e n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))
  | e => do
    match (← cPExpr e n C M).copyArray? with
    | some c => pure c
    | none => throw "internal: a copy of a value that is not an array"

/-- `cPExprOwned` of arguments. -/
partial def cArgsOwned {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M : List JsTy) :
    ConvM (JsArgs S C M (σs.map (lowerTy cfg))) :=
  match as with
  | .nil => pure .nil
  | .cons a as => return .cons (← cPExprOwned a n C M) (← cArgsOwned as n C M)

/-- Arguments. -/
partial def cArgs {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M : List JsTy) :
    ConvM (JsArgs S C M (σs.map (lowerTy cfg))) :=
  match as with
  | .nil => pure .nil
  | .cons a as => return .cons (← cPExpr a n C M) (← cArgs as n C M)

/-- Arguments, each bound as a constant (unless it is one already), for `rest`, which receives
    where they live. -/
partial def cArgsBind {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M J : List JsTy) {e : JsEnd} (acc : List Ref)
    (rest : List Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J e)) :
    ConvM (JsBlock S C M J e) :=
  match as with
  | .nil => rest acc.reverse C
  | .cons a as => do
    bindConst (← cPExpr a n C M) fun r C' => cArgsBind as n C' M J (r :: acc) rest

/-- An argument bound as a constant (unless it is one already), for `rest`, which receives
    where it lives; a record literal, when `flat`, has its fields bound one by one
    (`Ref.fields`). -/
partial def cBindArg {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {o : Lvl}
    (a : PExpr Δ Φ Γ σ o) (n : Names) (C M J : List JsTy) {e : JsEnd} (flat : Bool)
    (rest : Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J e)) :
    ConvM (JsBlock S C M J e) :=
  match flat, a with
  | true, .record_mk as => cArgsBind as n C M J [] fun rs C' => rest (.fields rs false) C'
  | _, a => do bindConst (← cPExpr a n C M) rest

/-- Elements of an array or list literal of type `A`. -/
partial def cElems {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} {A : JsTy}
    (es : Elems Δ Φ Γ t o) (n : Names) (C M : List JsTy) :
    ConvM (JsParts S C M A (lowerTy cfg t)) :=
  match es with
  | .nil => pure .nil
  | .cons a as => return .elem (← cPExpr a n C M) (← cElems as n C M)

/-- A constructor of a union: `{ tag: i, _1: … }`. -/
partial def unionLit {C M : List JsTy} {bs : List Bool} {b : Bool} [UnionShape bs]
    (cs : Ctors ks bs) (c : Ctor ks b) (ix : CtorIx cs c) {σs : List JsTy} (as : JsArgs S C M σs) :
    ConvM (JsExpr S C M (lowerTy cfg (Ty.union (d := true) cs))) :=
  unionMk _ (ctorIxIndex ix) as

/-- An array literal: `[e₀, …]`, or `Uint8Array.of(…)` for a typed array. -/
partial def arrayLit {C M : List JsTy} (t : Ty ks)
    (ps : JsParts S C M (lowerTy cfg (Ty.array (d := true) t)) (lowerTy cfg t)) :
    ConvM (JsExpr S C M (lowerTy cfg (Ty.array (d := true) t))) := do
  let A' := lowerTy cfg (Ty.array (d := true) t)
  match JsArrayLayout.of? A' with
  | some ⟨E, l⟩ =>
    return .array_mk l (← castParts ps E)
  | none => throw "internal: the layout of an array"

/-- A value of known shape. -/
partial def cVal {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ τ o) (n : Names) (C M : List JsTy) (fl : List Bool := []) :
    ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match v with
  | Val.lam (σ := σ) (τ := ρ) b => do
    match lowerTy cfg (Ty.fn (d := true) σ ρ) with
    | .fn (d₀ :: ds) c =>
      -- all the parameters of the type at once
      let ps := paramRefs C (d₀ :: ds)
      -- a closure owns the parameters `fl` says (a version of a local function, `Own.lamPlan`)
      -- and borrows the others; nothing from outside is owned in it (it may run later, or many
      -- times)
      let body ← cApplyBody b { n with own := n.own.none } (pushAll (d₀ :: ds) C) M
        (ps.map (·.1)) (ps.zipIdx.map fun (_, i) => fl.getD i false) c
      castE (.lam ((d₀ :: ds).map fun _ => "x") body) _
    | _ => throw "internal: the type of a lambda"
  | Val.thunk_mk (τ := t) b => do
    let body ← cBody b n C M [] []
    let lz : JsExpr S C M (.fn [] (lowerTy cfg t.relax)) := .lam (σs := []) [] body
    lowerExtern "lean_mk_thunk" (.cons lz .nil)
  | Val.lazy_mk b => do castE (.lam (σs := []) [] (← cBody b n C M [] [])) _
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | Val.union_mk (cs := cs) (c := c) ix args => do
    let l? := knownCtorLvl? (S := S) n.ctors n.bools (ctorIxIndex ix)
      (argsLvls (S := S) cfg args n) (lowerTy cfg τ) (nullary := false)
    if let some v ← knownGet? l? _ then return v
    unionLit cs c ix (← cArgs args n C M)
  | Val.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | Val.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
  | Val.data_in b j e => do
    if let some v ← knownGet? (ctorLvl? (S := S) cfg e (lowerTy cfg τ) n (nullary := false)) _ then return v
    foldE (← cPExpr e n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))

/-- A statement that answers a function, applied to the parameters `ps` (bound in `C`, the
    first one outermost), answering a value of type `r`: the chain of lambdas `val k := fun x =>
    …; ret k` takes the parameters one after the other; any other statement computes the
    function (a block computing it into a join point), which is then called on the parameters
    left (`f(y)`).  `fl` says which of the parameters are owned (`Own.Term.walkApplied`). -/
partial def cApplyTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ [] o) (n : Names) (C M : List JsTy) (ps : List Ref) (fl : List Bool)
    (r : JsTy) :
    ConvM (JsBlock S C M [] (.ret r)) :=
  let whole : ConvM (JsBlock S C M [] (.ret r)) := do
    let blk ← cTerm t n C M []
    if h : lowerTy cfg τ = r then return h ▸ blk else
    match lowerTy cfg τ with
    | .fn ds c =>
      if ds.length != ps.length then throw "internal: the parameters of a function" else
      let call ← papCall (.c C.length) ((ps.zip ds).map fun (p, t) => (p, t)) c
        (C := lowerTy cfg τ :: C) (M := M)
      castRet ((JsBlock.join "f" ((blk.retToJump (k := .ret c)))
        ((JsBlock.ret call)))) r
    | _ => throw "internal: applying a value that is not a function"
  if ps.isEmpty then whole else
  match t with
  | .letV _ v (.ret (.kvar k)) =>
    if k.index != 0 then whole else
    match v with
    | Val.lam b => cApplyBody b n C M ps fl r
    | _ => whole
  | _ => whole

/-- The body of a lambda applied to the parameters `ps` (its own parameter first), owned or not
    (`fl`). -/
partial def cApplyBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (ps : List Ref) (fl : List Bool)
    (r : JsTy) : ConvM (JsBlock S C M [] (.ret r)) :=
  match ps with
  | [] => throw "internal: a lambda without a parameter"
  | p :: ps' =>
    let f := fl.headD false
    match b with
    | .closed t =>
      cApplyTerm t { n with u := [p], own := n.own.closedBody [f] } C M ps' fl.tail r
    | .opened t _ =>
      cApplyTerm t { n with u := p :: n.u, own := n.own.pushU [f] } C M ps' fl.tail r

/-- The body of a closure, a delay or a loop, whose parameters live at `xs` (innermost first;
    `C` already holds them) and are owned or not (`fl`; nothing from outside is owned in the
    body): a block ending in `return`. -/
partial def cBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (xs : List Ref) (fl : List Bool)
    (mod : Own.Env → Own.Env := id) : ConvM (JsBlock S C M [] (.ret (lowerTy cfg τ))) :=
  match b with
  | .closed t => cTerm t { n with u := xs, own := mod (n.own.body true fl) } C M []
  | .opened t _ => cTerm t { n with u := xs ++ n.u, own := mod (n.own.body false fl) } C M []

/-- The initial value of a loop whose accumulator is an owning closure owning `m`
    (`Own.AccMode.ownFn`): a local function is given by its version owning the most of `m`. -/
partial def cPExprFn {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (m : List Bool) (n : Names) (C M : List JsTy) :
    ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .kvar x => match n.own.kf.getD x.index none with
    | some fi => match fnVersionRef? n fi m with
      | some r => r.get _
      | none => cPExpr e n C M
    | none => cPExpr e n C M
  | e => cPExpr e n C M

/-- A computation, followed by the block `k` builds from where its result lives. -/
partial def cComp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (c : Comp Δ d Φ Γ τ ℓ) (n : Names) (C M J : List JsTy) {e : JsEnd}
    (k : Ref → (C' M' : List JsTy) → ConvM (JsBlock S C' M' J e)) : ConvM (JsBlock S C M J e) :=
  match c with
  | Comp.app (σ := σ) (τ := τ) f a _ => do
    -- the function, as a constant (or the partial application it is)
    let withF (rest : Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J e)) :
        ConvM (JsBlock S C M J e) := do
      match pexprRef? f n with
      | some r@(.c _) | some r@(.pap ..) | some r@.none => rest r C
      | _ => return (← bindConst (← cPExpr f n C M) rest)
    withF fun fr C₁ => do
      -- a record literal passed to the accumulator of a loop keeping it in one variable per
      -- field: its fields bound one by one (`Ref.fields`)
      let toFlatAcc : Bool := match fr with
        | .pap (.c l) _ | .c l => n.flatAcc == some l
        | _ => false
      return (← cBindArg a n C₁ M J toFlatAcc fun ar C₂ => do
        let (base, args) := match fr with
          | .pap b as => (b, as)
          | r => (r, [])
        let args := args ++ [(ar, lowerTy cfg σ)]
        if τ.isFn then
          -- a partial application: the call waits for the other parameters
          k (.pap base args) C₂ M
        else
          -- a local function with versions: the version owning the most arguments the caller
          -- gives up (`Own.FnOwn.choose`, as `Own.Comp.cost` decides it)
          let (base, copies) := match Own.appOffer n.cx f a with
            | some (fi, off) =>
              ((fnVersionRef? n fi off).getD base, fi.copyMask off)
            | none => (base, [])
          -- an owning closure copies the arguments it owns that the caller keeps
          let call : JsExpr S C₂ M (lowerTy cfg τ) :=
            .app (← base.get (.fn (args.map (·.2)) (lowerTy cfg τ))) (← refArgsCopy args copies)
          return (JsBlock.const "x" call (← k (.c C₂.length) _ M)))
  | .share e => do
    let ee ← cNeu e n C M
    return (JsBlock.const "x" ee (← k (.c C.length) _ M))
  | Comp.nat_rec (τ := ρ) cnt z s _ => do
    let N := lowerTy cfg (Ty.nat : Ty ks)
    let some nt := JsNatTy.of? N | throw "internal: the representation of a Nat"
    let α := lowerTy cfg ρ
    let cntE ← cPExpr cnt n C M
    -- the body owns its accumulator when every iteration hands the next an owned value (the
    -- initial value copied first if it is not owned, when that saves copies in the body)
    let mode := Own.natRecAcc n.cx z s n.allowFn
    let zE ← match mode with
      | .copy => cPExprOwned z n C M
      | .ownFn m _ => cPExprFn z m n C M
      | _ => cPExpr z n C M
    let accLvl := M.length
    let M' := α :: M
    let acc : JsMem M' α := .zero
    -- the body: the counter, then the accumulator it reads
    let body ← cBody s n (α :: N :: C) M' [.c (C.length + 1), .c C.length] [mode.owns, false]
      (accEnv mode 0 (Own.accFnId d n.cx.env) ρ)
    let rest ← k (.m accLvl) C M'
    return JsBlock.letMut "acc" zE (JsBlock.forRange "i" nt cntE.wkM (loopBody acc body) rest)
  | Comp.array_foldl (t := t) (ρ := ρ) arr z s _ => do
    let A := lowerTy cfg (Ty.array (d := true) t)
    let α := lowerTy cfg ρ
    let arrE ← cPExpr arr n C M
    let mode := Own.foldlAcc n.cx z s n.allowFn
    let zE ← match mode with
      | .copy => cPExprOwned z n C M
      | .ownFn m _ => cPExprFn z m n C M
      | _ => cPExpr z n C M
    let some ⟨E, l⟩ := JsArrayLayout.of? A | throw "internal: the layout of an array"
    let M' := α :: M
    let body ← cBody s n (α :: lowerTy cfg t :: C) M' [.c C.length, .c (C.length + 1)]
      [false, mode.owns] (accEnv mode 1 (Own.accFnId d n.cx.env) ρ)
    let body ← castBodyElem body E
    let rest ← k (.m M.length) C M'
    return (JsBlock.letMut "acc" zE
      ((JsBlock.forOf "e" l arrE.wkM ((loopBody .zero body)) rest)))
  | Comp.data_rec (b := b) ρ _ branches j e _ =>
    let B := Δ.block b
    -- the answers at the holes of a layer are owned when every branch answers an owned value
    let f := if Own.dataRecOwns n.cx b ρ branches then Own.Env.withHoles (Own.recHoles b ρ)
      else fun e => e
    -- a branch that starts with a case analysis of its layer, read nowhere else, is fused with the
    -- case analysis that maps the layer (`fusedArms`)
    dataFold B ρ (fun i => Ty.pair (.data (B.ref i)) (ρ i))
      (fun i x C' => cBody (branches i) n C' M [x] [false] f) j e
      (fun i => (branches i).casesOnParam)
  | Comp.data_brec (b := b) ρ 0 _ branches j e _ =>
    -- depth `0`: the windows are the pairs of `data_rec`
    let B := Δ.block b
    dataFold B ρ (fun i => B.win ρ 0 i) (fun i x C' => cBody (branches i) n C' M [x] [false]) j e
  | .data_brec _ _ (_ + 1) _ _ _ _ _ => notYet
  | Comp.thunk_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e : JsExpr S C M (lowerTy cfg t.relax) ← lowerExtern "lean_thunk_get_own" (.cons pe .nil)
    return (JsBlock.const "x" e (← k (.c C.length) _ M))
  | Comp.lazy_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e ← forceLazy pe (lowerTy cfg t.relax)
    return (JsBlock.const "x" e (← k (.c C.length) _ M))
where
  /-- The fold over the block `B` answering `ρ`, whose branch `i` (`branch i`) runs on the layer
      of member `i` with every hole `i'` filled by `σt i'`, applied to `e`, a value of member
      `j` (`recFuns`): `const go0 = (v) => …; …; const x = go_j(e);` and the rest. -/
  dataFold {oe : Lvl} (B : Δ.Block) (ρ : Fin (B.k + 1) → Ty ks) (σt : Fin (B.k + 1) → Ty ks)
      (branch : (i : Fin (B.k + 1)) → Ref → (C' : List JsTy) →
        ConvM (JsBlock S C' M [] (.ret (lowerTy cfg (ρ i)))))
      (j : Fin (B.k + 1)) (sub : PExpr Δ Φ Γ (.data (B.ref j)) oe)
      (fused : Fin (B.k + 1) → Bool := fun _ => false) : ConvM (JsBlock S C M J e) := do
    let members : Fin (B.k + 1) → Σ g, Decl B.ks' (B.k + 1) g :=
      fun i => (B.bs.decl? i.val).getD ⟨0, default⟩
    let T : Fin (B.k + 1) → JsTy := fun i => lowerTy cfg (Ty.data (d := true) (B.ref i))
    let R : Fin (B.k + 1) → JsTy := fun i => lowerTy cfg (ρ i)
    recFuns cfg B.old (fun i => .data (B.ref i)) σt members T R branch (fun C' => do
      let ee ← castE (← cPExpr sub n C' M) (T j)
      let call : JsExpr S C' M (R j) :=
        .app (← (Ref.c (C.length + j.val)).get (.fn [T j] (R j))) (.cons ee .nil)
      return .const "x" call (← k (.c C'.length) (R j :: C') M)) fused

/-- A statement: a block every path of which ends in a `return` (or a jump). -/
partial def cTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  match t with
  | .ret p => do
    let (cx, _) := n.own.stmt (fun v => Own.PExpr.occ v p) (fun _ => false)
    match n.own.retFn with
    | some (m, _) => return (JsBlock.retOrRaise (← cPExprFn p m { n with cx } C M))
    | none => return (JsBlock.retOrRaise (← cPExpr p { n with cx } C M))
  | Term.letV uk v t => cLetV uk v t n C M J
  | .letE uu c t =>
    let normal (_ : Unit) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
      let (cx, env') := n.own.stmt (fun w => Own.Comp.occ w c)
        (fun w => (Own.Term.occ (w.upU 1) t).n > 0)
      let allow := Own.fnAllow cx env' c t
      let fr := (Own.Comp.fnResult cx c allow).or (Own.papInfo cx c (Own.Term.occ (.u 0) t)).1
      let own := env'.pushUF (Own.Comp.owned cx c allow) fr
      cComp c { n with cx, allowFn := allow } C M J fun x C' M' =>
        cTerm t { n with u := x :: n.u, own } C' M' J
    -- a fold answering a function, applied at once: a loop when its step calls the answer at
    -- the predecessor only in tail position (`cTailLoop`); the initial function is called in
    -- the base case
    match c, t with
    | Comp.nat_rec (τ := ρ) cnt z s _, t =>
      let viaLoop : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) := do
        let .fn ds _ := lowerTy cfg ρ | throw "tail loop: the answer is not a function"
        let (cx, _) := n.own.stmt (fun w => Own.Comp.occ w c)
          (fun w => (Own.Term.occ (w.upU 1) t).n > 0)
        -- the variables of the loop are owned as the parameters of an owning closure would be
        let mode := Own.natRecAcc cx z s n.allowFn
        let base (C' M' : List JsTy) (ps : List Ref) (r : JsTy) :
            ConvM (JsBlock S C' M' [] (.ret r)) := do
          let zE ← match mode with
            | .ownFn m _ => cPExprFn z m { n with cx } C' M'
            | _ => cPExpr z { n with cx } C' M'
          match lowerTy cfg ρ with
          | .fn ds' c' =>
            let zF ← castE zE (.fn ds' c')
            let call : JsExpr S C' M' c' := .app zF (← castArgs (← refArgs (ps.zip ds')) ds')
            castRet (.ret call) r
          | _ => throw "tail loop: the answer is not a function"
        if ds.isEmpty then throw "tail loop: no parameter"
        cTailLoop cnt s base mode uu t { n with cx } C M J
      tryCatch viaLoop fun _ => normal ()
    | _, _ => normal ()
  | Term.record_casesOn (t := t₀) (fs := fs) us e t => do
    let m := (t₀ :: fs.toList).length
    let (cx, env') := n.own.stmt (fun w => Own.Neu.occ w e)
      (fun w => (Own.Term.occ (w.upU m) t).n > 0)
    let (bs, hs) := Own.recordFields cx t₀ fs e
    let own := env'.pushUH bs hs
    -- a record kept in one variable per field (`Ref.fields`): its fields are those variables
    let kept? : Option (List Ref) := match e with
      | .var x => match n.u.getD x.index .none with
        | .fields rs _ => if rs.length == m then some rs else none
        | _ => none
      | _ => none
    match kept? with
    | some rs =>
      -- an answer of a fold not computed yet (`Ref.call`, `JsTerm.Lower.DataRec`) is computed
      -- here, once, if it is read
      bindCalls rs (usedFields us) fun rs' C' => cTerm t { n with u := rs' ++ n.u, own } C' M J
    | none =>
    let ee ← cNeu e { n with cx } C M
    return (← destructureAny ee (usedFields us) fun refs C' =>
      cTerm t { n with u := refs ++ n.u, own } C' M J)
  | .branch b => cBranch b n C M J
  | Term.jump (σ := σ) j p => do
    let (cx, _) := n.own.stmt (fun v => Own.PExpr.occ v p) (fun _ => false)
    -- a join point written at its jumps (`JoinInl`): the arm of the constructor passed, here, on
    -- the fields of the literal
    let inl? : Option JoinInl := (n.inl.getD j.index none).bind fun inl =>
      match p.ctorTag? with
      | some t => if inl.tags.contains t then some inl else none
      | none => none
    match inl?, p.ctorArgs? with
    | some inl, some ⟨tag, _, _, args⟩ =>
      if h : inl.sig = S then
        cArgsBind args { n with cx } C M J [] fun rs C' =>
          h ▸ inl.conv tag rs (fun i => n.jmap (i + j.index + 1)) n.bounds n.ctors C' M J
            (lowerTy cfg τ)
      else throw "internal: the signature of a join point"
    | _, _ =>
    let pe ← cPExpr p { n with cx } C M
    match JsMem.ofIndex? J (n.jmap j.index) (lowerTy cfg σ) with
    | some jm => return (JsBlock.jumpOrRaise jm pe)
    | none => throw "internal: a join point"

/-- `val k := v; t`.  A local function gets one constant per version generated
    (`Own.lamPlan`); any other value one constant. -/
partial def cLetV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
    (uk : Usage1ω) (v : Val Δ d Φ Γ σ o) (t : Term Δ d (⟨σ, uk, o, true⟩ :: Φ) Γ τ js o')
    (n : Names) (C M J : List JsTy) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  let ce := n.own.stmt (fun w => Own.Val.occ w v) (fun w => (Own.Term.occ (w.upK 1) t).n > 0)
  let cx := ce.1
  let env' := ce.2
  -- `val k := fun x => …; let f := nat_rec n k s; f a …`, `k` used only there: the tail loop of
  -- the fold (`cTailLoop`), with the body of `k` in its base case
  let viaLoop? : Option (ConvM (JsBlock S C M J (.ret (lowerTy cfg τ)))) :=
    match v, t with
    | Val.lam b, tt@(Term.letE uu c@(Comp.nat_rec cnt (.kvar k0) s _) t') =>
      if k0.index == 0 && uk == .one then
        -- the variables of the loop are owned as the parameters of an owning closure would be
        let plan := Own.lamPlan uk cx env' b tt
        let (cx', _) := (env'.pushKF true (some plan.info)).stmt (fun w => Own.Comp.occ w c)
          (fun w => (Own.Term.occ (w.upU 1) t').n > 0)
        let mode := Own.natRecAcc cx' (.kvar k0) s n.allowFn
        let fl := match mode with
          | .ownFn m _ => m
          | _ => []
        some (cTailLoop cnt s
          (fun C' M' ps r => cApplyBody b { n with cx, own := n.own.none } C' M' ps
            (ps.zipIdx.map fun (_, i) => fl.getD i false) r)
          mode uu t' { n with k := .none :: n.k, own := env'.pushK false, cx := cx' } C M J)
      else none
    | _, _ => none
  let general (_ : Unit) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  match v, t with
  | Val.lam (σ := σ₁) (τ := τ₁) b, t =>
    let plan := Own.lamPlan uk cx env' b t
    let own := env'.pushKF true (some plan.info)
    let F := lowerTy cfg (Ty.fn (d := true) σ₁ τ₁)
    let rec versions (vs : List (Own.FnVer × Bool)) (C' : List JsTy) (refs : List Ref) :
        ConvM (JsBlock S C' M J (.ret (lowerTy cfg τ))) :=
      match vs with
      | [] =>
        let refs := refs.reverse
        let n' : Names := { n with k := refs.headD Ref.none :: n.k, own := own }
        cTerm t { n' with fns := (plan.info.id, refs) :: n.fns } C' M J
      | (ver, e) :: vs => do
        if !e then versions vs C' (.none :: refs) else
        let ve ← cVal (Val.lam b) { n with cx } C' M ver.mask
        return JsBlock.const (if ver.mask.any (·) then "k_mut" else "k") ve
          (← versions vs (F :: C') (.c C'.length :: refs))
    versions (plan.info.vers.zip plan.emit) C []
  | v, t => do
    -- a constructor built again on the fields of a case analysis: a new name of the value
    -- taken apart, no constant
    if let some l := valCtorLvl? (S := S) cfg v n then
      return (← cTerm t { n with k := .c l :: n.k, own := env'.pushK (Own.Val.owned cx v) }
        C M J)
    let ve ← cVal v { n with cx } C M
    return (JsBlock.const "k" ve
      (← cTerm t { n with k := .c C.length :: n.k, own := env'.pushK (Own.Val.owned cx v) }
        (lowerTy cfg σ :: C) M J))
  match viaLoop? with
  | some m => tryCatch m fun _ => general ()
  | none => general ()

/-- The applications `let x₁ := x₀ a₁; let x₂ := x₁ a₂; …` of the answer `x₀` of a fold (the
    unknown `0` of `t`, `bound - 1` applications already read, whose arguments are `args`),
    `left` more of them, each result used only by the next application: `k` receives the
    statement after the last one, the number of unknowns the applications bind, and the
    arguments (converted where the fold is, `C` and `M`: the applications are not written). -/
partial def cTailChain {d : Nat} {Φ : KCtx ks} {Γ' : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {X : Type} (t : Term Δ d Φ Γ' τ js o) (left bound : Nat) (n : Names) (C M : List JsTy)
    (mask : List Bool) (args : List ((σ : JsTy) × JsExpr S C M σ))
    (k : {Γ'' : UCtx ks} → {o' : Lvl} → Term Δ d Φ Γ'' τ js o' → Nat →
      List ((σ : JsTy) × JsExpr S C M σ) → ConvM X) : ConvM X :=
  match t with
  | .letE u (Comp.app (σ := σ) (.neu (.var x)) a _) t' => do
    if x.index != 0 then throw "tail loop: not an application of the fold"
    if left > 1 && u != .one then throw "tail loop: a partial application used more than once"
    -- the argument must not read the answers of the applications (they are not written)
    if (List.range bound).any fun i => (Own.PExpr.occ (.u i) a).n > 0 then
      throw "tail loop: an argument reads the fold"
    let own := n.own.pushU (List.replicate bound false)
    let (cx, _) := own.stmt (fun w => Own.PExpr.occ w a)
      (fun w => (Own.Term.occ (w.upU 1) t').n > 0)
    let na : Names := { n with u := List.replicate bound .none ++ n.u, own, cx }
    -- an argument for a variable of the loop that is owned: copied unless owned
    let ae ← if mask.getD (bound - 1) false then cPExprOwned a na C M else cPExpr a na C M
    let args := args ++ [⟨lowerTy cfg σ, ae⟩]
    if left ≤ 1 then k t' (bound + 1) args
    else cTailChain t' (left - 1) (bound + 1) n C M mask args k
  | _ => throw "tail loop: the fold is not applied to all its parameters"

/-- `let f := nat_rec cnt z s; f a₁ … aₙ; rest` (`t` the statement after the fold), when the
    step `s` computes the function at `i + 1` from the function `acc` at `i` calling `acc` only
    in tail position (`acc b₁ … bₙ` answered as it is: `f` is tail recursive): the loop
    `let p₁ = a₁; …; let j = cnt; while (true) { if (j === 0) { base } j--; step }`, whose
    step is the body of the function `s` answers on `p₁ … pₙ` with each tail call `acc b₁ … bₙ`
    written `p₁ = b₁; …; continue;` (`JsBlock.tailToLoop`), and whose base case is `base` on
    `p₁ … pₙ` (the initial function called, or its body).  The function at `j` applied to
    `p₁ … pₙ` is the answer at every iteration, so the loop computes `f a₁ … aₙ` without a
    closure per step and without a call per step (a tail-recursive Lean function on a `Nat`
    runs in constant stack).  An error when the shape is not this one (a call of `acc` that is
    not a tail call, a closure reading a variable of the loop, …): the caller then converts the
    fold as it is. -/
partial def cTailLoop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ρ τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {u₁ u₂ : Usage01ω} {on os : Lvl}
    (cnt : PExpr Δ Φ Γ .nat on) (s : Body Δ d Φ Γ [⟨ρ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] ρ os)
    (base : (C' M' : List JsTy) → List Ref → (r : JsTy) → ConvM (JsBlock S C' M' [] (.ret r)))
    (mode : Own.AccMode) (u : Usage1ω) (t : Term Δ d Φ (⟨ρ, u, d⟩ :: Γ) τ js o)
    (n : Names) (C M J : List JsTy) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  -- first with the records of leaves kept in one variable per field, when there is one
  match lowerTy cfg ρ with
  | .fn ds _ =>
    if ds.any (scalarRecordFields? · |>.isSome) then
      tryCatch (cTailLoopAt cnt s base mode u t n C M J true) fun _ =>
        cTailLoopAt cnt s base mode u t n C M J false
    else cTailLoopAt cnt s base mode u t n C M J false
  | _ => cTailLoopAt cnt s base mode u t n C M J false

/-- `cTailLoop`, keeping (when `flatOk`) the variables of the loop that hold a record of
    leaves given as a record literal or a variable in one variable per field (`Ref.fields`),
    strictly in the step (an error when the step reads such a record whole: it would build it
    at every iteration). -/
partial def cTailLoopAt {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ρ τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {u₁ u₂ : Usage01ω} {on os : Lvl}
    (cnt : PExpr Δ Φ Γ .nat on) (s : Body Δ d Φ Γ [⟨ρ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] ρ os)
    (base : (C' M' : List JsTy) → List Ref → (r : JsTy) → ConvM (JsBlock S C' M' [] (.ret r)))
    (mode : Own.AccMode) (u : Usage1ω) (t : Term Δ d Φ (⟨ρ, u, d⟩ :: Γ) τ js o)
    (n : Names) (C0 M J : List JsTy) (flatOk : Bool) :
    ConvM (JsBlock S C0 M J (.ret (lowerTy cfg τ))) := do
  unless u == .one do throw "tail loop: the fold is used more than once"
  let F := lowerTy cfg ρ
  let .fn ds R := F | throw "tail loop: the answer is not a function"
  let N := lowerTy cfg (Ty.nat : Ty ks)
  let some nt := JsNatTy.of? N | throw "internal: the representation of a Nat"
  -- the parameters an owning closure would own (`Own.AccMode.ownFn`): owned variables of the
  -- loop, whose initial values are copied unless owned; the tail calls of the step hand owned
  -- values over (copied by the call of the owning closure `acc` otherwise)
  let mask := match mode with
    | .ownFn m _ => m
    | _ => []
  let accMod := accEnv mode 0 (Own.accFnId d n.cx.env) ρ
  cTailChain t ds.length 1 n C0 M mask [] fun tRest bound args0 => do
    -- the parameters kept in one variable per field
    let flat : List Bool := (ds.zip args0).zipIdx.map fun ((dt, ⟨_, e⟩), i) =>
      flatOk && !(mask.getD i false) && (scalarRecordFields? dt).isSome &&
        (e.isAtom || e.isRecordMk)
    let fieldsOf (dt : JsTy) : List JsTy := (scalarRecordFields? dt).getD []
    let ds' := (ds.zip flat).flatMap fun (dt, f) => if f then fieldsOf dt else [dt]
    flattenInit [] (args0.zip flat) fun C args => do
    -- the initial values of the variables of the loop
    let some argsJs := argsOfList? args ds' | throw "tail loop: the types of the arguments"
    let M1 := pushAll ds' M
    let lvls := (List.range ds'.length).map (M.length + ·)
    -- where each parameter lives: a variable, or one variable per field
    let mkRefs (strict : Bool) : List Ref := Id.run do
      let mut off := M.length
      let mut out : Array Ref := #[]
      for (dt, f) in ds.zip flat do
        if f then
          let k := (fieldsOf dt).length
          out := out.push (Ref.fields ((List.range k).map fun j => Ref.m (off + j)) strict)
          off := off + k
        else
          out := out.push (Ref.m off)
          off := off + 1
      return out.toList
    let pRefs := mkRefs true
    -- the counter, already decremented in the step, is the predecessor the step reads
    let iRef := if u₂ == .zero then Ref.none else Ref.m M1.length
    let accRef := Ref.c C.length
    let fl := pRefs.zipIdx.map fun (_, i) => mask.getD i false
    let flatAccLvl := if flat.any (·) then some C.length else none
    let stepB : JsBlock S (F :: C) (N :: M1) [] (.ret R) ← match os, s with
      | _, .closed ts =>
        let own := accMod (n.own.body true [mode.owns, false])
        cApplyTerm ts { n with u := [accRef, iRef], own, flatAcc := flatAccLvl }
          (F :: C) (N :: M1) pRefs fl R
      | _, .opened ts _ =>
        let own := accMod (n.own.body false [mode.owns, false])
        cApplyTerm ts { n with u := [accRef, iRef] ++ n.u, own, flatAcc := flatAccLvl }
          (F :: C) (N :: M1) pRefs fl R
    let emit : {C M J : List JsTy} → (σs : List JsTy) → JsArgs S C M σs →
        Option (JsBlock S C M J .loop) := fun σs as => loopNextFlat flat ds' lvls σs as
    let some loopB := stepB.tailToLoop 0 emit | throw "tail loop: the step"
    let dropAcc : JsRenM Option (F :: C) C := fun x => match x with
      | .zero => none
      | .succ y => some y
    let some stepL := loopB.renameM dropAcc (fun x => some x)
      | throw "tail loop: a call of the fold that is not a tail call"
    let baseB ← base C (N :: M1) (mkRefs false) R
    let baseL : JsBlock S C (N :: M1) [R] .loop := baseB.retToJump
    -- a closure reading a variable of the loop would see its later values
    let captured (b : JsBlock S C (N :: M1) [R] .loop) : Bool :=
      b.occs.any fun oc => oc.isMut && oc.inClosure && oc.idx ≤ ds'.length
    if captured baseL || captured stepL then
      throw "tail loop: a closure reads a variable of the loop"
    let cntE ← cPExpr cnt n C M1
    let nR : Names := { n with u := .c C.length :: (List.replicate (bound - 1) .none ++ n.u),
                               own := n.own.pushU (List.replicate bound false) }
    let restB ← cTerm tRest nR (R :: C) M1 J
    return letMutsThen "p" argsJs (.countdown "j" nt cntE baseL stepL restB)

/-- A branch in tail position. -/
partial def cBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    (b : Branch Δ d Φ Γ τ js ℓ) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  match b with
  | .ite c t e => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w c)
      (fun w => (Own.Term.occ w t).n > 0 || (Own.Term.occ w e).n > 0)
    let ce ← castE (← cNeu c { n with cx } C M) (.terminal .bool)
    let (nt, ne) := n.splitOn c
    -- a test of a boolean held in a constant: its value in each branch
    let (nt, ne) := match c with
      | .var x => match n.u.getD x.index .none with
        | .c l => ({ nt with bools := (l, true) :: nt.bools },
                   { ne with bools := (l, false) :: ne.bools })
        | _ => (nt, ne)
      | _ => (nt, ne)
    return (JsBlock.ite ce (← cTerm t { nt with own } C M J) (← cTerm e { ne with own } C M J))
  | Branch.enum_casesOn (s := s) c bs => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w c)
      (fun w => (List.finRange _).any fun j => (Own.Term.occ w (bs j)).n > 0)
    let ce ← cNeu c { n with cx } C M
    let n := { n with own }
    let k := s.nOfConstructors
    let rec arms (m start : Nat) : ConvM (JsEnumArms S C M J (.ret (lowerTy cfg τ)) m) :=
      match m with
      | 0 => pure .nil
      | m + 1 => do
        if h : start < k then
          return .cons (← cTerm (bs ⟨start, h⟩) n C M J) (← arms m (start + 1))
        else throw "internal: an arm of a case analysis"
    return (JsBlock.enumCases ce (← arms k 0))
  | Branch.union_casesOn e brs => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w e)
      (fun w => (Own.Branches.occ w brs).n > 0)
    -- a value known to be one constructor (the layer of a fused fold, `Ref.ctor`): its arm
    let known? : Option (Nat × List Ref) := match e with
      | .var x => match n.u.getD x.index .none with
        | .ctor tag fs => some (tag, fs)
        | _ => none
      | _ => none
    if let some (tag, fs) := known? then
      return ← cBranchAt brs tag fs { n with own } C M J
    let ee ← cNeu e { n with cx } C M
    -- the constant taken apart, if it is one: each arm knows its constructor (`CtorFact`)
    let src? : Option (Nat × JsTy) :=
      let ofVar (i : Nat) : Option (Nat × JsTy) := match n.u.getD i .none with
        | .c l => (C[C.length - 1 - l]?).map (l, ·)
        | _ => none
      e.scrutVar?.bind ofVar
    return (← unionCasesAny ee
      (← cBranches brs { n with own } (Own.Neu.owned cx e) (Own.Neu.partOwned cx e) C M J src?))
  -- `join j (x : Nat) := body; case e of | cᵢ => jump j i`: `x` is the position of the
  -- constructor of `e` (`toCtorIdx e`), read from `e` itself (`JsExpr.enumIndex`, nothing at all
  -- for a `number` when the enum starts at `0`) instead of computed by a case analysis
  | Branch.join σ _ uₓ body br =>
    match br with
    | Branch.enum_casesOn (s := s) c _ =>
    if isCtorIdxCases br then do
      let σ' := lowerTy cfg σ
      let some nt := JsNatTy.of? σ' | throw "internal: the representation of a Nat"
      let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w c)
        (fun w => (Own.Term.occ (w.upU 1) body).n > 0)
      let ce ← cNeu c { n with cx } C M
      let own := own.pushU [false]
      bindConst ce fun r C' => do
        -- a `BigInt` read more than once is converted once
        if nt.isBigInt && uₓ == .many then
          let ie : JsExpr S C' M σ' := .enumIndex nt (← r.get (.enum s.nOfConstructors s.shift))
          return .const "x" ie
            (← cTerm body { n with u := .c C'.length :: n.u, own } (σ' :: C') M J)
        else
          cTerm body { n with u := .enumIdx r s.nOfConstructors s.shift :: n.u, own } C' M J
    else cJoin σ body br n C M J
    | br => cJoin σ body br n C M J

/-- A join point in front of a branch (`JsBlock.join`). -/
partial def cJoin {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o : Lvl} (σ : Ty ks) {u : Usage1ω} {uₓ : Usage01ω}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (br : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ)
    (n : Names) (C M J : List JsTy) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) := do
    let σ' := lowerTy cfg σ
    let envBr := Own.joinBranchEnv n.own body
    -- the join point owns its parameter when every jump passes an owned value
    let own := (Own.joinBodyEnv n.own br).pushU [Own.joinParam σ envBr br]
    -- a body starting with a case analysis of the parameter, and jumps passing constructor
    -- literals, each constructor at one jump only: the arm of each such constructor is written at
    -- its jump, on the fields of the literal, so that no value is built to be taken apart at once
    -- (`JoinInl`); when every jump is one of those, there is no join point left
    let tags := br.jumpCtors 0
    let once : List Nat := (tags.filterMap id).filter fun t => (tags.filter (· == some t)).length == 1
    if body.casesOnHead && !once.isEmpty then
      let conv (tag : Nat) (frefs : List Ref) (jm : Nat → Nat) (bounds : BoundFacts)
          (ctors : List CtorFact) (C' M' J' : List JsTy) (τ' : JsTy) :
          ConvM (JsBlock S C' M' J' (.ret τ')) := do
        let n' : Names := { n with u := .ctor tag frefs :: n.u, own, jmap := jm, bounds, ctors }
        castRet (← cTerm body n' C' M' J') τ'
      let entry : Option JoinInl := some { tags := once, sig := S, conv }
      if tags.all (fun t => match t with | some t => once.contains t | none => false) then
        cBranch br { n with own := envBr, inl := entry :: n.inl, jmap := jmapSkip n.jmap } C M J
      else
        let block ← cBranch br { n with own := envBr, inl := entry :: n.inl, jmap := jmapPush n.jmap }
          C M (σ' :: J)
        let rest ← cTerm body { n with u := .c C.length :: n.u, own } (σ' :: C) M J
        return (JsBlock.join "x" block rest)
    else
    let block ← cBranch br { n with own := envBr, inl := none :: n.inl, jmap := jmapPush n.jmap }
      C M (σ' :: J)
    let rest ← cTerm body { n with u := .c C.length :: n.u, own } (σ' :: C) M J
    return (JsBlock.join "x" block rest)

/-- The arm `tag` of a union's case analysis on a value known to be that constructor, whose
    fields are `fs` (`Ref.ctor`): no test.  A field read more than once that holds calls not
    made yet (`Ref.call`) has them made first, once. -/
partial def cBranchAt {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) (tag : Nat) (fs : List Ref) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  let arm (k : Nat) (us : List Usage01ω) (go : List Ref → (C' : List JsTy) →
      ConvM (JsBlock S C' M J (.ret (lowerTy cfg τ)))) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
    if fs.length != k then throw "internal: the fields of a known constructor" else
    bindShared fs us go
  let withFields (rs : List Ref) : Names :=
    let own := n.own.pushUH (Own.fieldsOwned rs.length false) (Own.fieldsOwned rs.length false)
    { n with u := rs ++ n.u, own }
  match brs, tag with
  | Branches.two (c₁ := c₁) us₁ _ b₁ _, 0 =>
    arm c₁.binds.length us₁ fun rs C' =>
      cTerm b₁ (withFields rs) C' M J
  | Branches.two (c₂ := c₂) _ us₂ _ b₂, 1 =>
    arm c₂.binds.length us₂ fun rs C' =>
      cTerm b₂ (withFields rs) C' M J
  | Branches.cons (c := c) us b _, 0 =>
    arm c.binds.length us fun rs C' =>
      cTerm b (withFields rs) C' M J
  | Branches.cons _ _ rest, k + 1 => cBranchAt rest k fs n C M J
  | _, _ => throw "internal: a known constructor out of range"
where
  /-- The fields `fs`, those read more than once (`us`) that hold calls not made yet made
      first. -/
  bindShared {C : List JsTy} (fs : List Ref) (us : List Usage01ω)
      (go : List Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J (.ret (lowerTy cfg τ)))) :
      ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
    match fs with
    | [] => go [] C
    | f :: fs' =>
      match f, us.headD .many with
      | .fields rs s, .many =>
        bindCalls rs [] fun rs' C' => bindShared (C := C') fs' us.tail fun fs'' C'' =>
          go (.fields rs' s :: fs'') C''
      | _, _ => bindShared fs' us.tail fun fs'' C' => go (f :: fs'') C'

/-- The arms of a union's case analysis: each binds the fields it uses
    (`const { _1: f₁, _2: f₂ } = s;`), owned or not (`ow`), and continues. -/
partial def cBranches {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) (n : Names) (ow ph : Bool) (C M J : List JsTy)
    (src? : Option (Nat × JsTy) := none) (tag : Nat := 0) :
    ConvM (JsUnionArms S C M J (.ret (lowerTy cfg τ)) (lowerCtors cfg cs)) :=
  -- the fact the arm of constructor `t` knows, its fields in `r`
  let facts (t : Nat) (r : List Ref) : List CtorFact := match src? with
    | some (l, ty) => { src := l, ty, tag := t, fields := r } :: n.ctors
    | none => n.ctors
  match brs with
  | Branches.two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂ => do
    let (⟨u₁, s₁⟩, r₁) := mkSel (lowerCtor cfg c₁) (usedFields us₁) C
    let (⟨u₂, s₂⟩, r₂) := mkSel (lowerCtor cfg c₂) (usedFields us₂) C
    let own₁ := n.own.pushUH (Own.fieldsOwned c₁.binds.length ow)
      (Own.fieldsOwned c₁.binds.length ph)
    let own₂ := n.own.pushUH (Own.fieldsOwned c₂.binds.length ow)
      (Own.fieldsOwned c₂.binds.length ph)
    let a₁ ← cTerm b₁ { n with u := r₁ ++ n.u, own := own₁, ctors := facts tag r₁ } (pushAll u₁ C) M J
    let a₂ ← cTerm b₂ { n with u := r₂ ++ n.u, own := own₂, ctors := facts (tag + 1) r₂ }
      (pushAll u₂ C) M J
    return .cons s₁ a₁ (.cons s₂ a₂ .nil)
  | Branches.cons (c := c) us b rest => do
    let (⟨u, s⟩, r) := mkSel (lowerCtor cfg c) (usedFields us) C
    let own := n.own.pushUH (Own.fieldsOwned c.binds.length ow) (Own.fieldsOwned c.binds.length ph)
    let a ← cTerm b { n with u := r ++ n.u, own, ctors := facts tag r } (pushAll u C) M J
    return .cons s a (← cBranches rest n ow ph C M J src? (tag + 1))

end

end

/-! ## Whole functions -/

/-- Convert a closed program into an exported JavaScript function named `name`
    (`export const name = (params) => …`), of all the parameters of its type (none when it is
    not a function).  `paramNames` are the preferred names of its parameters.  `owned` says
    which parameters the function owns (`OwnVersion.owned`; none by default): it may update
    those in place.  The conversion is the whole translation: the finished function is not
    rewritten afterwards (every optimisation is done on `Term`, before, by `Term.optimize`,
    and the updates done in place are decided on `Term`, by `LeanScript.Term.Ownership`). -/
def termToJs (cfg : JsConfig) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) (owned : List Bool := []) : Except String JsFun := do
  -- datatypes of equal layouts share one object id (`canonDecls`)
  let cfg := withCanonDecls cfg ct.Δ
  let τ := lowerTy cfg ct.τ
  let (ds, ret) := match τ with
    | .fn ds c => (ds, c)
    | t => ([], t)
  let ps : List (String × JsTy) := ds.zipIdx.map fun (t, i) => (paramNames.getD i s!"p{i}", t)
  let sig := jsSigOf cfg ct.Δ
  let fl := ds.zipIdx.map fun (_, i) => owned.getD i false
  let body ← cApplyTerm (S := sig) cfg ct.term {} (pushAll ds []) [] ((paramRefs [] ds).map (·.1))
    fl ret
  let body ← if h : pushAll ds [] = pushAll (ps.map (·.2)) [] then pure (h ▸ body) else
    throw "internal: the parameters of a function"
  return { name, leanName, sig, params := ps, ret, body }

end MoreJs

end
