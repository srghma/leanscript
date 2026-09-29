module

public import LeanScript.Term.Syntax.Packed
public import LeanScript.Term.Extern.Name

@[expose] public section

set_option autoImplicit false

/-!
# Ownership: which values a statement may update in place

A Lean `Array` is persistent: `a.set i x` answers a new array and leaves `a` alone.  In
JavaScript the copy can be avoided — the array updated in place (`…_mutable` operations of
`runtime.js`) — when **nothing else refers to the array**: nothing reads it afterwards, and no
other value holds it.  Lean decides this at run time with reference counts; here it is decided
**statically**, on `Term`, and the decisions are used when `Term` is converted to JavaScript
(`JsTerm.Lower.FromTerm`).

## Owned values

A value is **owned** at a point of a statement when the statement holds the only reference to
it:

* an **array** is owned when no other live variable or value refers to it (shallow: its
  elements are never updated in place, so they may be shared);
* a **record**, a **union** or a **declared datatype** is owned when it is referenced only here
  *and* each of its fields that may hold an array is owned (deep: taking an owned record apart
  gives owned fields);
* a value of any other type never needs owning (`Own.Ty.needsOwn`): it is never updated in
  place.

Values become owned by being built here (a literal, `Array.replicate`, `Array.emptyWithCapacity`,
the copy an update makes), by being the result of an update done in place, by being a field of
an owned value taken apart where it is used for the last time, and by being a parameter of a
function (or loop) that **owns** that parameter: its callers give up the value.

## Consuming and updating

An owned variable is **consumed** where it is used for the last time, if its other uses in the
same statement only read it (`Array.size`, `a[i]!`: *read slots*, `Own.readSlot?`).  A variable
used in any other way (stored into a value, passed to a function, captured by a closure, updated
without being consumed) **escapes**: it is not owned afterwards, since something may still hold
it.

An update of the array `a` (`Array.push`, `set!`, `set`, `swapIfInBounds`, `swap`, `pop`) is done
**in place** (`Own.Ctx.updatable`) when `a` is owned and is used for the last time there, and its
only other uses in the statement are reads inside the arguments of the update itself (they are
evaluated before it).

## The environment

`Own.Env` gives, for each unknown and each known value of a statement (in the order of the
contexts `Γ` and `Φ`, innermost first), whether it is owned.  `Own.Ctx` is the environment in
which one part `S` of a statement (a computation, a value, the operand of a `ret`, …) is
examined: every variable used again after `S` is already marked not owned there, and it knows
how often each variable occurs in `S` (`Own.Occ`).

The analysis of whole statements (which loops own their accumulator, which join points their
parameter, which parameters of a function are worth owning) is `LeanScript.Term.Ownership.Walk`.
This is an analysis for code generation: `Term.eval` is not affected (the updates in place are
invisible in the semantics of `Term`, where arrays are values), and nothing here is proved.
-/

namespace LeanScript

namespace Own

/-! ## Types that need owning -/

mutual
/-- Does a value of this type hold an array that could be updated in place (an array, or a
    record, union or declared datatype that may hold one)? -/
partial def Ty.needsOwn {ks : List Nat} {d : Bool} : Ty ks d → Bool
  | .array _ => true
  | .record t fs => Ty.needsOwn t || Fields.needsOwn fs
  | Ty.union cs => Ctors.needsOwn cs
  | .data _ => true
  | _ => false
/-- `Ty.needsOwn` of fields. -/
partial def Fields.needsOwn {ks : List Nat} : Fields ks → Bool
  | .one t => Ty.needsOwn t
  | .cons t fs => Ty.needsOwn t || Fields.needsOwn fs
/-- `Ty.needsOwn` of the constructors of a union. -/
partial def Ctors.needsOwn {ks : List Nat} {bs : List Bool} : Ctors ks bs → Bool
  | .two a b => Ctor.needsOwn a || Ctor.needsOwn b
  | .cons a cs => Ctor.needsOwn a || Ctors.needsOwn cs
/-- `Ty.needsOwn` of a constructor. -/
partial def Ctor.needsOwn {ks : List Nat} {b : Bool} : Ctor ks b → Bool
  | .nullary => false
  | .fields fs => Fields.needsOwn fs
end

/-! ## The externs over arrays -/

/-- The updates of an array (their array is the first argument). -/
def updateExterns : List String :=
  ["lean_array_push", "lean_array_set", "lean_array_fset", "lean_array_swap",
   "lean_array_fswap", "lean_array_pop"]

/-- Is the extern an update of an array? -/
def isUpdate (name : String) : Bool := updateExterns.contains name

/-- The updates whose `…_immutable` operation may answer its argument itself (`set!` and
    `swapIfInBounds`, out of bounds): when such an update is not done in place, the conversion
    copies the array and updates the copy in place (`…_mutable([...a], …)`), so that its answer
    is always a new array. -/
def copyThenUpdate (name : String) : Bool :=
  name == "lean_array_set" || name == "lean_array_swap"

/-- The externs that always answer a new array: every update when it is not done in place (a
    copy: see `copyThenUpdate`), and the constructors of arrays. -/
def freshExterns : List String :=
  updateExterns ++
  ["lean_mk_array", "lean_mk_empty_array_with_capacity__Array_emptyWithCapacity",
   "lean_mk_empty_array_with_capacity__Array_mkEmpty"]

/-- Does the extern always answer a new array? -/
def isFresh (name : String) : Bool := freshExterns.contains name

/-- The argument an extern only reads (its answer does not refer to it): the array of
    `a[i]!` and of `Array.size`. -/
def readSlot? (name : String) : Option Nat :=
  if name == "lean_array_get" || name == "lean_array_get_borrowed" then some 1
  else if name == "lean_array_get_size" then some 0
  else none

/-! ## Variables and occurrences -/

/-- A variable of a statement: an unknown or a known value, by its de Bruijn position. -/
inductive V where
  | u (i : Nat)
  | k (i : Nat)
  deriving BEq, Inhabited, Repr

/-- The variable, seen from under `n` more unknowns. -/
def V.upU (n : Nat) : V → V
  | .u i => .u (i + n)
  | .k i => .k i

/-- The variable, seen from under `n` more known values. -/
def V.upK (n : Nat) : V → V
  | .u i => .u i
  | .k i => .k (i + n)

/-- How often a variable occurs in a piece of code: all its occurrences (`n`), and those that
    are not in a read slot (`esc`: the value may be held by something else afterwards). -/
structure Occ where
  n : Nat := 0
  esc : Nat := 0
  /-- The occurrences inside the body of a loop or a fold of the code (they run after the
      loop has started updating its accumulator). -/
  inBody : Nat := 0
  /-- The occurrences inside the body of a closure or a delay (which may run later, any number
      of times). -/
  inClosure : Nat := 0
  deriving Inhabited, Repr, BEq

instance : Add Occ :=
  ⟨fun a b => ⟨a.n + b.n, a.esc + b.esc, a.inBody + b.inBody, a.inClosure + b.inClosure⟩⟩

/-- One escaping occurrence. -/
def Occ.one : Occ := ⟨1, 1, 0, 0⟩

/-- One occurrence in a read slot. -/
def Occ.read : Occ := ⟨1, 0, 0, 0⟩

/-- The occurrences are inside a closure or a delay (which may run later): they all escape. -/
def Occ.allEsc (o : Occ) : Occ := { o with esc := o.n, inClosure := o.n }

/-- The occurrences are inside the body of a loop. -/
def Occ.loop (o : Occ) : Occ := { o with inBody := o.n }

section Occurrences
variable {ks : List Nat} {Δ : DSig ks}

/-- Is the unknown the variable? -/
def uIs {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ) : V → Bool
  | .u i => x.index == i
  | .k _ => false

/-- Is the known value the variable? -/
def kIs {Φ : KCtx ks} {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o) : V → Bool
  | .k i => x.index == i
  | .u _ => false

mutual
/-- Occurrences of a variable in a neutral expression. -/
partial def Neu.occ {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (v : V) :
    Neu Δ Φ Γ τ ℓ → Occ
  | .var x => if uIs x v then Occ.one else {}
  | .data_out _ _ n => Neu.occ v n
  | .cond c a b => Neu.occ v c + PExpr.occ v a + PExpr.occ v b
  | .extern e args _ => Args.occAt v (readSlot? (externName e)) 0 args
/-- Occurrences of a variable in a pure expression. -/
partial def PExpr.occ {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (v : V) :
    PExpr Δ Φ Γ τ o → Occ
  | .neu n => Neu.occ v n
  | .kvar x => if kIs x v then Occ.one else {}
  | .lit _ _ => {}
  | .enum_mk _ _ => {}
  | .record_mk args => Args.occAt v none 0 args
  | .union_mk _ args => Args.occAt v none 0 args
  | .array_mk es => Elems.occ v es
  | .list_mk es => Elems.occ v es
  | .data_in _ _ e => PExpr.occ v e
/-- Occurrences of a variable in arguments, the one at position `slot` (if any) being a read
    slot (at position `pos` for the first of `args`). -/
partial def Args.occAt {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (v : V)
    (slot : Option Nat) (pos : Nat) : Args Δ Φ Γ σs o → Occ
  | .nil => {}
  | .cons a as =>
    let here : Occ :=
      if slot == some pos then
        match a with
        | .neu (.var x) => if uIs x v then Occ.read else {}
        | .kvar x => if kIs x v then Occ.read else {}
        | a => PExpr.occ v a
      else PExpr.occ v a
    here + Args.occAt v slot (pos + 1) as
/-- Occurrences of a variable in the elements of a literal. -/
partial def Elems.occ {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} (v : V) :
    Elems Δ Φ Γ t o → Occ
  | .nil => {}
  | .cons e es => PExpr.occ v e + Elems.occ v es
end

/-- Occurrences of a variable as the array a loop runs over (only read, but while the loop runs:
    the caller marks them `Occ.loop`). -/
def PExpr.occRead {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (v : V) :
    PExpr Δ Φ Γ τ o → Occ
  | .neu (.var x) => if uIs x v then Occ.read else {}
  | .kvar x => if kIs x v then Occ.read else {}
  | a => PExpr.occ v a

mutual
/-- Occurrences of a variable in a value: those in a closure or a delay all escape. -/
partial def Val.occ {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (v : V) :
    Val Δ d Φ Γ τ o → Occ
  | .lam b => (Body.occ v b).allEsc
  | .thunk_mk b => (Body.occ v b).allEsc
  | .lazy_mk b => (Body.occ v b).allEsc
  | .record_mk args => Args.occAt v none 0 args
  | .union_mk _ args => Args.occAt v none 0 args
  | .array_mk es => Elems.occ v es
  | .list_mk es => Elems.occ v es
  | .data_in _ _ e => PExpr.occ v e
/-- Occurrences of a variable (of the context outside) in a body. -/
partial def Body.occ {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} (v : V) :
    Body Δ d Φ Γ bs τ o → Occ
  | .closed t => match v with
    | .u _ => {}
    | .k i => Term.occ (.k i) t
  | .opened t _ => Term.occ (v.upU bs.length) t
/-- Occurrences of a variable in a computation. -/
partial def Comp.occ {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (v : V) :
    Comp Δ d Φ Γ τ ℓ → Occ
  | .app f a _ => PExpr.occ v f + PExpr.occ v a
  | .share n => Neu.occ v n
  | .nat_rec n z s _ => PExpr.occ v n + PExpr.occ v z + (Body.occ v s).loop
  | .array_foldl a z s _ => (PExpr.occRead v a).loop + PExpr.occ v z + (Body.occ v s).loop
  | .data_rec _ _ _ brs _ e _ =>
    (List.finRange _).foldl (fun acc j => acc + (Body.occ v (brs j)).loop) (PExpr.occ v e)
  | .data_brec _ _ _ _ brs _ e _ =>
    (List.finRange _).foldl (fun acc j => acc + (Body.occ v (brs j)).loop) (PExpr.occ v e)
  | .thunk_force e => PExpr.occ v e
  | .lazy_force e => PExpr.occ v e
/-- Occurrences of a variable in a statement (all the arms of its branches). -/
partial def Term.occ {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (v : V) : Term Δ d Φ Γ τ js o → Occ
  | .ret e => PExpr.occ v e
  | .letV _ val b => Val.occ v val + Term.occ (v.upK 1) b
  | .letE _ c b => Comp.occ v c + Term.occ (v.upU 1) b
  | .record_casesOn (t := t) (fs := fs) _ n b =>
    Neu.occ v n + Term.occ (v.upU (t :: fs.toList).length) b
  | .branch br => Branch.occ v br
  | .jump _ e => PExpr.occ v e
/-- Occurrences of a variable in a branch. -/
partial def Branch.occ {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (v : V) : Branch Δ d Φ Γ τ js ℓ → Occ
  | .ite c t e => Neu.occ v c + Term.occ v t + Term.occ v e
  | .enum_casesOn e bs => (List.finRange _).foldl (fun acc j => acc + Term.occ v (bs j))
      (Neu.occ v e)
  | .union_casesOn e bs => Neu.occ v e + Branches.occ v bs
  | .join _ _ _ body main => Term.occ (v.upU 1) body + Branch.occ v main
/-- Occurrences of a variable in the arms of a union's case analysis. -/
partial def Branches.occ {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (v : V) :
    Branches Δ d Φ Γ cs τ js o → Occ
  | .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
    Term.occ (v.upU c₁.binds.length) b₁ + Term.occ (v.upU c₂.binds.length) b₂
  | .cons (c := c) _ b rest => Term.occ (v.upU c.binds.length) b + Branches.occ v rest
end

end Occurrences

/-! ## Environments -/

/-- Which unknowns (`u`) and known values (`k`) are owned, innermost first. -/
structure Env where
  u : List Bool := []
  k : List Bool := []
  deriving Inhabited, Repr

namespace Env

/-- Is the variable owned? -/
def get (e : Env) : V → Bool
  | .u i => e.u.getD i false
  | .k i => e.k.getD i false

/-- The environment where the owned variables satisfying `p` are no longer owned (`p` is only
    asked about owned variables). -/
def kill (e : Env) (p : V → Bool) : Env :=
  { u := e.u.mapIdx fun i b => b && !p (.u i)
    k := e.k.mapIdx fun i b => b && !p (.k i) }

/-- Nothing owned, with the same number of variables. -/
def none (e : Env) : Env := { u := e.u.map fun _ => false, k := e.k.map fun _ => false }

/-- New unknowns, innermost first. -/
def pushU (e : Env) (bs : List Bool) : Env := { e with u := bs ++ e.u }

/-- A new known value. -/
def pushK (e : Env) (b : Bool) : Env := { e with k := b :: e.k }

/-- Is any variable owned? -/
def any (e : Env) : Bool := e.u.any id || e.k.any id

end Env

/-- The environment in which a part `S` of a statement is examined: `env` has every variable
    used after `S` marked not owned; `occ v` is how often `v` occurs in `S`. -/
structure Ctx where
  env : Env
  occ : V → Occ

instance : Inhabited Ctx := ⟨⟨{}, fun _ => {}⟩⟩

namespace Ctx

/-- The variable can be consumed at one of its escaping occurrences in `S` (stored into a
    value, passed on): it is owned, not used after `S`, and its other occurrences in `S` only
    read it, before any loop of `S` starts (a loop may update the value it was given). -/
def consumable (c : Ctx) (v : V) : Bool :=
  let o := c.occ v
  c.env.get v && o.esc == 1 && o.inBody == 0

/-- The variable can be updated in place by an update whose other arguments have the
    occurrences `rest`: it is owned, not used after `S`, and its other occurrences in `S` are
    reads inside those arguments (evaluated before the update). -/
def updatable (c : Ctx) (v : V) (rest : Occ) : Bool :=
  c.env.get v && (c.occ v).n == 1 + rest.n && rest.esc == 0

end Ctx

/-- The context of a part of a statement whose occurrences are `occS`, followed by code in which
    the variables satisfying `live` are used; and the environment after it (the variables that
    escaped in it are no longer owned). -/
def Env.stmt (env : Env) (occS : V → Occ) (live : V → Bool) : Ctx × Env :=
  (⟨env.kill live, occS⟩, env.kill fun v => (occS v).esc > 0)

end Own

end LeanScript

end
