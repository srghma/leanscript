module
public import LeanScript.Ty
public import LeanScript.DeBruijn
@[expose] public section

namespace LeanScript

/-! ## Variables -/

/-- The types of the values in scope, innermost first. -/
abbrev Ctx := List Ty

/-- A variable: a de Bruijn index into the context, carrying the type it is bound at. -/
abbrev Var (Γ : Ctx) (τ : Ty) : Type := DeBruijn Γ τ

/-- The variable just bound. -/
abbrev Var.head {Γ : Ctx} {τ : Ty} : Var (τ :: Γ) τ := DeBruijn.head

/-- A variable bound further out. -/
abbrev Var.tail {Γ : Ctx} {τ1 τ2 : Ty} (v : Var Γ τ1) : Var (τ2 :: Γ) τ1 :=
  DeBruijn.tail v

/-- Membership notation: `Γ ∋ τ`. -/
infix:40 " ∋ " => Var

/-- Expand a natural number literal into nested `Var.tail` / `Var.head`. -/
syntax "var_get_elem" (ppSpace term) : term
macro_rules | `(term| var_get_elem $n) => match n.1.toNat with
| 0     => `(term| DeBruijn.head)
| n + 1 => `(term| DeBruijn.tail (var_get_elem $(Lean.quote n)))

/-- Sugar: `v♯0` is `Var.head`, `v♯1` is `Var.tail Var.head`, … -/
macro "v♯" n:term:90 : term => `(var_get_elem $n)

/-- The de Bruijn index of a variable: how many binders out it is. -/
abbrev Var.index {Γ : Ctx} {τ : Ty} (v : Var Γ τ) : Nat := DeBruijn.index v

/-! ## The signature of a module

A `Term` is written against a fixed list of top-level declarations — the ones the
compiled module binds, plus the ones it imports from the runtime.  A reference to one of
them is a `GlobalRef`, an index into that list, so the *name* and the *type* of a global
are read off the signature rather than written at the use site.
-/

/-- One top-level declaration a term may refer to: the name it is bound to, and its
    type.

    There is deliberately **no** `isInlined` field: whether a declaration is inlined is a
    property of the *translation* into this language, not of the language, and an
    inlined declaration simply does not reach a signature. -/
structure GlobalDecl where
  /-- The identifier the declaration is bound to. -/
  name : String
  /-- Its type. -/
  ty : Ty
  deriving DecidableEq

/-- Are all of these names different? -/
def declNamesUnique : List GlobalDecl → Bool
  | [] => true
  | d :: ds => !ds.any (fun e => e.name == d.name) && declNamesUnique ds

/-- The signature of the module being compiled: every top-level name a `Term` of it may
    mention, **each of them declared once**.  The proof is a field, so a signature that
    declares a name twice cannot be built; `by decide` discharges it for a signature
    written out. -/
structure Sig where
  /-- The declarations, in order. -/
  decls : List GlobalDecl
  /-- No name is declared twice. -/
  h_names_unique : declNamesUnique decls = true := by decide

/-- A reference to a declaration of the signature — a de Bruijn index into it, whose
    type is the one the signature gives it.  There is no other way to name a global, so
    a `Term` cannot call a name that is not declared, nor call a declared one at a type
    it does not have. -/
abbrev GlobalRef (ds : List GlobalDecl) (τ : Ty) : Type :=
  DeBruijnProj GlobalDecl.ty ds τ

/-- The declaration just bound. -/
@[match_pattern] abbrev GlobalRef.here {g : GlobalDecl} {ds : List GlobalDecl} :
    GlobalRef (g :: ds) g.ty := DeBruijnProj.head

/-- A declaration bound further out. -/
@[match_pattern] abbrev GlobalRef.there {g : GlobalDecl} {ds : List GlobalDecl} {τ : Ty}
    (r : GlobalRef ds τ) : GlobalRef (g :: ds) τ := DeBruijnProj.tail r

/-- The name a reference resolves to: the name of the declaration it points at. -/
def GlobalRef.name {ds : List GlobalDecl} {τ : Ty} (r : GlobalRef ds τ) : String :=
  r.entry.name

@[simp] theorem GlobalRef.name_here {g : GlobalDecl} {ds : List GlobalDecl} :
    (GlobalRef.here (g := g) (ds := ds)).name = g.name := rfl

@[simp] theorem GlobalRef.name_there {g : GlobalDecl} {ds : List GlobalDecl} {τ : Ty}
    (r : GlobalRef ds τ) : (GlobalRef.there (g := g) r).name = r.name := rfl

/-! ## Labels have a context of their own

A label is not a value: it cannot be passed, stored or returned, and the only thing that
may be done with one is to jump to it.  That is not a discipline checked after the fact
— it is the shape of the language.  A label is bound in `Ω`, a context whose entries are
the *argument types* a jump to it supplies, and the only constructor that reads `Ω` is
`Tail.jmp`.  A `Term` has no `Ω` at all, so a value can never name a label.

A label has **no result type**: jumping to it does not come back, so the block it is part
of answers with the type the enclosing `Term.block` answers with.
-/

/-- The labels in scope, innermost first; an entry is what a jump to that label
    supplies. -/
abbrev LCtx := List (List Ty)

/-- A label in scope: a de Bruijn index into `Ω`, separate from the index of a
    variable — the same family, at a different entry type. -/
abbrev LVar (Ω : LCtx) (ps : List Ty) : Type := DeBruijn Ω ps

/-- The innermost label. -/
abbrev LVar.head {Ω : LCtx} {ps : List Ty} : LVar (ps :: Ω) ps := DeBruijn.head

/-- A label bound further out. -/
abbrev LVar.tail {Ω : LCtx} {ps qs : List Ty} (v : LVar Ω ps) : LVar (qs :: Ω) ps :=
  DeBruijn.tail v

/-- Membership notation for labels: `Ω ∋ₗ ps`. -/
infix:40 " ∋ₗ " => LVar

/-- The de Bruijn index of a label. -/
abbrev LVar.index {Ω : LCtx} {ps : List Ty} (v : LVar Ω ps) : Nat := DeBruijn.index v

/-! ## Recursions have a context of their own

A self-reference is no more a value than a label is: it can be *called*, and nothing
else.  So it lives in a context of its own, `Ρ`, whose entries record what a recursion
takes and what it answers with — and **not** its measure.  That omission is the whole
termination argument of the grammar: a `Term.selfCall` has nowhere to put a measure, so
the only measure a recursion can ever run at is the one the semantics computes from the
arguments of the call, and the call happens only when that measure is smaller.
-/

/-- The signature of a recursion in scope: the types of its arguments and the type it
    answers with.  There is deliberately **no measure component**. -/
structure RSig where
  /-- The argument types of the recursive function. -/
  ps : List Ty
  /-- Its result type. -/
  ret : Ty
  deriving DecidableEq

/-- The measured recursions whose body we are inside, innermost first. -/
abbrev RCtx := List RSig

/-- A recursion in scope: a de Bruijn index into `Ρ`, separate from the index of a
    variable and from the index of a label — again the same family, at a third entry
    type. -/
abbrev RVar (Ρ : RCtx) (r : RSig) : Type := DeBruijn Ρ r

/-- The innermost recursion. -/
abbrev RVar.head {Ρ : RCtx} {r : RSig} : RVar (r :: Ρ) r := DeBruijn.head

/-- A recursion bound further out. -/
abbrev RVar.tail {Ρ : RCtx} {r s : RSig} (v : RVar Ρ r) : RVar (s :: Ρ) r :=
  DeBruijn.tail v

/-- Membership notation for recursions: `Ρ ∋ᵣ r`. -/
infix:40 " ∋ᵣ " => RVar

/-- The de Bruijn index of a recursion. -/
abbrev RVar.index {Ρ : RCtx} {r : RSig} (v : RVar Ρ r) : Nat := DeBruijn.index v
