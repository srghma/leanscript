module

public import LeanScript.NTerm.Ctx
public import LeanScript.Term.Term

@[expose] public section

set_option autoImplicit false

/-!
# Normal-form terms (proposal B): two contexts, *known* and *unknown*

The grammar of `LeanScript.NTerm`: A-normal terms in which **every redex that could be
evaluated has been**, by construction, while a redex that cannot be evaluated (because it is
stuck on an unknown) is kept, and its operands are shared rather than duplicated.

```
Neu     Φ Γ   ::= var x                          -- x : UVar Γ τ, an unknown
                | data_out b j Neu | cond Neu PExpr PExpr
                | extern e (Args true)           -- at least one open argument
PExpr   Φ Γ o ::= neu Neu                        -- o = true
                | kvar k                         -- k : KVar Φ τ o, a known value by name
                | lit | enum_mk                  -- o = false
                | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
                | data_in b j PExpr
Val     Φ Γ o ::= lam Body | thunk_mk Body | lazy_mk Body
                | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
                | data_in b j PExpr
Body    Φ Γ bs o ::= closed (Term Φ.closedOnly bs)   -- o = false: sees no unknown
                   | opened (Term Φ (bs ++ Γ))        -- o = true:  Γ is not empty
Comp    Φ Γ   ::= app PExpr PExpr                -- at least one operand open
                | share Neu
                | nat_rec PExpr PExpr Body | array_foldl PExpr PExpr Body
                | data_rec … Body … PExpr | data_brec … Body … PExpr
                                                 -- at least one operand or the body open
                | thunk_force (PExpr true) | lazy_force (PExpr true)
Term    Φ Γ js ::= ret PExpr
                 | letV u Val Term               -- extends Φ
                 | letE u Comp Term              -- extends Γ
                 | record_casesOn us Neu Term    -- extends Γ with the fields
                 | branch Branch
                 | jump j PExpr
Branch  Φ Γ js ::= ite Neu Term Term | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
                 | join σ u uₓ Term Branch        -- a join point, only in front of a branch
```

**Known and unknown.**  A statement has two variable contexts (`LeanScript.NTerm.Ctx`):
`Φ`, the *known* values, bound by `letV` to a value of known shape; and `Γ`, the *unknowns*,
bound by `letE` (the result of a computation), by case analyses, and as parameters of
closures, loops and join points.  Only an unknown is neutral (`Neu.var` takes a `UVar Γ`), so
a known value is never taken apart, called or forced: the normaliser does that itself.  A
known value can be passed on by name (`PExpr.kvar`), which is how a closure, a delay or a
data literal is **shared** instead of copied.

**Open and closed.**  Every pure expression, argument list, value and body carries a flag
`o : Bool`, *open*: whether it mentions an unknown.  It is computed by the constructors
(`neu` is open, `lit` is closed, a constructor is open when one of its arguments is, a known
variable is as open as its entry in `Φ`), except for the bodies of closures, delays and loops:
a **closed** body (`Body.closed`) sees only the closed known values and its own binders; an
**open** body (`Body.opened`) sees everything, and exists only when there is an unknown in
scope.

**The rule.**  Every elimination needs an open operand:

* `extern e args` needs `args : Args σs true`, at least one open argument;
* `app f a` needs `f` or `a` open.  A closed known closure applied to a closed argument is
  β-reduced by the normaliser; applied to an open argument, the call is kept and the closure
  shared (it is not inlined);
* the folds need an open operand or an open body.  A loop over a literal whose body is open
  is kept, not unrolled;
* the forces need an open delay (an unknown one, or an open known one): the body of a closed
  delay is already a value;
* `record_casesOn`, `ite`, `enum_casesOn`, `union_casesOn`, `data_out` and `cond` take a
  `Neu`: a known value is never taken apart.

So a term with no unknown (`Γ = []`) whose known values are closed contains no computation
at all: it is a chain of `letV`s ending in `ret v` (`LeanScript.NTerm.Term.closed_isValue`).

**Join points.**  A join point is only allowed in front of a branch (`Branch.join`), so a
join point whose continuation is a known jump (`join j x := b; jump j v`, a redex) cannot be
written.  A join point that is not jumped to at all is allowed (its usage is `zero`): it is
dead code, which an optimiser removes.

**Usages.**  Every binder carries a `Usage` (`0 | 1 | ω`); a binder annotated `zero` cannot
be referenced, so a dead binding is dropped by a simple strengthening.
-/

namespace LeanScript.NTerm

/-! ## Layer 1: pure expressions -/

mutual

/-- **Neutral expressions**: stuck on an unknown.  A variable of `Γ` (never of `Φ`), an
    elimination of a neutral value, or a call of an extern with at least one open argument. -/
inductive Neu {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Ty ks → Type where
  /-- An unknown. -/
  | var {τ : Ty ks} : UVar Γ τ → Neu Δ Φ Γ τ
  /-- One layer out of a neutral value of member `j` of block `b`. -/
  | data_out (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      Neu Δ Φ Γ (.data ((Δ.block b).ref j)) → Neu Δ Φ Γ ((Δ.block b).unfold j)
  /-- The pure conditional on a neutral condition. -/
  | cond {τ : Ty ks} {o₁ o₂ : Bool} : Neu Δ Φ Γ .bool → PExpr Δ Φ Γ τ o₁ → PExpr Δ Φ Γ τ o₂ →
      Neu Δ Φ Γ τ
  /-- A call of an extern with at least one open argument. -/
  | extern {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) : Args Δ Φ Γ σs true →
      Neu Δ Φ Γ τ

/-- **Pure expressions** of type `τ`, open (`o = true`) when they mention an unknown. -/
inductive PExpr {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    Ty ks → Bool → Type where
  /-- A neutral expression. -/
  | neu {τ : Ty ks} : Neu Δ Φ Γ τ → PExpr Δ Φ Γ τ true
  /-- A known value, by name. -/
  | kvar {τ : Ty ks} {o : Bool} : KVar Φ τ o → PExpr Δ Φ Γ τ o
  /-- A literal of a leaf type. -/
  | lit (p : LeanPrimTy) (v : p.denote) : PExpr Δ Φ Γ (.prim p) false
  /-- A constructor of an enum. -/
  | enum_mk (s : LeanEnumSchema) : Fin s.nOfConstructors → PExpr Δ Φ Γ (.enum s) false
  /-- A record, from its fields. -/
  | record_mk {t : Ty ks} {fs : Fields ks} {o : Bool} : Args Δ Φ Γ (t :: fs.toList) o →
      PExpr Δ Φ Γ (.record t fs) o
  /-- A constructor of a union, from its fields. -/
  | union_mk {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {h : UnionShape bs}
      {c : Ctor ks b} {o : Bool} : CtorIx cs c → Args Δ Φ Γ c.binds o →
      PExpr Δ Φ Γ (.union cs (h := h)) o
  /-- An array literal. -/
  | array_mk {t : Ty ks} {o : Bool} : Elems Δ Φ Γ t o → PExpr Δ Φ Γ (.array t) o
  /-- A list literal. -/
  | list_mk {t : Ty ks} {o : Bool} : Elems Δ Φ Γ t o → PExpr Δ Φ Γ (.list t) o
  /-- One layer in. -/
  | data_in (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) {o : Bool} :
      PExpr Δ Φ Γ ((Δ.block b).unfold j) o → PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) o

/-- Arguments; open when one of them is. -/
inductive Args {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    List (Ty ks) → Bool → Type where
  | nil : Args Δ Φ Γ [] false
  | cons {σ : Ty ks} {σs : List (Ty ks)} {o₁ o₂ : Bool} : PExpr Δ Φ Γ σ o₁ →
      Args Δ Φ Γ σs o₂ → Args Δ Φ Γ (σ :: σs) (o₁ || o₂)

/-- The elements of an array or list literal; open when one of them is. -/
inductive Elems {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    Ty ks → Bool → Type where
  | nil {t : Ty ks} : Elems Δ Φ Γ t false
  | cons {t : Ty ks} {o₁ o₂ : Bool} : PExpr Δ Φ Γ t o₁ → Elems Δ Φ Γ t o₂ →
      Elems Δ Φ Γ t (o₁ || o₂)

end

/-! ## Layers 2 and 3: values, bodies, computations, statements -/

mutual

/-- **Values of known shape**, bound by `Term.letV` into the known context.  Open when they
    mention an unknown. -/
inductive Val {ks : List Nat} (Δ : DSig ks) : KCtx ks → UCtx ks → Ty ks → Bool → Type where
  /-- A closure; its parameter is an unknown of the body. -/
  | lam {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage} {o : Bool} :
      Body Δ Φ Γ [⟨σ, u⟩] τ o → Val Δ Φ Γ (.fn σ τ) o
  /-- A memoised delay. -/
  | thunk_mk {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Bool} :
      Body Δ Φ Γ [] τ.relax o → Val Δ Φ Γ (.thunk τ) o
  /-- A delay that is recomputed every time. -/
  | lazy_mk {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Bool} :
      Body Δ Φ Γ [] τ.relax o → Val Δ Φ Γ (.lazy τ) o
  /-- A record literal. -/
  | record_mk {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} {o : Bool} :
      Args Δ Φ Γ (t :: fs.toList) o → Val Δ Φ Γ (.record t fs) o
  /-- A constructor of a union. -/
  | union_mk {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {b : Bool} {cs : Ctors ks bs}
      {h : UnionShape bs} {c : Ctor ks b} {o : Bool} : CtorIx cs c → Args Δ Φ Γ c.binds o →
      Val Δ Φ Γ (.union cs (h := h)) o
  /-- An array literal. -/
  | array_mk {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Bool} :
      Elems Δ Φ Γ t o → Val Δ Φ Γ (.array t) o
  /-- A list literal. -/
  | list_mk {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Bool} :
      Elems Δ Φ Γ t o → Val Δ Φ Γ (.list t) o
  /-- One layer in. -/
  | data_in {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) {o : Bool} :
      PExpr Δ Φ Γ ((Δ.block b).unfold j) o → Val Δ Φ Γ (.data ((Δ.block b).ref j)) o

/-- **The body of a closure, a delay or a loop**, binding `bs` (unknowns).  A closed body sees
    only the closed known values and `bs`; an open body sees everything, and needs an unknown
    in scope. -/
inductive Body {ks : List Nat} (Δ : DSig ks) :
    KCtx ks → UCtx ks → UCtx ks → Ty ks → Bool → Type where
  | closed {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} :
      Term Δ (KCtx.closedOnly Φ) bs τ [] → Body Δ Φ Γ bs τ false
  | opened {Φ : KCtx ks} {γ : UBinder ks} {Γ bs : UCtx ks} {τ : Ty ks} :
      Term Δ Φ (bs ++ γ :: Γ) τ [] → Body Δ Φ (γ :: Γ) bs τ true

/-- **Computations**: one step whose result is an unknown, named by `Term.letE`.  Each one has
    an open operand (or an open body), so none can be computed by the normaliser. -/
inductive Comp {ks : List Nat} (Δ : DSig ks) : KCtx ks → UCtx ks → Ty ks → Type where
  /-- A call; the function is an unknown or a known closure, and the function or the argument
      is open. -/
  | app {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Bool} :
      PExpr Δ Φ Γ (.fn σ τ) of → PExpr Δ Φ Γ σ oa → (of || oa) = true → Comp Δ Φ Γ τ
  /-- A neutral expression computed once and shared by name. -/
  | share {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} : Neu Δ Φ Γ τ → Comp Δ Φ Γ τ
  /-- `Nat.rec` with a non-dependent motive: the step binds the answer so far (index `0`)
      and the predecessor (index `1`). -/
  | nat_rec {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage} {on oz os : Bool} :
      PExpr Δ Φ Γ .nat on → PExpr Δ Φ Γ τ oz → Body Δ Φ Γ [⟨τ, u₁⟩, ⟨.nat, u₂⟩] τ os →
      (on || oz || os) = true → Comp Δ Φ Γ τ
  /-- `Array.foldl`: the step binds the element (index `0`) and the accumulator (index `1`). -/
  | array_foldl {Φ : KCtx ks} {Γ : UCtx ks} {t ρ : Ty ks} {u₁ u₂ : Usage} {oa oz os : Bool} :
      PExpr Δ Φ Γ (.array t) oa → PExpr Δ Φ Γ ρ oz → Body Δ Φ Γ [⟨t, u₁⟩, ⟨ρ, u₂⟩] ρ os →
      (oa || oz || os) = true → Comp Δ Φ Γ ρ
  /-- The fold of block `b`, answering `ρ i` at member `i`. -/
  | data_rec {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
      (us : Fin ((Δ.block b).k + 1) → Usage) {os oe : Bool}
      (branches : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ Φ Γ [⟨(Δ.block b).recBody ρ i, us i⟩] (ρ i) os)
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe → (oe || os) = true → Comp Δ Φ Γ (ρ j)
  /-- Course-of-values recursion over block `b`. -/
  | data_brec {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
      (k : Nat) (us : Fin ((Δ.block b).k + 1) → Usage) {os oe : Bool}
      (branches : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ Φ Γ [⟨(Δ.block b).brecBody ρ k i, us i⟩] (ρ i) os)
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe → (oe || os) = true → Comp Δ Φ Γ (ρ j)
  /-- The value of an open memoised delay (an unknown one, or an open known one). -/
  | thunk_force {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} :
      PExpr Δ Φ Γ (.thunk τ) true → Comp Δ Φ Γ τ.relax
  /-- The value of an open lazy delay. -/
  | lazy_force {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} :
      PExpr Δ Φ Γ (.lazy τ) true → Comp Δ Φ Γ τ.relax

/-- **Statements**: `let`s ending in a tail. -/
inductive Term {ks : List Nat} (Δ : DSig ks) : KCtx ks → UCtx ks → Ty ks → UCtx ks → Type where
  /-- The answer. -/
  | ret {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} {o : Bool} :
      PExpr Δ Φ Γ τ o → Term Δ Φ Γ τ js
  /-- `val %k := v; body`: share a value of known shape by name, used `u` times. -/
  | letV {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : UCtx ks} {o : Bool} (u : Usage) :
      Val Δ Φ Γ σ o → Term Δ (⟨σ, u, o⟩ :: Φ) Γ τ js → Term Δ Φ Γ τ js
  /-- `let x := c; body`: name the result of a computation, used `u` times. -/
  | letE {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : UCtx ks} (u : Usage) :
      Comp Δ Φ Γ σ → Term Δ Φ (⟨σ, u⟩ :: Γ) τ js → Term Δ Φ Γ τ js
  /-- Take a neutral record apart; the fields are used `us` times. -/
  | record_casesOn {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} {τ : Ty ks}
      {js : UCtx ks} (us : List Usage) :
      Neu Δ Φ Γ (.record t fs) → Term Δ Φ (UCtx.annot (t :: fs.toList) us ++ Γ) τ js →
      Term Δ Φ Γ τ js
  /-- A branch, in tail position. -/
  | branch {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} :
      Branch Δ Φ Γ τ js → Term Δ Φ Γ τ js
  /-- Jump to a join point. -/
  | jump {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} {σ : Ty ks} {o : Bool} :
      UVar js σ → PExpr Δ Φ Γ σ o → Term Δ Φ Γ τ js

/-- **Branches** on a neutral value, and the join points in front of them. -/
inductive Branch {ks : List Nat} (Δ : DSig ks) : KCtx ks → UCtx ks → Ty ks → UCtx ks → Type where
  | ite {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} :
      Neu Δ Φ Γ .bool → Term Δ Φ Γ τ js → Term Δ Φ Γ τ js → Branch Δ Φ Γ τ js
  | enum_casesOn {Φ : KCtx ks} {Γ : UCtx ks} {s : LeanEnumSchema} {τ : Ty ks} {js : UCtx ks} :
      Neu Δ Φ Γ (.enum s) → (Fin s.nOfConstructors → Term Δ Φ Γ τ js) → Branch Δ Φ Γ τ js
  | union_casesOn {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
      {h : UnionShape bs} {τ : Ty ks} {js : UCtx ks} :
      Neu Δ Φ Γ (.union cs (h := h)) → Branches Δ Φ Γ cs τ js → Branch Δ Φ Γ τ js
  /-- `join j (x : σ) := body; main`: `j` is used `u` times, `x` is used `uₓ` times. -/
  | join {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} (σ : Ty ks) (u uₓ : Usage) :
      Term Δ Φ (⟨σ, uₓ⟩ :: Γ) τ js → Branch Δ Φ Γ τ (⟨σ, u⟩ :: js) → Branch Δ Φ Γ τ js

/-- The branches of a union's case analysis; each binds the fields of its constructor. -/
inductive Branches {ks : List Nat} (Δ : DSig ks) :
    KCtx ks → UCtx ks → {bs : List Bool} → Ctors ks bs → Ty ks → UCtx ks → Type where
  | two {Φ : KCtx ks} {Γ : UCtx ks} {a b : Bool} {c : Ctor ks a} {d : Ctor ks b} {τ : Ty ks}
      {js : UCtx ks} (us₁ us₂ : List Usage) :
      Term Δ Φ (UCtx.annot c.binds us₁ ++ Γ) τ js → Term Δ Φ (UCtx.annot d.binds us₂ ++ Γ) τ js →
      Branches Δ Φ Γ (.two c d) τ js
  | cons {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {bs : List Bool} {c : Ctor ks a}
      {cs : Ctors ks bs} {τ : Ty ks} {js : UCtx ks} (us : List Usage) :
      Term Δ Φ (UCtx.annot c.binds us ++ Γ) τ js → Branches Δ Φ Γ cs τ js →
      Branches Δ Φ Γ (.cons c cs) τ js

end

end LeanScript.NTerm

end
