module

public import LeanScript.Term.Ctx
public import LeanScript.Term.Extern
public import LeanScript.Ty.DenBrec

@[expose] public section

set_option autoImplicit false

/-!
# Normal-form terms (proposal B): two contexts, *known* and *unknown*

The grammar of `LeanScript.Term`: A-normal terms in which **every redex that could be
evaluated has been**, by construction, while a redex that cannot be evaluated (because it is
stuck on an unknown) is kept, and its operands are shared rather than duplicated.

```
Neu     Φ Γ ℓ   ::= var x                        -- x : UVar Γ τ ℓ, an unknown
                  | data_out b j Neu | cond Neu PExpr PExpr
                  | extern e Args                -- at least one open argument
PExpr   Φ Γ o   ::= neu Neu                      -- o = some ℓ
                  | kvar k                       -- k : KVar Φ τ o, a known value by name
                  | lit | enum_mk                -- o = none
                  | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
                  | data_in b j PExpr
Val   d Φ Γ o   ::= lam Body | thunk_mk Body | lazy_mk Body
                  | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
                  | data_in b j PExpr
Body  d Φ Γ bs o ::= closed (Term (d+1) Φ.closedOnly bs)   -- o = none: sees no unknown
                   | opened (Term (d+1) Φ (bs ++ Γ) (some m)) (m ≤ d)
                                                 -- o = some m: mentions something outside
Comp  d Φ Γ ℓ   ::= app PExpr PExpr                -- at least one operand open
                  | share Neu
                  | nat_rec PExpr PExpr Body | array_foldl PExpr PExpr Body
                  | data_rec … Body … PExpr | data_brec … Body … PExpr
                                                 -- at least one operand or the body open
                  | thunk_force (PExpr (some ℓ)) | lazy_force (PExpr (some ℓ))
Term  d Φ Γ js o ::= ret PExpr
                   | letV (u : 1|ω) Val Term      -- extends Φ
                   | letE (u : 1|ω) Comp Term     -- extends Γ, at level d
                   | record_casesOn us Neu Term   -- extends Γ with the fields (us : 0|1|ω)
                   | branch Branch
                   | jump j PExpr
Branch d Φ Γ js ℓ ::= ite Neu Term Term | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
                   | join σ (u : 1|ω) (uₓ : 0|1|ω) Term Branch
                                                 -- a join point, only in front of a branch
```

**Known and unknown.**  A statement has two variable contexts (`LeanScript.Term.Ctx`):
`Φ`, the *known* values, bound by `letV` to a value of known shape; and `Γ`, the *unknowns*,
bound by `letE` (the result of a computation), by case analyses, and as parameters of
closures, loops and join points.  Only an unknown is neutral (`Neu.var` takes a `UVar Γ`), so
a known value is never taken apart, called or forced: the normaliser does that itself.  A
known value can be passed on by name (`PExpr.kvar`), which is how a closure, a delay or a
data literal is **shared** instead of copied.

**Open and closed: levels.**  Every syntactic class is indexed by the smallest *level* of
the unknowns it mentions (`Lvl := Option Nat`; `none` means that it mentions no unknown: it
is **closed**; `some ℓ` means that it is **open**).  The level of an unknown is the depth at
which it is bound (`UBinder.lv`): a statement at depth `d` (`Term Δ d …`) binds its unknowns
at level `d`, the parameters of a closure, delay or loop body inside it at level `d + 1`.  The
level is computed by the constructors (`neu` has the level of the neutral expression, `lit`
is closed, a constructor has the smallest level of its arguments, a known variable has the
level recorded in `Φ`, a `let` has the smallest level of its two parts), so it cannot lie.

Neutral expressions, computations and branches are always open, so their level is a `Nat`.

**Bodies, exactly.**  The body of a closure, a delay or a loop, at depth `d`, is typed at depth
`d + 1`, and is

* **closed** (`Body.closed`): it sees only the closed known values and its own parameters;
* **open** (`Body.opened`): it sees everything, and its level `m` is `≤ d`: it *actually*
  mentions something bound outside of it (an outer unknown, or an open known value).

So the openness of a body is **exact**: a body that mentions nothing from outside cannot be
marked open (its level would be `d + 1` or more, or `none`), and one that does cannot be marked
closed (it cannot even be typed in the closed view).

**The rule.**  Every elimination needs an open operand:

* `extern e args h` needs `h : o = some ℓ` for `args : Args σs o`: at least one open argument;
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
at all: it is a chain of `letV`s ending in `ret v` (`LeanScript.Term.closed_isValue`).

**Join points.**  A join point is only allowed in front of a branch (`Branch.join`), so a
join point whose continuation is a known jump (`join j x := b; jump j v`, a redex) cannot be
written.

**Usages.**  Definition binders (`letV`, `letE`, the join point of `join`) carry a `Usage1ω`
(`1 | ω`); pattern binders (the fields of a case analysis, the parameters of closures, loop
bodies and join points) carry a `Usage01ω` (`0 | 1 | ω`), and one annotated `0` cannot be
referenced.
-/

namespace LeanScript

/-! ## Layer 1: pure expressions -/

mutual

/-- **Neutral expressions**: stuck on an unknown.  A variable of `Γ` (never of `Φ`), an
    elimination of a neutral value, or a call of an extern with at least one open argument.
    `ℓ` is the smallest level they mention. -/
inductive Neu {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Ty ks → Nat → Type where
  /-- An unknown. -/
  | var {τ : Ty ks} {ℓ : Nat} : UVar Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  /-- One layer out of a neutral value of member `j` of block `b`. -/
  | data_out (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) {ℓ : Nat} :
      Neu Δ Φ Γ (.data ((Δ.block b).ref j)) ℓ → Neu Δ Φ Γ ((Δ.block b).unfold j) ℓ
  /-- The pure conditional on a neutral condition. -/
  | cond {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl} : Neu Δ Φ Γ .bool ℓ → PExpr Δ Φ Γ τ o₁ →
      PExpr Δ Φ Γ τ o₂ → Neu Δ Φ Γ τ (Lvl.meetL ℓ (Lvl.meet o₁ o₂))
  /-- A call of an extern with at least one open argument. -/
  | extern {σs : List (Ty ks)} {τ : Ty ks} {o : Lvl} {ℓ : Nat} (e : Extern ks σs τ) :
      Args Δ Φ Γ σs o → o = some ℓ → Neu Δ Φ Γ τ ℓ

/-- **Pure expressions** of type `τ` and level `o`. -/
inductive PExpr {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    Ty ks → Lvl → Type where
  /-- A neutral expression. -/
  | neu {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → PExpr Δ Φ Γ τ (some ℓ)
  /-- A known value, by name. -/
  | kvar {τ : Ty ks} {o : Lvl} : KVar Φ τ o → PExpr Δ Φ Γ τ o
  /-- A literal of a leaf type. -/
  | lit (p : LeanPrimTy) (v : p.denote) : PExpr Δ Φ Γ (.prim p) none
  /-- A constructor of an enum. -/
  | enum_mk (s : LeanEnumSchema) : Fin s.nOfConstructors → PExpr Δ Φ Γ (.enum s) none
  /-- A record, from its fields. -/
  | record_mk {t : Ty ks} {fs : Fields ks} {o : Lvl} : Args Δ Φ Γ (t :: fs.toList) o →
      PExpr Δ Φ Γ (.record t fs) o
  /-- A constructor of a union, from its fields. -/
  | union_mk {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {h : UnionShape bs}
      {c : Ctor ks b} {o : Lvl} : CtorIx cs c → Args Δ Φ Γ c.binds o →
      PExpr Δ Φ Γ (.union cs (h := h)) o
  /-- An array literal. -/
  | array_mk {t : Ty ks} {o : Lvl} : Elems Δ Φ Γ t o → PExpr Δ Φ Γ (.array t) o
  /-- A list literal. -/
  | list_mk {t : Ty ks} {o : Lvl} : Elems Δ Φ Γ t o → PExpr Δ Φ Γ (.list t) o
  /-- One layer in. -/
  | data_in (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) {o : Lvl} :
      PExpr Δ Φ Γ ((Δ.block b).unfold j) o → PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) o

/-- Arguments; their level is the smallest of their levels. -/
inductive Args {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    List (Ty ks) → Lvl → Type where
  | nil : Args Δ Φ Γ [] none
  | cons {σ : Ty ks} {σs : List (Ty ks)} {o₁ o₂ : Lvl} : PExpr Δ Φ Γ σ o₁ →
      Args Δ Φ Γ σs o₂ → Args Δ Φ Γ (σ :: σs) (Lvl.meet o₁ o₂)

/-- The elements of an array or list literal; their level is the smallest of their levels. -/
inductive Elems {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :
    Ty ks → Lvl → Type where
  | nil {t : Ty ks} : Elems Δ Φ Γ t none
  | cons {t : Ty ks} {o₁ o₂ : Lvl} : PExpr Δ Φ Γ t o₁ → Elems Δ Φ Γ t o₂ →
      Elems Δ Φ Γ t (Lvl.meet o₁ o₂)

end

/-! ## Layers 2 and 3: values, bodies, computations, statements -/

mutual

/-- **Values of known shape**, bound by `Term.letV` into the known context, at depth `d`. -/
inductive Val {ks : List Nat} (Δ : DSig ks) : Nat → KCtx ks → UCtx ks → Ty ks → Lvl → Type where
  /-- A closure; its parameter is an unknown of the body, at level `d + 1`. -/
  | lam {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω} {o : Lvl} :
      Body Δ d Φ Γ [⟨σ, u, d + 1⟩] τ o → Val Δ d Φ Γ (.fn σ τ) o
  /-- A memoised delay. -/
  | thunk_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Lvl} :
      Body Δ d Φ Γ [] τ.relax o → Val Δ d Φ Γ (.thunk τ) o
  /-- A delay that is recomputed every time. -/
  | lazy_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Lvl} :
      Body Δ d Φ Γ [] τ.relax o → Val Δ d Φ Γ (.lazy τ) o
  /-- A record literal. -/
  | record_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} {o : Lvl} :
      Args Δ Φ Γ (t :: fs.toList) o → Val Δ d Φ Γ (.record t fs) o
  /-- A constructor of a union. -/
  | union_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {b : Bool}
      {cs : Ctors ks bs} {h : UnionShape bs} {c : Ctor ks b} {o : Lvl} : CtorIx cs c →
      Args Δ Φ Γ c.binds o → Val Δ d Φ Γ (.union cs (h := h)) o
  /-- An array literal. -/
  | array_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} :
      Elems Δ Φ Γ t o → Val Δ d Φ Γ (.array t) o
  /-- A list literal. -/
  | list_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} :
      Elems Δ Φ Γ t o → Val Δ d Φ Γ (.list t) o
  /-- One layer in. -/
  | data_in {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
      {o : Lvl} : PExpr Δ Φ Γ ((Δ.block b).unfold j) o →
      Val Δ d Φ Γ (.data ((Δ.block b).ref j)) o

/-- **The body of a closure, a delay or a loop** at depth `d`, binding `bs` (unknowns, at
    level `d + 1`).  A closed body sees only the closed known values and `bs`; an open body
    sees everything, and mentions something bound outside of it (its level `m` is `≤ d`). -/
inductive Body {ks : List Nat} (Δ : DSig ks) :
    Nat → KCtx ks → UCtx ks → UCtx ks → Ty ks → Lvl → Type where
  | closed {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
      Term Δ (d + 1) (KCtx.closedOnly Φ) bs τ [] o → Body Δ d Φ Γ bs τ none
  | opened {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {m : Nat} :
      Term Δ (d + 1) Φ (bs ++ Γ) τ [] (some m) → m ≤ d → Body Δ d Φ Γ bs τ (some m)

/-- **Computations**: one step whose result is an unknown, named by `Term.letE`.  Each one has
    an open operand (or an open body), so none can be computed by the normaliser; `ℓ` is the
    smallest level they mention. -/
inductive Comp {ks : List Nat} (Δ : DSig ks) : Nat → KCtx ks → UCtx ks → Ty ks → Nat → Type where
  /-- A call; the function is an unknown or a known closure, and the function or the argument
      is open. -/
  | app {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Lvl} {ℓ : Nat} :
      PExpr Δ Φ Γ (.fn σ τ) of → PExpr Δ Φ Γ σ oa → Lvl.meet of oa = some ℓ → Comp Δ d Φ Γ τ ℓ
  /-- A neutral expression computed once and shared by name. -/
  | share {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
      Neu Δ Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  /-- `Nat.rec` with a non-dependent motive: the step binds the answer so far (index `0`)
      and the predecessor (index `1`). -/
  | nat_rec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage01ω}
      {on oz os : Lvl} {ℓ : Nat} :
      PExpr Δ Φ Γ .nat on → PExpr Δ Φ Γ τ oz →
      Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ os →
      Lvl.meet (Lvl.meet on oz) os = some ℓ → Comp Δ d Φ Γ τ ℓ
  /-- `Array.foldl`: the step binds the element (index `0`) and the accumulator (index `1`). -/
  | array_foldl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t ρ : Ty ks} {u₁ u₂ : Usage01ω}
      {oa oz os : Lvl} {ℓ : Nat} :
      PExpr Δ Φ Γ (.array t) oa → PExpr Δ Φ Γ ρ oz →
      Body Δ d Φ Γ [⟨t, u₁, d + 1⟩, ⟨ρ, u₂, d + 1⟩] ρ os →
      Lvl.meet (Lvl.meet oa oz) os = some ℓ → Comp Δ d Φ Γ ρ ℓ
  /-- The fold of block `b`, answering `ρ i` at member `i`. -/
  | data_rec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks)
      (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (us : Fin ((Δ.block b).k + 1) → Usage01ω)
      {os : Fin ((Δ.block b).k + 1) → Lvl} {oe : Lvl} {ℓ : Nat}
      (branches : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ d Φ Γ [⟨(Δ.block b).recBody ρ i, us i, d + 1⟩] (ρ i) (os i))
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe →
      Lvl.meet oe (Lvl.meetFin _ os) = some ℓ → Comp Δ d Φ Γ (ρ j) ℓ
  /-- Course-of-values recursion over block `b`. -/
  | data_brec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks)
      (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat) (us : Fin ((Δ.block b).k + 1) → Usage01ω)
      {os : Fin ((Δ.block b).k + 1) → Lvl} {oe : Lvl} {ℓ : Nat}
      (branches : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ d Φ Γ [⟨(Δ.block b).brecBody ρ k i, us i, d + 1⟩] (ρ i) (os i))
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe →
      Lvl.meet oe (Lvl.meetFin _ os) = some ℓ → Comp Δ d Φ Γ (ρ j) ℓ
  /-- The value of an open memoised delay (an unknown one, or an open known one). -/
  | thunk_force {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {ℓ : Nat} :
      PExpr Δ Φ Γ (.thunk τ) (some ℓ) → Comp Δ d Φ Γ τ.relax ℓ
  /-- The value of an open lazy delay. -/
  | lazy_force {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {ℓ : Nat} :
      PExpr Δ Φ Γ (.lazy τ) (some ℓ) → Comp Δ d Φ Γ τ.relax ℓ

/-- **Statements** at depth `d`: `let`s ending in a tail. -/
inductive Term {ks : List Nat} (Δ : DSig ks) :
    Nat → KCtx ks → UCtx ks → Ty ks → JCtx ks → Lvl → Type where
  /-- The answer. -/
  | ret {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
      PExpr Δ Φ Γ τ o → Term Δ d Φ Γ τ js o
  /-- `val %k := v; body`: share a value of known shape by name, used `u` times. -/
  | letV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
      (u : Usage1ω) :
      Val Δ d Φ Γ σ o → Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o' →
      Term Δ d Φ Γ τ js (Lvl.meet o o')
  /-- `let x := c; body`: name the result of a computation, used `u` times. -/
  | letE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl}
      (u : Usage1ω) :
      Comp Δ d Φ Γ σ ℓ → Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o' →
      Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o'))
  /-- Take a neutral record apart; the fields are used `us` times. -/
  | record_casesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
      {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω) :
      Neu Δ Φ Γ (.record t fs) ℓ → Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o' →
      Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o'))
  /-- A branch, in tail position. -/
  | branch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
      Branch Δ d Φ Γ τ js ℓ → Term Δ d Φ Γ τ js (some ℓ)
  /-- Jump to a join point. -/
  | jump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {σ : Ty ks} {o : Lvl} :
      JVar js σ → PExpr Δ Φ Γ σ o → Term Δ d Φ Γ τ js o

/-- **Branches** on a neutral value, and the join points in front of them. -/
inductive Branch {ks : List Nat} (Δ : DSig ks) :
    Nat → KCtx ks → UCtx ks → Ty ks → JCtx ks → Nat → Type where
  | ite {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} :
      Neu Δ Φ Γ .bool ℓ → Term Δ d Φ Γ τ js o₁ → Term Δ d Φ Γ τ js o₂ →
      Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))
  | enum_casesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {s : LeanEnumSchema} {τ : Ty ks}
      {js : JCtx ks} {ℓ : Nat} {os : Fin s.nOfConstructors → Lvl} :
      Neu Δ Φ Γ (.enum s) ℓ → ((i : Fin s.nOfConstructors) → Term Δ d Φ Γ τ js (os i)) →
      Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meetFin _ os))
  | union_casesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
      {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o : Lvl} :
      Neu Δ Φ Γ (.union cs (h := h)) ℓ → Branches Δ d Φ Γ cs τ js o →
      Branch Δ d Φ Γ τ js (Lvl.meetL ℓ o)
  /-- `join j (x : σ) := body; main`: `j` is used `u` times, `x` is used `uₓ` times. -/
  | join {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
      (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) :
      Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o → Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ →
      Branch Δ d Φ Γ τ js (Lvl.meetL ℓ o)

/-- The branches of a union's case analysis; each binds the fields of its constructor. -/
inductive Branches {ks : List Nat} (Δ : DSig ks) :
    Nat → KCtx ks → UCtx ks → {bs : List Bool} → Ctors ks bs → Ty ks → JCtx ks → Lvl → Type where
  | two {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a b : Bool} {c₁ : Ctor ks a} {c₂ : Ctor ks b}
      {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us₁ us₂ : List Usage01ω) :
      Term Δ d Φ (UCtx.annot d c₁.binds us₁ ++ Γ) τ js o₁ →
      Term Δ d Φ (UCtx.annot d c₂.binds us₂ ++ Γ) τ js o₂ →
      Branches Δ d Φ Γ (.two c₁ c₂) τ js (Lvl.meet o₁ o₂)
  | cons {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {bs : List Bool} {c : Ctor ks a}
      {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us : List Usage01ω) :
      Term Δ d Φ (UCtx.annot d c.binds us ++ Γ) τ js o₁ → Branches Δ d Φ Γ cs τ js o₂ →
      Branches Δ d Φ Γ (.cons c cs) τ js (Lvl.meet o₁ o₂)

end

end LeanScript

end
