module

public import LeanScript.Ty.DenBrec
public import LeanScript.Term.PExpr
public import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# `Term`: A-normal terms over a datatype signature, in three layers

The one grammar of terms of the language.  `#leanscript_to_term` (`LeanScript.TermElab.ToTerm`)
translates Lean definitions to it.  It follows the three layers of the `PCL` grammar
(`proposals/AnfSplitProposals.md`, proposal 1), without its proof-carrying parts:

```
Neu   ::= var | data_out b j Neu | cond Neu PExpr PExpr | extern e Args
PExpr ::= neu Neu | lit | enum_mk | record_mk Args | union_mk ix Args | array_mk Elems
        | data_in b j PExpr
Comp  ::= app PExpr PExpr | lam Term | share PExpr
        | nat_rec PExpr PExpr Term | array_foldl PExpr PExpr Term
        | data_rec b ρ Termᵢ j PExpr | data_brec b ρ k Termᵢ j PExpr
        | thunk_mk Term | thunk_force PExpr | lazy_mk Term | lazy_force PExpr
Term  ::= ret PExpr | letE Comp Term | record_casesOn Neu Term
        | ite Neu Term Term | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
        | join σ Term Term | jump j PExpr
```

* `PExpr Δ Γ τ` (with the lists `Args` and `Elems`) — **pure expressions**: variables,
  literals, constructors, one layer in or out of a recursive datatype, the pure conditional
  `cond` and the calls of externs (`PExpr.extern e args`, `e` an entry of the catalogue
  `LeanInitPureExtern`).  They bind nothing and never branch in the control flow of the term.  `PExpr` is an ordinary inductive, not mutual with the two other layers.
* `Neu Δ Γ τ` — the **neutral** pure expressions, those whose head is not an introduction
  form: a variable, `data_out` or `cond` of a neutral expression, or a call of an extern.  A pure
  expression is a neutral one (`PExpr.neu`) or an introduction form (a literal, a
  constructor, `data_in`).  `PExpr.var`, `PExpr.data_out`, `PExpr.cond` and `PExpr.extern`
  are abbreviations of `PExpr.neu` of the neutral forms.
* `Comp Δ Γ τ` — **computations**: one step whose value a `let` names: an application, a
  closure, a shared pure value (a call of an extern computed once, say), a fold, a delay.
* `Term Δ Γ τ js` — **statements** (`PCL`'s `Expr`): `let`s of computations ending in a tail.
  `js` are the join points in scope (`JCtx`): the types of their parameters.

The grammar is **strictly A-normal**: every operand of a computation or a statement is a pure
expression, so every application, closure, fold and delay is named by a `Term.letE`, in
the order it is evaluated (a call of an extern is a pure expression, which `Comp.share` names
when its value is to be computed once).  It is **B-normal** (branching normal): a branch (`ite`,
`enum_casesOn`, `union_casesOn`) is always the tail of a statement; a branch in the middle of
a computation is written with a **join point** for the rest of it
(`join j x := rest; if c then …; jump j a else …; jump j b`).  There is no β-redex either:
the function of an application is a pure expression and a closure is a computation, so
`app (lam b) a` cannot be written.  There is no **ι-redex** (the elimination of an explicitly
constructed value) either: everything that takes a value apart — `data_out`, the condition of
`cond` and `ite`, the scrutinee of `record_casesOn`, `enum_casesOn` and `union_casesOn` — takes
a *neutral* expression (`Neu`), which is never a literal nor a constructor.  So
`data_out b j (data_in b j e)`, `record_casesOn (record_mk args) body`,
`union_casesOn (union_mk ix args) brs`, `enum_casesOn (enum_mk s i) brs` and
`cond (lit .bool true) a b` are ill-typed.  (The folds `nat_rec`, `array_foldl`, `data_rec` and
`data_brec` are loops, not one-step eliminations, and take any pure expression: unrolling a
loop over a literal is not a local rewrite.  A value bound by a `let` is a variable, hence
neutral: A-normal form never looks through a `let`.)  All of this is enforced by the types; in addition the
translator and the notation never `share` (or bind) a trivial pure expression
(`PExpr.isTrivial`: a variable or a literal), which is used in place.

A join point needs no predicate (there are no path conditions): its scope is only the list of
the types of the join points, and its value is a closure over its definition environment.
The bodies of closures, folds and delays are statements with no join point in scope (`[]`),
so a loop never jumps out to the enclosing continuation.

A statement is indexed by the program's datatype signature `Δ : DSig ks`, a context `Γ` of
closed types, its type and its join points.  Recursive datatypes have three term formers and a
course-of-values form of the fold, available at every block of the signature:

* `PExpr.data_in b j e` — one layer in: `e` is a value of member `j`'s unfolded body;
* `PExpr.data_out b j e` — one layer out; the unfolded body is again a closed type, so it
  is taken apart with the ordinary `Term.record_casesOn` / `Term.union_casesOn`;
* `Comp.data_rec b ρ branches j e` — the fold of a whole block, with one answer type
  `ρ i` per member and one branch per member.  Branch `i` binds member `i`'s body in which
  every hole `i'` is the pair of the subvalue and the answer at it;
* `Comp.data_brec b ρ k branches j e` — course-of-values recursion, the fold whose branches
  see the answers `k + 1` levels down (`LeanScript.DSig.dataBrec`).

There is no fixpoint and no fuel: every loop is a fold (`data_rec`, `nat_rec`,
`array_foldl`), so the evaluators (`LeanScript.Term.eval`) are total and structural.

Leaf operations are **externs**: an entry `e : Extern ks σs τ` of the catalogue
`LeanInitPureExtern` (`LeanScript.LeanInitPureExterns`), called on the pure expressions of its
arguments by `Neu.extern e args` (`PExpr.extern`).  There is one kind of extern: every entry of
the catalogue is a pure function of the values of its arguments, whether it is a machine
operation (`lean_nat_add`), a function on strings or arrays, or builds a leaf value
(`lean_mk_empty_array_with_capacity__Array_emptyWithCapacity`).  Every entry has a shorthand in
the namespaces `PExpr` and `Neu` (`LeanScript.Term.ExternShorthands`):
`PExpr.lean_string_any (.lit .string "12345") f` is
`.neu (.extern .lean_string_any (.cons (.lit .string "12345") (.cons f .nil)))`.  Its value is
the Lean function the entry stands for (`LeanScript.Extern.eval`).  The types of the
arguments and of the result are types of the language: a proposition is `.bool`, and a proof
that the Lean function takes is erased — the evaluator decides it on the values of the
arguments (`if h : i < a.size then a.set i x h else a`); in a term translated from a Lean
program it always holds (the program had to prove it).  Because a closure (a `Term`) and the
branches of `enum_casesOn`/`data_rec` are functions, the layers `Comp` and `Term` have no
decidable equality.

Renaming, weakening and substitution of variables, with the facts that they commute with
evaluation, are in `LeanScript.Term.TermSubst`.

The files: the contexts, variables and other definitions shared by the layers are in
`LeanScript.Term.Common`; layer 1 (`Neu`, `PExpr`, `Args`, `Elems`, one mutual block) is in
`LeanScript.Term.PExpr`; layers 2 and 3 (`Comp`, `Term`, `Branches`, the other mutual block)
are here.
-/

namespace LeanScript

/-! ## Layers 2 and 3: computations and statements -/

mutual

/-- **Layer 2, computations** (`PCL`'s `Comp`): one step whose value a `Term.letE` names.
    Every operand is a pure expression; the bodies of a closure, a fold or a delay are
    statements with no join point in scope (`[]`), so a body never jumps out of itself. -/
inductive Comp {ks : List Nat} (Δ : DSig ks) : Ctx ks → Ty ks → Type where
  /-- Application of a function value to an argument. -/
  | app {Γ : Ctx ks} {σ τ : Ty ks} : PExpr Δ Γ (.fn σ τ) → PExpr Δ Γ σ → Comp Δ Γ τ
  /-- `fun x => body`: a `let`-bound closure. -/
  | lam {Γ : Ctx ks} {σ τ : Ty ks} : Term Δ (σ :: Γ) τ [] → Comp Δ Γ (.fn σ τ)
  /-- A pure expression computed once and shared by name (never a trivial one, a variable or
      a literal, `PExpr.isTrivial`: those are used in place).  This is how the value of a
      call of an extern (`Neu.extern`) is computed once rather than wherever it is used. -/
  | share {Γ : Ctx ks} {τ : Ty ks} : PExpr Δ Γ τ → Comp Δ Γ τ
  /-- `Nat.rec` with a non-dependent motive: the successor branch binds the predecessor
      (index `1`) and the answer at it (index `0`). -/
  | nat_rec {Γ : Ctx ks} {τ : Ty ks} : PExpr Δ Γ .nat → PExpr Δ Γ τ →
      Term Δ (τ :: .nat :: Γ) τ [] → Comp Δ Γ τ
  /-- `Array.foldl`: the step binds the element (index `0`) and the accumulator (index `1`). -/
  | array_foldl {Γ : Ctx ks} {t ρ : Ty ks} : PExpr Δ Γ (.array t) → PExpr Δ Γ ρ →
      Term Δ (t :: ρ :: Γ) ρ [] → Comp Δ Γ ρ
  /-- The fold of block `b`, answering `ρ i` at member `i`.  Branch `i` binds member `i`'s
      body in which every hole `i'` is the pair of the subvalue and the answer at it. -/
  | data_rec {Γ : Ctx ks} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
      (branches : (i : Fin ((Δ.block b).k + 1)) → Term Δ ((Δ.block b).recBody ρ i :: Γ) (ρ i) [])
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Γ (.data ((Δ.block b).ref j)) → Comp Δ Γ (ρ j)
  /-- Course-of-values recursion over block `b`, answering `ρ i` at member `i` and looking
      `k + 1` levels down: branch `i` binds member `i`'s body in which every hole is the
      window of depth `k` of the subvalue (`DSig.Block.win`: the subvalue, the answer at it
      and, below depth `0`, its own body of windows one level shallower).  `k = 0` is
      `data_rec`. -/
  | data_brec {Γ : Ctx ks} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
      (branches : (i : Fin ((Δ.block b).k + 1)) →
        Term Δ ((Δ.block b).brecBody ρ k i :: Γ) (ρ i) [])
      (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Γ (.data ((Δ.block b).ref j)) → Comp Δ Γ (ρ j)
  /-- A memoised delay (`Thunk.mk`) of a computation.  A delay denotes its value, so this
      evaluates to the value of the body: it only matters for printing. -/
  | thunk_mk {Γ : Ctx ks} {τ : Ty ks false} : Term Δ Γ τ.relax [] → Comp Δ Γ (.thunk τ)
  /-- The value a memoised delay holds (`Thunk.get`); evaluates to the value of the
      argument. -/
  | thunk_force {Γ : Ctx ks} {τ : Ty ks false} : PExpr Δ Γ (.thunk τ) → Comp Δ Γ τ.relax
  /-- A delay that is recomputed every time (`fun (_ : Unit) => e`) of a computation;
      evaluates to the value of the body: it only matters for printing. -/
  | lazy_mk {Γ : Ctx ks} {τ : Ty ks false} : Term Δ Γ τ.relax [] → Comp Δ Γ (.lazy τ)
  /-- The value a lazy delay holds (`f ()`); evaluates to the value of the argument. -/
  | lazy_force {Γ : Ctx ks} {τ : Ty ks false} : PExpr Δ Γ (.lazy τ) → Comp Δ Γ τ.relax

/-- **Layer 3, statements** (`PCL`'s `Expr`): a term of type `τ` in context `Γ`, over the
    datatype signature `Δ`, with the join points `js` in scope.  A statement is a chain of
    `let`s of computations (and of record destructurings) ending in a tail: a pure answer,
    a branch, a join point or a jump. -/
inductive Term {ks : List Nat} (Δ : DSig ks) : Ctx ks → Ty ks → JCtx ks → Type where
  /-- The answer: a pure expression. -/
  | ret {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks} : PExpr Δ Γ τ → Term Δ Γ τ js
  /-- `let x := c; body`: `x` is de Bruijn index `0` of `body`. -/
  | letE {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} : Comp Δ Γ σ → Term Δ (σ :: Γ) τ js →
      Term Δ Γ τ js
  /-- Take a record apart: the body binds the fields, the first field innermost (index `0`).
      A record has one constructor, so this does not branch. -/
  | record_casesOn {Γ : Ctx ks} {t : Ty ks} {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} :
      Neu Δ Γ (.record t fs) → Term Δ ((t :: fs.toList) ++ Γ) τ js → Term Δ Γ τ js
  /-- `if c then t else e`, in tail position. -/
  | ite {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks} : Neu Δ Γ .bool → Term Δ Γ τ js →
      Term Δ Γ τ js → Term Δ Γ τ js
  /-- Case analysis of an enum, in tail position: one branch per constructor. -/
  | enum_casesOn {Γ : Ctx ks} {s : LeanEnumSchema} {τ : Ty ks} {js : JCtx ks} :
      Neu Δ Γ (.enum s) → (Fin s.nOfConstructors → Term Δ Γ τ js) → Term Δ Γ τ js
  /-- Case analysis of a union, in tail position: each branch binds the fields of its
      constructor. -/
  | union_casesOn {Γ : Ctx ks} {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs}
      {τ : Ty ks} {js : JCtx ks} :
      Neu Δ Γ (.union cs (h := h)) → Branches Δ Γ cs τ js → Term Δ Γ τ js
  /-- `join j (x : σ) := body; main`: the join point `j` (index `0` of the join points of
      `main`) finishes the statement from a value `x` of type `σ`.  This is how a branch that
      is not in tail position is written. -/
  | join {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks} (σ : Ty ks) : Term Δ (σ :: Γ) τ js →
      Term Δ Γ τ (σ :: js) → Term Δ Γ τ js
  /-- Jump to a join point with the value of its parameter. -/
  | jump {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks} {σ : Ty ks} : JVar js σ → PExpr Δ Γ σ →
      Term Δ Γ τ js

/-- The branches of a union's case analysis, following its constructors. -/
inductive Branches {ks : List Nat} (Δ : DSig ks) :
    Ctx ks → {bs : List Bool} → Ctors ks bs → Ty ks → JCtx ks → Type where
  | two {Γ : Ctx ks} {a b : Bool} {c : Ctor ks a} {d : Ctor ks b} {τ : Ty ks} {js : JCtx ks} :
      Term Δ (c.binds ++ Γ) τ js → Term Δ (d.binds ++ Γ) τ js → Branches Δ Γ (.two c d) τ js
  | cons {Γ : Ctx ks} {a : Bool} {bs : List Bool} {c : Ctor ks a} {cs : Ctors ks bs}
      {τ : Ty ks} {js : JCtx ks} :
      Term Δ (c.binds ++ Γ) τ js → Branches Δ Γ cs τ js → Branches Δ Γ (.cons c cs) τ js

end

/-- `let x := c; x`: the statement whose answer is the value of the computation `c`.  The
    normaliser (`LeanScript.TermElab.Anf`) writes a computation in tail position with it, so that the
    expected type of the statement reaches `c` when it is elaborated; the notation and the
    translator then unfold it, so it never remains in a term. -/
abbrev Term.ofComp {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks}
    (c : Comp Δ Γ τ) : Term Δ Γ τ js :=
  .letE c (.ret (.var .head))

end LeanScript

end
