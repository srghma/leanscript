module

public import LeanScript.Ty
public import LeanScript.LeanInitPureExterns

@[expose] public section

namespace LeanScript

/-!
# The catalogue of functions the runtime implements, at `Ty`

`LeanScript.LeanInitPureExterns` lists the pure `@[extern]` functions of Lean's `Init`,
split by arity and by how much of the type language each of them needs: the families
whose argument and result types are *terminal* (`LeanInitPureExtern1OnlyPrim`, …) are
indexed by `LeanPrimTy`, and the ones that are polymorphic, or mention an array, a list,
a thunk, an `Option` or a product, are indexed by a type language `X` handed to them.
That split is what makes the catalogue reusable: this module instantiates it at `Ty`,
and a later type language can instantiate the very same families at its own types.

`Extern σs τ` is the result: one entry per function, carrying the types of its arguments
and its result.  A term applies one with `Term.extern`, whose type is the **curried**
arrow `σ₁ ⇒ ⋯ ⇒ σₙ ⇒ τ`, so an extern can be applied to one argument at a time and can
neither be applied to too many arguments nor to arguments of the wrong types.

What each entry *means* — the Lean function on the values its arguments hold — is in
`LeanScript.ExternEval`, `LeanScript.ExternEval1`, `LeanScript.ExternEval2` and
`LeanScript.ExternEvalMisc`, and `LeanScript.Expr.Step` runs it (`EXTERN_EVALUATION.md`).
-/

/-- A terminal type is a type. -/
instance : Coe LeanPrimTy Ty := ⟨Ty.prim⟩

/-- An array/list/task/promise/thunk/lazy of a terminal type is a type. -/
instance : Coe (LeanPrimTyCovariant LeanPrimTy) Ty :=
  ⟨fun c => Ty.primCovariant (c.map Ty.prim)⟩

/-- An array/list/task/promise/thunk/lazy of a type is a type. -/
instance : Coe (LeanPrimTyCovariant Ty) Ty := ⟨Ty.primCovariant⟩

/-- A one-argument function between terminal types, as a `Ty`. -/
abbrev primFn1 (a b : LeanPrimTy) : Ty := .fn (.prim a) (.prim b)

/-- A two-argument (curried) function between terminal types, as a `Ty`. -/
abbrev primFn2 (a b c : LeanPrimTy) : Ty := .fn (.prim a) (.fn (.prim b) (.prim c))

/-- A product of two terminal types, as a `Ty`. -/
abbrev primProd (a b : LeanPrimTy) : Ty := Ty.prod (.prim a) (.prim b)

/-- The one-argument polymorphic externs, at `Ty`. -/
abbrev Extern1At := @LeanInitPureExtern1 Ty _ _ _ Ty.option primProd

/-- The two-argument polymorphic externs, at `Ty`. -/
abbrev Extern2At := @LeanInitPureExtern2 Ty _ _ _ Ty.option primFn1

/-- The three-argument polymorphic externs, at `Ty`. -/
abbrev Extern3At :=
  @LeanInitPureExtern3 Ty _ _ primFn1 primFn2 Ty.byteArray Ty.floatArray

/-- The four-argument polymorphic externs, at `Ty`. -/
abbrev Extern4At := @LeanInitPureExtern4 Ty _ _ Ty.fn

/-- The six-argument polymorphic externs, at `Ty`. -/
abbrev Extern6At := @LeanInitPureExtern6 Ty Ty.byteArray

/-- A function of the runtime, with the types of its arguments and of its result.  The
    constructors are the families of `LeanScript.LeanInitPureExterns`, instantiated here. -/
inductive Extern : List Ty → Ty → Type where
  /-- A pure constant of the runtime (`lean_version_get_major`, …).  It carries no
      argument, and the type language has no function type of no arguments, so it is a
      *delayed* value: `Ty.lazy`, which `Term.lazyForce` runs. -/
  | const : ∀ {p : LeanPrimTy}, LeanInitPureExternLazy p → Extern [] (Ty.lazy (.prim p))
  /-- A one-argument function between terminal types. -/
  | prim1 : ∀ {a b : LeanPrimTy},
      LeanInitPureExtern1OnlyPrim a b → Extern [.prim a] (.prim b)
  /-- A two-argument function between terminal types. -/
  | prim2 : ∀ {a b c : LeanPrimTy},
      LeanInitPureExtern2OnlyPrim a b c → Extern [.prim a, .prim b] (.prim c)
  /-- A three-argument function between terminal types. -/
  | prim3 : ∀ {a b c d : LeanPrimTy},
      LeanInitPureExtern3OnlyPrim a b c d → Extern [.prim a, .prim b, .prim c] (.prim d)
  /-- A five-argument function between terminal types. -/
  | prim5 : ∀ {a b c d e f : LeanPrimTy}, LeanInitPureExtern5 a b c d e f →
      Extern [.prim a, .prim b, .prim c, .prim d, .prim e] (.prim f)
  /-- A one-argument function of the polymorphic catalogue. -/
  | poly1 : ∀ {α β : Ty}, Extern1At α β → Extern [α] β
  /-- A two-argument function of the polymorphic catalogue. -/
  | poly2 : ∀ {α β γ : Ty}, Extern2At α β γ → Extern [α, β] γ
  /-- A three-argument function of the polymorphic catalogue. -/
  | poly3 : ∀ {α β γ δ : Ty}, Extern3At α β γ δ → Extern [α, β, γ] δ
  /-- A four-argument function of the polymorphic catalogue. -/
  | poly4 : ∀ {α β γ δ ε : Ty}, Extern4At α β γ δ ε → Extern [α, β, γ, δ] ε
  /-- A six-argument function of the polymorphic catalogue. -/
  | poly6 : ∀ {α : Ty} {b : LeanPrimTy} {γ : Ty} {d e f : LeanPrimTy} {ζ : Ty},
      Extern6At α b γ d e f ζ →
      Extern [α, .prim b, γ, .prim d, .prim e, .prim f] ζ

/-- The catalogue, under the name the terms use. -/
abbrev Externs := Extern

end LeanScript

end
