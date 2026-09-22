module

public import LeanScript.Expr
public import LeanScript.Rec

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator

`Term.evalClosed` runs a closed term of the language:

* it takes **no fuel**;
* it answers in `τ.den`, not in `Option` and not in an error monad — it never gets stuck,
  so there is no progress theorem to prove and no neutral term to characterise;
* it is neither `partial` nor `unsafe`, and it uses no `sorry` and no extra axiom.

Everything but one node is an ordinary structural recursion on the term.  The exception is
`Term.fixAcc`, which recurses on its `hacc` field with `Acc.rec` — `fixLoop` below — so
the recursion of the object language is carried by the recursion of Lean, and terminates
for the same reason.
-/

namespace LeanScript

open LeanScript.Expr

/-! ## The three environments a term is evaluated in -/

/-- The values of the top-level declarations of the module's signature. -/
def GEnv : List GlobalDecl → Type
  | [] => PUnit
  | d :: ds => d.ty.den × GEnv ds

/-- The value a reference to a top-level declaration resolves to. -/
def GEnv.get : ∀ {ds : List GlobalDecl} {τ : Ty}, GEnv ds → GlobalRef ds τ → τ.den
  | _ :: _, _, (v, _), .head => v
  | _ :: _, _, (_, g), .tail r => GEnv.get g r

/-- The value a variable resolves to. -/
def Env.get : ∀ {Γ : Ctx} {τ : Ty}, Env Γ → (Γ ∋ τ) → τ.den
  | _ :: _, _, (v, _), .head => v
  | _ :: _, _, (_, γ), .tail w => Env.get γ w

/-- Put the values of `as` in front of an environment of `bs`. -/
def Env.append {as bs : Ctx} (x : Env as) (y : Env bs) : Env (as ++ bs) :=
  cast (congrArg Tup (Ty.denList_append as bs).symm) (Tup.append x y)

/-- The recursions in scope, as the functions they compute. -/
def REnv : RCtx → Type
  | [] => PUnit
  | e :: Ρ => (Env e.ps → e.ret.den) × REnv Ρ

/-- The function a recursion in scope computes. -/
def REnv.get : ∀ {Ρ : RCtx} {e : RSig}, REnv Ρ → (Ρ ∋ᵣ e) → (Env e.ps → e.ret.den)
  | _ :: _, _, (f, _), .head => f
  | _ :: _, _, (_, ρ), .tail v => REnv.get ρ v

/-- The join points in scope: a jump to one is the whole of the rest of the block, so a
    label denotes a function from its arguments to the answer of the enclosing block. -/
def LEnv (τ : Ty) : LCtx → Type
  | [] => PUnit
  | ps :: Ω => (Env ps → τ.den) × LEnv τ Ω

/-- The function a join point in scope computes. -/
def LEnv.get : ∀ {τ : Ty} {Ω : LCtx} {ps : List Ty}, LEnv τ Ω → (Ω ∋ₗ ps) →
    (Env ps → τ.den)
  | _, _ :: _, _, (f, _), .head => f
  | _, _ :: _, _, (_, l), .tail v => LEnv.get l v

/-! ## The recursion

`fixLoop` is `Term.fixAcc`'s semantics **here**, in the junk-completed evaluator.  It
recurses on the accessibility proof, so it terminates; the self reference it hands the
body re-enters the loop exactly at the argument tuples whose subject descends.

A term whose self calls have been *proved* to descend is run by `LeanScript.EvalProof`,
which needs nothing else: no fuel, no measure and no value to answer a call that does
not descend with.  This evaluator is the one that runs a term with **no such proof in
hand**, which is what the kernel checks of the compiled snapshots do, and the price of
that is exactly one thing: at a call that does not descend it answers with *some*
element of `τ.den` — `Classical.choice` of the `hne` field, which is a proof that one
exists and not a value anyone chose.  `LeanScript.EvalProof.evalTerm_eq_evalTerm`
says the two evaluators agree wherever that never happens. -/

/-- The fixed point a `Term.fixAcc` denotes, junk-completed.

* `body as self` is the body of the recursion, at the argument tuple `as`, with `self` the
  self reference;
* `hne` says `τ` has a value, which is what a call that does *not* descend is answered
  with — an arbitrary one, never reached by a term whose calls descend;
* the recursion is on `Acc r x`, so it terminates. -/
def fixLoop {ps : Ctx} {τ : Ty} {α : Type} (r : α → α → Prop) (rdec : DecidableRel r)
    (subject : Env ps → α) (body : Env ps → (Env ps → τ.den) → τ.den)
    (hne : Nonempty τ.den) : ∀ {x : α}, Acc r x → Env ps → τ.den := fun h =>
  Acc.rec (motive := fun _ _ => Env ps → τ.den)
    (fun x _ ih as =>
      body as fun as' =>
        match rdec (subject as') x with
        | isTrue hlt => ih (subject as') hlt as'
        | isFalse _ => Classical.choice hne)
    h

/-! ## The fields of a constructor of a recursive type

`RecFlds` says which `Ty` each field of a constructor of a recursive tagged union has,
and these two functions are the two directions that fact buys: the fields of a
constructor, as an environment, are the fields of a value of `Mu`, and the other way
round.  Neither recurses into a field: one level is all a constructor and its eliminator
ever look at. -/

/-- The fields a constructor was given, as the fields of a value of the fixed point. -/
def recFldsToArgs {l : LeanTaggedUnionSchemaSealed} :
    ∀ {ds : List FDesc} {σs : List Ty}, RecFlds l ds σs → Env σs →
      MuArgs [RTy.fdescTU l.schema] ds
  | _, _, .nil, _ => .nil
  | _, _, .prim fts, (v, vs) => .cons (.primA v) (recFldsToArgs fts vs)
  | _, _, .self fts, (v, vs) => .cons (.selfA v) (recFldsToArgs fts vs)

/-- The fields of a value of the fixed point, as the environment a branch binds. -/
def recArgsToEnv {l : LeanTaggedUnionSchemaSealed} :
    ∀ {ds : List FDesc} {σs : List Ty}, RecFlds l ds σs →
      MuArgs [RTy.fdescTU l.schema] ds → Env σs
  | _, _, .nil, _ => PUnit.unit
  | _, _, .prim fts, .cons (.primA v) as => (v, recArgsToEnv fts as)
  | _, _, .self fts, .cons (.selfA v) as => (v, recArgsToEnv fts as)

/-! ## The evaluator -/

mutual

/-- Run a term. -/
def evalTerm {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ρ : RCtx} {τ : Ty}, Term Sg Γ Ρ τ → Env Γ → REnv Ρ → τ.den
  | _, _, _, .var v, γ, _ => Env.get γ v
  | _, _, _, .lam b, γ, ρ => fun x => evalTerm g b (x, γ) ρ
  | _, _, _, .ap f a, γ, ρ => (evalTerm g f γ ρ) (evalTerm g a γ ρ)
  | _, _, _, .lit _ v, _, _ => v
  | _, _, _, .global r, _, _ => GEnv.get g r
  | _, _, _, .letE e b, γ, ρ => evalTerm g b (evalTerm g e γ ρ, γ) ρ
  | _, _, _, .bool_elim c t e, γ, ρ =>
      cond (evalTerm g c γ ρ) (evalTerm g t γ ρ) (evalTerm g e γ ρ)
  | _, _, _, .lazyMk (τ := τ₀) e, γ, ρ => cast (den_lazy τ₀).symm (evalTerm g e γ ρ)
  | _, _, _, .lazyForce (τ := τ₀) e, γ, ρ => cast (den_lazy τ₀) (evalTerm g e γ ρ)
  | _, _, _, .thunkMk (τ := τ₀) e, γ, ρ => cast (den_thunk τ₀).symm (evalTerm g e γ ρ)
  | _, _, _, .thunkForce (τ := τ₀) e, γ, ρ => cast (den_thunk τ₀) (evalTerm g e γ ρ)
  | _, _, _, .prim _ f sp, γ, ρ => f (evalSpine g sp γ ρ)
  | _, _, _, .enum_mk _ i, _, _ => i
  | _, _, _, .enum_elim e cs, γ, ρ => evalEnumCases g cs (evalTerm g e γ ρ) γ ρ
  | _, _, _, .record_mk fs sp, γ, ρ => Ty.recMk fs (evalSpine g sp γ ρ)
  | _, _, _, .record_elim e b, γ, ρ =>
      evalTerm g b (Env.append (Ty.recFlds (evalTerm g e γ ρ)) γ) ρ
  | _, _, _, .taggedUnion_mk l t ht sp, γ, ρ => Ty.tsumMk l t ht (evalSpine g sp γ ρ)
  | _, _, _, .taggedUnion_elim e cs, γ, ρ =>
      let v := evalTerm g e γ ρ
      evalCases g cs (Ty.tsumTag v) (Ty.tsumTag_lt v) (Ty.tsumFlds v) γ ρ
  | _, _, _, .block t, γ, ρ => evalTail g t γ PUnit.unit ρ
  | _, _, _, .fixAcc _ r rdec subject hacc _ body hne, γ, ρ =>
      Ty.curryFn fun as =>
        fixLoop r rdec subject
          (fun as' self => evalTerm g body (Env.append as' γ) (self, ρ))
          hne (hacc as) as
  | _, _, _, .selfCall v sp, γ, ρ => (REnv.get ρ v) (evalSpine g sp γ ρ)
  | _, _, _, .recTU_mk _ t ht fts sp, γ, ρ =>
      Mu.mk t ht (recFldsToArgs fts (evalSpine g sp γ ρ))
  | _, _, _, .recTU_elim e cs, γ, ρ =>
      match evalTerm g e γ ρ with
      | .mk t ht args => evalRecCases g cs t ht args γ ρ

/-- Run a list of terms. -/
def evalSpine {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ρ : RCtx} {σs : List Ty}, Spine Sg Γ Ρ σs → Env Γ → REnv Ρ → Env σs
  | _, _, _, .nil, _, _ => PUnit.unit
  | _, _, _, .cons e sp, γ, ρ => (evalTerm g e γ ρ, evalSpine g sp γ ρ)

/-- Run the branch of a dispatch that constructor `t` selects, with that constructor's
    fields bound in front of the environment. -/
def evalCases {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ρ : RCtx} {cs : List (List Ty)} {τ : Ty}, Cases Sg Γ Ρ cs τ →
      (t : Nat) → (ht : t < cs.length) → Env (cs[t]'ht) → Env Γ → REnv Ρ → τ.den
  | _, _, _, _, .nil, t, ht, _, _, _ => absurd ht (Nat.not_lt_zero t)
  | _, _, _, _, .cons b _, 0, _, flds, γ, ρ => evalTerm g b (Env.append flds γ) ρ
  | _, _, _, _, .cons _ rest, t + 1, ht, flds, γ, ρ =>
      evalCases g rest t (by simpa using ht) flds γ ρ

/-- Run the branch of a dispatch on a recursive tagged union that constructor `t`
    selects, with that constructor's fields bound in front of the environment. -/
def evalRecCases {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ρ : RCtx} {l : LeanTaggedUnionSchemaSealed}
      {cs : List (List FDesc)} {τ : Ty},
      RecCases Sg Γ Ρ l cs τ → (t : Nat) → (ht : t < cs.length) →
      MuArgs [RTy.fdescTU l.schema] (cs.getD t []) → Env Γ → REnv Ρ → τ.den
  | _, _, _, _, _, .nil, t, ht, _, _, _ => absurd ht (Nat.not_lt_zero t)
  | _, _, _, _, _, .cons fts b _, 0, _, args, γ, ρ =>
      evalTerm g b (Env.append (recArgsToEnv fts args) γ) ρ
  | _, _, _, _, _, .cons _ _ rest, t + 1, ht, args, γ, ρ =>
      evalRecCases g rest t (by simpa using ht) args γ ρ

/-- Run the branch of a dispatch on an enum that constructor `i` selects. -/
def evalEnumCases {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ρ : RCtx} {τ : Ty} {n : Nat}, EnumCases Sg Γ Ρ τ n → Fin n →
      Env Γ → REnv Ρ → τ.den
  | _, _, _, _, .nil, i, _, _ => i.elim0
  | _, _, _, _, .cons b _, ⟨0, _⟩, γ, ρ => evalTerm g b γ ρ
  | _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, γ, ρ =>
      evalEnumCases g rest ⟨i, by omega⟩ γ ρ

/-- Run a block. -/
def evalTail {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty}, Tail Sg Γ Ω Ρ τ → Env Γ → LEnv τ Ω →
      REnv Ρ → τ.den
  | _, _, _, _, .ret e, γ, _, ρ => evalTerm g e γ ρ
  | _, _, _, _, .jmp l sp, γ, lenv, ρ => (LEnv.get lenv l) (evalSpine g sp γ ρ)
  | _, _, _, _, .letT e t, γ, lenv, ρ => evalTail g t (evalTerm g e γ ρ, γ) lenv ρ
  | _, _, _, _, .iteT c a b, γ, lenv, ρ =>
      cond (evalTerm g c γ ρ) (evalTail g a γ lenv ρ) (evalTail g b γ lenv ρ)
  | _, _, _, _, .caseT e cs, γ, lenv, ρ =>
      let v := evalTerm g e γ ρ
      evalCasesT g cs (Ty.tsumTag v) (Ty.tsumTag_lt v) (Ty.tsumFlds v) γ lenv ρ
  | _, _, _, _, .enumCaseT e cs, γ, lenv, ρ =>
      evalEnumCasesT g cs (evalTerm g e γ ρ) γ lenv ρ
  | _, _, _, _, .join _ body rest, γ, lenv, ρ =>
      evalTail g rest γ ((fun as => evalTail g body (Env.append as γ) lenv ρ), lenv) ρ

/-- Run the branch of a `Tail.caseT` that constructor `t` selects. -/
def evalCasesT {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {cs : List (List Ty)} {τ : Ty},
      CasesT Sg Γ Ω Ρ cs τ → (t : Nat) → (ht : t < cs.length) → Env (cs[t]'ht) →
      Env Γ → LEnv τ Ω → REnv Ρ → τ.den
  | _, _, _, _, _, .nil, t, ht, _, _, _, _ => absurd ht (Nat.not_lt_zero t)
  | _, _, _, _, _, .cons b _, 0, _, flds, γ, lenv, ρ =>
      evalTail g b (Env.append flds γ) lenv ρ
  | _, _, _, _, _, .cons _ rest, t + 1, ht, flds, γ, lenv, ρ =>
      evalCasesT g rest t (by simpa using ht) flds γ lenv ρ

/-- Run the branch of a `Tail.enumCaseT` that constructor `i` selects. -/
def evalEnumCasesT {Sg : Sig} (g : GEnv Sg.decls) :
    ∀ {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} {n : Nat}, EnumCasesT Sg Γ Ω Ρ τ n →
      Fin n → Env Γ → LEnv τ Ω → REnv Ρ → τ.den
  | _, _, _, _, _, .nil, i, _, _, _ => i.elim0
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, γ, lenv, ρ => evalTail g b γ lenv ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, γ, lenv, ρ =>
      evalEnumCasesT g rest ⟨i, by omega⟩ γ lenv ρ

end

/-- **Run a closed term.**  No fuel, no `Option`, no `partial`, no `sorry`. -/
def Term.evalClosed {Sg : Sig} {τ : Ty} (g : GEnv Sg.decls) (t : Term Sg [] [] τ) : τ.den :=
  evalTerm g t PUnit.unit PUnit.unit

end LeanScript

end
