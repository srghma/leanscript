module

public import LeanScript.Term.Optimize.InlineRetEval

@[expose] public section

set_option autoImplicit false

/-!
# A join point that takes its parameter apart, written at the jumps passing a constructor

```
join j (x : σ) := case x of | c₁ fs₁ => b₁ | … | cₙ fsₙ => bₙ
…  jump j (cᵢ args)  …
```

When the body of a join point is a case analysis of its parameter (a *case-of-case*, which is
what Lean's `match (match e with …) with …` and `Option.map f (Option.map g x)` become), a jump
that passes a constructor literal `cᵢ args` is replaced by the arm `bᵢ` of that constructor, its
fields bound to `args` (`Term.subst`: the substitution is moved from the context of the join
point to the context of the jump, `JPos`).  The same for a join point whose body takes
its parameter, a record, apart (`join j (x : σ) := let ⟨fs⟩ := x; b`): a jump passing a record
literal is `b` with the fields bound to the literal's.  When no jump to `j` is left, the join
point is dropped.  The rewrite is only kept when the join point disappears and the number of calls does
not grow (`Branch.joinCtor`), so no call is duplicated.

The walk is `Term.jcWalk`; it may change the level of a statement, which is kept where the
level is recorded in a type (`Term.keepLvl`, as in `Term.retWalk`).

**Proved:** `Term.joinCtor_eval` (the value does not change) and `Term.numCalls_joinCtor` (no
call is added, `LeanScript.Term.Optimize.CountJoinCtor`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

/-- The arm of the constructor `ix` of a union's case analysis. -/
def Branches.select : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → {b : Bool} → {c : Ctor ks b} → CtorIx cs c →
    (us : List Usage01ω) × (o' : Lvl) × Term Δ d Φ (UCtx.annot d c.binds us ++ Γ) τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ _ b₁ _, _, _, .two₁ => ⟨us₁, _, b₁⟩
  | _, _, _, _, _, _, _, _, .two _ us₂ _ b₂, _, _, .two₂ => ⟨us₂, _, b₂⟩
  | _, _, _, _, _, _, _, _, .cons us b _, _, _, .head => ⟨us, _, b⟩
  | _, _, _, _, _, _, _, _, .cons _ _ bs, _, _, .tail ix => bs.select ix


/-- The body of a join point that is a case analysis of its parameter (of type `σ`): of a union
    (its arms), or of a record (the rest of the body, under the fields). -/
inductive CaseJoin (Δ : DSig ks) (d : Nat) (Φ : KCtx ks) (Γ : UCtx ks) (σ : Ty ks)
    (uₓ : Usage01ω) (τ : Ty ks) (js : JCtx ks) where
  | union (bs : List Bool) (cs : Ctors ks bs) (h : UnionShape bs) (hσ : σ = Ty.union cs (h := h))
      (o : Lvl) (brs : Branches Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) cs τ js o)
  | record (t : Ty ks) (fs : Fields ks) (hσ : σ = Ty.record t fs) (us : List Usage01ω) (o : Lvl)
      (body : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ ⟨σ, uₓ, d⟩ :: Γ) τ js o)

/-- The value of the join point's body on `x`. -/
def CaseJoin.sem {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {uₓ : Usage01ω} {τ : Ty ks}
    {js : JCtx ks} : CaseJoin Δ d Φ Γ σ uₓ τ js → KEnv Δ Φ → UEnv Δ Γ → JEnv Δ τ js →
    Ty.Den Δ σ → Ty.Den Δ τ
  | .union _ _ _ hσ _ brs, κ, ρ, jκ, x =>
      brs.eval κ (Tuple.cons x ρ) jκ (cast (congrArg (Ty.Den Δ) hσ) x)
  | .record _ fs hσ us _ body, κ, ρ, jκ, x =>
      let r := cast (congrArg (Ty.Den Δ) hσ) x
      body.eval κ (Tuple.append (UEnv.ofDL d _ us (Tuple.cons r.1 (Fields.toDL fs r.2)))
        (Tuple.cons x ρ)) jκ

/-- The body of a join point, when it is a case analysis of its parameter. -/
def Term.caseJoin? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
    {τ : Ty ks} {js : JCtx ks} :
    {o : Lvl} → Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o → Option (CaseJoin Δ d Φ Γ σ uₓ τ js)
  | _, .branch (.union_casesOn n brs) => n.isHead?.map fun h => .union _ _ _ h.down.symm _ brs
  | _, .record_casesOn us n b => n.isHead?.map fun h => .record _ _ h.down.symm us _ b
  | _, _ => none

/-- The fields of a record literal. -/
def PExpr.recordLit? {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} :
    {o : Lvl} → PExpr Δ Φ Γ (.record t fs) o → Option ((o' : Lvl) × Args Δ Φ Γ (t :: fs.toList) o')
  | _, .record_mk args => some ⟨_, args⟩
  | _, _ => none

/-- Is the jump to the join point `b` (then its parameter has the type of `b`'s)? -/
def JVar.same? : {js : JCtx ks} → {σ' σ : Ty ks} → JVar js σ' → JVar js σ →
    Option (PLift (σ' = σ))
  | _, _, _, .head, .head => some ⟨rfl⟩
  | _, _, _, .tail a, .tail b => JVar.same? a b
  | _, _, _, _, _ => none

/-- Where a jump is, seen from the join point (whose contexts are `Φ₀`, `Γ₀`, `js₀`): the
    renamings of the contexts of the join point into the current ones, and the join point. -/
structure JPos (Φ₀ : KCtx ks) (Γ₀ : UCtx ks) (js₀ : JCtx ks) (σ : Ty ks) (Φ : KCtx ks)
    (Γ : UCtx ks) (js : JCtx ks) where
  rk : KLRen Φ₀ Φ
  ru : ULRen Γ₀ Γ
  rj : JRen js₀ js
  jv : JVar js σ

section JPos
variable {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks}

/-- Under one more known value. -/
def JPos.wkK {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js)
    (b : KBinder ks) : JPos Φ₀ Γ₀ js₀ σ (b :: Φ) Γ js :=
  ⟨fun k => (P.rk k).map fun p => ⟨p.1, .tail p.2⟩, P.ru, P.rj, P.jv⟩

/-- Under one more unknown. -/
def JPos.wk1 {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js)
    (b : UBinder ks) : JPos Φ₀ Γ₀ js₀ σ Φ (b :: Γ) js :=
  ⟨P.rk, fun x => (P.ru x).map fun p => ⟨p.1, .tail p.2⟩, P.rj, P.jv⟩

/-- Under the unknowns `bs`. -/
def JPos.wkN {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js)
    (bs : UCtx ks) : JPos Φ₀ Γ₀ js₀ σ Φ (bs ++ Γ) js :=
  ⟨P.rk, fun x => (P.ru x).bind fun p => (URen.wkN bs p.2).map fun y => ⟨p.1, y⟩, P.rj, P.jv⟩

/-- Under one more join point. -/
def JPos.wkJ {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js)
    (b : JBinder ks) : JPos Φ₀ Γ₀ js₀ σ Φ Γ (b :: js) :=
  ⟨P.rk, P.ru, fun j => (P.rj j).map .tail, .tail P.jv⟩

/-- In front of the join point itself (the main branch). -/
def JPos.init {u : Usage1ω} : JPos Φ₀ Γ₀ js₀ σ Φ₀ Γ₀ (⟨σ, u⟩ :: js₀) :=
  ⟨KLRen.id, ULRen.idL, fun j => some (.tail j), .head⟩

end JPos

/-- `jump j e` where `j` is the join point and `e` a constructor literal: the arm of the
    constructor, its fields bound to the fields of `e` (and the parameter to `e`, when it is used
    at most once: only by the case analysis). -/
def JPos.jump? {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks}
    {uₓ : Usage01ω} {τ : Ty ks} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    (C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀) (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) {σ' : Ty ks}
    (j : JVar js σ') {o : Lvl} (e : PExpr Δ Φ Γ σ' o) :
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o') :=
  match JVar.same? j P.jv with
  | none => none
  | some h =>
      let xs : Option ((o : Lvl) × PExpr Δ Φ Γ σ o) :=
        if uₓ.atMostOnce then some ⟨_, h.down ▸ e⟩ else none
      match C with
      | .union _ cs hsh hσ _ brs =>
          match ((h.down.trans hσ) ▸ e : PExpr Δ Φ Γ (.union cs (h := hsh)) o).unionLit? with
          | none => none
          | some ⟨_, c, ix, _, args⟩ =>
              let sel := brs.select ix
              sel.2.2.subst (D' := d) P.rk
                (USub.ofArgs (USub.consOpt xs (USub.ofRen P.ru)) d c.binds sel.1 args) P.rj
      | .record t fs hσ us _ body =>
          match ((h.down.trans hσ) ▸ e : PExpr Δ Φ Γ (.record t fs) o).recordLit? with
          | none => none
          | some ⟨_, args⟩ =>
              body.subst (D' := d) P.rk
                (USub.ofArgs (USub.consOpt xs (USub.ofRen P.ru)) d (t :: fs.toList) us args) P.rj

/-- `jump j e` where `j` is the join point and `e` a constructor literal (`JPos.jump?`) or a
    conditional of such (`c ? a : b`, recursively, at most `fuel` deep):
    `if c then (jump j a) else (jump j b)`, each jump replaced.  So a `bind` whose continuation
    answers `if q then some x else none` writes the arms of the `match` that follows. -/
def JPos.jumpCond? {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks}
    {uₓ : Usage01ω} {τ : Ty ks} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    (C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀) (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) {σ' : Ty ks}
    (j : JVar js σ') : (fuel : Nat) → {o : Lvl} → PExpr Δ Φ Γ σ' o →
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | fuel + 1, _, .neu (.cond c a b) =>
      match JPos.jumpCond? C P j fuel a, JPos.jumpCond? C P j fuel b with
      | some ta, some tb => some ⟨_, .branch (.ite c ta.2 tb.2)⟩
      | _, _ => none
  | _, _, e => JPos.jump? C P j e

/-! ## Replacing the jumps -/

section Repl
variable {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
  {τ : Ty ks} (C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀)

mutual
/-- Replace the jumps to the join point that pass a constructor literal, or a conditional of
    such (`JPos.jumpCond?`). -/
def Term.jcRepl : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    JPos Φ₀ Γ₀ js₀ σ Φ Γ js → {o : Lvl} → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, P, _, .letV u v b => ⟨_, .letV u v (b.jcRepl (P.wkK _)).2⟩
  | _, _, _, P, _, .letE u c b => ⟨_, .letE u c (b.jcRepl (P.wk1 _)).2⟩
  | _, _, _, P, _, .record_casesOn us n b => ⟨_, .record_casesOn us n (b.jcRepl (P.wkN _)).2⟩
  | _, _, _, P, _, .branch br => ⟨_, .branch (br.jcRepl P).2⟩
  | _, _, _, P, _, .jump j e => (JPos.jumpCond? C P j 8 e).getD ⟨_, .jump j e⟩
/-- `Term.jcRepl` in a branch. -/
def Branch.jcRepl : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    JPos Φ₀ Γ₀ js₀ σ Φ Γ js → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ →
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, P, _, .ite c t e => ⟨_, .ite c (t.jcRepl P).2 (e.jcRepl P).2⟩
  | _, _, _, P, _, .enum_casesOn e bs => ⟨_, .enum_casesOn e (fun i => ((bs i).jcRepl P).2)⟩
  | _, _, _, P, _, .union_casesOn e bs => ⟨_, .union_casesOn e (bs.jcRepl P).2⟩
  | _, _, _, P, _, .join σ' u uₓ' body main =>
      ⟨_, .join σ' u uₓ' (body.jcRepl (P.wk1 _)).2 (main.jcRepl (P.wkJ _)).2⟩
/-- `Term.jcRepl` in the branches of a union's case analysis. -/
def Branches.jcRepl : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    JPos Φ₀ Γ₀ js₀ σ Φ Γ js → {bs : List Bool} → {cs : Ctors ks bs} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, P, _, _, _, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (b₁.jcRepl (P.wkN _)).2 (b₂.jcRepl (P.wkN _)).2⟩
  | _, _, _, P, _, _, _, .cons us b bs => ⟨_, .cons us (b.jcRepl (P.wkN _)).2 (bs.jcRepl P).2⟩
end

end Repl

/-- `join j x := body; main` (both already walked): when `body` takes `x` apart, the jumps of
    `main` passing a constructor literal are replaced by the arm of that constructor; the result
    is kept when no jump to `j` is left (the join point is dropped) and no call is added. -/
def Branch.joinCtor {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ' :=
  match body.caseJoin? with
  | none => ⟨_, .join σ u uₓ body main⟩
  | some C =>
      match (main.jcRepl C JPos.init).2.rename KRen.id URen.id JRen.drop with
      | some b =>
          if b.numCalls ≤ body.numCalls + main.numCalls then ⟨_, b⟩
          else ⟨_, .join σ u uₓ body main⟩
      | none => ⟨_, .join σ u uₓ body main⟩

/-! ## A case analysis of a conditional of constructors -/

/-- `t[fields := args]`, `t` under the fields `ts` (used `us` times) of a case analysis: the
    fields substituted by the arguments (`Term.subst`); when that fails (an argument that
    computes something, for a field used more than once), the first neutral argument that is not
    an unknown is named by `let` first (`Args.shareFirst`), and so on, at most `fuel` times. -/
def Term.substFields (d : Nat) {Φ : KCtx ks} {τ : Ty ks} {js : JCtx ks} (ts : List (Ty ks))
    (us : List Usage01ω) : (fuel : Nat) → {Γ : UCtx ks} → {o oa : Lvl} →
    Term Δ d Φ (UCtx.annot d ts us ++ Γ) τ js o → Args Δ Φ Γ ts oa →
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | 0, _, _, _, t, args =>
      t.subst (D' := d) KLRen.id (USub.ofArgs (USub.ofRen ULRen.idL) d ts us args) JRen.id
  | fuel + 1, _, _, _, t, args =>
      match t.subst (D' := d) KLRen.id (USub.ofArgs (USub.ofRen ULRen.idL) d ts us args) JRen.id with
      | some r => some r
      | none =>
          match Args.shareFirst d args with
          | none => none
          | some ⟨_, _, n, _, args'⟩ =>
              match t.rename KRen.id (URen.liftN URen.wk1 (UCtx.annot d ts us)) JRen.id with
              | none => none
              | some t' =>
                  (Term.substFields d ts us fuel t' args').map fun r =>
                    ⟨_, .letE .many (.share n) r.2⟩

/-- `case e of brs` for a union literal `e`: the arm of its constructor, its fields bound to the
    fields of `e` (`Term.substFields`). -/
def Branches.caseLit? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (brs : Branches Δ d Φ Γ cs τ js o)
    {o' : Lvl} (e : PExpr Δ Φ Γ (.union cs (h := h)) o') :
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'') :=
  match e.unionLit? with
  | none => none
  | some ⟨_, c, ix, _, args⟩ =>
      let sel := brs.select ix
      Term.substFields d c.binds sel.1 c.binds.length sel.2.2 args

/-- `case e of brs` for `e` a constructor literal (`Branches.caseLit?`) or a conditional of
    such (`c ? a : b`, recursively): the arm of the literal, or `if c then (case a of brs) else
    (case b of brs)`.  So `if p then some x else if q then some y else none` taken apart is
    `if p then … else if q then … else …`. -/
def Branches.caseOf? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (brs : Branches Δ d Φ Γ cs τ js o) :
    (fuel : Nat) → {o' : Lvl} → PExpr Δ Φ Γ (.union cs (h := h)) o' →
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'')
  | fuel + 1, _, .neu (.cond c a b) =>
      match brs.caseOf? fuel a, brs.caseOf? fuel b with
      | some ta, some tb => some ⟨_, .branch (.ite c ta.2 tb.2)⟩
      | _, _ => none
  | _, _, e => brs.caseLit? e

/-- `case (c ? a : b) of brs`, where `a` and `b` are constructor literals (or conditionals of
    such, `Branches.caseOf?`): `if c then (case a of brs) else (case b of brs)`, each case
    analysis of a literal reduced to its arm (`Branches.caseLit?`).  This is what
    `match (if c then some x else none) with …` becomes. -/
def Neu.caseCond? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o) :
    Option ((ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ') :=
  match n with
  | .cond c a b =>
      match brs.caseOf? 8 a, brs.caseOf? 8 b with
      | some ta, some tb => some ⟨_, .ite c ta.2 tb.2⟩
      | _, _ => none
  | _ => none

/-! ### The arm of a constructor with one field, as a join point -/

/-- A statement under the one field `σ` of a constructor (`UCtx.annot d [σ] us`), as a
    statement under one unknown. -/
def Term.underOne {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    (us : List Usage01ω) → Term Δ d Φ (UCtx.annot d [σ] us ++ Γ) τ js o →
    (u : Usage01ω) × Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o
  | [], t => ⟨.many, t⟩
  | u :: _, t => ⟨u, t⟩

/-- The field of a literal of the second constructor, with one field `σ`, of a union of two. -/
def CtorIx.twoSecond? {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a} {σ : Ty ks} :
    {b : Bool} → {c : Ctor ks b} → CtorIx (.two c₁ (.fields (.one σ))) c → {o' : Lvl} →
    Args Δ Φ Γ c.binds o' → Option ((o'' : Lvl) × PExpr Δ Φ Γ σ o'')
  | _, _, .two₁, _, _ => none
  | _, _, .two₂, _, .cons x .nil => some ⟨_, x⟩

/-- The field of `e` when it is a literal of the second constructor (one field `σ`). -/
def PExpr.twoSecond? {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a} {σ : Ty ks}
    {h : UnionShape [a, true]} {o' : Lvl}
    (e : PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o') :
    Option ((o'' : Lvl) × PExpr Δ Φ Γ σ o'') :=
  e.unionLit?.bind fun r => r.2.2.1.twoSecond? r.2.2.2.2

/-- A leaf `e` of a conditional of literals taken apart by `brs`, whose second constructor has
    one field `σ`, under `join j (f : σ) := (the arm of the second constructor)`: a literal of
    the second constructor jumps to `j` with its field; another literal is its arm
    (`Branches.caseLit?`), seen under `j`. -/
def Branches.leafJump? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a}
    {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o) {o' : Lvl}
    (e : PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o') :
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ (⟨σ, .many⟩ :: js) o'') :=
  match PExpr.twoSecond? e with
  | some x => some ⟨_, .jump .head x.2⟩
  | none =>
      (brs.caseLit? e).bind fun r =>
        (r.2.rename KRen.id URen.id (fun j => some (.tail j))).map fun t => ⟨_, t⟩

/-- `Branches.leafJump?` at every leaf of a conditional of literals (at most `fuel` deep). -/
def Branches.joinTree? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a}
    {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o) :
    (fuel : Nat) → {o' : Lvl} → PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o' →
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ (⟨σ, .many⟩ :: js) o'')
  | fuel + 1, _, .neu (.cond c x y) =>
      match brs.joinTree? fuel x, brs.joinTree? fuel y with
      | some tx, some ty => some ⟨_, .branch (.ite c tx.2 ty.2)⟩
      | _, _ => none
  | _, _, e => brs.leafJump? e

/-- `case (c ? x : y) of brs` (`x`, `y` literals or conditionals of such) where the second
    constructor has one field `σ`: `join j (f : σ) := (its arm); if c then … else …`, a leaf of
    the second constructor jumping to `j` with its field, any other leaf its own arm.  The arm
    of the second constructor is written once, and no record is built for it. -/
def Branches.caseJoin? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a}
    {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o)
    (n : Neu Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) ℓ) :
    Option ((ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ') :=
  match n with
  | .cond c x y =>
      match brs.joinTree? 8 x, brs.joinTree? 8 y with
      | some tx, some ty =>
          let arm := brs.select .two₂
          let body := Term.underOne arm.1 arm.2.2
          some ⟨_, .join σ .many body.1 body.2 (.ite c tx.2 ty.2)⟩
      | _, _ => none
  | _ => none

/-- `Branches.caseJoin?` for a union whose second constructor has one field. -/
def Branch.caseJoinAny? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {ℓ : Nat} : {bs : List Bool} → {cs : Ctors ks bs} → {h : UnionShape bs} →
    Neu Δ Φ Γ (.union cs (h := h)) ℓ → Branches Δ d Φ Γ cs τ js o →
    Option ((ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ')
  | _, .two _ (.fields (.one _)), _, n, brs => brs.caseJoin? n
  | _, _, _, _, _ => none

/-- `case n of brs`, rewritten by `Neu.caseCond?` when that adds no call (an arm selected by
    both constructors would be written twice); otherwise, when the second constructor has one
    field, its arm as a join point that the leaves of that constructor jump to
    (`Branch.caseJoinAny?`), when that adds no call. -/
def Branch.caseCond {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o) :
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ' :=
  match n.caseCond? brs with
  | some r =>
      if r.2.numCalls ≤ brs.numCalls then r
      else
        match Branch.caseJoinAny? n brs with
        | some r' => if r'.2.numCalls ≤ brs.numCalls then r' else ⟨_, .union_casesOn n brs⟩
        | none => ⟨_, .union_casesOn n brs⟩
  | none => ⟨_, .union_casesOn n brs⟩

/-- `let ⟨fs⟩ := e; body` for `e` a record literal (its fields substituted,
    `Term.substFields`) or a conditional of such (`c ? a : b`, recursively, at most `fuel`
    deep): `if c then (let ⟨fs⟩ := a; body) else (let ⟨fs⟩ := b; body)`, each reduced.  This is
    what `match (if c then (some x, none) else (none, some y)) with …` becomes. -/
def Term.recordCaseOf? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl} (us : List Usage01ω)
    (body : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o) :
    (fuel : Nat) → {o' : Lvl} → PExpr Δ Φ Γ (.record t fs) o' →
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'')
  | fuel + 1, _, .neu (.cond c a b) =>
      match Term.recordCaseOf? us body fuel a, Term.recordCaseOf? us body fuel b with
      | some ta, some tb => some ⟨_, .branch (.ite c ta.2 tb.2)⟩
      | _, _ => none
  | _, _, e =>
      match e.recordLit? with
      | some ⟨_, args⟩ => Term.substFields d (t :: fs.toList) us (t :: fs.toList).length body args
      | none => none

/-- `let ⟨fs⟩ := n; body`, rewritten by `Term.recordCaseOf?` when that adds no call (the body
    is written once per literal). -/
def Term.recordCaseCond {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (body : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o) :
    (o' : Lvl) × Term Δ d Φ Γ τ js o' :=
  match Term.recordCaseOf? us body 8 (.neu n) with
  | some r => if r.2.numCalls ≤ body.numCalls then r else ⟨_, .record_casesOn us n body⟩
  | none => ⟨_, .record_casesOn us n body⟩

/-- A statement that is a case analysis: `Branch.caseCond` on it (`Term.recordCaseCond` for a
    record's). -/
def Term.caseCondTop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} :
    (o : Lvl) × Term Δ d Φ Γ τ js o → (o : Lvl) × Term Δ d Φ Γ τ js o
  | ⟨_, .branch (.union_casesOn n brs)⟩ => ⟨_, .branch (Branch.caseCond n brs).2⟩
  | ⟨_, .record_casesOn us n body⟩ => Term.recordCaseCond us n body
  | r => r

/-- Is the neutral expression a conditional? -/
def Neu.isCond {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Bool
  | .cond .. => true
  | _ => false

/-- Is the statement a case analysis (of a union, or of a record) of the innermost unknown? -/
def Term.isCaseOnHead {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    {τ : Ty ks} {js : JCtx ks} : {o : Lvl} → Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o → Bool
  | _, .branch (.union_casesOn n _) => n.isHead?.isSome
  | _, .record_casesOn _ n _ => n.isHead?.isSome
  | _, _ => false

/-- `let x [1] := share (c ? a : b); case x of brs`: the conditional is written in the case
    analysis (`x` is used once, there; `Term.subst`), which `Branch.caseCond` then rewrites into
    `if c then … else …`.  Kept only when it adds no call. -/
def Term.shareCase {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match c with
  | .share n =>
      if u = .one ∧ n.isCond = true ∧ b.isCaseOnHead = true then
        match b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL)) JRen.id with
        | some r =>
            if (Term.caseCondTop r).2.numCalls ≤ b.numCalls then Term.caseCondTop r
            else ⟨_, .letE u (.share n) b⟩
        | none => ⟨_, .letE u (.share n) b⟩
      else ⟨_, .letE u (.share n) b⟩
  | c => ⟨_, .letE u c b⟩

/-! ## The walk -/

mutual
/-- `Term.jcWalk` inside the bodies of a value (the level of the value is kept). -/
def Val.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.jcWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.jcWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.jcWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.jcWalk` in a body: free in a closed body, level kept in an open one. -/
def Body.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.jcWalk.2
  | _, _, _, _, _, _, .opened t h => .opened (t.keepLvl t.jcWalk) h
/-- `Term.jcWalk` in the bodies of a computation. -/
def Comp.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.jcWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.jcWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h => .data_rec b ρ us (fun i => (brs i).jcWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).jcWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The walk**: every join point that takes its parameter apart is written at the jumps
    passing a constructor literal (`Branch.joinCtor`); the level may change. -/
def Term.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, _, _, _, .letV u v b => ⟨_, .letV u v.jcWalk b.jcWalk.2⟩
  | _, _, _, _, _, _, .letE u c b => Term.shareCase u c.jcWalk b.jcWalk.2
  | _, _, _, _, _, _, .record_casesOn us n b => Term.recordCaseCond us n b.jcWalk.2
  | _, _, _, _, _, _, .branch br => ⟨_, .branch br.jcWalk.2⟩
  | _, _, _, _, _, _, .jump j e => ⟨_, .jump j e⟩
/-- `Term.jcWalk` in a branch. -/
def Branch.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, .ite c t e => ⟨_, .ite c t.jcWalk.2 e.jcWalk.2⟩
  | _, _, _, _, _, _, .enum_casesOn e bs => ⟨_, .enum_casesOn e (fun i => (bs i).jcWalk.2)⟩
  | _, _, _, _, _, _, .union_casesOn e bs => Branch.caseCond e bs.jcWalk.2
  | _, _, _, _, _, _, .join σ u uₓ body main => Branch.joinCtor σ u uₓ body.jcWalk.2 main.jcWalk.2
/-- `Term.jcWalk` in the branches of a union's case analysis. -/
def Branches.jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => ⟨_, .two us₁ us₂ b₁.jcWalk.2 b₂.jcWalk.2⟩
  | _, _, _, _, _, _, _, _, .cons us b bs => ⟨_, .cons us b.jcWalk.2 bs.jcWalk.2⟩
end

/-- **Join points that take their parameter apart, written at the jumps passing a constructor
    literal.**  At the top the level is kept. -/
def Term.joinCtor {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.keepLvl t.jcWalk

end LeanScript

end
