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
point to the context of the jump, `JPos`).  When no jump to `j` is left, the join point is
dropped.  The rewrite is only kept when the join point disappears and the number of calls does
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

/-- The constructor and the fields of a union literal. -/
def PExpr.unionLit? {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} : {o : Lvl} → PExpr Δ Φ Γ (.union cs (h := h)) o →
    Option ((b : Bool) × (c : Ctor ks b) × CtorIx cs c × (o' : Lvl) × Args Δ Φ Γ c.binds o')
  | _, .union_mk ix args => some ⟨_, _, ix, _, args⟩
  | _, _ => none

/-- The body of a join point that is a case analysis of its parameter (of type `σ`). -/
structure CaseJoin (Δ : DSig ks) (d : Nat) (Φ : KCtx ks) (Γ : UCtx ks) (σ : Ty ks)
    (uₓ : Usage01ω) (τ : Ty ks) (js : JCtx ks) where
  bs : List Bool
  cs : Ctors ks bs
  h : UnionShape bs
  hσ : σ = Ty.union cs (h := h)
  o : Lvl
  brs : Branches Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) cs τ js o

/-- The value of the join point's body on `x`. -/
def CaseJoin.sem {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {uₓ : Usage01ω} {τ : Ty ks}
    {js : JCtx ks} (C : CaseJoin Δ d Φ Γ σ uₓ τ js) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) (x : Ty.Den Δ σ) : Ty.Den Δ τ :=
  C.brs.eval κ (Tuple.cons x ρ) jκ (cast (congrArg (Ty.Den Δ) C.hσ) x)

/-- The body of a join point, when it is a case analysis of its parameter. -/
def Term.caseJoin? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
    {τ : Ty ks} {js : JCtx ks} :
    {o : Lvl} → Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o → Option (CaseJoin Δ d Φ Γ σ uₓ τ js)
  | _, .branch (.union_casesOn n brs) => n.isHead?.map fun h => ⟨_, _, _, h.down.symm, _, brs⟩
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
      match ((h.down.trans C.hσ) ▸ e : PExpr Δ Φ Γ (.union C.cs (h := C.h)) o).unionLit? with
      | none => none
      | some ⟨_, c, ix, _, args⟩ =>
          let sel := C.brs.select ix
          let xs : Option ((o : Lvl) × PExpr Δ Φ Γ σ o) :=
            if uₓ.atMostOnce then some ⟨_, h.down ▸ e⟩ else none
          sel.2.2.subst (D' := d) P.rk
            (USub.ofArgs (USub.consOpt xs (USub.ofRen P.ru)) d c.binds sel.1 args) P.rj

/-! ## Replacing the jumps -/

section Repl
variable {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
  {τ : Ty ks} (C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀)

mutual
/-- Replace the jumps to the join point that pass a constructor literal (`JPos.jump?`). -/
def Term.jcRepl : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    JPos Φ₀ Γ₀ js₀ σ Φ Γ js → {o : Lvl} → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, P, _, .letV u v b => ⟨_, .letV u v (b.jcRepl (P.wkK _)).2⟩
  | _, _, _, P, _, .letE u c b => ⟨_, .letE u c (b.jcRepl (P.wk1 _)).2⟩
  | _, _, _, P, _, .record_casesOn us n b => ⟨_, .record_casesOn us n (b.jcRepl (P.wkN _)).2⟩
  | _, _, _, P, _, .branch br => ⟨_, .branch (br.jcRepl P).2⟩
  | _, _, _, P, _, .jump j e => (JPos.jump? C P j e).getD ⟨_, .jump j e⟩
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

/-- `case (c ? a : b) of brs`, where `a` and `b` are constructor literals: `if c then (case a
    of brs) else (case b of brs)`, each case analysis of a literal reduced to its arm
    (`Branches.caseLit?`).  This is what `match (if c then some x else none) with …` becomes. -/
def Neu.caseCond? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o) :
    Option ((ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ') :=
  match n with
  | .cond c a b =>
      match brs.caseLit? a, brs.caseLit? b with
      | some ta, some tb => some ⟨_, .ite c ta.2 tb.2⟩
      | _, _ => none
  | _ => none

/-- `case n of brs`, rewritten by `Neu.caseCond?` when that adds no call (an arm selected by
    both constructors would be written twice). -/
def Branch.caseCond {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o) :
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ' :=
  match n.caseCond? brs with
  | some r => if r.2.numCalls ≤ brs.numCalls then r else ⟨_, .union_casesOn n brs⟩
  | none => ⟨_, .union_casesOn n brs⟩

/-- A statement that is a case analysis: `Branch.caseCond` on it. -/
def Term.caseCondTop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} :
    (o : Lvl) × Term Δ d Φ Γ τ js o → (o : Lvl) × Term Δ d Φ Γ τ js o
  | ⟨_, .branch (.union_casesOn n brs)⟩ => ⟨_, .branch (Branch.caseCond n brs).2⟩
  | r => r

/-- Is the neutral expression a conditional? -/
def Neu.isCond {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Bool
  | .cond .. => true
  | _ => false

/-- Is the statement a case analysis of the innermost unknown? -/
def Term.isCaseOnHead {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    {τ : Ty ks} {js : JCtx ks} : {o : Lvl} → Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o → Bool
  | _, .branch (.union_casesOn n _) => n.isHead?.isSome
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
  | _, _, _, _, _, _, .record_casesOn us n b => ⟨_, .record_casesOn us n b.jcWalk.2⟩
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
