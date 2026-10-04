module

public import LeanScript.Term.Optimize.JoinCtor
public import LeanScript.Term.Optimize.Occ

@[expose] public section

set_option autoImplicit false

/-!
# A shared conditional written at its case analyses, and tests that only pick a jump argument

Three rewrites, done by one walk (`Term.cjWalk`, at the top `Term.condJump`):

* **A shared conditional written where it is taken apart** (`Term.shareSubst`):
  `let x := share (c ? a : b); body`, where `x` is used once, or is used only as the operand of
  union case analyses (`Term.onlyScrut`), is `body[x := c ? a : b]` (`Term.subst`).  This is what
  `let o := if c then some v else none; … o.get! … o.get! …` becomes: each `case x of …` is now a
  case analysis of a conditional of constructor literals, which `Branch.caseCond`
  (`LeanScript.Term.Optimize.JoinCtor`) rewrites into `if c then (arm of a) else (arm of b)`, so
  that no record is built for `o`.  Also when `c ? a : b` is a conditional of two constants and
  `x` is used only as an argument of extern calls whose other arguments are constants
  (`Term.onlyFoldUse`): each call then folds into a conditional of two constants
  (`Neu.condFold`, run later by `Term.arithWalk`), and the repeated test is shared again by
  hoisting; `let s := c ? "Hello" : "Default"; f (s ++ ", World") (s ++ ", Universe")` becomes
  `let b := c; f (b ? "Hello, World" : "Default, World") (b ? "Hello, Universe" : …)`.
* **A test whose two arms jump to the same join point** (`Term.condJumps`):
  `if c then jump j a else jump j b` is `jump j (c ? a : b)`.
* **A join point that only one jump reaches, from its own branch** (`Branch.joinJump`):
  `join j x := body; jump j a` (which the rewrite above produces) is `body[x := a]` when `a` costs
  nothing to repeat or `x` is used at most once, otherwise `let x := share a; body` for a neutral
  `a`; `join j x := body; jump k a` (a jump further out) is `jump k a`.

The level of a statement may change; it is kept where it is recorded in a type
(`Term.keepLvl`, as in `Term.jcWalk`).

**Proved:** `Term.condJump_eval` (the value does not change, `CondJumpEval`) and
`Term.numCalls_condJump` (no call is added, `CountCondJump`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Uses of an unknown only as the operand of a union case analysis -/

/-- Is the neutral expression the unknown at position `i`? -/
def Neu.isVarAt (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ Γ τ ℓ → Bool
  | .var x => x.index == i
  | _ => false

/-- All of `f 0, …, f (n-1)`. -/
def Fin.allCJ : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && Fin.allCJ n (fun i => f i.succ)

mutual
/-- The unknown at position `i` is used only as the operand of union case analyses (and not
    inside the bodies of closures, delays and loops). -/
def Term.onlyScrut (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Bool
  | _, _, _, _, _, _, .ret e => e.countU i == Usage01ω.zero
  | _, _, _, _, _, _, .letV _ v b => v.countU i == Usage01ω.zero && b.onlyScrut i
  | _, _, _, _, _, _, .letE _ c b => c.countU i == Usage01ω.zero && b.onlyScrut (i + 1)
  | _, _, _, _, _, _, .record_casesOn (t := t) (fs := fs) _ n b =>
      n.countU i == Usage01ω.zero && b.onlyScrut (i + (t :: fs.toList).length)
  | _, _, _, _, _, _, .branch br => br.onlyScrut i
  | _, _, _, _, _, _, .jump _ e => e.countU i == Usage01ω.zero
/-- `Term.onlyScrut` in a branch. -/
def Branch.onlyScrut (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Bool
  | _, _, _, _, _, _, .ite c t e => c.countU i == Usage01ω.zero && t.onlyScrut i && e.onlyScrut i
  | _, _, _, _, _, _, .enum_casesOn e bs =>
      e.countU i == Usage01ω.zero && Fin.allCJ _ (fun j => (bs j).onlyScrut i)
  | _, _, _, _, _, _, .union_casesOn e bs => (e.isVarAt i || e.countU i == Usage01ω.zero) && bs.onlyScrut i
  | _, _, _, _, _, _, .join _ _ _ body main => body.onlyScrut (i + 1) && main.onlyScrut i
/-- `Term.onlyScrut` in the branches of a union's case analysis. -/
def Branches.onlyScrut (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Bool
  | _, _, _, _, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
      b₁.onlyScrut (i + c₁.binds.length) && b₂.onlyScrut (i + c₂.binds.length)
  | _, _, _, _, _, _, _, _, .cons (c := c) _ b bs => b.onlyScrut (i + c.binds.length) && bs.onlyScrut i
end

/-! ## Uses of an unknown only as an argument of extern calls on constants -/

/-- Every argument is a constant or the unknown at position `i` itself. -/
def Args.cstOrVar (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Bool
  | _, _, .nil => true
  | _, _, .cons a as =>
      (a.cst?.isSome || (match a with | .neu n => n.isVarAt i | _ => false)) && as.cstOrVar i

mutual
/-- The unknown at position `i` occurs only as an argument of extern calls whose other arguments
    are constants (so that, written as a conditional of constants, each such call folds
    into a conditional of constants, `Neu.condFold`). -/
def Neu.onlyFoldArg (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Bool
  | _, _, .var x => x.index != i
  | _, _, .data_out _ _ n => n.onlyFoldArg i
  | _, _, .cond c a b => c.onlyFoldArg i && a.onlyFoldArg i && b.onlyFoldArg i
  | _, _, .extern _ args _ => args.cstOrVar i || args.onlyFoldArg i
/-- `Neu.onlyFoldArg` in a pure expression. -/
def PExpr.onlyFoldArg (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → Bool
  | _, _, .neu n => n.onlyFoldArg i
  | _, _, .kvar _ => true
  | _, _, .lit _ _ => true
  | _, _, .enum_mk _ _ => true
  | _, _, .record_mk args => args.onlyFoldArg i
  | _, _, .union_mk _ args => args.onlyFoldArg i
  | _, _, .array_mk es => es.onlyFoldArg i
  | _, _, .list_mk es => es.onlyFoldArg i
  | _, _, .data_in _ _ e => e.onlyFoldArg i
/-- `Neu.onlyFoldArg` in arguments. -/
def Args.onlyFoldArg (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Bool
  | _, _, .nil => true
  | _, _, .cons a as => a.onlyFoldArg i && as.onlyFoldArg i
/-- `Neu.onlyFoldArg` in elements. -/
def Elems.onlyFoldArg (i : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → Bool
  | _, _, .nil => true
  | _, _, .cons e es => e.onlyFoldArg i && es.onlyFoldArg i
end

/-- `Neu.onlyFoldArg` in a computation (not inside the bodies of loops). -/
def Comp.onlyFoldArg (i : Nat) {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ τ ℓ → Bool
  | .app f a _ => f.onlyFoldArg i && a.onlyFoldArg i
  | .share n => n.onlyFoldArg i
  | c => c.countU i == Usage01ω.zero

mutual
/-- The unknown at position `i` is used only as an argument of extern calls on constants
    (`Neu.onlyFoldArg`), and not inside the bodies of closures, delays and loops. -/
def Term.onlyFoldUse (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Bool
  | _, _, _, _, _, _, .ret e => e.onlyFoldArg i
  | _, _, _, _, _, _, .letV _ v b => v.countU i == Usage01ω.zero && b.onlyFoldUse i
  | _, _, _, _, _, _, .letE _ c b => c.onlyFoldArg i && b.onlyFoldUse (i + 1)
  | _, _, _, _, _, _, .record_casesOn (t := t) (fs := fs) _ n b =>
      n.onlyFoldArg i && b.onlyFoldUse (i + (t :: fs.toList).length)
  | _, _, _, _, _, _, .branch br => br.onlyFoldUse i
  | _, _, _, _, _, _, .jump _ e => e.onlyFoldArg i
/-- `Term.onlyFoldUse` in a branch. -/
def Branch.onlyFoldUse (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Bool
  | _, _, _, _, _, _, .ite c t e => c.onlyFoldArg i && t.onlyFoldUse i && e.onlyFoldUse i
  | _, _, _, _, _, _, .enum_casesOn e bs =>
      e.onlyFoldArg i && Fin.allCJ _ (fun j => (bs j).onlyFoldUse i)
  | _, _, _, _, _, _, .union_casesOn e bs => e.onlyFoldArg i && bs.onlyFoldUse i
  | _, _, _, _, _, _, .join _ _ _ body main => body.onlyFoldUse (i + 1) && main.onlyFoldUse i
/-- `Term.onlyFoldUse` in the branches of a union's case analysis. -/
def Branches.onlyFoldUse (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Bool
  | _, _, _, _, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
      b₁.onlyFoldUse (i + c₁.binds.length) && b₂.onlyFoldUse (i + c₂.binds.length)
  | _, _, _, _, _, _, _, _, .cons (c := c) _ b bs =>
      b.onlyFoldUse (i + c.binds.length) && bs.onlyFoldUse i
end

/-- Is the neutral expression a conditional of two constants? -/
def Neu.isCondCst {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Bool
  | .cond _ a b => a.cst?.isSome && b.cst?.isSome
  | _ => false

/-- When `let x := share n; b` is rewritten into `b[x := n]` (`Term.shareSubst`): `n` is a
    conditional, and `x` is used once, or only as the operand of union case analyses, or (`n`
    being a conditional of constants) only as an argument of extern calls on constants, each of
    which then folds into a conditional of constants. -/
def Term.shareSubstOk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') : Bool :=
  n.isCond && (u == .one || b.onlyScrut 0 || (n.isCondCst && b.onlyFoldUse 0))

/-! ## The rewrites -/

/-- `let x := share (c ? a : b); body` is `body[x := c ? a : b]` when `x` is used once or only as
    the operand of union case analyses (when the substitution succeeds). -/
def Term.shareSubst {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match c with
  | .share n =>
      if Term.shareSubstOk u n b then
        match b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL)) JRen.id with
        | some r => r
        | none => ⟨_, .letE u (.share n) b⟩
      else ⟨_, .letE u (.share n) b⟩
  | c => ⟨_, .letE u c b⟩

/-- `if c then t else e`, which is `jump j (c ? a : b)` when `t` is `jump j a` and `e` is
    `jump j b`. -/
def Term.condJumps {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match t, e with
  | .jump j a, .jump j' b =>
      match JVar.same? j' j with
      | some h => ⟨_, .jump j (.neu (.cond c a (h.down ▸ b)))⟩
      | none => ⟨_, .branch (.ite c (.jump j a) (.jump j' b))⟩
  | t, e => ⟨_, .branch (.ite c t e)⟩

/-- `let x := share n; body` for a parameter `x` of a join point used `uₓ` times (not for an
    unused one). -/
def Term.bindShare {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {ℓ : Nat} (n : Neu Δ Φ Γ σ ℓ) :
    (uₓ : Usage01ω) → Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o → Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | .one, body => some ⟨_, .letE .one (.share n) body⟩
  | .many, body => some ⟨_, .letE .many (.share n) body⟩
  | .zero, _ => none

/-- The parameter `x` of a join point bound to `a` in its body: by substitution when `a` costs
    nothing to repeat or `x` is used at most once, otherwise by `let x := share a` when `a` is
    neutral. -/
def Term.bindParam {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {o' : Lvl} (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (a : PExpr Δ Φ Γ σ o') : Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'') :=
  if a.isCheap || uₓ.atMostOnce then
    body.subst (D' := d) KLRen.id (USub.cons ⟨_, a⟩ (USub.ofRen ULRen.idL)) JRen.id
  else
    match a with
    | .neu n => Term.bindShare n uₓ body
    | _ => none

/-- `join j x := body; main`, `main` rewritten into `main'`: when `main'` is a jump to `j`, the
    body with the parameter bound to the argument (`Term.bindParam`); when it is a jump further
    out, that jump; when it is a branch, the join point in front of it; otherwise the join point
    as it was. -/
def Branch.joinJump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (o' : Lvl) × Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o' → (o'' : Lvl) × Term Δ d Φ Γ τ js o''
  | ⟨_, .branch br⟩ => ⟨_, .branch (.join σ u uₓ body br)⟩
  | ⟨_, .jump j a⟩ =>
      match j.split with
      | .inl h =>
          match Term.bindParam uₓ body (h.down ▸ a) with
          | some r => r
          | none => ⟨_, .branch (.join σ u uₓ body main)⟩
      | .inr j' => ⟨_, .jump j' a⟩
  | _ => ⟨_, .branch (.join σ u uₓ body main)⟩

/-! ## The walk -/

mutual
/-- `Term.cjWalk` inside the bodies of a value (the level of the value is kept). -/
def Val.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.cjWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.cjWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.cjWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.cjWalk` in a body: free in a closed body, level kept in an open one. -/
def Body.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.cjWalk.2
  | _, _, _, _, _, _, .opened t h => .opened (t.keepLvl t.cjWalk) h
/-- `Term.cjWalk` in the bodies of a computation. -/
def Comp.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.cjWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.cjWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h => .data_rec b ρ us (fun i => (brs i).cjWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).cjWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The walk**: `Term.shareSubst`, `Term.condJumps` and `Branch.joinJump`, bottom-up; the
    level may change. -/
def Term.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, _, _, _, .letV u v b => ⟨_, .letV u v.cjWalk b.cjWalk.2⟩
  | _, _, _, _, _, _, .letE u c b => Term.shareSubst u c.cjWalk b.cjWalk.2
  | _, _, _, _, _, _, .record_casesOn us n b => ⟨_, .record_casesOn us n b.cjWalk.2⟩
  | _, _, _, _, _, _, .branch br => br.cjWalk
  | _, _, _, _, _, _, .jump j e => ⟨_, .jump j e⟩
/-- `Term.cjWalk` in a branch; the result is a statement. -/
def Branch.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → (o : Lvl) × Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ite c t e => Term.condJumps c t.cjWalk.2 e.cjWalk.2
  | _, _, _, _, _, _, .enum_casesOn e bs => ⟨_, .branch (.enum_casesOn e (fun i => (bs i).cjWalk.2))⟩
  | _, _, _, _, _, _, .union_casesOn e bs => ⟨_, .branch (.union_casesOn e bs.cjWalk.2)⟩
  | _, _, _, _, _, _, .join σ u uₓ body main => Branch.joinJump σ u uₓ body.cjWalk.2 main main.cjWalk
/-- `Term.cjWalk` in the branches of a union's case analysis. -/
def Branches.cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => ⟨_, .two us₁ us₂ b₁.cjWalk.2 b₂.cjWalk.2⟩
  | _, _, _, _, _, _, _, _, .cons us b bs => ⟨_, .cons us b.cjWalk.2 bs.cjWalk.2⟩
end

/-- **Shared conditionals written at their case analyses, tests that only pick a jump argument
    made conditionals, and join points reached by one jump inlined.**  At the top the level is
    kept. -/
def Term.condJump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.keepLvl t.cjWalk

end LeanScript

end
