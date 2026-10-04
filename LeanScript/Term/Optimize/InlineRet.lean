module

public import LeanScript.Term.Optimize.InlineOnce

@[expose] public section

set_option autoImplicit false

/-!
# Inlining in tail position, with the level of a statement allowed to change

`Term.inlineKnown` (`LeanScript.Term.Optimize.Inline`) keeps the level index of every
statement, so it cannot inline a call whose answer is a literal: `let y := k a; ret y` with
`k := fun _ => "a"` would become `ret "a"`, which is closed while the `let` was open.  The same
constraint stops dead-code elimination (`Term.dce`) from dropping a dead `let` that is the only
mention of an unknown.

`Term.inlineRet` walks a statement returning a statement **of any level**
(`(o' : Lvl) × Term … o'`).  The level only matters where it is recorded in a type: in the
level of a value bound by `val` (and so in the known context) and in the level of an open body.
There the new statement is used only when it has the old level (`Term.keepLvl`); a closed body
records no level at all, so inside it (every translated function is one) the walk is free.

The rewrites, bottom-up:

* **tail inlining**: `let y := c; ret y` (or `jump j y`) where `c` is a call `k a` of a known
  closure computing an expression (`val k := fun x => (closed) ret e[x]`) becomes `ret e[a]`
  whatever `e[a]` is (a literal, a data literal, a neutral expression of any level); when `c`
  is `share n`, it becomes `ret n`;
* **inlining a call as a shared expression of any level**: `let y := k a; b` becomes
  `let y := share e[a]; b` when `e[a]` is neutral (of any level, where `Term.inlineKnown` asks
  for the level of the call);
* **dead bindings**: `let y := c; b` and `val k := v; b` where `b` does not mention the binder
  become `b`, even when this changes the level;
* **an open closure called in tail position**: `val k := fun x => (open) body; let y := k a;
  ret y` becomes `body[x := a]` at the depth of the call (`Term.openTailCall?`; `a` costs
  nothing to repeat, or `x` is used at most once).  The substitution reduces a case analysis
  that `a` makes known (`case x of …` for an enum literal `a` is the arm of its constructor);
* **an open closure called once, anywhere in the `let`s after it**: `val k := fun x => (open)
  body; let y := k a; rest` becomes `body[x := a]` with its answer bound to `y`
  (`Term.openLetCall?`, `Term.bindRet`: `rest` becomes a join point when the body ends in a
  branch).

**Proved:** `Term.inlineRet_eval` (the value does not change, in any environment) and
`Term.numCalls_inlineRet` (no call is added).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

/-- Use `r` when it has the level `o` of `t`, otherwise keep `t`. -/
def Term.keepLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) (r : (o' : Lvl) × Term Δ d Φ Γ τ js o') : Term Δ d Φ Γ τ js o :=
  if h : r.1 = o then h ▸ r.2 else t

/-- The answer of a computation as a pure expression, when it is known: `share n` answers `n`,
    a call of a known closure computing an expression answers that expression. -/
def Comp.answer? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat} (I : KInfo Δ Φ) :
    Comp Δ d Φ Γ σ ℓ → Option ((o : Lvl) × PExpr Δ Φ Γ σ o)
  | .share n => some ⟨_, .neu n⟩
  | .app (.kvar k) a _ => (I.get k).bind fun e => e.apply a
  | _ => none

/-- `b` with its innermost unknown replaced by `p`, when `b` is `ret x` or `jump j x` for that
    unknown `x`. -/
def Term.substTail {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    {op : Lvl} (p : PExpr Δ Φ Γ σ op) :
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o →
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | _, _, _, .ret e => e.isHead?.map fun h => ⟨_, .ret (h.down ▸ p)⟩
  | _, _, _, .jump j e => e.isHead?.map fun h => ⟨_, .jump j (h.down ▸ p)⟩
  | _, _, _, .letV _ _ _ => none
  | _, _, _, .letE _ _ _ => none
  | _, _, _, .record_casesOn _ _ _ => none
  | _, _, _, .branch _ => none

/-- A computation sharing the pure expression, when it is neutral (of any level). -/
def PExpr.shareAny? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} :
    {o : Lvl} → PExpr Δ Φ Γ τ o → Option ((ℓ : Nat) × Comp Δ d Φ Γ τ ℓ)
  | _, .neu n => some ⟨_, .share n⟩
  | _, _ => none

/-- What the walk knows about the known values in scope: the closures computing an expression
    (`KInfo`) and the closures with a closed body (`BInfo`). -/
structure RInfo (Δ : DSig ks) (Φ : KCtx ks) : Type where
  e : KInfo Δ Φ
  b : BInfo Δ Φ

/-- Nothing is known. -/
def RInfo.empty {Φ : KCtx ks} : RInfo Δ Φ := ⟨KInfo.empty, BInfo.empty⟩

/-- Seen from a closed body. -/
def RInfo.toClosed {Φ : KCtx ks} (I : RInfo Δ Φ) : RInfo Δ (KCtx.closedOnly Φ) :=
  ⟨I.e.toClosed, I.b.toClosed⟩

/-- The body of a closure bound by `val` used once (the closures used more than once are not
    inlined, so that no code is duplicated). -/
def Val.blockFnIf {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} {o : Lvl} :
    Usage1ω → Val Δ d Φ Γ ty o → Option (BlockFn Δ Φ ty)
  | .one, v => v.blockFn?
  | .many, _ => none

/-- What is known under `val k := v` (used `u` times). -/
def RInfo.cons {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {o : Lvl} (u : Usage1ω)
    (v : Val Δ d Φ Γ σ o) (I : RInfo Δ Φ) : RInfo Δ (⟨σ, u, o, true⟩ :: Φ) :=
  ⟨KInfo.cons v.exprFn? I.e, BInfo.cons (v.blockFnIf u) I.b⟩

/-- The body of the closure called by `c`, at the call, when `c` calls a known closure with a
    closed body and no call (`BlockFn.applyP`: the argument is any pure expression). -/
def Comp.blockCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat} {js : JCtx ks}
    (B : BInfo Δ Φ) : Comp Δ d Φ Γ σ ℓ → Option ((o : Lvl) × Term Δ d Φ Γ σ js o)
  | .app (.kvar k) a _ =>
      (B.get k).bind fun f => if f.body.numCalls = 0 then f.applyP a else none
  | _ => none

/-- `let y := c; b` where `c` calls a known closure with a closed body: the body in tail
    position, or a straight-line body followed by `b`. -/
def Term.blockLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (B : BInfo Δ Φ) (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    Option ((o : Lvl) × Term Δ d Φ Γ τ js o) :=
  match b.retHead? with
  | some h => (c.blockCall? B (js := js)).map fun r => ⟨r.1, h.down ▸ r.2⟩
  | none => (c.blockCall? B (js := [])).bind fun r => Term.bindRet r.2 b

/-- `Term.blockLetE` after naming by `let` (up to `fuel`) the fields of a record literal passed
    to the call that compute something, so that the inlined body can take the record apart
    without repeating them. -/
def Term.blockLetS {d : Nat} {Φ : KCtx ks} {σ τ : Ty ks} {js : JCtx ks} (B : BInfo Δ Φ)
    (u : Usage1ω) : (fuel : Nat) → {Γ : UCtx ks} → {ℓ : Nat} → {o' : Lvl} → Comp Δ d Φ Γ σ ℓ →
    Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o' → Option ((o : Lvl) × Term Δ d Φ Γ τ js o)
  | 0, _, _, _, c, b => Term.blockLetE B u c b
  | fuel + 1, _, _, _, c, b =>
      match c.shareArg? with
      | none => Term.blockLetE B u c b
      | some ⟨_, _, n, _, c'⟩ =>
          (b.rename KRen.id (URen.lift URen.wk1 _) JRen.id).bind fun b' =>
            (Term.blockLetS B u fuel c' b').map fun r => ⟨_, .letE .many (.share n) r.2⟩

/-- `let y := c; b` (both already walked), with the rewrites of the tail, of a shared answer
    and of a dead `let`. -/
def Term.retLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (I : RInfo Δ Φ) (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match b.rename KRen.id URen.drop JRen.id with
  | some b' => ⟨_, b'⟩
  | none =>
      match c.answer? I.e with
      | some ⟨_, p⟩ =>
          match Term.substTail p b with
          | some r => r
          | none =>
              match p.shareAny? (d := d) with
              | some ⟨_, c'⟩ => ⟨_, .letE u c' b⟩
              | none => ⟨_, .letE u c b⟩
      | none =>
          match Term.blockLetE I.b u c b with
          | some r => r
          | none => (Term.blockLetS I.b u 16 c b).getD ⟨_, .letE u c b⟩

/-- A closure with an open body. -/
structure OpenFn (Δ : DSig ks) (d : Nat) (Φ : KCtx ks) (Γ : UCtx ks) (ty : Ty ks) where
  σ : Ty ks
  τ : Ty ks
  hty : ty = .fn σ τ
  u : Usage01ω
  m : Nat
  body : Term Δ (d + 1) Φ (⟨σ, u, d + 1⟩ :: Γ) τ [] (some m)

def Val.openFn? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} :
    {o : Lvl} → Val Δ d Φ Γ ty o → Option (OpenFn Δ d Φ Γ ty)
  | _, .lam (.opened t _) => some ⟨_, _, rfl, _, _, t⟩
  | _, _ => none

/-- Is the known variable the innermost one? -/
def KVar.isHead? {Φ : KCtx ks} {b : KBinder ks} {t : Ty ks} {o : Lvl} :
    KVar (b :: Φ) t o → Option (PLift (t = b.ty))
  | .head => some ⟨rfl⟩
  | .tail _ => none

/-- Is the pure expression the innermost known variable? -/
def PExpr.isKHead? {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} {t : Ty ks} :
    {o : Lvl} → PExpr Δ (b :: Φ) Γ t o → Option (PLift (t = b.ty))
  | _, .kvar k => k.isHead?
  | _, _ => none

/-- A call `k a` of the innermost known variable `k`: the argument `a`. -/
def Comp.appHead? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d (b :: Φ) Γ τ ℓ →
      Option ((σ : Ty ks) × (oa : Lvl) × PExpr Δ (b :: Φ) Γ σ oa × PLift (b.ty = .fn σ τ))
  | .app f a _ => f.isKHead?.map fun h => ⟨_, _, a, ⟨h.down.symm⟩⟩
  | _ => none

/-- `let y := k a; ret y` for the innermost known variable `k`: the argument `a`. -/
def Term.tailCallHead? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} {τ : Ty ks}
    {js : JCtx ks} : {o' : Lvl} → Term Δ d (b :: Φ) Γ τ js o' →
      Option ((σ : Ty ks) × (oa : Lvl) × PExpr Δ (b :: Φ) Γ σ oa × PLift (b.ty = .fn σ τ))
  | _, .letE _ c rest =>
      match c.appHead?, rest.retHead? with
      | some ⟨σ, oa, a, ⟨h₁⟩⟩, some ⟨h₂⟩ => some ⟨σ, oa, a, ⟨h₂ ▸ h₁⟩⟩
      | _, _ => none
  | _, _ => none

/-- `val k := fun x => (open) body; let y := k a; ret y` (`k` used nowhere else): the body at
    the depth of the call, `x` replaced by `a` (a pure expression that costs nothing to repeat,
    or any one when `x` is used at most once). -/
def Term.openTailCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} (u : Usage1ω) (v : Val Δ d Φ Γ ty o)
    (b : Term Δ d (⟨ty, u, o, true⟩ :: Φ) Γ τ js o') :
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'') :=
  match v.openFn?, b.tailCallHead? with
  | some ⟨σ₁, τ₁, _, uₓ, _, body⟩, some ⟨σa, _, a, _⟩ =>
      if hst : σa = σ₁ ∧ τ₁ = τ then
        match a.rename KRen.drop URen.id with
        | some a' =>
            if a'.isCheap || uₓ.atMostOnce then
              (body.subst (D' := d) (js' := js) KLRen.id
                (USub.cons ⟨_, hst.1 ▸ a'⟩ (USub.ofRen ULRen.idL)) JRen.ofNil).map
                fun r => ⟨r.1, hst.2 ▸ r.2⟩
            else none
        | none => none
      else none
  | _, _ => none

/-- `val k := fun x => (open) body; let y := k a; rest` (`k` used nowhere else, so `rest` does
    not mention it): the body at the depth of the call, `x` replaced by `a` (a pure expression
    that costs nothing to repeat, or any one when `x` is used at most once), its answer bound to
    `y` (`Term.bindRet`: when the body ends in a branch, `rest` becomes a join point that its
    answers jump to).  The calls of the body are moved, not copied. -/
def Term.openLetCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} (u : Usage1ω) (v : Val Δ d Φ Γ ty o)
    (b : Term Δ d (⟨ty, u, o, true⟩ :: Φ) Γ τ js o') :
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'') :=
  match v.openFn?, b with
  | some ⟨σ₁, τ₁, _, uₓ, _, body⟩, .letE (σ := σc) _ c rest =>
      match c.appHead? with
      | some ⟨σa, _, a, _⟩ =>
          if hst : σa = σ₁ ∧ τ₁ = σc then
            match a.rename KRen.drop URen.id, rest.rename KRen.drop URen.id JRen.id with
            | some a', some rest' =>
                if a'.isCheap || uₓ.atMostOnce then
                  (body.subst (D' := d) (js' := []) KLRen.id
                    (USub.cons ⟨_, hst.1 ▸ a'⟩ (USub.ofRen ULRen.idL)) JRen.ofNil).bind
                    fun r => Term.bindRet (hst.2 ▸ r.2 : Term Δ d Φ Γ σc [] r.1) rest'
                else none
            | _, _ => none
          else none
      | none => none
  | _, _ => none

/-- `val k := v; b` (both already walked), dropped when `b` does not mention `k`; when `k` is a
    closure with a closed body called exactly once in `b` (`Term.inlineAt`), its body replaces
    the call; when `k` is a closure with an open body and `b` is `let y := k a; ret y`
    (`Term.openTailCall?`), `b` is the body of `k` with its parameter replaced by `a`. -/
def Term.retLetV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
    (u : Usage1ω) (v : Val Δ d Φ Γ σ o) (b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o') :
    (o'' : Lvl) × Term Δ d Φ Γ τ js o'' :=
  match b.rename KRen.drop URen.id JRen.id with
  | some b' => ⟨_, b'⟩
  | none =>
      match v.blockFn?.bind fun f => b.inlineAt (InlTgt.single (b := ⟨σ, u, o, true⟩) f) with
      | some r => r
      | none =>
          match Term.openTailCall? u v b with
          | some r => r
          | none =>
              match Term.openLetCall? u v b with
              | some r => r
              | none => ⟨_, .letV u v b⟩

/-! ## The walk -/

mutual
/-- `Term.retWalk` inside the bodies of a value (the level of the value is kept). -/
def Val.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → RInfo Δ Φ → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b, I => .lam (b.retWalk I)
  | _, _, _, _, _, .thunk_mk b, I => .thunk_mk (b.retWalk I)
  | _, _, _, _, _, .lazy_mk b, I => .lazy_mk (b.retWalk I)
  | _, _, _, _, _, .record_mk args, _ => .record_mk args
  | _, _, _, _, _, .union_mk ix args, _ => .union_mk ix args
  | _, _, _, _, _, .array_mk es, _ => .array_mk es
  | _, _, _, _, _, .list_mk es, _ => .list_mk es
  | _, _, _, _, _, .data_in b j e, _ => .data_in b j e
/-- `Term.retWalk` in a body: free in a closed body, level kept in an open one. -/
def Body.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → RInfo Δ Φ → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t, I => .closed (t.retWalk I.toClosed).2
  | _, _, _, _, _, _, .opened t h, I => .opened (t.keepLvl (t.retWalk I)) h
/-- `Term.retWalk` in the bodies of a computation. -/
def Comp.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → RInfo Δ Φ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h, _ => .app f a h
  | _, _, _, _, _, .share n, _ => .share n
  | _, _, _, _, _, .nat_rec n z s h, I => .nat_rec n z (s.retWalk I) h
  | _, _, _, _, _, .array_foldl a z s h, I => .array_foldl a z (s.retWalk I) h
  | _, _, _, _, _, .data_rec b ρ us brs j e h, I =>
      .data_rec b ρ us (fun i => (brs i).retWalk I) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h, I =>
      .data_brec b ρ k us (fun i => (brs i).retWalk I) j e h
  | _, _, _, _, _, .thunk_force e, _ => .thunk_force e
  | _, _, _, _, _, .lazy_force e, _ => .lazy_force e
/-- **The walk**, knowing `I` about the known values in scope; the level may change. -/
def Term.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → RInfo Δ Φ → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, .ret e, _ => ⟨_, .ret e⟩
  | _, _, _, _, _, _, .letV u v b, I =>
      let v' := v.retWalk I
      Term.retLetV u v' (b.retWalk (RInfo.cons u v' I)).2
  | _, _, _, _, _, _, .letE u c b, I => Term.retLetE I u (c.retWalk I) (b.retWalk I).2
  | _, _, _, _, _, _, .record_casesOn us n b, I => ⟨_, .record_casesOn us n (b.retWalk I).2⟩
  | _, _, _, _, _, _, .branch br, I => ⟨_, .branch (br.retWalk I).2⟩
  | _, _, _, _, _, _, .jump j e, _ => ⟨_, .jump j e⟩
/-- `Term.retWalk` in a branch. -/
def Branch.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → RInfo Δ Φ → (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, .ite c t e, I => ⟨_, .ite c (t.retWalk I).2 (e.retWalk I).2⟩
  | _, _, _, _, _, _, .enum_casesOn e bs, I =>
      ⟨_, .enum_casesOn e (fun i => ((bs i).retWalk I).2)⟩
  | _, _, _, _, _, _, .union_casesOn e bs, I => ⟨_, .union_casesOn e (bs.retWalk I).2⟩
  | _, _, _, _, _, _, .join σ u uₓ body main, I =>
      ⟨_, .join σ u uₓ (body.retWalk I).2 (main.retWalk I).2⟩
/-- `Term.retWalk` in the branches of a union's case analysis. -/
def Branches.retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → RInfo Δ Φ → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I =>
      ⟨_, .two us₁ us₂ (b₁.retWalk I).2 (b₂.retWalk I).2⟩
  | _, _, _, _, _, _, _, _, .cons us b bs, I => ⟨_, .cons us (b.retWalk I).2 (bs.retWalk I).2⟩
end

/-- **Inlining in tail position and dropping dead bindings, the level allowed to change
    inside closed bodies.**  At the top the level is kept. -/
def Term.inlineRet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.keepLvl (t.retWalk RInfo.empty)

end LeanScript

end
