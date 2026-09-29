module

public import LeanScript.Term.Optimize.Subst

@[expose] public section

set_option autoImplicit false

/-!
# Inlining with arguments and answers that are not neutral

The pieces of `LeanScript.Term.Optimize.InlineBlock` rename the parameter of an inlined body to
an unknown, and bind the answer of a straight-line body with `let y := share e` — so both the
argument and the answer had to be neutral.  With `Term.subst` (`LeanScript.Term.Optimize.Subst`)
they can be any pure expression:

* `BlockFn.applyP`: the body of a known closure at a call `k a`, `a` any pure expression.  The
  parameter is renamed to `a` when `a` is neutral (`BlockFn.applyNeu`), otherwise `a` is
  substituted for it (a known closure passed to the closure is then called by name, a record
  built for the call is taken apart by the body without being built);
* `Term.bindRet`: a straight-line body `…; ret e` followed by the rest `b` of the caller, `e`
  any pure expression: `let y := share e; b` when `e` is neutral, otherwise `b` with `e`
  substituted for `y`.

A pure expression that is not a name or a literal (a record, a constructor, an array or list
literal, a layer of a datatype) is substituted only for a variable used at most once; one used
more often is first bound by `val` (`let` cannot name it), and its name substituted, so that no
value is built twice.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Small maps -/

/-- The unknowns renamed to themselves. -/
def ULRen.idL {Γ : UCtx ks} : ULRen Γ Γ := fun x => some ⟨_, x⟩

/-- No unknown to substitute. -/
def USub.none {Φ' : KCtx ks} {Γ' : UCtx ks} : USub Δ Φ' [] Γ' := fun x => nomatch x

/-- One more known value in the target, the levels kept. -/
def KLRen.wk1 {Φ : KCtx ks} {b : KBinder ks} : KLRen Φ (b :: Φ) := fun k => some ⟨_, .tail k⟩

/-- A pure expression that costs nothing to repeat: a known value by name, a literal. -/
def PExpr.isAtom {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} : {o : Lvl} → PExpr Δ Φ Γ τ o → Bool
  | _, .kvar _ => true
  | _, .lit _ _ => true
  | _, .enum_mk _ _ => true
  | _, _ => false

/-- A pure expression that is a value of known shape (a constructor or a literal of a
    collection). -/
def PExpr.toVal? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} :
    {o : Lvl} → PExpr Δ Φ Γ τ o → Option (Val Δ d Φ Γ τ o)
  | _, .record_mk args => some (.record_mk args)
  | _, .union_mk ix args => some (.union_mk ix args)
  | _, .array_mk es => some (.array_mk es)
  | _, .list_mk es => some (.list_mk es)
  | _, .data_in b j e => some (.data_in b j e)
  | _, _ => none

/-! ## Binding a pure expression to the innermost unknown -/

/-- `b` with the pure expression `e` for its innermost unknown (used `u` times): substituted
    when it is an atom or `u` is at most one, otherwise bound by `val` first. -/
def Term.bindAns {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} {u : Usage01ω} (e : PExpr Δ Φ Γ σ o) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') :
    Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'') :=
  if e.isAtom || u.atMostOnce then
    b.subst KLRen.id (USub.cons ⟨_, e⟩ (USub.ofRen ULRen.idL)) JRen.id
  else
    (e.toVal? (d := d)).bind fun v =>
      (b.subst (KLRen.wk1 (b := ⟨σ, .many, o, true⟩))
          (USub.cons ⟨_, .kvar .head⟩ (USub.ofRen ULRen.idL)) JRen.id).map
        fun r => ⟨_, .letV .many v r.2⟩

/-- `t`, whose answer is then bound to the innermost unknown of `b`: `t` is a line of `let`s and
    case analyses of records ending in `ret e` (the answer is `let y := share e; b` at its end
    when `e` is neutral, `b` with `e` for `y` otherwise, `Term.bindAns`), or in a branch (`b`
    becomes a join point, and the answers of the branch jump to it). -/
def Term.bindRet {d : Nat} {σ τ : Ty ks} {u : Usage1ω} :
    {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o o' : Lvl} → Term Δ d Φ Γ σ [] o →
    Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o' → Option ((o'' : Lvl) × Term Δ d Φ Γ τ js o'')
  | _, _, _, _, _, .ret e, b =>
      match e.toNeu? with
      | some n => some ⟨_, .letE u (.share n.2) b⟩
      | none => Term.bindAns e b
  | _, _, _, _, _, .letE u' c t, b =>
      (b.rename KRen.id (URen.lift URen.wk1 _) JRen.id).bind fun b' =>
        (Term.bindRet t b').map fun r => ⟨_, .letE u' c r.2⟩
  | _, _, _, _, _, .letV u' v t, b =>
      (b.rename KRen.wk1 URen.id JRen.id).bind fun b' =>
        (Term.bindRet t b').map fun r => ⟨_, .letV u' v r.2⟩
  | _, _, _, _, _, .record_casesOn us n t, b =>
      (b.rename KRen.id (URen.lift (URen.wkN _) _) JRen.id).bind fun b' =>
        (Term.bindRet t b').map fun r => ⟨_, .record_casesOn us n r.2⟩
  | _, _, _, _, _, .branch br, b =>
      some ⟨_, .branch (.join _ .many _ b (br.retToJump JMap.ofNil .head))⟩
  | _, _, _, _, _, .jump _ _, _ => none

/-! ## The body at a call on any argument -/

/-- The body of `f`, at depth `d`, applied to the pure expression `a`: `BlockFn.applyNeu` when
    `a` is neutral; otherwise `a` is substituted for the parameter (bound by `val` first when
    it is not an atom and the parameter is used more than once). -/
def BlockFn.applyP {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {oa : Lvl} (f : BlockFn Δ Φ (.fn σ τ)) (a : PExpr Δ Φ Γ σ oa) :
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o') :=
  match a.toNeu? with
  | some n => f.applyNeu n.2
  | none =>
      match f with
      | ⟨σ', τ', _, u, _, _, body⟩ =>
          if hs : σ' = σ ∧ τ' = τ then
            let body : Term Δ _ Φ [⟨σ, u, _⟩] τ [] _ := hs.2 ▸ hs.1 ▸ body
            if a.isAtom || u.atMostOnce then
              body.subst (D' := d) KLRen.id (USub.cons ⟨_, a⟩ USub.none) JRen.ofNil
            else
              (a.toVal? (d := d)).bind fun v =>
                (body.subst (D' := d) (KLRen.wk1 (b := ⟨σ, .many, oa, true⟩))
                    (USub.cons ⟨_, .kvar .head⟩ USub.none) JRen.ofNil).map
                  fun r => ⟨_, .letV .many v r.2⟩
          else none


/-! ## Sharing the fields of a record built for a call -/

/-- A neutral expression that is not an unknown (it computes something). -/
def Neu.isVar {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Bool
  | .var _ => true
  | _ => false

/-- The first argument that is a neutral expression computing something, taken out: it is named
    by a new unknown (at level `d`), which replaces it among the arguments. -/
def Args.shareFirst (d : Nat) {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Option ((τ : Ty ks) × (ℓn : Nat) × Neu Δ Φ Γ τ ℓn × (o' : Lvl) ×
      Args Δ Φ (⟨τ, Usage1ω.many.toUsage01ω, d⟩ :: Γ) σs o')
  | _, _, .nil => none
  | _, _, .cons a as =>
      match a with
      | .neu n =>
          if n.isVar then
            (Args.shareFirst d as).bind fun r =>
              (PExpr.rename KRen.id URen.wk1 (.neu n)).map fun a' =>
                ⟨r.1, r.2.1, r.2.2.1, _, .cons a' r.2.2.2.2⟩
          else
            (as.rename KRen.id URen.wk1).map fun as' =>
              ⟨_, _, n, _, .cons (.neu (.var (.head (by decide)))) as'⟩
      | a =>
          (Args.shareFirst d as).bind fun r =>
            (a.rename KRen.id URen.wk1).map fun a' => ⟨r.1, r.2.1, r.2.2.1, _, .cons a' r.2.2.2.2⟩

/-- A call of a known value on a record literal with a field that computes something: that field,
    and the call with the field named by a new unknown. -/
def Comp.shareArg? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ σ ℓ → Option ((τ : Ty ks) × (ℓn : Nat) × Neu Δ Φ Γ τ ℓn × (ℓ' : Nat) ×
      Comp Δ d Φ (⟨τ, Usage1ω.many.toUsage01ω, d⟩ :: Γ) σ ℓ')
  | .app (.kvar k) (.record_mk args) _ =>
      (Args.shareFirst d args).bind fun r =>
        (Lvl.some? (Lvl.meet _ r.2.2.2.1)).map fun h =>
          ⟨r.1, r.2.1, r.2.2.1, _, .app (.kvar k) (.record_mk r.2.2.2.2) h.2⟩
  | _ => none

/-! ## The innermost unknown -/

/-- The innermost unknown, as a variable: its type is the one of the binder. -/
def UVar.isHead? {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat} :
    {τ : Ty ks} → {ℓ' : Nat} → UVar (⟨σ, u, ℓ⟩ :: Γ) τ ℓ' → Option (PLift (τ = σ))
  | _, _, .head _ => some ⟨rfl⟩
  | _, _, .tail _ => none

/-- The innermost unknown, as a neutral expression. -/
def Neu.isHead? {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat} :
    {τ : Ty ks} → {ℓ' : Nat} → Neu Δ Φ (⟨σ, u, ℓ⟩ :: Γ) τ ℓ' → Option (PLift (τ = σ))
  | _, _, .var x => x.isHead?
  | _, _, .data_out _ _ _ => none
  | _, _, .cond _ _ _ => none
  | _, _, .extern _ _ _ => none

/-- The innermost unknown, as a pure expression. -/
def PExpr.isHead? {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat} :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ (⟨σ, u, ℓ⟩ :: Γ) τ o → Option (PLift (τ = σ))
  | _, _, .neu n => n.isHead?
  | _, _, .kvar _ => none
  | _, _, .lit _ _ => none
  | _, _, .enum_mk _ _ => none
  | _, _, .record_mk _ => none
  | _, _, .union_mk _ _ => none
  | _, _, .array_mk _ => none
  | _, _, .list_mk _ => none
  | _, _, .data_in _ _ _ => none

/-- `b` is `ret x` for its innermost unknown `x`. -/
def Term.retHead? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat} :
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o →
    Option (PLift (τ = σ))
  | _, _, _, .ret e => e.isHead?
  | _, _, _, .jump _ _ => none
  | _, _, _, .letV _ _ _ => none
  | _, _, _, .letE _ _ _ => none
  | _, _, _, .record_casesOn _ _ _ => none
  | _, _, _, .branch _ => none

end LeanScript

end
