module

public import LeanScript.Term.Optimize.Append
public import LeanScript.Term.Rename.Weaken

@[expose] public section

set_option autoImplicit false

/-!
# Known sequence literals in append chains

`val k := #["a", "b"]; …; let y := share (k ++ xs)`: the append chain `k ++ xs` has a literal
operand that is only known by name, so `Term.appendWalk` cannot merge it with its neighbours,
and the JavaScript backend writes `array__lean_array_append_mutable(["a", "b"], xs)` instead of
the literal `["a", "b", ...xs]`.

`Term.knownLits` (`Term.litWalk`) walks a statement knowing, for each known value in scope, whether it is a
**constant** array or list literal (`LitOf`: a literal whose elements mention no variable at
all, `PExpr.cst?`), and replaces every operand of an append (`lean_array_append`,
`lean_list_append`) that names such a value by the literal itself (`Neu.litOpnds`).
`Term.appendWalk`, run right after it, then merges the literal with its neighbours, and
dead-code elimination drops the `val` when nothing else refers to it.

Only operands of appends are replaced: there the literal is copied into the result anyway, so
writing it in place costs nothing, whereas elsewhere it would build the literal once per use
instead of once.  A constant literal does not depend on the contexts, so the facts need no
weakening under binders; they are dropped in closed bodies (which see another known context).

**Proved:** `Term.knownLits_eval` (the value does not change) and `Term.numCalls_knownLits` (no
call is added: only pure expressions change).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Constant pure expressions -/

section Cst
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
/-- The pure expression as a constant (no variable, so in the empty contexts), when it mentions
    no variable at all: a literal, or a literal constructor of constants. -/
def PExpr.cst? : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Option (PExpr Δ [] [] τ none)
  | _, _, .neu _ => none
  | _, _, .kvar _ => none
  | _, _, .lit p v => some (.lit p v)
  | _, _, .enum_mk s i => some (.enum_mk s i)
  | _, _, .record_mk args => args.cst?.map .record_mk
  | _, _, .union_mk ix args => args.cst?.map (.union_mk ix)
  | _, _, .array_mk es => es.cst?.map .array_mk
  | _, _, .list_mk es => es.cst?.map .list_mk
  | _, _, .data_in b j e => e.cst?.map (.data_in b j)
/-- Constant arguments. -/
def Args.cst? : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Option (Args Δ [] [] σs none)
  | _, _, .nil => some .nil
  | _, _, .cons a as =>
    match a.cst?, as.cst? with
    | some a', some as' => some (.cons a' as')
    | _, _ => none
/-- Constant elements. -/
def Elems.cst? : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Option (Elems Δ [] [] t none)
  | _, _, .nil => some .nil
  | _, _, .cons e es =>
    match e.cst?, es.cst? with
    | some e', some es' => some (.cons e' es')
    | _, _ => none
end

mutual
theorem PExpr.cst?_eval : {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) →
    (c : PExpr Δ [] [] τ none) → e.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    e.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .neu _, _, h, _, _ => by simp [PExpr.cst?] at h
  | _, _, .kvar _, _, h, _, _ => by simp [PExpr.cst?] at h
  | _, _, .lit _ _, c, h, _, _ => by simp only [PExpr.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .enum_mk _ _, c, h, _, _ => by
      simp only [PExpr.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .record_mk args, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [PExpr.eval, Args.cst?_eval args a' ha κ ρ] <;> rfl
  | _, _, .union_mk _ args, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [PExpr.eval, Args.cst?_eval args a' ha κ ρ] <;> rfl
  | _, _, .array_mk es, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, Elems.cst?_eval es e' he κ ρ] <;> rfl
  | _, _, .list_mk es, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, Elems.cst?_eval es e' he κ ρ] <;> rfl
  | _, _, .data_in _ _ e, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, PExpr.cst?_eval e e' he κ ρ] <;> rfl
theorem Args.cst?_eval : {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    (c : Args Δ [] [] σs none) → as.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    as.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .nil, c, h, _, _ => by simp only [Args.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons a as, c, h, κ, ρ => by
      simp only [Args.cst?] at h
      split at h
      · rename_i a' as' ha has
        cases h
        simp only [Args.eval, PExpr.cst?_eval a a' ha κ ρ, Args.cst?_eval as as' has κ ρ]
      · cases h
theorem Elems.cst?_eval : {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) →
    (c : Elems Δ [] [] t none) → es.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    es.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .nil, c, h, _, _ => by simp only [Elems.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons e es, c, h, κ, ρ => by
      simp only [Elems.cst?] at h
      split at h
      · rename_i e' es' he hes
        cases h
        simp only [Elems.eval, PExpr.cst?_eval e e' he κ ρ, Elems.cst?_eval es es' hes κ ρ]
      · cases h
end

end Cst

/-! ## Constants in any context -/

/-- The empty list, embedded into any list. -/
def Thin.nilTo {α : Type} : (ys : List α) → Thin [] ys
  | [] => .nil
  | _ :: ys => .skip (Thin.nilTo ys)

section Embed
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
theorem Neu.thin_nil_eval (θk : Thin [] Φ) (θu : Thin [] Γ) : {τ : Ty ks} → {ℓ : Nat} →
    (n : Neu Δ [] [] τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (n.thin θk θu).eval κ ρ = n.eval Tuple.nil Tuple.nil
  | _, _, .var x, _, _ => nomatch x
  | _, _, .data_out _ _ n, κ, ρ => by
      simp only [Neu.thin, Neu.eval, Neu.thin_nil_eval θk θu n κ ρ]
  | _, _, .cond c a b, κ, ρ => by
      simp only [Neu.thin, Neu.eval, Neu.thin_nil_eval θk θu c κ ρ,
        PExpr.thin_nil_eval θk θu a κ ρ, PExpr.thin_nil_eval θk θu b κ ρ]
  | _, _, .extern _ args _, κ, ρ => by
      simp only [Neu.thin, Neu.eval, Args.thin_nil_eval θk θu args κ ρ]
theorem PExpr.thin_nil_eval (θk : Thin [] Φ) (θu : Thin [] Γ) : {τ : Ty ks} → {o : Lvl} →
    (e : PExpr Δ [] [] τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (e.thin θk θu).eval κ ρ = e.eval Tuple.nil Tuple.nil
  | _, _, .neu n, κ, ρ => by simp only [PExpr.thin, PExpr.eval, Neu.thin_nil_eval θk θu n κ ρ]
  | _, _, .kvar k, _, _ => nomatch k
  | _, _, .lit _ _, _, _ => rfl
  | _, _, .enum_mk _ _, _, _ => rfl
  | _, _, .record_mk args, κ, ρ => by
      simp only [PExpr.thin, PExpr.eval, Args.thin_nil_eval θk θu args κ ρ] <;> rfl
  | _, _, .union_mk _ args, κ, ρ => by
      simp only [PExpr.thin, PExpr.eval, Args.thin_nil_eval θk θu args κ ρ] <;> rfl
  | _, _, .array_mk es, κ, ρ => by
      simp only [PExpr.thin, PExpr.eval, Elems.thin_nil_eval θk θu es κ ρ] <;> rfl
  | _, _, .list_mk es, κ, ρ => by
      simp only [PExpr.thin, PExpr.eval, Elems.thin_nil_eval θk θu es κ ρ] <;> rfl
  | _, _, .data_in _ _ e, κ, ρ => by
      simp only [PExpr.thin, PExpr.eval, PExpr.thin_nil_eval θk θu e κ ρ] <;> rfl
theorem Args.thin_nil_eval (θk : Thin [] Φ) (θu : Thin [] Γ) : {σs : List (Ty ks)} →
    {o : Lvl} → (as : Args Δ [] [] σs o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (as.thin θk θu).eval κ ρ = as.eval Tuple.nil Tuple.nil
  | _, _, .nil, _, _ => rfl
  | _, _, .cons a as, κ, ρ => by
      simp only [Args.thin, Args.eval, PExpr.thin_nil_eval θk θu a κ ρ,
        Args.thin_nil_eval θk θu as κ ρ]
theorem Elems.thin_nil_eval (θk : Thin [] Φ) (θu : Thin [] Γ) : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ [] [] t o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (es.thin θk θu).eval κ ρ = es.eval Tuple.nil Tuple.nil
  | _, _, .nil, _, _ => rfl
  | _, _, .cons e es, κ, ρ => by
      simp only [Elems.thin, Elems.eval, PExpr.thin_nil_eval θk θu e κ ρ,
        Elems.thin_nil_eval θk θu es κ ρ]
end

end Embed

/-! ## Known constant literals -/

/-- A constant array or list literal, the value of a known variable of type `τ` and level `o`. -/
inductive LitOf (Δ : DSig ks) : Ty ks → Lvl → Type where
  | mk (k : SeqKind) {t : Ty ks} (c : Elems Δ [] [] t none) : LitOf Δ (k.ty t) none

/-- The literal, in any context. -/
def LitOf.expr {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} → LitOf Δ τ o →
    PExpr Δ Φ Γ τ o
  | _, _, .mk k c => k.lit (c.thin (Thin.nilTo _) (Thin.nilTo _))

/-- The value of the literal. -/
def LitOf.den : {τ : Ty ks} → {o : Lvl} → LitOf Δ τ o → Ty.Den Δ τ
  | _, _, .mk k c => (k.lit c).eval (Φ := []) (Γ := []) Tuple.nil Tuple.nil

theorem LitOf.expr_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (f : LitOf Δ τ o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (f.expr : PExpr Δ Φ Γ τ o).eval κ ρ = f.den := by
  cases f with
  | mk k c =>
    apply SeqKind.toL_inj k
    simp only [LitOf.expr, LitOf.den, SeqKind.lit_eval, Elems.thin_nil_eval]

/-- What is known of the known values in scope: which are constant sequence literals. -/
structure LitInfo (Δ : DSig ks) (Φ : KCtx ks) : Type where
  get : ∀ {τ : Ty ks} {o : Lvl}, KVar Φ τ o → Option (LitOf Δ τ o)

/-- Nothing is known. -/
def LitInfo.empty {Φ : KCtx ks} : LitInfo Δ Φ := ⟨fun _ => none⟩

/-- The lookup under one more `val`, whose value is `new` when known. -/
def LitInfo.consGet {Φ : KCtx ks} (I : LitInfo Δ Φ) {σ : Ty ks} {u : Usage1ω} {o : Lvl}
    (new : Option (LitOf Δ σ o)) : {τ : Ty ks} → {o' : Lvl} →
    KVar (⟨σ, u, o, true⟩ :: Φ) τ o' → Option (LitOf Δ τ o')
  | _, _, .head => new
  | _, _, .tail x => I.get x

/-- Under one more `val`, whose value is `new` when known. -/
def LitInfo.cons {Φ : KCtx ks} (I : LitInfo Δ Φ) {σ : Ty ks} {u : Usage1ω} {o : Lvl}
    (new : Option (LitOf Δ σ o)) : LitInfo Δ (⟨σ, u, o, true⟩ :: Φ) :=
  ⟨fun x => I.consGet new x⟩

/-- What is known holds in the known environment `κ`. -/
def LitInfo.Holds {Φ : KCtx ks} (I : LitInfo Δ Φ) (κ : KEnv Δ Φ) : Prop :=
  ∀ {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o) (f : LitOf Δ τ o), I.get x = some f → κ.get x = f.den

theorem LitInfo.empty_holds {Φ : KCtx ks} (κ : KEnv Δ Φ) :
    LitInfo.Holds (LitInfo.empty (Δ := Δ) (Φ := Φ)) κ :=
  fun _ _ h => by simp [LitInfo.empty] at h

/-- The constant literal a value is, when it is one. -/
def Val.litOf? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Option (LitOf Δ τ o)
  | _, none, .array_mk es => es.cst?.map (LitOf.mk .array)
  | _, none, .list_mk es => es.cst?.map (LitOf.mk .list)
  | _, _, _ => none

theorem Val.litOf?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ τ o) (f : LitOf Δ τ o) (h : v.litOf? = some f) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : v.eval κ ρ = f.den := by
  unfold Val.litOf? at h
  split at h
  · rename_i es
    revert h
    cases hc : es.cst? with
    | none => intro h; cases h
    | some c =>
      intro h; cases h
      simp only [Val.eval, LitOf.den, SeqKind.lit, PExpr.eval, Elems.cst?_eval _ c hc κ ρ] <;> rfl
  · rename_i es
    revert h
    cases hc : es.cst? with
    | none => intro h; cases h
    | some c =>
      intro h; cases h
      simp only [Val.eval, LitOf.den, SeqKind.lit, PExpr.eval, Elems.cst?_eval _ c hc κ ρ] <;> rfl
  · cases h

theorem LitInfo.cons_holds {Φ : KCtx ks} {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ)
    {σ : Ty ks} {u : Usage1ω} {o : Lvl} (new : Option (LitOf Δ σ o)) (v : Ty.Den Δ σ)
    (hnew : ∀ f, new = some f → v = f.den) :
    (I.cons (u := u) new).Holds (Tuple.cons v κ : KEnv Δ (⟨σ, u, o, true⟩ :: Φ)) := by
  intro τ o' x f hx
  cases x with
  | head => simp only [KEnv.get, Tuple.head_cons]; exact hnew f hx
  | tail x => simp only [KEnv.get, Tuple.tail_cons]; exact hI x f hx

/-! ## Replacing the operands of appends -/

section Walk
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- A known constant literal named by an operand is written in place. -/
def PExpr.subLit (I : LitInfo Δ Φ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    PExpr Δ Φ Γ τ o
  | _, _, .kvar x =>
    match I.get x with
    | some f => f.expr
    | none => .kvar x
  | _, _, e => e

theorem PExpr.subLit_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) {τ : Ty ks}
    {o : Lvl} (e : PExpr Δ Φ Γ τ o) (ρ : UEnv Δ Γ) : (e.subLit I).eval κ ρ = e.eval κ ρ := by
  unfold PExpr.subLit
  split
  · rename_i x
    split
    · rename_i f hf
      rw [LitOf.expr_eval, PExpr.eval, hI x f hf]
    · rfl
  · rfl

/-- An append of arrays or of lists, with its operands that name known constant literals
    written in place (the same value wherever `I` holds). -/
def Neu.litApp? (I : LitInfo Δ Φ) : {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) →
    Option {m : Neu Δ Φ Γ τ ℓ // ∀ κ, I.Holds κ → ∀ ρ, m.eval κ ρ = n.eval κ ρ}
  | .array _, _, .extern (.arrayStdExtern (.lean_array_append t)) (.cons a (.cons b .nil)) h =>
      some ⟨.extern (.arrayStdExtern (.lean_array_append t))
        (.cons (a.subLit I) (.cons (b.subLit I) .nil)) h, fun _ hI ρ => by
          simp only [Neu.eval, Args.eval, PExpr.subLit_eval hI]⟩
  | .list _, _, .extern (.arrayStdExtern (.lean_list_append t)) (.cons a (.cons b .nil)) h =>
      some ⟨.extern (.arrayStdExtern (.lean_list_append t))
        (.cons (a.subLit I) (.cons (b.subLit I) .nil)) h, fun _ hI ρ => by
          simp only [Neu.eval, Args.eval, PExpr.subLit_eval hI]⟩
  | _, _, _ => none

/-- `Neu.litApp?`, or the neutral expression itself. -/
def Neu.litOpnds (I : LitInfo Δ Φ) {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) : Neu Δ Φ Γ τ ℓ :=
  match n.litApp? I with
  | some m => m.1
  | none => n

theorem Neu.litOpnds_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) {τ : Ty ks}
    {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) (ρ : UEnv Δ Γ) : (n.litOpnds I).eval κ ρ = n.eval κ ρ := by
  unfold Neu.litOpnds
  split
  · rename_i m _; exact m.2 κ hI ρ
  · rfl

mutual
/-- `Args.litOpnds` at every extern call of a neutral expression. -/
def Neu.litWalk (I : LitInfo Δ Φ) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j e => .data_out b j (e.litWalk I)
  | _, _, .cond c a b => .cond (c.litWalk I) (a.litWalk I) (b.litWalk I)
  | _, _, .extern e args h => Neu.litOpnds I (.extern e (args.litWalk I) h)
/-- `Neu.litWalk` in a pure expression. -/
def PExpr.litWalk (I : LitInfo Δ Φ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu (n.litWalk I)
  | _, _, .kvar k => .kvar k
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk (args.litWalk I)
  | _, _, .union_mk ix args => .union_mk ix (args.litWalk I)
  | _, _, .array_mk es => .array_mk (es.litWalk I)
  | _, _, .list_mk es => .list_mk (es.litWalk I)
  | _, _, .data_in b j e => .data_in b j (e.litWalk I)
/-- `Neu.litWalk` in arguments. -/
def Args.litWalk (I : LitInfo Δ Φ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons (a.litWalk I) (as.litWalk I)
/-- `Neu.litWalk` in the elements of a literal. -/
def Elems.litWalk (I : LitInfo Δ Φ) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons (e.litWalk I) (es.litWalk I)
end

mutual
theorem Neu.litWalk_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → (ρ : UEnv Δ Γ) →
    (n.litWalk I).eval κ ρ = n.eval κ ρ
  | _, _, .var _, _ => rfl
  | _, _, .data_out _ _ e, ρ => by simp only [Neu.litWalk, Neu.eval, Neu.litWalk_eval hI e ρ]
  | _, _, .cond c a b, ρ => by
      simp only [Neu.litWalk, Neu.eval, Neu.litWalk_eval hI c ρ, PExpr.litWalk_eval hI a ρ,
        PExpr.litWalk_eval hI b ρ]
  | _, _, .extern e args _, ρ => by
      simp only [Neu.litWalk, Neu.litOpnds_eval hI, Neu.eval, Args.litWalk_eval hI args ρ]
theorem PExpr.litWalk_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → (ρ : UEnv Δ Γ) →
    (e.litWalk I).eval κ ρ = e.eval κ ρ
  | _, _, .neu n, ρ => by simp only [PExpr.litWalk, PExpr.eval, Neu.litWalk_eval hI n ρ]
  | _, _, .kvar _, _ => rfl
  | _, _, .lit _ _, _ => rfl
  | _, _, .enum_mk _ _, _ => rfl
  | _, _, .record_mk args, ρ => by
      simp only [PExpr.litWalk, PExpr.eval, Args.litWalk_eval hI args ρ] <;> rfl
  | _, _, .union_mk _ args, ρ => by
      simp only [PExpr.litWalk, PExpr.eval, Args.litWalk_eval hI args ρ] <;> rfl
  | _, _, .array_mk es, ρ => by
      simp only [PExpr.litWalk, PExpr.eval, Elems.litWalk_eval hI es ρ] <;> rfl
  | _, _, .list_mk es, ρ => by
      simp only [PExpr.litWalk, PExpr.eval, Elems.litWalk_eval hI es ρ] <;> rfl
  | _, _, .data_in _ _ e, ρ => by
      simp only [PExpr.litWalk, PExpr.eval, PExpr.litWalk_eval hI e ρ] <;> rfl
theorem Args.litWalk_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) → (ρ : UEnv Δ Γ) →
    (as.litWalk I).eval κ ρ = as.eval κ ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons a as, ρ => by
      simp only [Args.litWalk, Args.eval, PExpr.litWalk_eval hI a ρ, Args.litWalk_eval hI as ρ]
theorem Elems.litWalk_eval {I : LitInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → (ρ : UEnv Δ Γ) →
    (es.litWalk I).eval κ ρ = es.eval κ ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons e es, ρ => by
      simp only [Elems.litWalk, Elems.eval, PExpr.litWalk_eval hI e ρ, Elems.litWalk_eval hI es ρ]
end

end Walk

/-! ## The walk over statements -/

mutual
/-- `Term.litWalk` in a value. -/
def Val.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    LitInfo Δ Φ → Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, I, .lam b => .lam (b.litWalk I)
  | _, _, _, _, _, I, .thunk_mk b => .thunk_mk (b.litWalk I)
  | _, _, _, _, _, I, .lazy_mk b => .lazy_mk (b.litWalk I)
  | _, _, _, _, _, I, .record_mk args => .record_mk (args.litWalk I)
  | _, _, _, _, _, I, .union_mk ix args => .union_mk ix (args.litWalk I)
  | _, _, _, _, _, I, .array_mk es => .array_mk (es.litWalk I)
  | _, _, _, _, _, I, .list_mk es => .list_mk (es.litWalk I)
  | _, _, _, _, _, I, .data_in b j e => .data_in b j (e.litWalk I)
/-- `Term.litWalk` in a body: a closed body sees other known values, and starts knowing
    nothing. -/
def Body.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    LitInfo Δ Φ → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, _, .closed t => .closed (t.litWalk LitInfo.empty)
  | _, _, _, _, _, _, I, .opened t h => .opened (t.litWalk I) h
/-- `Term.litWalk` in a computation. -/
def Comp.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    LitInfo Δ Φ → Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, I, .app f a h => .app (f.litWalk I) (a.litWalk I) h
  | _, _, _, _, _, I, .share n => .share (n.litWalk I)
  | _, _, _, _, _, I, .nat_rec n z s h => .nat_rec (n.litWalk I) (z.litWalk I) (s.litWalk I) h
  | _, _, _, _, _, I, .array_foldl a z s h =>
      .array_foldl (a.litWalk I) (z.litWalk I) (s.litWalk I) h
  | _, _, _, _, _, I, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).litWalk I) j (e.litWalk I) h
  | _, _, _, _, _, I, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).litWalk I) j (e.litWalk I) h
  | _, _, _, _, _, I, .thunk_force e => .thunk_force (e.litWalk I)
  | _, _, _, _, _, I, .lazy_force e => .lazy_force (e.litWalk I)
/-- **Known constant literals written in place in append chains** (`Neu.litOpnds`): walk a
    statement knowing `I`; a `val` of a constant array or list literal is known in its body. -/
def Term.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → LitInfo Δ Φ → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, I, .ret e => .ret (e.litWalk I)
  | _, _, _, _, _, _, I, .letV u v b => .letV u (v.litWalk I) (b.litWalk (I.cons v.litOf?))
  | _, _, _, _, _, _, I, .letE u c b => .letE u (c.litWalk I) (b.litWalk I)
  | _, _, _, _, _, _, I, .record_casesOn us n b => .record_casesOn us (n.litWalk I) (b.litWalk I)
  | _, _, _, _, _, _, I, .branch br => .branch (br.litWalk I)
  | _, _, _, _, _, _, I, .jump j e => .jump j (e.litWalk I)
/-- `Term.litWalk` in a branch. -/
def Branch.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → LitInfo Δ Φ → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, I, .ite c t e => .ite (c.litWalk I) (t.litWalk I) (e.litWalk I)
  | _, _, _, _, _, _, I, .enum_casesOn e bs =>
      .enum_casesOn (e.litWalk I) (fun i => (bs i).litWalk I)
  | _, _, _, _, _, _, I, .union_casesOn e bs => .union_casesOn (e.litWalk I) (bs.litWalk I)
  | _, _, _, _, _, _, I, .join σ u uₓ body main =>
      .join σ u uₓ (body.litWalk I) (main.litWalk I)
/-- `Term.litWalk` in the branches of a union's case analysis. -/
def Branches.litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    LitInfo Δ Φ → Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, I, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ (b₁.litWalk I) (b₂.litWalk I)
  | _, _, _, _, _, _, _, _, I, .cons us b bs => .cons us (b.litWalk I) (bs.litWalk I)
end

mutual
theorem Val.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : LitInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Holds κ →
    (ρ : UEnv Δ Γ) → (v.litWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval]; funext x; rw [Body.litWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .thunk_mk b, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval]; rw [Body.litWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .lazy_mk b, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval]; rw [Body.litWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .record_mk args, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval, Args.litWalk_eval hI args ρ] <;> rfl
  | _, _, _, _, _, .union_mk _ args, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval, Args.litWalk_eval hI args ρ] <;> rfl
  | _, _, _, _, _, .array_mk es, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval, Elems.litWalk_eval hI es ρ] <;> rfl
  | _, _, _, _, _, .list_mk es, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval, Elems.litWalk_eval hI es ρ] <;> rfl
  | _, _, _, _, _, .data_in _ _ e, I, κ, hI, ρ => by
      simp only [Val.litWalk, Val.eval, PExpr.litWalk_eval hI e ρ]
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Body.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : LitInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Holds κ →
    (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (b.litWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, κ, _, _, _ => by
      simp only [Body.litWalk, Body.eval]
      exact Term.litWalk_eval t _ _ (LitInfo.empty_holds _) _ _
  | _, _, _, _, _, _, .opened t _, I, κ, hI, _, _ => by
      simp only [Body.litWalk, Body.eval]; exact Term.litWalk_eval t I κ hI _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Comp.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : LitInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Holds κ →
    (ρ : UEnv Δ Γ) → (c.litWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a _, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI f ρ, PExpr.litWalk_eval hI a ρ]
  | _, _, _, _, _, .share n, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, Neu.litWalk_eval hI n ρ]
  | _, _, _, _, _, .nat_rec n z s _, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI n ρ, PExpr.litWalk_eval hI z ρ]
      congr 1; funext k acc; exact Body.litWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .array_foldl a z s _, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval]
      rw [PExpr.litWalk_eval hI a ρ, PExpr.litWalk_eval hI z ρ]
      congr 1; funext acc x; exact Body.litWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI e ρ]
      congr 1; funext i x; exact Body.litWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI e ρ]
      congr 1; funext i x; exact Body.litWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .thunk_force e, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI e ρ]
  | _, _, _, _, _, .lazy_force e, I, κ, hI, ρ => by
      simp only [Comp.litWalk, Comp.eval, PExpr.litWalk_eval hI e ρ]
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Term.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : LitInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Holds κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (t.litWalk I).eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, I, κ, hI, ρ, _ => by
      simp only [Term.litWalk, Term.eval, PExpr.litWalk_eval hI e ρ]
  | _, _, _, _, _, _, .letV u v b, I, κ, hI, ρ, jκ => by
      simp only [Term.litWalk, Term.eval, Val.litWalk_eval v I κ hI ρ]
      exact Term.litWalk_eval b _ _ (LitInfo.cons_holds hI _ _
        (fun f hf => Val.litOf?_eval v f hf κ ρ)) ρ jκ
  | _, _, _, _, _, _, .letE u c b, I, κ, hI, ρ, jκ => by
      simp only [Term.litWalk, Term.eval, Comp.litWalk_eval c I κ hI ρ,
        Term.litWalk_eval b I κ hI _ jκ]
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, hI, ρ, jκ => by
      simp only [Term.litWalk, Term.eval, Neu.litWalk_eval hI n ρ,
        Term.litWalk_eval b I κ hI _ jκ]
  | _, _, _, _, _, _, .branch br, I, κ, hI, ρ, jκ => by
      simp only [Term.litWalk, Term.eval, Branch.litWalk_eval br I κ hI ρ jκ]
  | _, _, _, _, _, _, .jump _ e, I, κ, hI, ρ, jκ => by
      simp only [Term.litWalk, Term.eval, PExpr.litWalk_eval hI e ρ]
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branch.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : LitInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Holds κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (br.litWalk I).eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, hI, ρ, jκ => by
      simp only [Branch.litWalk, Branch.eval, Neu.litWalk_eval hI c ρ,
        Term.litWalk_eval t I κ hI ρ jκ, Term.litWalk_eval e I κ hI ρ jκ]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.litWalk, Branch.eval]; rw [Neu.litWalk_eval hI e ρ]
      exact Term.litWalk_eval _ I κ hI ρ jκ
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.litWalk, Branch.eval, Neu.litWalk_eval hI e ρ]
      exact Branches.litWalk_eval bs I κ hI ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, hI, ρ, jκ => by
      simp only [Branch.litWalk, Branch.eval, Branch.litWalk_eval main I κ hI ρ _]
      congr 2
      funext v
      exact Term.litWalk_eval body I κ hI _ jκ
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branches.litWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : LitInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Holds κ →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → ∀ x, (br.litWalk I).eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.litWalk, Branches.eval]
      congr 1
      · funext v; exact Term.litWalk_eval b₁ I κ hI _ jκ
      · funext v; exact Term.litWalk_eval b₂ I κ hI _ jκ
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.litWalk, Branches.eval]
      congr 1
      · funext v; exact Term.litWalk_eval b I κ hI _ jκ
      · funext r; exact Branches.litWalk_eval bs I κ hI ρ jκ r
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ _ _ => x
end

/-- `Term.litWalk` from the top of a statement, knowing nothing. -/
def Term.knownLits {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.litWalk LitInfo.empty

/-- **Writing the known constant literals in place does not change the value.** -/
theorem Term.knownLits_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : t.knownLits.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.litWalk_eval t _ κ (LitInfo.empty_holds κ) ρ jκ

/-! ## No call is added -/

mutual
theorem Val.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (I : LitInfo Δ Φ) → (v : Val Δ d Φ Γ τ o) → (v.litWalk I).numCalls = v.numCalls
  | _, _, _, _, _, I, .lam b => by simp only [Val.litWalk, Val.numCalls, Body.numCalls_litWalk I b]
  | _, _, _, _, _, I, .thunk_mk b => by
      simp only [Val.litWalk, Val.numCalls, Body.numCalls_litWalk I b]
  | _, _, _, _, _, I, .lazy_mk b => by
      simp only [Val.litWalk, Val.numCalls, Body.numCalls_litWalk I b]
  | _, _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Body.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (I : LitInfo Δ Φ) → (b : Body Δ d Φ Γ bs τ o) → (b.litWalk I).numCalls = b.numCalls
  | _, _, _, _, _, _, _, .closed t => by
      simp only [Body.litWalk, Body.numCalls, Term.numCalls_litWalk _ t]
  | _, _, _, _, _, _, I, .opened t _ => by
      simp only [Body.litWalk, Body.numCalls, Term.numCalls_litWalk I t]
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Comp.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (I : LitInfo Δ Φ) → (c : Comp Δ d Φ Γ τ ℓ) → (c.litWalk I).numCalls = c.numCalls
  | _, _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, I, .nat_rec _ _ s _ => by
      simp only [Comp.litWalk, Comp.numCalls, Body.numCalls_litWalk I s]
  | _, _, _, _, _, I, .array_foldl _ _ s _ => by
      simp only [Comp.litWalk, Comp.numCalls, Body.numCalls_litWalk I s]
  | _, _, _, _, _, I, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.litWalk, Comp.numCalls, Body.numCalls_litWalk I]
  | _, _, _, _, _, I, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.litWalk, Comp.numCalls, Body.numCalls_litWalk I]
  | _, _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Term.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (I : LitInfo Δ Φ) → (t : Term Δ d Φ Γ τ js o) →
    (t.litWalk I).numCalls = t.numCalls
  | _, _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, I, .letV _ v b => by
      simp only [Term.litWalk, Term.numCalls, Val.numCalls_litWalk I v, Term.numCalls_litWalk _ b]
  | _, _, _, _, _, _, I, .letE _ c b => by
      simp only [Term.litWalk, Term.numCalls, Comp.numCalls_litWalk I c, Term.numCalls_litWalk I b]
  | _, _, _, _, _, _, I, .record_casesOn _ _ b => by
      simp only [Term.litWalk, Term.numCalls, Term.numCalls_litWalk I b]
  | _, _, _, _, _, _, I, .branch br => by
      simp only [Term.litWalk, Term.numCalls, Branch.numCalls_litWalk I br]
  | _, _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Branch.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (I : LitInfo Δ Φ) → (br : Branch Δ d Φ Γ τ js ℓ) →
    (br.litWalk I).numCalls = br.numCalls
  | _, _, _, _, _, _, I, .ite c t e => by
      simp only [Branch.litWalk, Branch.numCalls, Term.numCalls_litWalk I t,
        Term.numCalls_litWalk I e]
  | _, _, _, _, _, _, I, .enum_casesOn _ bs => by
      simp only [Branch.litWalk, Branch.numCalls, Term.numCalls_litWalk I]
  | _, _, _, _, _, _, I, .union_casesOn _ bs => by
      simp only [Branch.litWalk, Branch.numCalls, Branches.numCalls_litWalk I bs]
  | _, _, _, _, _, _, I, .join _ _ _ body main => by
      simp only [Branch.litWalk, Branch.numCalls, Term.numCalls_litWalk I body,
        Branch.numCalls_litWalk I main]
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Branches.numCalls_litWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (I : LitInfo Δ Φ) → (br : Branches Δ d Φ Γ cs τ js o) → (br.litWalk I).numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, I, .two _ _ b₁ b₂ => by
      simp only [Branches.litWalk, Branches.numCalls, Term.numCalls_litWalk I b₁,
        Term.numCalls_litWalk I b₂]
  | _, _, _, _, _, _, _, _, I, .cons _ b bs => by
      simp only [Branches.litWalk, Branches.numCalls, Term.numCalls_litWalk I b,
        Branches.numCalls_litWalk I bs]
  termination_by structural _ _ _ _ _ _ _ _ _ x => x
end

/-- Writing the known constant literals in place adds no call. -/
theorem Term.numCalls_knownLits {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.knownLits.numCalls = t.numCalls :=
  Term.numCalls_litWalk _ t

end LeanScript

end
