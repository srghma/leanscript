module

public import LeanScript.Term.Optimize.HoistExpr
public import LeanScript.Term.Optimize.Cond
public import LeanScript.Term.Optimize.CountRename

@[expose] public section

set_option autoImplicit false

/-!
# A test both arms of an `if` begin with is made first

`Branch.shareTest p t e`: when both arms of `if p then t else e` begin by testing the same
condition `q` and do the same thing when it holds,

```
if p then (if q then X else Y)          if q then X
     else (if q then X else Z)    ⟹    else if p then Y else Z
```

(and symmetrically when they do the same thing when `q` does *not* hold:
`if p then (if q then Y else X) else (if q then Z else X)` is
`if q then (if p then Y else Z) else X`).  The language is pure and total, so the two tests
can be swapped; the rewritten statement never evaluates more tests than the original (one
fewer when `q` holds), and `X` is written once instead of twice.  This is the order the
compiled `match` of purescript-backend-optimizer tests a row whose earlier columns are
wildcards: `| ⟨_, 4, _⟩ => …` after `| ⟨1, 2, 3⟩` is tested before the column that the later
rows constrain.

An arm "begins with a test" when it is `if q then X else Y` or the conditional answer
`ret (q ? a : b)` (read as `if q then ret a else ret b`, `Term.testView?`).  The two
conditions are recognised as the same by a syntactic comparison (`Neu.same`: the same
unknowns, known values, literals and calls of externs, `Extern.beq`), which implies that they
have the same value (`Neu.same_eval`); the shared arm `X` must be an answer `ret a` or a jump
`jump j a` written the same way in both (`Term.sameTail`).

The rewrite is proved to preserve the value (`Branch.shareTest_eval`), and to add no call
(`Branch.numCalls_shareTest`).  `Term.shareTestWalk` applies it at every `if`, bottom-up.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Literals, externs -/

/-- Are two literals of a leaf type recognised as equal?  (Only for the leaves whose equality
    is decidable structurally; `false` otherwise.) -/
def LeanPrimTy.litBEq : (p : LeanPrimTy) → p.denote → p.denote → Bool
  | .bool, a, b => decide (a = b)
  | .nat, a, b => decide (a = b)
  | .int, a, b => decide (a = b)
  | .uint8, a, b => decide (a = b)
  | .uint16, a, b => decide (a = b)
  | .uint32, a, b => decide (a = b)
  | .uint64, a, b => decide (a = b)
  | .int8, a, b => decide (a = b)
  | .int16, a, b => decide (a = b)
  | .int32, a, b => decide (a = b)
  | .int64, a, b => decide (a = b)
  | .char, a, b => decide (a = b)
  | .string, a, b => decide (a = b)
  | .float, a, b => decide (a = b)
  | .float32, a, b => decide (a = b)
  | _, _, _ => false

theorem LeanPrimTy.eq_of_litBEq (p : LeanPrimTy) (a b : p.denote) (h : p.litBEq a b = true) :
    a = b := by
  cases p <;> simp_all [LeanPrimTy.litBEq]

/-- The entries of `PreludeExtern` that take no type argument, by their constructor index
    (`Extern.beq` does not recognise the entries of this family: some of them take one). -/
def Extern.preludeOfIdx (ks : List Nat) :
    Nat → Option ((σs : List (Ty ks)) × (τ : Ty ks) × Extern ks σs τ)
  | 0 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat_mk⟩
  | 1 => some ⟨_, _, .preludeExtern .lean_uint32_dec_eq⟩
  | 2 => some ⟨_, _, .preludeExtern .lean_uint32_dec_lt⟩
  | 3 => some ⟨_, _, .preludeExtern .lean_nat_div⟩
  | 4 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat__UInt32_ofNatLT⟩
  | 5 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat__Char_ofNatAux⟩
  | 7 => some ⟨_, _, .preludeExtern .lean_uint8_to_nat__UInt8_toBitVec⟩
  | 8 => some ⟨_, _, .preludeExtern .lean_nat_dec_lt⟩
  | 9 => some ⟨_, _, .preludeExtern .lean_nat_mod__Nat_modCore⟩
  | 10 => some ⟨_, _, .preludeExtern .lean_nat_mod__Nat_mod⟩
  | 12 => some ⟨_, _, .preludeExtern .lean_nat_sub⟩
  | 13 => some ⟨_, _, .preludeExtern .lean_uint8_dec_lt⟩
  | 14 => some ⟨_, _, .preludeExtern .lean_uint32_dec_le⟩
  | 17 => some ⟨_, _, .preludeExtern .lean_nat_dec_eq__Nat_decEq⟩
  | 18 => some ⟨_, _, .preludeExtern .lean_nat_dec_eq__Nat_beq⟩
  | 21 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat__UInt8_ofNat⟩
  | 22 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat__UInt8_ofNatLT⟩
  | 23 => some ⟨_, _, .preludeExtern .lean_uint8_dec_le⟩
  | 24 => some ⟨_, _, .preludeExtern .lean_nat_dec_le__Nat_ble⟩
  | 25 => some ⟨_, _, .preludeExtern .lean_nat_dec_le__Nat_decLe⟩
  | 27 => some ⟨_, _, .preludeExtern .lean_nat_add⟩
  | 29 => some ⟨_, _, .preludeExtern .lean_uint16_to_nat__UInt16_toBitVec⟩
  | 30 => some ⟨_, _, .preludeExtern .lean_uint16_of_nat_mk⟩
  | 31 => some ⟨_, _, .preludeExtern .lean_uint16_dec_eq⟩
  | 32 => some ⟨_, _, .preludeExtern .lean_string_dec_eq⟩
  | 33 => some ⟨_, _, .preludeExtern .lean_nat_pred⟩
  | 34 => some ⟨_, _, .preludeExtern .lean_string_mk__String_ofList⟩
  | 35 => some ⟨_, _, .preludeExtern .lean_string_hash⟩
  | 36 => some ⟨_, _, .preludeExtern .lean_uint64_to_nat__UInt64_toBitVec⟩
  | 37 => some ⟨_, _, .preludeExtern .lean_uint64_of_nat_mk⟩
  | 38 => some ⟨_, _, .preludeExtern .lean_uint32_to_nat__UInt32_toNat⟩
  | 39 => some ⟨_, _, .preludeExtern .lean_uint32_to_nat__UInt32_toBitVec⟩
  | 40 => some ⟨_, _, .preludeExtern .lean_uint64_dec_eq⟩
  | 41 => some ⟨_, _, .preludeExtern .lean_uint16_of_nat__UInt16_ofNatLT⟩
  | 42 => some ⟨_, _, .preludeExtern .lean_name_eq⟩
  | 43 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat_mk⟩
  | 44 => some ⟨_, _, .preludeExtern .lean_uint8_dec_eq⟩
  | 45 => some ⟨_, _, .preludeExtern .lean_nat_pow⟩
  | 46 => some ⟨_, _, .preludeExtern .lean_nat_mul⟩
  | 47 => some ⟨_, _, .preludeExtern .lean_string_utf8_byte_size⟩
  | 49 => some ⟨_, _, .preludeExtern .lean_uint64_mix_hash⟩
  | 50 => some ⟨_, _, .preludeExtern .lean_uint64_of_nat__UInt64_ofNatLT⟩
  | _ => none

/-- The constructor index of an entry of `PreludeExtern`. -/
def Extern.preludeIdx? {σs : List (Ty ks)} {τ : Ty ks} : Extern ks σs τ → Option Nat
  | .preludeExtern e => some e.ctorIdx
  | _ => none

theorem Extern.preludeOfIdx_eq {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) (k : Nat)
    (hk : e.preludeIdx? = some k) (x : (σs : List (Ty ks)) × (τ : Ty ks) × Extern ks σs τ)
    (h : Extern.preludeOfIdx ks k = some x) : x = ⟨σs, τ, e⟩ := by
  cases e with
  | preludeExtern e =>
      simp only [Extern.preludeIdx?, Option.some.injEq] at hk
      subst hk
      cases e <;> simp [Extern.preludeOfIdx, PreludeExtern.ctorIdx] at h <;> exact h.symm
  | _ => simp [Extern.preludeIdx?] at hk

/-- Are two calls of externs, maybe of different signatures, recognised as the same extern?
    (By `Extern.beq`, or as the same entry of `PreludeExtern` without type argument.) -/
def Extern.hbeq {σs σs' : List (Ty ks)} {τ τ' : Ty ks} (e : Extern ks σs τ)
    (e' : Extern ks σs' τ') : Bool :=
  (if h : σs = σs' ∧ τ = τ' then Extern.beq (h.1 ▸ h.2 ▸ e) e' else false) ||
  (match e.preludeIdx?, e'.preludeIdx? with
    | some k, some k' => k == k' && (Extern.preludeOfIdx ks k).isSome
    | _, _ => false)

theorem Extern.hbeq_eq {σs σs' : List (Ty ks)} {τ τ' : Ty ks} {e : Extern ks σs τ}
    {e' : Extern ks σs' τ'} (h : e.hbeq e' = true) : σs = σs' ∧ τ = τ' ∧ HEq e e' := by
  unfold Extern.hbeq at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨rfl, rfl, heq_of_eq (Extern.eq_of_beq h)⟩
    · cases h
  · split at h
    · rename_i k k' hk hk'
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨rfl, x, hx⟩ := h
      have e1 := Extern.preludeOfIdx_eq e k hk x hx
      have e2 := Extern.preludeOfIdx_eq e' k hk' x hx
      rw [e1] at e2
      cases e2
      exact ⟨rfl, rfl, HEq.rfl⟩
    · cases h

/-! ## Syntactic equality of pure expressions -/

theorem Fields.toList_inj : {fs fs' : Fields ks} → fs.toList = fs'.toList → fs = fs'
  | .one _, .one _, h => by simp only [Fields.toList, List.cons.injEq, and_true] at h; rw [h]
  | .one _, .cons _ fs', h => by
      cases fs' <;> simp [Fields.toList] at h
  | .cons _ fs, .one _, h => by
      cases fs <;> simp [Fields.toList] at h
  | .cons _ _, .cons _ _, h => by
      simp only [Fields.toList, List.cons.injEq] at h
      rw [h.1, Fields.toList_inj h.2]

section Same
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
/-- Are the two neutral expressions written the same way?  (Unknowns, conditionals and calls
    of externs are compared; `false` for anything else.) -/
def Neu.same : {τ τ' : Ty ks} → {ℓ ℓ' : Nat} → Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ' ℓ' → Bool
  | _, _, _, _, .var x, n' => match n' with
    | .var y => x.index == y.index
    | _ => false
  | _, _, _, _, .cond c a b, n' => match n' with
    | .cond c' a' b' => c.same c' && a.same a' && b.same b'
    | _ => false
  | _, _, _, _, .extern e args _, n' => match n' with
    | .extern e' args' _ => e.hbeq e' && args.same args'
    | _ => false
  | _, _, _, _, .data_out _ _ _, _ => false
/-- Are the two pure expressions written the same way?  (Neutral expressions, known values,
    literals of the leaves of `LeanPrimTy.litBEq` and constructors of enums; `false` for
    anything else.) -/
def PExpr.same : {τ τ' : Ty ks} → {o o' : Lvl} → PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ' o' → Bool
  | _, _, _, _, .neu n, e' => match e' with
    | .neu n' => n.same n'
    | _ => false
  | _, _, _, _, .kvar x, e' => match e' with
    | .kvar y => x.index == y.index
    | _ => false
  | _, _, _, _, .lit p v, e' => match e' with
    | .lit p' v' => if h : p = p' then p'.litBEq (h ▸ v) v' else false
    | _ => false
  | _, _, _, _, .enum_mk s i, e' => match e' with
    | .enum_mk s' i' => if h : s = s' then (h ▸ i) == i' else false
    | _ => false
  | _, _, _, _, .record_mk args, e' => match e' with
    | .record_mk args' => args.same args'
    | _ => false
  | _, _, _, _, .union_mk (bs := bs) (b := b) (cs := cs) (c := c) ix args, e' => match e' with
    | .union_mk (bs := bs') (b := b') (cs := cs') (c := c') ix' args' =>
        if (⟨bs, cs, b, c, ix⟩ : (bs : List Bool) × (cs : Ctors ks bs) × (b : Bool) ×
            (c : Ctor ks b) × CtorIx cs c) = ⟨bs', cs', b', c', ix'⟩ then args.same args'
        else false
    | _ => false
  | _, _, _, _, .array_mk es, e' => match e' with
    | .array_mk es' => es.same es'
    | _ => false
  | _, _, _, _, .list_mk es, e' => match e' with
    | .list_mk es' => es.same es'
    | _ => false
  | _, _, _, _, .data_in b j e, e' => match e' with
    | .data_in b' j' e'' => if h : b = b' then (h ▸ j) == j' && e.same e'' else false
    | _ => false
/-- Are the two element lists written the same way (of the same element type)? -/
def Elems.same : {t t' : Ty ks} → {o o' : Lvl} → Elems Δ Φ Γ t o → Elems Δ Φ Γ t' o' → Bool
  | t, t', _, _, .nil, es' => match es' with
    | .nil => decide (t = t')
    | _ => false
  | _, _, _, _, .cons e es, es' => match es' with
    | .cons e' es' => e.same e' && es.same es'
    | _ => false
/-- Are the two argument lists written the same way? -/
def Args.same : {σs σs' : List (Ty ks)} → {o o' : Lvl} → Args Δ Φ Γ σs o →
    Args Δ Φ Γ σs' o' → Bool
  | _, _, _, _, .nil, as' => match as' with
    | .nil => true
    | _ => false
  | _, _, _, _, .cons a as, as' => match as' with
    | .cons a' as' => a.same a' && as.same as'
    | _ => false
end

mutual
/-- Two neutral expressions written the same way have the same type and the same value. -/
theorem Neu.same_eval : {τ τ' : Ty ks} → {ℓ ℓ' : Nat} → (n : Neu Δ Φ Γ τ ℓ) →
    (n' : Neu Δ Φ Γ τ' ℓ') → n.same n' = true →
    τ = τ' ∧ ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ), HEq (n.eval κ ρ) (n'.eval κ ρ)
  | _, _, _, _, .var x, n', h => by
      cases n' with
      | var y =>
          have ⟨h1, h2⟩ := UVar.eq_of_index_eq (Δ := Δ) x y (by simpa [Neu.same] using h)
          exact ⟨h1, fun _ ρ => by simpa [Neu.eval] using h2 ρ⟩
      | _ => simp [Neu.same] at h
  | _, _, _, _, .cond c a b, n', h => by
      cases n' with
      | cond c' a' b' =>
          simp only [Neu.same, Bool.and_eq_true] at h
          obtain ⟨⟨hc, ha⟩, hb⟩ := h
          have ⟨_, hc2⟩ := Neu.same_eval c c' hc
          have ⟨hτ, ha2⟩ := PExpr.same_eval a a' ha
          have ⟨_, hb2⟩ := PExpr.same_eval b b' hb
          subst hτ
          refine ⟨rfl, fun κ ρ => ?_⟩
          have e1 : (c.eval κ ρ : Bool) = c'.eval κ ρ := eq_of_heq (hc2 κ ρ)
          simp only [Neu.eval, e1]
          split
          · exact ha2 κ ρ
          · exact hb2 κ ρ
      | _ => simp [Neu.same] at h
  | _, _, _, _, .extern e args _, n', h => by
      cases n' with
      | extern e' args' _ =>
          simp only [Neu.same, Bool.and_eq_true] at h
          obtain ⟨he, ha⟩ := h
          obtain ⟨rfl, rfl, he⟩ := Extern.hbeq_eq he
          cases he
          have ⟨_, ha2⟩ := Args.same_eval args args' ha
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [Neu.eval, eq_of_heq (ha2 κ ρ)]
          exact HEq.rfl
      | _ => simp [Neu.same] at h
  | _, _, _, _, .data_out _ _ _, _, h => by simp [Neu.same] at h
/-- Two pure expressions written the same way have the same type and the same value. -/
theorem PExpr.same_eval : {τ τ' : Ty ks} → {o o' : Lvl} → (e : PExpr Δ Φ Γ τ o) →
    (e' : PExpr Δ Φ Γ τ' o') → e.same e' = true →
    τ = τ' ∧ ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ), HEq (e.eval κ ρ) (e'.eval κ ρ)
  | _, _, _, _, .neu n, e', h => by
      cases e' with
      | neu n' =>
          have ⟨h1, h2⟩ := Neu.same_eval n n' (by simpa [PExpr.same] using h)
          exact ⟨h1, fun κ ρ => by simpa [PExpr.eval] using h2 κ ρ⟩
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .kvar x, e', h => by
      cases e' with
      | kvar y =>
          have ⟨h1, h2⟩ := KVar.eq_of_index_eq (Δ := Δ) x y (by simpa [PExpr.same] using h)
          exact ⟨h1, fun κ _ => by simpa [PExpr.eval] using h2 κ⟩
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .lit p v, e', h => by
      cases e' with
      | lit p' v' =>
          simp only [PExpr.same] at h
          split at h
          · rename_i hp
            subst hp
            have := LeanPrimTy.eq_of_litBEq p v v' h
            subst this
            exact ⟨rfl, fun _ _ => HEq.rfl⟩
          · cases h
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .enum_mk s i, e', h => by
      cases e' with
      | enum_mk s' i' =>
          simp only [PExpr.same] at h
          split at h
          · rename_i hs
            subst hs
            have : i = i' := by simpa using h
            subst this
            exact ⟨rfl, fun _ _ => HEq.rfl⟩
          · cases h
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .record_mk args, e', h => by
      cases e' with
      | record_mk args' =>
          simp only [PExpr.same] at h
          have ⟨h1, h2⟩ := Args.same_eval args args' h
          simp only [List.cons.injEq] at h1
          obtain ⟨rfl, h3⟩ := h1
          have := Fields.toList_inj h3
          subst this
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [PExpr.eval, eq_of_heq (h2 κ ρ)]
          exact HEq.rfl
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .union_mk ix args, e', h => by
      cases e' with
      | union_mk ix' args' =>
          simp only [PExpr.same] at h
          split at h
          · rename_i hs
            cases hs
            have ⟨_, h2⟩ := Args.same_eval args args' h
            refine ⟨rfl, fun κ ρ => ?_⟩
            simp only [PExpr.eval, eq_of_heq (h2 κ ρ)]
            exact HEq.rfl
          · cases h
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .array_mk es, e', h => by
      cases e' with
      | array_mk es' =>
          simp only [PExpr.same] at h
          have ⟨h1, h2⟩ := Elems.same_eval es es' h
          subst h1
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [PExpr.eval, eq_of_heq (h2 κ ρ)]
          exact HEq.rfl
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .list_mk es, e', h => by
      cases e' with
      | list_mk es' =>
          simp only [PExpr.same] at h
          have ⟨h1, h2⟩ := Elems.same_eval es es' h
          subst h1
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [PExpr.eval, eq_of_heq (h2 κ ρ)]
          exact HEq.rfl
      | _ => simp [PExpr.same] at h
  | _, _, _, _, .data_in b j e, e', h => by
      cases e' with
      | data_in b' j' e'' =>
          simp only [PExpr.same] at h
          split at h
          · rename_i hb
            subst hb
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨rfl, h1⟩ := h
            have ⟨_, h2⟩ := PExpr.same_eval e e'' h1
            refine ⟨rfl, fun κ ρ => ?_⟩
            simp only [PExpr.eval, eq_of_heq (h2 κ ρ)]
            exact HEq.rfl
          · cases h
      | _ => simp [PExpr.same] at h
/-- Two element lists written the same way have the same element type and the same values. -/
theorem Elems.same_eval : {t t' : Ty ks} → {o o' : Lvl} → (es : Elems Δ Φ Γ t o) →
    (es' : Elems Δ Φ Γ t' o') → es.same es' = true →
    t = t' ∧ ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ), HEq (es.eval κ ρ) (es'.eval κ ρ)
  | _, _, _, _, .nil, es', h => by
      cases es' with
      | nil =>
          simp only [Elems.same, decide_eq_true_eq] at h
          subst h
          exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [Elems.same.eq_def] at h
  | _, _, _, _, .cons e es, es', h => by
      cases es' with
      | cons e' es' =>
          simp only [Elems.same, Bool.and_eq_true] at h
          have ⟨h1, h2⟩ := PExpr.same_eval e e' h.1
          have ⟨_, h4⟩ := Elems.same_eval es es' h.2
          subst h1
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [Elems.eval, eq_of_heq (h2 κ ρ), eq_of_heq (h4 κ ρ)]
          exact HEq.rfl
      | _ => simp [Elems.same.eq_def] at h
/-- Two argument lists written the same way have the same types and the same values. -/
theorem Args.same_eval : {σs σs' : List (Ty ks)} → {o o' : Lvl} → (as : Args Δ Φ Γ σs o) →
    (as' : Args Δ Φ Γ σs' o') → as.same as' = true →
    σs = σs' ∧ ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ), HEq (as.eval κ ρ) (as'.eval κ ρ)
  | _, _, _, _, .nil, as', h => by
      cases as' with
      | nil => exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [Args.same] at h
  | _, _, _, _, .cons a as, as', h => by
      cases as' with
      | cons a' as' =>
          simp only [Args.same, Bool.and_eq_true] at h
          have ⟨h1, h2⟩ := PExpr.same_eval a a' h.1
          have ⟨h3, h4⟩ := Args.same_eval as as' h.2
          subst h1; subst h3
          refine ⟨rfl, fun κ ρ => ?_⟩
          simp only [Args.eval, eq_of_heq (h2 κ ρ), eq_of_heq (h4 κ ρ)]
          exact HEq.rfl
      | _ => simp [Args.same] at h
end

end Same

/-! ## The shared arm -/

section Tail
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- Are the two statements the same answer (`ret a`) or the same jump (`jump j a`)? -/
def Term.sameTail {o o' : Lvl} : Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o' → Bool
  | .ret e, t' => match t' with
    | .ret e' => e.same e'
    | _ => false
  | .jump j e, t' => match t' with
    | .jump j' e' => j.index == j'.index && e.same e'
    | _ => false
  | _, _ => false

theorem Term.sameTail_eval {o o' : Lvl} (t : Term Δ d Φ Γ τ js o) (t' : Term Δ d Φ Γ τ js o')
    (h : t.sameTail t' = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.eval κ ρ jκ = t'.eval κ ρ jκ := by
  cases t with
  | ret e =>
      cases t' with
      | ret e' =>
          simp only [Term.sameTail] at h
          simp only [Term.eval]
          exact eq_of_heq ((PExpr.same_eval e e' h).2 κ ρ)
      | _ => simp [Term.sameTail] at h
  | jump j e =>
      cases t' with
      | jump j' e' =>
          simp only [Term.sameTail, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hj, he⟩ := h
          have ⟨hσ, he2⟩ := PExpr.same_eval e e' he
          subst hσ
          rw [JVar.eq_of_index_eq j j' hj]
          simp only [Term.eval, eq_of_heq (he2 κ ρ)]
      | _ => simp [Term.sameTail] at h
  | _ => simp [Term.sameTail] at h

/-! ## Statements that begin with a test -/

/-- A statement read as `if q then t else e`. -/
structure TestView (Δ : DSig ks) (d : Nat) (Φ : KCtx ks) (Γ : UCtx ks) (τ : Ty ks)
    (js : JCtx ks) where
  ℓ : Nat
  q : Neu Δ Φ Γ .bool ℓ
  o₁ : Lvl
  o₂ : Lvl
  t : Term Δ d Φ Γ τ js o₁
  e : Term Δ d Φ Γ τ js o₂

/-- The conditional `q ? a : b`, as the test `if q then ret a else ret b`. -/
def Neu.condView? {τ' : Ty ks} {ℓ' : Nat} (hτ : τ' = τ) :
    Neu Δ Φ Γ τ' ℓ' → Option (TestView Δ d Φ Γ τ js)
  | .cond q a b => some ⟨_, q, _, _, .ret (hτ ▸ a), .ret (hτ ▸ b)⟩
  | _ => none

/-- `Neu.condView?` of a pure expression. -/
def PExpr.condView? {o : Lvl} : PExpr Δ Φ Γ τ o → Option (TestView Δ d Φ Γ τ js)
  | .neu n => Neu.condView? rfl n
  | _ => none

/-- The statement as `if q then t else e`, when it is an `if`, or the conditional answer
    `ret (q ? a : b)` (read as `if q then ret a else ret b`). -/
def Term.testView? {o : Lvl} : Term Δ d Φ Γ τ js o → Option (TestView Δ d Φ Γ τ js)
  | .branch br => match br with
    | .ite q t e => some ⟨_, q, _, _, t, e⟩
    | _ => none
  | .ret e => PExpr.condView? e
  | _ => none

theorem Neu.condView?_eval {τ' : Ty ks} {ℓ' : Nat} (hτ : τ' = τ) (n : Neu Δ Φ Γ τ' ℓ')
    (v : TestView Δ d Φ Γ τ js) (h : Neu.condView? hτ n = some v) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    hτ ▸ n.eval κ ρ = (Branch.ite v.q v.t v.e).eval κ ρ jκ := by
  subst hτ
  cases n with
  | cond q a b =>
      simp only [Neu.condView?, Option.some.injEq] at h
      subst h
      simp only [Term.eval, Neu.eval, Branch.eval]
  | _ => simp [Neu.condView?] at h

theorem Term.testView?_eval {o : Lvl} (t : Term Δ d Φ Γ τ js o) (v : TestView Δ d Φ Γ τ js)
    (h : t.testView? = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.eval κ ρ jκ = (Branch.ite v.q v.t v.e).eval κ ρ jκ := by
  cases t with
  | branch br =>
      cases br with
      | ite q t e => simp only [Term.testView?, Option.some.injEq] at h; subst h; rfl
      | _ => simp [Term.testView?] at h
  | ret e =>
      cases e with
      | neu n =>
          simp only [Term.testView?, PExpr.condView?] at h
          exact Neu.condView?_eval rfl n v h κ ρ jκ
      | _ => simp [Term.testView?, PExpr.condView?] at h
  | _ => simp [Term.testView?] at h

theorem Term.testView?_numCalls {o : Lvl} (t : Term Δ d Φ Γ τ js o)
    (v : TestView Δ d Φ Γ τ js) (h : t.testView? = some v) :
    v.t.numCalls + v.e.numCalls = t.numCalls := by
  cases t with
  | branch br =>
      cases br with
      | ite q t e => simp only [Term.testView?, Option.some.injEq] at h; subst h; rfl
      | _ => simp [Term.testView?] at h
  | ret e =>
      cases e with
      | neu n =>
          simp only [Term.testView?, PExpr.condView?] at h
          cases n with
          | cond q a b =>
              simp only [Neu.condView?, Option.some.injEq] at h
              subst h; rfl
          | _ => simp [Neu.condView?] at h
      | _ => simp [Term.testView?, PExpr.condView?] at h
  | _ => simp [Term.testView?] at h

/-! ## The rewrite -/

/-- `if p then t else e`, where, when both arms begin with the same test `q` and do the same
    thing when it holds (resp. when it does not), that test is made first:
    `if q then X else if p then Y else Z` (resp. `if q then (if p then Y else Z) else X`). -/
def Branch.shareTest {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) :=
  match t.testView?, e.testView? with
  | some vt, some ve =>
    if vt.q.same ve.q then
      if vt.t.sameTail ve.t then
        let b := Branch.ite vt.q vt.t (.branch (Branch.ite p vt.e ve.e))
        if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then b.castLvlC h else .ite p t e
      else if vt.e.sameTail ve.e then
        let b := Branch.ite vt.q (.branch (Branch.ite p vt.t ve.t)) vt.e
        if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then b.castLvlC h else .ite p t e
      else .ite p t e
    else .ite p t e
  | _, _ => .ite p t e

theorem Branch.shareTest_eval {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Branch.shareTest p t e).eval κ ρ jκ = (Branch.ite p t e).eval κ ρ jκ := by
  unfold Branch.shareTest
  split
  · rename_i vt ve hvt hve
    have et := Term.testView?_eval t vt hvt κ ρ jκ
    have ee := Term.testView?_eval e ve hve κ ρ jκ
    split
    · rename_i hq
      have eq : (vt.q.eval κ ρ : Bool) = ve.q.eval κ ρ :=
        eq_of_heq ((Neu.same_eval vt.q ve.q hq).2 κ ρ)
      split
      · rename_i hx
        have ex := Term.sameTail_eval vt.t ve.t hx κ ρ jκ
        split
        · rw [Branch.castLvlC_eval]
          simp only [Branch.eval, Term.eval] at et ee ⊢
          rw [et, ee, ← eq]
          cases (p.eval κ ρ : Bool) <;> cases (vt.q.eval κ ρ : Bool) <;> simp [ex]
        · rfl
      · split
        · rename_i _ hy
          have ey := Term.sameTail_eval vt.e ve.e hy κ ρ jκ
          split
          · rw [Branch.castLvlC_eval]
            simp only [Branch.eval, Term.eval] at et ee ⊢
            rw [et, ee, ← eq]
            cases (p.eval κ ρ : Bool) <;> cases (vt.q.eval κ ρ : Bool) <;> simp [ey]
          · rfl
        · rfl
    · rfl
  · rfl

theorem Branch.numCalls_shareTest {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    (Branch.shareTest p t e).numCalls ≤ (Branch.ite p t e).numCalls := by
  unfold Branch.shareTest
  split
  · rename_i vt ve hvt hve
    have ht := Term.testView?_numCalls t vt hvt
    have he := Term.testView?_numCalls e ve hve
    split
    · split
      · split
        · rw [Branch.numCalls_castLvlC]
          simp only [Branch.numCalls, Term.numCalls]; omega
        · exact Nat.le_refl _
      · split
        · split
          · rw [Branch.numCalls_castLvlC]
            simp only [Branch.numCalls, Term.numCalls]; omega
          · exact Nat.le_refl _
        · exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

end Tail

/-! ## The walk -/

mutual
/-- `Term.shareTestWalk` in a value. -/
def Val.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.shareTestWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.shareTestWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.shareTestWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.shareTestWalk` in a body. -/
def Body.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.shareTestWalk
  | _, _, _, _, _, _, .opened t h => .opened t.shareTestWalk h
/-- `Term.shareTestWalk` in a computation. -/
def Comp.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.shareTestWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.shareTestWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).shareTestWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).shareTestWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **A test both arms of an `if` begin with is made first** (`Branch.shareTest`), at every
    `if` of a statement, bottom-up. -/
def Term.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.shareTestWalk b.shareTestWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.shareTestWalk b.shareTestWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.shareTestWalk
  | _, _, _, _, _, _, .branch br => .branch br.shareTestWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.shareTestWalk` in a branch. -/
def Branch.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => Branch.shareTest c t.shareTestWalk e.shareTestWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).shareTestWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.shareTestWalk
  | _, _, _, _, _, _, .join σ u uₓ body main =>
      .join σ u uₓ body.shareTestWalk main.shareTestWalk
/-- `Term.shareTestWalk` in the branches of a union's case analysis. -/
def Branches.shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ =>
      .two us₁ us₂ b₁.shareTestWalk b₂.shareTestWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.shareTestWalk bs.shareTestWalk
end

mutual
theorem Val.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.shareTestWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.shareTestWalk, Val.eval]; funext x; rw [Body.shareTestWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.shareTestWalk, Val.eval]; rw [Body.shareTestWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.shareTestWalk, Val.eval]; rw [Body.shareTestWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.shareTestWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.shareTestWalk, Body.eval]; exact Term.shareTestWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.shareTestWalk, Body.eval]; exact Term.shareTestWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.shareTestWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.shareTestWalk, Comp.eval]
      congr 1; funext k acc; exact Body.shareTestWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.shareTestWalk, Comp.eval]
      congr 1; funext acc x; exact Body.shareTestWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.shareTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.shareTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.shareTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.shareTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
/-- **Making first a test both arms of an `if` begin with does not change the value of a
    statement.** -/
theorem Term.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.shareTestWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.shareTestWalk, Term.eval, Val.shareTestWalk_eval v,
        Term.shareTestWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.shareTestWalk, Term.eval, Comp.shareTestWalk_eval c,
        Term.shareTestWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.shareTestWalk, Term.eval, Term.shareTestWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.shareTestWalk, Term.eval, Branch.shareTestWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.shareTestWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.shareTestWalk]
      rw [Branch.shareTest_eval]
      simp only [Branch.eval, Term.shareTestWalk_eval t, Term.shareTestWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.shareTestWalk, Branch.eval]
      exact Term.shareTestWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.shareTestWalk, Branch.eval]
      exact Branches.shareTestWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.shareTestWalk, Branch.eval, Branch.shareTestWalk_eval main,
        Term.shareTestWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.shareTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.shareTestWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.shareTestWalk, Branches.eval, Term.shareTestWalk_eval b₁,
        Term.shareTestWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.shareTestWalk, Branches.eval, Term.shareTestWalk_eval b,
        Branches.shareTestWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.shareTestWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.shareTestWalk, Val.numCalls]; exact Body.numCalls_shareTestWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.shareTestWalk, Val.numCalls]; exact Body.numCalls_shareTestWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.shareTestWalk, Val.numCalls]; exact Body.numCalls_shareTestWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.shareTestWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.shareTestWalk, Body.numCalls]; exact Term.numCalls_shareTestWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.shareTestWalk, Body.numCalls]; exact Term.numCalls_shareTestWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.shareTestWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.shareTestWalk, Comp.numCalls]; exact Body.numCalls_shareTestWalk s
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.shareTestWalk, Comp.numCalls]; exact Body.numCalls_shareTestWalk s
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.shareTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_shareTestWalk (brs i))
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.shareTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_shareTestWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    t.shareTestWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV _ v b => by
      have := Val.numCalls_shareTestWalk v
      have := Term.numCalls_shareTestWalk b
      simp only [Term.shareTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE _ c b => by
      have := Comp.numCalls_shareTestWalk c
      have := Term.numCalls_shareTestWalk b
      simp only [Term.shareTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn _ _ b => by
      simp only [Term.shareTestWalk, Term.numCalls]; exact Term.numCalls_shareTestWalk b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.shareTestWalk, Term.numCalls]; exact Branch.numCalls_shareTestWalk br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.shareTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have := Branch.numCalls_shareTest c t.shareTestWalk e.shareTestWalk
      have := Term.numCalls_shareTestWalk t
      have := Term.numCalls_shareTestWalk e
      simp only [Branch.shareTestWalk, Branch.numCalls] at *; omega
  | _, _, _, _, _, _, .enum_casesOn _ bs => by
      simp only [Branch.shareTestWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_shareTestWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn _ bs => by
      simp only [Branch.shareTestWalk, Branch.numCalls]; exact Branches.numCalls_shareTestWalk bs
  | _, _, _, _, _, _, .join _ _ _ body main => by
      have := Term.numCalls_shareTestWalk body
      have := Branch.numCalls_shareTestWalk main
      simp only [Branch.shareTestWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_shareTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.shareTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => by
      have := Term.numCalls_shareTestWalk b₁
      have := Term.numCalls_shareTestWalk b₂
      simp only [Branches.shareTestWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons _ b bs => by
      have := Term.numCalls_shareTestWalk b
      have := Branches.numCalls_shareTestWalk bs
      simp only [Branches.shareTestWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
