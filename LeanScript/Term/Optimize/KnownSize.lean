module

public import LeanScript.Term.Optimize.KnownTest
public import LeanScript.Term.Optimize.SubstEval
public import LeanScript.Term.Optimize.CountSubst
public import LeanScript.Term.Optimize.InlineSubstEval

@[expose] public section

set_option autoImplicit false

/-!
# Known sizes of arrays

```
val k := #[1, 2, x]
ret (lean_array_get_size(k) == 3 ? k : #[])
```

The array `k` is a literal of three elements, known by name, so its size is known: the test is
`3 == 3`, which is `true`, and the statement is `ret k`.  Lean writes such tests when a program
looks at the size of an array it has just built (`let a := #[1, 2, f ()]; if a.size == 3 then …`,
`Tests/SnapshotsPBOPure/InlineReferenceOpArrayLength.lean`); so does `a[0]?` on such an array,
which tests `0 < a.size` and then reads `a[0]`.

`Term.sizeWalk I t` walks a statement knowing, for each known value in scope, its **shape**
(`Shape`): nothing, or an array of `n` elements, each with its own shape (an array literal of
array literals, or of known values whose shape is known).  The facts are about the known values
only and do not depend on the unknowns, so they need no weakening under binders; they are
carried into open bodies and dropped in closed bodies (which see another known context).

* `lean_array_get_size a`, where the shape of `a` is an array of `n` elements, is the literal
  `n` (`Neu.knownSize?`); the shape of `lean_array_get d a i`, for a literal `i` below the size
  of `a`, is the shape of element `i` (`PExpr.shape`);
* an extern call whose arguments have all become constants is the literal of its value
  (`Neu.mkExtern?`: `lean_nat_dec_eq 3 3` is `true`);
* `c ? a : b` and `if c then t else e` on a condition that has become a boolean literal are the
  arm it takes;
* a join point whose branch has become a jump to it, `join j x := body; jump j a`, is
  `body[x := a]` (`Term.subst`, which reduces in turn what the argument makes known: a case
  analysis of a constructor, a test, a constant extern call), when `a` costs nothing to repeat
  or `x` is used at most once.

The result may have another level, and is returned with it (as in `Term.knownTestWalk`); a body
or a value must keep its level, so an open body whose level changes is kept as it was.

**Proved:** `Term.knownSizes_eval` (the value does not change) and `Term.numCalls_knownSizes`
(no call is added).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Shapes -/

/-- What is known of the shape of a value: nothing, or an array of `n` elements whose element
    `i` has the shape `elem i`. -/
inductive Shape where
  | unk
  | arr (n : Nat) (elem : Nat → Shape)

/-- The shape describes the value `v` of type `τ`. -/
def Shape.Holds (Δ : DSig ks) : Shape → (τ : Ty ks) → Ty.Den Δ τ → Prop
  | .unk, _, _ => True
  | .arr n f, .array t, v =>
      let a : Array (Ty.Den Δ t) := v
      a.size = n ∧ ∀ (i : Nat) (h : i < a.size), Shape.Holds Δ (f i) t (a[i]'h)
  | .arr _ _, _, _ => True

@[simp] theorem Shape.holds_unk (τ : Ty ks) (v : Ty.Den Δ τ) : Shape.unk.Holds Δ τ v := by
  cases τ <;> simp [Shape.Holds]

/-- What is known of the known values in scope: their shapes. -/
structure SizeInfo (Φ : KCtx ks) : Type where
  get : ∀ {τ : Ty ks} {o : Lvl}, KVar Φ τ o → Shape

/-- Nothing is known. -/
def SizeInfo.empty {Φ : KCtx ks} : SizeInfo Φ := ⟨fun _ => .unk⟩

/-- The lookup under one more `val`, whose value has the shape `new`. -/
def SizeInfo.consGet {Φ : KCtx ks} (I : SizeInfo Φ) {σ : Ty ks} {u : Usage1ω} {o : Lvl}
    (new : Shape) : {τ : Ty ks} → {o' : Lvl} → KVar (⟨σ, u, o, true⟩ :: Φ) τ o' → Shape
  | _, _, .head => new
  | _, _, .tail x => I.get x

/-- Under one more `val`, whose value has the shape `new`. -/
def SizeInfo.cons {Φ : KCtx ks} (I : SizeInfo Φ) {σ : Ty ks} {u : Usage1ω} {o : Lvl}
    (new : Shape) : SizeInfo (⟨σ, u, o, true⟩ :: Φ) :=
  ⟨fun x => I.consGet new x⟩

/-- What is known holds in the known environment `κ`. -/
def SizeInfo.Holds {Φ : KCtx ks} (I : SizeInfo Φ) (κ : KEnv Δ Φ) : Prop :=
  ∀ {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o), (I.get x).Holds Δ τ (κ.get x)

theorem SizeInfo.empty_holds {Φ : KCtx ks} (κ : KEnv Δ Φ) :
    (SizeInfo.empty (Φ := Φ)).Holds κ :=
  fun _ => Shape.holds_unk _ _

theorem SizeInfo.cons_holds {Φ : KCtx ks} {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ)
    {σ : Ty ks} {u : Usage1ω} {o : Lvl} (new : Shape) (v : Ty.Den Δ σ)
    (hnew : new.Holds Δ σ v) :
    (I.cons (u := u) (o := o) new).Holds (Tuple.cons v κ : KEnv Δ (⟨σ, u, o, true⟩ :: Φ)) := by
  intro τ o' x
  cases x with
  | head => simp only [KEnv.get, Tuple.head_cons]; exact hnew
  | tail x => simp only [KEnv.get, Tuple.tail_cons]; exact hI x

/-! ## The shape of a pure expression -/

section Shape
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The natural number a pure expression is, when it is a literal. -/
def PExpr.natLit? {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Option Nat
  | .lit p v => match p, v with
    | .nat, v => some v
    | _, _ => none
  | _ => none

theorem PExpr.natLit?_eval {o : Lvl} (e : PExpr Δ Φ Γ .nat o) (k : Nat)
    (h : e.natLit? = some k) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (e.eval κ ρ : Nat) = k := by
  cases e with
  | lit _ v =>
    simp only [PExpr.natLit?, Option.some.injEq] at h
    exact h
  | _ => simp [PExpr.natLit?] at h

/-- The shape of element `i` of a shape. -/
def Shape.at : Shape → Nat → Shape
  | .arr n f, i => if i < n then f i else .unk
  | .unk, _ => .unk

/-- The extern is `lean_array_get` (`a[i]!`, the default `d` out of bounds): its arguments are
    `d`, `a` and `i`. -/
def Extern.arrGet? : {σs : List (Ty ks)} → {τ : Ty ks} → Extern ks σs τ →
    Option (PLift (σs = [τ, .array τ, .nat]))
  | _, _, .preludeExtern (.lean_array_get _) => some ⟨rfl⟩
  | _, _, _ => none

/-- The value of `lean_array_get` on its arguments `d, a, i`: `a[i]`, or `d` out of bounds. -/
def Extern.arrGetFn {τ : Ty ks} (v : DenList (DSig.refDen Δ) [τ, .array τ, .nat]) : Ty.Den Δ τ :=
  @Array.get!Internal _ ⟨v.1⟩ v.2.1 v.2.2

mutual
/-- The shape of a neutral expression: element `i` of an array of known shape
    (`lean_array_get d a i`, `i` a literal). -/
def Neu.shape (I : SizeInfo Φ) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Shape
  | _, _, .var _ => .unk
  | _, _, .data_out _ _ _ => .unk
  | _, _, .cond _ _ _ => .unk
  | _, _, .extern e args _ =>
      match e.arrGet? with
      | some _ => args.getShape I
      | none => .unk
/-- The shape of a pure expression: a known value has its known shape, an array literal is an
    array of its elements' shapes. -/
def PExpr.shape (I : SizeInfo Φ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Shape
  | _, _, .neu n => n.shape I
  | _, _, .kvar x => I.get x
  | _, _, .lit _ _ => .unk
  | _, _, .enum_mk _ _ => .unk
  | _, _, .record_mk _ => .unk
  | _, _, .union_mk _ _ => .unk
  | _, _, .array_mk es => .arr es.length (es.shapeAt I)
  | _, _, .list_mk _ => .unk
  | _, _, .data_in _ _ _ => .unk
/-- The shape of `a[i]` for the arguments `d, a, i` of `lean_array_get`. -/
def Args.getShape (I : SizeInfo Φ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Shape
  | _, _, .nil => .unk
  | _, _, .cons _ rest => rest.getShape₂ I
/-- `Args.getShape` after the default `d`. -/
def Args.getShape₂ (I : SizeInfo Φ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Shape
  | _, _, .nil => .unk
  | _, _, .cons a rest => rest.getShape₃ (a.shape I)
/-- `Args.getShape` after the array, of shape `sa`. -/
def Args.getShape₃ (sa : Shape) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Shape
  | _, _, .nil => .unk
  | _, _, .cons i _ =>
      match i.natLit? with
      | some k => sa.at k
      | none => .unk
/-- The number of elements. -/
def Elems.length : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Nat
  | _, _, .nil => 0
  | _, _, .cons _ es => es.length + 1
/-- The shape of element `i`. -/
def Elems.shapeAt (I : SizeInfo Φ) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Nat → Shape
  | _, _, .nil, _ => .unk
  | _, _, .cons e _, 0 => e.shape I
  | _, _, .cons _ es, i + 1 => es.shapeAt I i
end

theorem Elems.length_eval (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ Φ Γ t o) → (es.eval κ ρ).length = es.length
  | _, _, .nil => rfl
  | _, _, .cons _ es => by
      simp only [Elems.eval, Elems.length, List.length_cons, Elems.length_eval κ ρ es]

theorem Shape.at_holds {t : Ty ks} (s : Shape) (v : Array (Ty.Den Δ t))
    (h : s.Holds Δ (.array t) v) (i : Nat) (hi : i < v.size) : (s.at i).Holds Δ t v[i] := by
  cases s with
  | unk => exact Shape.holds_unk _ _
  | arr n f =>
    simp only [Shape.Holds] at h
    obtain ⟨hn, hf⟩ := h
    simp only [Shape.at, show i < n from hn ▸ hi, ite_true]
    exact hf i hi

theorem Shape.at_holds' {t : Ty ks} (s : Shape) (v : Array (Ty.Den Δ t))
    (h : s.Holds Δ (.array t) v) (i : Nat) (d : Ty.Den Δ t) :
    (s.at i).Holds Δ t (@Array.get!Internal _ ⟨d⟩ v i) := by
  by_cases hi : i < v.size
  · have : @Array.get!Internal _ ⟨d⟩ v i = v[i] := by
      simp [Array.get!Internal, Array.getD, hi]
    rw [this]; exact Shape.at_holds s v h i hi
  · cases s with
    | unk => exact Shape.holds_unk _ _
    | arr n f =>
      simp only [Shape.Holds] at h
      simp only [Shape.at, show ¬ i < n from h.1 ▸ hi, ite_false]
      exact Shape.holds_unk _ _

mutual
theorem Neu.shape_holds {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → (ρ : UEnv Δ Γ) →
    (n.shape I).Holds Δ τ (n.eval κ ρ)
  | _, _, .var _, _ => Shape.holds_unk _ _
  | _, _, .data_out _ _ _, _ => Shape.holds_unk _ _
  | _, _, .cond _ _ _, _ => Shape.holds_unk _ _
  | _, _, .extern e args _, ρ => by
      simp only [Neu.shape, Neu.eval]
      split
      · rename_i r he
        have hg := fun τ' (h : _ = [τ', Ty.array τ', Ty.nat]) => Args.getShape_holds hI args ρ h
        unfold Extern.arrGet? at he
        split at he
        · exact hg _ rfl
        · cases he
      · exact Shape.holds_unk _ _
  termination_by structural _ _ n _ => n
theorem PExpr.shape_holds {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → (ρ : UEnv Δ Γ) →
    (e.shape I).Holds Δ τ (e.eval κ ρ)
  | _, _, .neu n, ρ => Neu.shape_holds hI n ρ
  | _, _, .kvar x, _ => hI x
  | _, _, .array_mk es, ρ => by
      simp only [PExpr.shape, PExpr.eval, Shape.Holds, List.size_toArray, Elems.length_eval,
        List.getElem_toArray, true_and]
      intro i hi
      exact Elems.shapeAt_holds hI es ρ i _
  | _, _, .lit _ _, _ => Shape.holds_unk _ _
  | _, _, .enum_mk _ _, _ => Shape.holds_unk _ _
  | _, _, .record_mk _, _ => Shape.holds_unk _ _
  | _, _, .union_mk _ _, _ => Shape.holds_unk _ _
  | _, _, .list_mk _, _ => Shape.holds_unk _ _
  | _, _, .data_in _ _ _, _ => Shape.holds_unk _ _
  termination_by structural _ _ e _ => e
theorem Args.getShape_holds {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {σs : List (Ty ks)} → {o : Lvl} → (args : Args Δ Φ Γ σs o) → (ρ : UEnv Δ Γ) →
    {τ : Ty ks} → (h : σs = [τ, .array τ, .nat]) →
    (args.getShape I).Holds Δ τ (Extern.arrGetFn (h ▸ args.eval κ ρ))
  | _, _, .cons d (.cons a (.cons i .nil)), ρ, _, h => by
      have ha := PExpr.shape_holds hI a ρ
      cases h
      cases hk : i.natLit? with
      | none => simp only [Args.getShape, Args.getShape₂, Args.getShape₃, hk]; exact Shape.holds_unk _ _
      | some k =>
        have hk' := PExpr.natLit?_eval i k hk κ ρ
        simp only [Args.getShape, Args.getShape₂, Args.getShape₃, hk, Extern.arrGetFn, Args.eval,
          Tuple.cons]
        rw [hk']
        exact Shape.at_holds' _ _ ha k _
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons _ .nil, _, _, h => by cases h
  | _, _, .cons _ (.cons _ .nil), _, _, h => by cases h
  | _, _, .cons _ (.cons _ (.cons _ (.cons _ _))), _, _, h => by cases h
  termination_by structural _ _ args _ _ _ => args
theorem Elems.shapeAt_holds {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → (ρ : UEnv Δ Γ) → (i : Nat) →
    (h : i < (es.eval κ ρ).length) → (es.shapeAt I i).Holds Δ t ((es.eval κ ρ)[i])
  | _, _, .nil, _, _, h => by simp [Elems.eval] at h
  | _, _, .cons e _, ρ, 0, _ => by
      simp only [Elems.shapeAt, Elems.eval, List.getElem_cons_zero]
      exact PExpr.shape_holds hI e ρ
  | _, _, .cons _ es, ρ, i + 1, h => by
      simp only [Elems.shapeAt, Elems.eval, List.getElem_cons_succ]
      exact Elems.shapeAt_holds hI es ρ i _
  termination_by structural _ _ es _ _ _ => es
end

end Shape

/-! ## Rewriting pure expressions -/

section Expr
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The extern is `lean_array_get_size`. -/
def Extern.isArrSize : {σs : List (Ty ks)} → {τ : Ty ks} → Extern ks σs τ → Bool
  | _, _, .preludeExtern (.lean_array_get_size _) => true
  | _, _, _ => false

/-- The literal `n`, at the type of natural numbers. -/
def PExpr.natLitOf? : (τ : Ty ks) → Nat → Option (PExpr Δ Φ Γ τ none)
  | .prim .nat, n => some (.lit .nat n)
  | _, _ => none

/-- The shape of the first argument. -/
def Args.firstShape (I : SizeInfo Φ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Shape
  | _, _, .nil => .unk
  | _, _, .cons a _ => a.shape I

/-- `lean_array_get_size a` for an array `a` of known size: the literal of its size. -/
def Neu.knownSize? (I : SizeInfo Φ) {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ)
    {o : Lvl} (args : Args Δ Φ Γ σs o) : Option (PExpr Δ Φ Γ τ none) :=
  match e.isArrSize, args.firstShape I with
  | true, .arr n _ => PExpr.natLitOf? τ n
  | _, _ => none

theorem Neu.knownSize?_eval {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) {σs : List (Ty ks)}
    {τ : Ty ks} (e : Extern ks σs τ) {o : Lvl} (args : Args Δ Φ Γ σs o) (l : PExpr Δ Φ Γ τ none)
    (h : Neu.knownSize? I e args = some l) (ρ : UEnv Δ Γ) :
    l.eval κ ρ = Extern.eval (DSig.refDen Δ) e (args.eval κ ρ) := by
  unfold Neu.knownSize? at h
  split at h
  · rename_i n f he hs
    unfold Extern.isArrSize at he
    split at he
    · cases args with
      | cons a rest =>
        cases rest with
        | nil =>
          have ha := PExpr.shape_holds hI a ρ
          simp only [Args.firstShape] at hs
          rw [hs] at ha
          have hsz : (a.eval κ ρ : Array _).size = n := ha.1
          change some (PExpr.lit .nat n) = some l at h
          cases h
          simp only [PExpr.eval, Args.eval, Extern.eval, PreludeExtern.eval, Tuple.cons, hsz]
          rfl
    · cases he
  · cases h

mutual
/-- **Known sizes in a neutral expression**, returned with the level of the result (a neutral
    expression can become a literal): `lean_array_get_size a` on an array of known size is its
    size, an extern call on constants is its value, a conditional on a literal is its arm. -/
def Neu.szW (I : SizeInfo Φ) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ →
    (o : Lvl) × PExpr Δ Φ Γ τ o
  | _, _, .var x => ⟨_, .neu (.var x)⟩
  | _, _, .data_out b j n =>
      match (n.szW I).2.toNeu? with
      | some m => ⟨_, .neu (.data_out b j m.2)⟩
      | none => ⟨_, .neu (.data_out b j n)⟩
  | _, _, .cond c a b =>
      match (c.szW I).2.boolLit? with
      | some true => a.szW I
      | some false => b.szW I
      | none =>
        match (c.szW I).2.toNeu? with
        | some m => ⟨_, .neu (.cond m.2 (a.szW I).2 (b.szW I).2)⟩
        | none => ⟨_, .neu (.cond c (a.szW I).2 (b.szW I).2)⟩
  | _, _, .extern e args h =>
      match Neu.knownSize? I e args with
      | some l => ⟨_, l⟩
      | none =>
        match Neu.mkExtern? e (args.szW I).2 with
        | some p => p
        | none => ⟨_, .neu (.extern e args h)⟩
/-- `Neu.szW` in a pure expression. -/
def PExpr.szW (I : SizeInfo Φ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | _, _, .neu n => n.szW I
  | _, _, .kvar x => ⟨_, .kvar x⟩
  | _, _, .lit p v => ⟨_, .lit p v⟩
  | _, _, .enum_mk s i => ⟨_, .enum_mk s i⟩
  | _, _, .record_mk args => ⟨_, .record_mk (args.szW I).2⟩
  | _, _, .union_mk ix args => ⟨_, .union_mk ix (args.szW I).2⟩
  | _, _, .array_mk es => ⟨_, .array_mk (es.szW I).2⟩
  | _, _, .list_mk es => ⟨_, .list_mk (es.szW I).2⟩
  | _, _, .data_in b j e => ⟨_, .data_in b j (e.szW I).2⟩
/-- `Neu.szW` in arguments. -/
def Args.szW (I : SizeInfo Φ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    (o' : Lvl) × Args Δ Φ Γ σs o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons a as => ⟨_, .cons (a.szW I).2 (as.szW I).2⟩
/-- `Neu.szW` in elements. -/
def Elems.szW (I : SizeInfo Φ) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    (o' : Lvl) × Elems Δ Φ Γ t o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons e es => ⟨_, .cons (e.szW I).2 (es.szW I).2⟩
end

mutual
theorem Neu.szW_eval {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → (ρ : UEnv Δ Γ) →
    (n.szW I).2.eval κ ρ = n.eval κ ρ
  | _, _, .var _, _ => rfl
  | _, _, .data_out b j n, ρ => by
      simp only [Neu.szW]
      split
      · rename_i m hm
        simp only [PExpr.eval, Neu.eval, PExpr.toNeu?_eval κ ρ _ hm, Neu.szW_eval hI n ρ]
      · rfl
  | _, _, .cond c a b, ρ => by
      have hc := Neu.szW_eval hI c ρ
      have ha := PExpr.szW_eval hI a ρ
      have hb := PExpr.szW_eval hI b ρ
      simp only [Neu.szW]
      split
      · rename_i hl
        have := PExpr.boolLit?_eval _ true hl κ ρ
        rw [hc] at this
        simp only [Neu.eval, this, ha]
      · rename_i hl
        have := PExpr.boolLit?_eval _ false hl κ ρ
        rw [hc] at this
        simp only [Neu.eval, this, hb]
      · dsimp only
        split
        · rename_i m hm
          simp only [PExpr.eval, Neu.eval, PExpr.toNeu?_eval κ ρ _ hm, hc, ha, hb]
        · simp only [PExpr.eval, Neu.eval, ha, hb]
  | _, _, .extern e args _, ρ => by
      have hargs := Args.szW_eval hI args ρ
      simp only [Neu.szW]
      split
      · rename_i l hl
        simp only [Neu.eval]
        exact Neu.knownSize?_eval hI e args l hl ρ
      · dsimp only
        split
        · rename_i p hp
          rw [Neu.mkExtern?_eval e _ p hp κ ρ, hargs]; rfl
        · rfl
  termination_by structural _ _ n _ => n
theorem PExpr.szW_eval {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → (ρ : UEnv Δ Γ) →
    (e.szW I).2.eval κ ρ = e.eval κ ρ
  | _, _, .neu n, ρ => Neu.szW_eval hI n ρ
  | _, _, .kvar _, _ => rfl
  | _, _, .lit _ _, _ => rfl
  | _, _, .enum_mk _ _, _ => rfl
  | _, _, .record_mk args, ρ => by
      simp only [PExpr.szW, PExpr.eval, Args.szW_eval hI args ρ] <;> rfl
  | _, _, .union_mk _ args, ρ => by
      simp only [PExpr.szW, PExpr.eval, Args.szW_eval hI args ρ] <;> rfl
  | _, _, .array_mk es, ρ => by
      simp only [PExpr.szW, PExpr.eval, Elems.szW_eval hI es ρ] <;> rfl
  | _, _, .list_mk es, ρ => by
      simp only [PExpr.szW, PExpr.eval, Elems.szW_eval hI es ρ] <;> rfl
  | _, _, .data_in _ _ e, ρ => by
      simp only [PExpr.szW, PExpr.eval, PExpr.szW_eval hI e ρ]
  termination_by structural _ _ e _ => e
theorem Args.szW_eval {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) → (ρ : UEnv Δ Γ) →
    (as.szW I).2.eval κ ρ = as.eval κ ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons a as, ρ => by
      simp only [Args.szW, Args.eval, PExpr.szW_eval hI a ρ, Args.szW_eval hI as ρ]
  termination_by structural _ _ as _ => as
theorem Elems.szW_eval {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → (ρ : UEnv Δ Γ) →
    (es.szW I).2.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons e es, ρ => by
      simp only [Elems.szW, Elems.eval, PExpr.szW_eval hI e ρ, Elems.szW_eval hI es ρ]
  termination_by structural _ _ es _ => es
end

end Expr

/-! ## Helpers of the walk -/

section Helpers
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- The shape of a value: an array literal is an array of its elements' shapes. -/
def Val.shape (I : SizeInfo Φ) {σ : Ty ks} {o : Lvl} : Val Δ d Φ Γ σ o → Shape
  | .array_mk es => .arr es.length (es.shapeAt I)
  | _ => .unk

theorem Val.shape_holds {I : SizeInfo Φ} {κ : KEnv Δ Φ} (hI : I.Holds κ) {σ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ σ o) (ρ : UEnv Δ Γ) : (v.shape I).Holds Δ σ (v.eval κ ρ) := by
  cases v with
  | array_mk es =>
    simp only [Val.shape, Val.eval, Shape.Holds, List.size_toArray, Elems.length_eval,
      List.getElem_toArray, true_and]
    intro i hi
    exact Elems.shapeAt_holds hI es ρ i _
  | _ => simp only [Val.shape]; exact Shape.holds_unk _ _

/-- The rewrites that `Term.subst` makes on its own (with no substitution): an extern call on
    constants is its value, a test or a case analysis of a literal is the arm it takes, a join
    point whose branch is a jump to it is its body. -/
def Term.sizeNorm {o : Lvl} (t : Term Δ d Φ Γ τ js o) : (o' : Lvl) × Term Δ d Φ Γ τ js o' :=
  match t.subst (D' := d) KLRen.id (USub.ofRen ULRen.idL) JRen.id with
  | some p => p
  | none => ⟨_, t⟩

theorem Term.sizeNorm_eval {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : t.sizeNorm.2.eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.sizeNorm
  split
  · rename_i p h
    exact Term.subst_eval (KLRen.Agree.id κ) (USub.Agree.ofRen (ULRen.Agree.idL ρ))
      (JRen.Agree.id jκ) t h
  · rfl

theorem Term.numCalls_sizeNorm {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.sizeNorm.2.numCalls ≤ t.numCalls := by
  unfold Term.sizeNorm
  split
  · rename_i p h
    exact Term.numCalls_subst t h
  · exact Nat.le_refl _

/-- `join j x := body; jump j a` is `body[x := a]`, when `a` costs nothing to repeat or `x` is
    used at most once (otherwise, or when the substitution fails, it is kept, with `main`). -/
def Term.sizeJoinSelf {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {oa : Lvl} (a : PExpr Δ Φ Γ σ oa) :
    (o : Lvl) × Term Δ d Φ Γ τ js o :=
  if a.isCheap || uₓ.atMostOnce then
    (body.subst (D' := d) KLRen.id (USub.cons ⟨_, a⟩ (USub.ofRen ULRen.idL)) JRen.id).getD
      ⟨_, .branch (.join σ u uₓ body main)⟩
  else ⟨_, .branch (.join σ u uₓ body main)⟩

/-- `join j x := body; jump k a`: `Term.sizeJoinSelf` when `k` is `j`, else `jump k a`. -/
def Term.sizeJoinJmp {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {σ' : Ty ks} (j : JVar (⟨σ, u⟩ :: js) σ')
    {oa : Lvl} (a : PExpr Δ Φ Γ σ' oa) : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match j.split with
  | .inl h => Term.sizeJoinSelf uₓ body main (h.down ▸ a)
  | .inr j' => ⟨_, .jump j' a⟩

/-- `join j x := body; main`, where `main` has become the statement `m`: a branch stays the
    branch of the join point; a jump to `j` is `Term.sizeJoinSelf`; a jump further out is that
    jump; otherwise `main` is kept. -/
def Term.sizeJoin (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {o' : Lvl}
    (m : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o') : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match m.asBranch?, m.asJump? with
  | some b, _ => ⟨_, .branch (.join σ u uₓ body b.2)⟩
  | none, some ⟨_, j, _, a⟩ => Term.sizeJoinJmp uₓ body main j a
  | none, none => ⟨_, .branch (.join σ u uₓ body main)⟩

theorem Term.sizeJoinSelf_eval {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {oa : Lvl} (a : PExpr Δ Φ Γ σ oa)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (hfb : (Branch.join σ u uₓ body main).eval κ ρ jκ =
      body.eval κ (Tuple.cons (a.eval κ ρ) ρ) jκ) :
    (Term.sizeJoinSelf uₓ body main a).2.eval κ ρ jκ =
      body.eval κ (Tuple.cons (a.eval κ ρ) ρ) jκ := by
  unfold Term.sizeJoinSelf
  by_cases hc : (a.isCheap || uₓ.atMostOnce) = true
  · rw [ite_eq_left hc]
    cases hs : body.subst (D' := d) KLRen.id (USub.cons ⟨_, a⟩ (USub.ofRen ULRen.idL)) JRen.id with
    | some r =>
      exact Term.subst_eval (KLRen.Agree.id κ)
        (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) body hs
    | none => exact hfb
  · rw [ite_eq_right hc]; exact hfb

theorem Term.sizeJoinJmp_eval {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {σ' : Ty ks} (j : JVar (⟨σ, u⟩ :: js) σ')
    {oa : Lvl} (a : PExpr Δ Φ Γ σ' oa) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (hfb : (Branch.join σ u uₓ body main).eval κ ρ jκ =
      JEnv.get (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) j (a.eval κ ρ)) :
    (Term.sizeJoinJmp uₓ body main j a).2.eval κ ρ jκ =
      JEnv.get (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) j (a.eval κ ρ) := by
  unfold Term.sizeJoinJmp
  split
  · rename_i hh hsplit
    rw [JVar.split_inl_get jκ _ j hsplit] at hfb ⊢
    dsimp only
    rw [← PExpr.eval_cast]
    exact Term.sizeJoinSelf_eval _ _ _ _ κ ρ jκ (by rw [hfb, PExpr.eval_cast])
  · rename_i j' hsplit
    rw [JVar.split_inr_get jκ _ j hsplit]
    rfl

theorem Term.sizeJoin_eval (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {o' : Lvl}
    (m : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (hm : m.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) =
      main.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ)) :
    (Term.sizeJoin σ u uₓ body main m).2.eval κ ρ jκ =
      (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  unfold Term.sizeJoin
  split
  · rename_i b _ hb
    simp only [Term.eval, Branch.eval]
    rw [← Term.asBranch?_eval κ ρ _ m hb]; exact hm
  · rename_i σ' j o'' a _ hr
    have hj := Term.asJump?_eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) m hr
    simp only at hj
    have hfb : (Branch.join σ u uₓ body main).eval κ ρ jκ =
        JEnv.get (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) j (a.eval κ ρ) := by
      simp only [Branch.eval]; rw [← hm, hj]
    rw [Term.sizeJoinJmp_eval uₓ body main j a κ ρ jκ hfb, hfb]
  · rfl

theorem Term.numCalls_sizeJoinSelf {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {oa : Lvl} (a : PExpr Δ Φ Γ σ oa) :
    (Term.sizeJoinSelf uₓ body main a).2.numCalls ≤ (Branch.join σ u uₓ body main).numCalls := by
  unfold Term.sizeJoinSelf
  by_cases hc : (a.isCheap || uₓ.atMostOnce) = true
  · rw [ite_eq_left hc]
    cases hs : body.subst (D' := d) KLRen.id (USub.cons ⟨_, a⟩ (USub.ofRen ULRen.idL)) JRen.id with
    | some r =>
      have := Term.numCalls_subst body hs
      simp only [Option.getD_some, Branch.numCalls]; omega
    | none => exact Nat.le_refl _
  · rw [ite_eq_right hc]; exact Nat.le_refl _

theorem Term.numCalls_sizeJoinJmp {σ : Ty ks} {u : Usage1ω} (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {σ' : Ty ks} (j : JVar (⟨σ, u⟩ :: js) σ')
    {oa : Lvl} (a : PExpr Δ Φ Γ σ' oa) :
    (Term.sizeJoinJmp uₓ body main j a).2.numCalls ≤ (Branch.join σ u uₓ body main).numCalls := by
  unfold Term.sizeJoinJmp
  split
  · exact Term.numCalls_sizeJoinSelf uₓ body main _
  · simp only [Term.numCalls]; omega

theorem Term.numCalls_sizeJoin (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) {ob : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js ob) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {o' : Lvl}
    (m : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o') (hm : m.numCalls ≤ main.numCalls) :
    (Term.sizeJoin σ u uₓ body main m).2.numCalls ≤ (Branch.join σ u uₓ body main).numCalls := by
  unfold Term.sizeJoin
  split
  · rename_i b _ hb
    have := Term.numCalls_asBranch? m hb
    simp only [Term.numCalls, Branch.numCalls]; omega
  · exact Term.numCalls_sizeJoinJmp uₓ body main _ _
  · exact Nat.le_refl _

end Helpers

/-! ## The walk -/

mutual
/-- `Term.sizeWalk` inside the bodies of a value (the value keeps its level). -/
def Val.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    SizeInfo Φ → Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, I, .lam b => .lam (b.sizeWalk I)
  | _, _, _, _, _, I, .thunk_mk b => .thunk_mk (b.sizeWalk I)
  | _, _, _, _, _, I, .lazy_mk b => .lazy_mk (b.sizeWalk I)
  | _, _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.sizeWalk` in a body: a closed body starts with nothing known (and is then rewritten
    by `Term.sizeNorm`), an open one with what is known in its context; an open body keeps its
    level (or is kept as it is). -/
def Body.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → SizeInfo Φ → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, _, .closed t => .closed (t.sizeWalk .empty).2.sizeNorm.2
  | _, _, _, _, _, _, I, .opened (m := m) t h =>
      let r := t.sizeWalk I
      if hr : r.1 = some m then .opened (r.2.castLvl hr) h else .opened t h
/-- `Term.sizeWalk` inside the bodies of a computation. -/
def Comp.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    SizeInfo Φ → Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, I, .nat_rec n z s h => .nat_rec n z (s.sizeWalk I) h
  | _, _, _, _, _, I, .array_foldl a z s h => .array_foldl a z (s.sizeWalk I) h
  | _, _, _, _, _, I, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).sizeWalk I) j e h
  | _, _, _, _, _, I, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).sizeWalk I) j e h
  | _, _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Known sizes**: walk a statement knowing the shapes of the known values in scope; the
    size of an array of known size is its literal (`PExpr.szW`), and a test on a condition that
    has become a literal is the arm it takes.  The result may have another level, and is
    returned with it. -/
def Term.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → SizeInfo Φ → Term Δ d Φ Γ τ js o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, I, .ret e => ⟨_, .ret (e.szW I).2⟩
  | _, _, _, _, _, _, I, .letV u v b =>
      ⟨_, .letV u (v.sizeWalk I) (b.sizeWalk (I.cons (v.shape I))).2⟩
  | _, _, _, _, _, _, I, .letE u c b => ⟨_, .letE u (c.sizeWalk I) (b.sizeWalk I).2⟩
  | _, _, _, _, _, _, I, .record_casesOn us n b => ⟨_, .record_casesOn us n (b.sizeWalk I).2⟩
  | _, _, _, _, _, _, I, .branch br => br.sizeWalk I
  | _, _, _, _, _, _, I, .jump j e => ⟨_, .jump j (e.szW I).2⟩
/-- `Term.sizeWalk` in a branch; the result is a statement (an `if` on a literal is gone, and
    so is a join point whose branch has become a jump, `Term.sizeJoin`). -/
def Branch.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → SizeInfo Φ → Branch Δ d Φ Γ τ js ℓ →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, I, .ite c t e =>
      match (c.szW I).2.boolLit? with
      | some true => t.sizeWalk I
      | some false => e.sizeWalk I
      | none => ⟨_, .branch (.ite c (t.sizeWalk I).2 (e.sizeWalk I).2)⟩
  | _, _, _, _, _, _, I, .enum_casesOn e bs =>
      ⟨_, .branch (.enum_casesOn e (fun i => ((bs i).sizeWalk I).2))⟩
  | _, _, _, _, _, _, I, .union_casesOn e bs => ⟨_, .branch (.union_casesOn e (bs.sizeWalk I).2)⟩
  | _, _, _, _, _, _, I, .join σ u uₓ body main =>
      Term.sizeJoin σ u uₓ (body.sizeWalk I).2 main (main.sizeWalk I).2
/-- `Term.sizeWalk` in the branches of a union's case analysis. -/
def Branches.sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → SizeInfo Φ →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, I, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (b₁.sizeWalk I).2 (b₂.sizeWalk I).2⟩
  | _, _, _, _, _, _, _, _, I, .cons us b bs => ⟨_, .cons us (b.sizeWalk I).2 (bs.sizeWalk I).2⟩
end

/-! ## The value does not change -/

mutual
theorem Val.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : SizeInfo Φ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Holds κ → (v.sizeWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, ρ, h => by
      simp only [Val.sizeWalk, Val.eval]; funext x
      rw [Body.sizeWalk_eval b I κ ρ _ h]
  | _, _, _, _, _, .thunk_mk b, I, κ, ρ, h => by
      simp only [Val.sizeWalk, Val.eval]; rw [Body.sizeWalk_eval b I κ ρ _ h]
  | _, _, _, _, _, .lazy_mk b, I, κ, ρ, h => by
      simp only [Val.sizeWalk, Val.eval]; rw [Body.sizeWalk_eval b I κ ρ _ h]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Body.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : SizeInfo Φ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → I.Holds κ →
    (b.sizeWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, κ, _, vs, _ => by
      simp only [Body.sizeWalk, Body.eval]
      exact (Term.sizeNorm_eval _ _ _ _).trans
        (Term.sizeWalk_eval t .empty _ _ _ (SizeInfo.empty_holds _))
  | _, _, _, _, _, _, .opened t _, I, κ, ρ, vs, h => by
      simp only [Body.sizeWalk]
      split
      · simp only [Body.eval]
        exact (Term.eval_castLvl _ _ _ _ _).trans (Term.sizeWalk_eval t I _ _ _ h)
      · rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Comp.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : SizeInfo Φ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Holds κ → (c.sizeWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, I, κ, ρ, h => by
      simp only [Comp.sizeWalk, Comp.eval]
      congr 1; funext k acc; exact Body.sizeWalk_eval s I κ ρ _ h
  | _, _, _, _, _, .array_foldl a z s _, I, κ, ρ, h => by
      simp only [Comp.sizeWalk, Comp.eval]
      congr 1; funext acc x; exact Body.sizeWalk_eval s I κ ρ _ h
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, ρ, h => by
      simp only [Comp.sizeWalk, Comp.eval]
      congr 1; funext i x; exact Body.sizeWalk_eval (brs i) I κ ρ _ h
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, ρ, h => by
      simp only [Comp.sizeWalk, Comp.eval]
      congr 1; funext i x; exact Body.sizeWalk_eval (brs i) I κ ρ _ h
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Term.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : SizeInfo Φ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → I.Holds κ →
    (t.sizeWalk I).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, I, κ, ρ, _, h => by
      simp only [Term.sizeWalk, Term.eval]; exact PExpr.szW_eval h e ρ
  | _, _, _, _, _, _, .letV u v b, I, κ, ρ, jκ, h => by
      simp only [Term.sizeWalk, Term.eval, Val.sizeWalk_eval v I κ ρ h]
      exact Term.sizeWalk_eval b _ _ ρ jκ
        (SizeInfo.cons_holds h _ (v.eval κ ρ) (Val.shape_holds h v ρ))
  | _, _, _, _, _, _, .letE u c b, I, κ, ρ, jκ, h => by
      simp only [Term.sizeWalk, Term.eval, Comp.sizeWalk_eval c I κ ρ h]
      exact Term.sizeWalk_eval b I κ _ jκ h
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, ρ, jκ, h => by
      simp only [Term.sizeWalk, Term.eval]
      exact Term.sizeWalk_eval b I κ _ jκ h
  | _, _, _, _, _, _, .branch br, I, κ, ρ, jκ, h => by
      simp only [Term.sizeWalk, Term.eval]
      exact Branch.sizeWalk_eval br I κ ρ jκ h
  | _, _, _, _, _, _, .jump _ e, I, κ, ρ, _, h => by
      simp only [Term.sizeWalk, Term.eval, PExpr.szW_eval h e ρ]
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branch.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : SizeInfo Φ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → I.Holds κ →
    (br.sizeWalk I).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, ρ, jκ, h => by
      have hc := Neu.szW_eval h c ρ
      have ht := Term.sizeWalk_eval t I κ ρ jκ h
      have he := Term.sizeWalk_eval e I κ ρ jκ h
      simp only [Branch.sizeWalk]
      split
      · rename_i hl
        have := PExpr.boolLit?_eval _ true hl κ ρ
        rw [hc] at this
        simp only [Branch.eval, this, ht]
      · rename_i hl
        have := PExpr.boolLit?_eval _ false hl κ ρ
        rw [hc] at this
        simp only [Branch.eval, this, he]
      · simp only [Term.eval, Branch.eval, ht, he]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, ρ, jκ, h => by
      simp only [Branch.sizeWalk, Term.eval, Branch.eval]
      exact Term.sizeWalk_eval _ I κ ρ jκ h
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, ρ, jκ, h => by
      simp only [Branch.sizeWalk, Term.eval, Branch.eval]
      exact Branches.sizeWalk_eval bs I κ ρ jκ h _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, ρ, jκ, h => by
      have hb : (fun v => (body.sizeWalk I).2.eval κ (Tuple.cons v ρ) jκ) =
          (fun v => body.eval κ (Tuple.cons v ρ) jκ) :=
        funext fun v => Term.sizeWalk_eval body I κ _ jκ h
      simp only [Branch.sizeWalk]
      rw [Term.sizeJoin_eval]
      · simp only [Branch.eval, hb]
      · rw [Branch.sizeWalk_eval main I κ ρ _ h]
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branches.sizeWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : SizeInfo Φ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → I.Holds κ →
      ∀ x, (br.sizeWalk I).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, ρ, jκ, h, x => by
      simp only [Branches.sizeWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.sizeWalk_eval b₁ I κ _ jκ h
      · funext v
        exact Term.sizeWalk_eval b₂ I κ _ jκ h
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, ρ, jκ, h, x => by
      simp only [Branches.sizeWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.sizeWalk_eval b I κ _ jκ h
      · funext r
        exact Branches.sizeWalk_eval bs I κ ρ jκ h r
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : SizeInfo Φ) →
    (v.sizeWalk I).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, I => by
      simp only [Val.sizeWalk, Val.numCalls]; exact Body.numCalls_sizeWalk b I
  | _, _, _, _, _, .thunk_mk b, I => by
      simp only [Val.sizeWalk, Val.numCalls]; exact Body.numCalls_sizeWalk b I
  | _, _, _, _, _, .lazy_mk b, I => by
      simp only [Val.sizeWalk, Val.numCalls]; exact Body.numCalls_sizeWalk b I
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Body.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : SizeInfo Φ) →
    (b.sizeWalk I).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, _ => by
      simp only [Body.sizeWalk, Body.numCalls]
      exact Nat.le_trans (Term.numCalls_sizeNorm _) (Term.numCalls_sizeWalk t .empty)
  | _, _, _, _, _, _, .opened t _, I => by
      simp only [Body.sizeWalk]
      split
      · simp only [Body.numCalls, Term.numCalls_castLvl]
        exact Term.numCalls_sizeWalk t I
      · exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Comp.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : SizeInfo Φ) →
    (c.sizeWalk I).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, I => by
      simp only [Comp.sizeWalk, Comp.numCalls]; exact Body.numCalls_sizeWalk s I
  | _, _, _, _, _, .array_foldl a z s _, I => by
      simp only [Comp.sizeWalk, Comp.numCalls]; exact Body.numCalls_sizeWalk s I
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I => by
      simp only [Comp.sizeWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_sizeWalk (brs i) I)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I => by
      simp only [Comp.sizeWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_sizeWalk (brs i) I)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Term.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (I : SizeInfo Φ) → (t.sizeWalk I).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, I => by
      have h₁ := Val.numCalls_sizeWalk v I
      have h₂ := Term.numCalls_sizeWalk b (I.cons (v.shape I))
      simp only [Term.sizeWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, I => by
      have h₁ := Comp.numCalls_sizeWalk c I
      have h₂ := Term.numCalls_sizeWalk b I
      simp only [Term.sizeWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, I => by
      simp only [Term.sizeWalk, Term.numCalls]
      exact Term.numCalls_sizeWalk b I
  | _, _, _, _, _, _, .branch br, I => by
      simp only [Term.sizeWalk, Term.numCalls]
      exact Branch.numCalls_sizeWalk br I
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branch.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (I : SizeInfo Φ) → (br.sizeWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, I => by
      have h₁ := Term.numCalls_sizeWalk t I
      have h₂ := Term.numCalls_sizeWalk e I
      simp only [Branch.sizeWalk]
      split <;> simp only [Term.numCalls, Branch.numCalls] <;> omega
  | _, _, _, _, _, _, .enum_casesOn e bs, I => by
      simp only [Branch.sizeWalk, Term.numCalls, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_sizeWalk (bs i) I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => by
      simp only [Branch.sizeWalk, Term.numCalls, Branch.numCalls]
      exact Branches.numCalls_sizeWalk bs I
  | _, _, _, _, _, _, .join σ u uₓ body main, I => by
      have h₁ := Term.numCalls_sizeWalk body I
      have h₂ := Branch.numCalls_sizeWalk main I
      simp only [Branch.sizeWalk]
      have := Term.numCalls_sizeJoin σ u uₓ (body.sizeWalk I).2 main (main.sizeWalk I).2 h₂
      simp only [Branch.numCalls] at this ⊢; omega
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branches.numCalls_sizeWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : SizeInfo Φ) →
    (br.sizeWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => by
      have h₁ := Term.numCalls_sizeWalk b₁ I
      have h₂ := Term.numCalls_sizeWalk b₂ I
      simp only [Branches.sizeWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, I => by
      have h₁ := Term.numCalls_sizeWalk b I
      have h₂ := Branches.numCalls_sizeWalk bs I
      simp only [Branches.sizeWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x _ => x
end

/-- **The known sizes of a statement** (`Term.sizeWalk`, then `Term.sizeNorm`), when this keeps
    the level of the statement. -/
def Term.knownSizes {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  if h : (t.sizeWalk .empty).2.sizeNorm.1 = o then (t.sizeWalk .empty).2.sizeNorm.2.castLvl h
  else t

/-- **The known sizes do not change the value.** -/
theorem Term.knownSizes_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.knownSizes.eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.knownSizes
  split
  · rw [Term.eval_castLvl, Term.sizeNorm_eval]
    exact Term.sizeWalk_eval t .empty κ ρ jκ (SizeInfo.empty_holds κ)
  · rfl

/-- The same for a whole program. -/
theorem Term.knownSizes_run {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    t.knownSizes.run = t.run :=
  t.knownSizes_eval _ _ _

/-- **The known sizes add no call.** -/
theorem Term.numCalls_knownSizes {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.knownSizes.numCalls ≤ t.numCalls := by
  unfold Term.knownSizes
  split
  · rw [Term.numCalls_castLvl]
    exact Nat.le_trans (Term.numCalls_sizeNorm _) (Term.numCalls_sizeWalk t .empty)
  · exact Nat.le_refl _

end LeanScript

end
