module

public import LeanScript.BuildEvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# Builders on operands, applications and primitive dispatches

The first half of the theorems of `LeanScript.BuildEvalFacts.Builders`: the redexes the
builders take apart, applications and extern calls, and the dispatches on the primitive
types.  Each says the A-normal term a builder of `LeanScript.Expr.Build` builds has the
value of the direct-style form it is named after.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## Redexes the builders take apart -/

/-- The value of an abstraction, read off its body by `Comp.lamBody?`. -/
theorem Comp.eval_of_lamBody? {Γ : Ctx} {σ τ : TyWf} {body : Term Sg (σ :: Γ) τ}
    (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → (e : ρ = TyWf.fn σ τ) → c.lamBody? e = some body →
    (e ▸ Comp.eval G c env : TyWf.Den (TyWf.fn σ τ)) = fun x => Term.eval G body (x, env)
  | _, .lam body', e, h => by
      obtain ⟨rfl, rfl⟩ := TyWf.fn_inj e
      cases h
      rfl
  | _, .global _, _, h | _, .bool_mk _, _, h | _, .nat_mk _, _, h | _, .int_mk _, _, h
  | _, .bitvec_mk _ _, _, h | _, .uint8_mk _, _, h | _, .uint16_mk _, _, h
  | _, .uint32_mk _, _, h | _, .uint64_mk _, _, h | _, .int8_mk _, _, h
  | _, .int16_mk _, _, h | _, .int32_mk _, _, h | _, .int64_mk _, _, h
  | _, .char_mk _, _, h | _, .string_mk _, _, h | _, .stringPos_mk _ _, _, h
  | _, .stringPosRaw_mk _, _, h | _, .substringRaw_mk _, _, h | _, .stringSlice_mk _, _, h
  | _, .float_mk _, _, h | _, .float32_mk _, _, h | _, .floatModel_mk _, _, h
  | _, .float32Model_mk _, _, h | _, .ap _ _, _, h | _, .extern _, _, h
  | _, .externCall _ _, _, h | _, .lazy_mk _, _, h | _, .lazy_force _, _, h
  | _, .thunk_mk _, _, h | _, .thunk_force _, _, h | _, .array_mk _, _, h
  | _, .enum_mk _ _, _, h | _, .record_mk _ _, _, h | _, .taggedUnion_mk _ _ _ _, _, h
  | _, .recTaggedUnion_mk _ _ _ _ _, _, h | _, .recObject_mk _ _ _, _, h
  | _, .recAlias_mk _ _ _, _, h | _, .mutualRecursiveFamily_mk _ _ _, _, h => by cases h

/-- A term that `Term.lamBody?` reads as an abstraction is the function its body
    computes. -/
theorem Term.eval_of_lamBody? {Γ : Ctx} {σ τ : TyWf} {f : Term Sg Γ (TyWf.fn σ τ)}
    {body : Term Sg (σ :: Γ) τ} (h : f.lamBody? = some body) (env : Env Γ) :
    Term.eval G f env = fun x => Term.eval G body (x, env) := by
  unfold Term.lamBody? at h
  split at h
  · exact Comp.eval_of_lamBody? G env _ rfl h
  · cases h

/-- The value of a step that `Comp.boolLit?` reads as a literal. -/
theorem Comp.eval_of_boolLit? {Γ : Ctx} {b : Bool} (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → c.boolLit? = some b → Comp.eval G c env ≍ b := by
  intro ρ c h
  cases c <;> cases h
  exact .rfl

/-- A term that `Term.boolLit?` reads as a literal has that value. -/
theorem Term.eval_of_boolLit? {Γ : Ctx} {t : Term Sg Γ (.prim .bool)} {b : Bool}
    (h : t.boolLit? = some b) (env : Env Γ) : (Term.eval G t env : Bool) = b := by
  unfold Term.boolLit? at h
  split at h
  · exact eq_of_heq (Comp.eval_of_boolLit? G env _ h)
  · cases h

/-- The value of a step that `Comp.natLit?` reads as a literal. -/
theorem Comp.eval_of_natLit? {Γ : Ctx} {n : Nat} (env : Env Γ) :
    {ρ : TyWf} → (c : Comp Sg Γ ρ) → c.natLit? = some n → Comp.eval G c env ≍ n := by
  intro ρ c h
  cases c <;> cases h
  exact .rfl

/-- A term that `Term.natLit?` reads as a literal has that value. -/
theorem Term.eval_of_natLit? {Γ : Ctx} {t : Term Sg Γ (.prim .nat)} {n : Nat}
    (h : t.natLit? = some n) (env : Env Γ) : (Term.eval G t env : Nat) = n := by
  unfold Term.natLit? at h
  split at h
  · exact eq_of_heq (Comp.eval_of_natLit? G env _ h)
  · cases h

/-! ## Applications and extern calls -/

/-- **`f a` is Lean's application of the value of `f` to the value of `a`.**  This covers
    the three ways `Term.ap` builds it: a β-reduction when `f` is an abstraction, a closed
    `f` bound after `a`, and both operands named in order. -/
theorem Term.eval_ap {Γ : Ctx} {σ τ : TyWf} (f : Term Sg Γ (TyWf.fn σ τ)) (a : Term Sg Γ σ)
    (env : Env Γ) : Term.eval G (Term.ap f a) env = Term.eval G f env (Term.eval G a env) := by
  unfold Term.ap
  cases hl : f.lamBody? with
  | some body =>
      simp only
      rw [Term.eval_of_lamBody? G hl env]
      exact Term.evalJ_bind G a body env (J := []) PUnit.unit
  | none =>
      simp only
      cases hc : f.closedStep? with
      | some c =>
          simp only
          rw [Term.eval_of_closedStep? G hc env]
          refine Term.evalJ_bindAtom G a _ env (J := []) PUnit.unit (Comp.eval G c Env.nil) ?_
          intro Δ ρ env' aa h
          show Term.eval G (.letE _ _) env' = _
          rw [Term.eval_letE]
          show Comp.eval G (c.rename Ren.nil) env' (Atom.eval (aa.rename Ren.wk) _) = _
          rw [Comp.eval_rename_nil, Atom.eval_rename (EnvRel.wk _ env')]
      | none =>
          simp only
          refine Term.evalJ_bindAtomOr G f _ _ env (J := []) PUnit.unit (fun v => v (Term.eval G a env))
            ?_ ?_
          · intro fa
            exact Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit (Atom.eval fa env)
              (fun _ => rfl) fun ρ' env' aa h' => by
                show Atom.eval (fa.rename ρ') env' (Atom.eval aa env') = _
                rw [Atom.eval_rename h']
          · intro Δ ρ env' fa h
            refine (Term.evalJ_bindAtom G (a.rename ρ) _ env' (J := []) PUnit.unit
              (Atom.eval fa env') ?_).trans ?_
            · intro Θ ρ' env'' aa h'
              show Atom.eval (fa.rename ρ') env'' (Atom.eval aa env'') = _
              rw [Atom.eval_rename h']
            · show Atom.eval fa env' (Term.eval G (a.rename ρ) env') = _
              rw [Term.eval_rename G ρ a h]

/-- An abstraction is the Lean function its body computes. -/
theorem Term.eval_lam {Γ : Ctx} {σ τ : TyWf} (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.lam body) env = fun x => Term.eval G body (x, env) :=
  rfl

/-- An extern applied to terms is the Lean function applied to their values. -/
theorem Term.eval_externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) (env : Env Γ) :
    Term.eval G (Term.externCall args call) env = Extern.eval (call (Spine.eval G args env)) :=
  Spine.eval_bindArgs G args Ren.id env env (EnvRel.id' env) _
    (fun vs => Extern.eval (call vs)) fun _ _ _ _ => rfl

/-- An extern that takes a proof, applied to terms: the Lean function where the decided
    proposition holds, and the fallback where it does not. -/
theorem Term.eval_externCallChecked' {Γ : Ctx} {σs : List TyWf} {τ : TyWf}
    (args : Spine Sg Γ σs) (call : TyWf.DenList σs → Option (Extern τ))
    (fallback : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.externCallChecked' args call fallback) env =
      match call (Spine.eval G args env) with
      | some e => Extern.eval e
      | none => Term.eval G fallback env := by
  refine Spine.eval_bindArgs G args Ren.id env env (EnvRel.id' env) _
    (fun vs => match call vs with
      | some e => Extern.eval e
      | none => Term.eval G fallback env) ?_
  intro Δ ρ env' as h
  show (match call (Args.eval G as env') with
    | some e => Dest.apply Dest.ret (J := []) PUnit.unit (Extern.eval e)
    | none => Term.eval G (fallback.rename ρ) env') = _
  rw [Term.eval_rename G ρ fallback h]
  dsimp only
  cases call (Args.eval G as env') <;> rfl

/-! ## Dispatches on the primitive types -/

/-- **`if c then t else e`** takes the branch the value of `c` selects.  This covers the
    literal case, which `Term.bool_casesOn'` reduces while building. -/
theorem Term.eval_bool_casesOn' {Γ : Ctx} {τ : TyWf} (c : Term Sg Γ (.prim .bool))
    (t e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.bool_casesOn' c t e) env =
      bif (Term.eval G c env : Bool) then Term.eval G t env else Term.eval G e env := by
  unfold Term.bool_casesOn'
  cases hb : c.boolLit? with
  | some b =>
      rw [Term.eval_of_boolLit? G hb env]
      cases b <;> rfl
  | none =>
      simp only
      refine Term.evalJ_bindAtomOr G c _ _ env (J := []) PUnit.unit
        (fun v => bif (v : Bool) then Term.eval G t env else Term.eval G e env) ?_ ?_
      · intro a
        show (match (Atom.eval a env : Bool) with
          | true => Term.eval G t env | false => Term.eval G e env) = _
        cases (Atom.eval a env : Bool) <;> rfl
      · intro Δ ρ env' a h
        show (match (Atom.eval a env' : Bool) with
          | true => Term.eval G (t.rename ρ) env' | false => Term.eval G (e.rename ρ) env') = _
        rw [Term.eval_rename G ρ t h, Term.eval_rename G ρ e h]
        cases (Atom.eval a env' : Bool) <;> rfl

/-- **`match n with | 0 => z | k + 1 => s`** takes the branch the value of `n` selects,
    binding the predecessor in the successor branch.  This covers the literal case, which
    `Term.nat_casesOn'` reduces while building. -/
theorem Term.eval_nat_casesOn' {Γ : Ctx} {τ : TyWf} (n : Term Sg Γ (.prim .nat))
    (z : Term Sg Γ τ) (s : Term Sg (TyWf.prim .nat :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.nat_casesOn' n z s) env =
      Nat.casesOn (motive := fun _ => TyWf.Den τ) (Term.eval G n env : Nat) (Term.eval G z env)
        fun k => Term.eval G s (k, env) := by
  unfold Term.nat_casesOn'
  cases hn : n.natLit? with
  | some m =>
      rw [Term.eval_of_natLit? G hn env]
      cases m with
      | zero => rfl
      | succ m => exact Term.eval_letE G (.nat_mk m) s env
  | none =>
      simp only
      refine Term.evalJ_bindAtomOr G n _ _ env (J := []) PUnit.unit
        (fun v => Nat.casesOn (motive := fun _ => TyWf.Den τ) (v : Nat) (Term.eval G z env)
          fun k => Term.eval G s (k, env)) ?_ ?_
      · intro a
        show (match (Atom.eval a env : Nat) with
          | 0 => Term.eval G z env | k + 1 => Term.eval G s (k, env)) = _
        cases (Atom.eval a env : Nat) <;> rfl
      · intro Δ ρ env' a h
        show (match (Atom.eval a env' : Nat) with
          | 0 => Term.eval G (z.rename ρ) env'
          | k + 1 => Term.eval G (s.rename (Ren.lift ρ)) (k, env')) = _
        rw [Term.eval_rename G ρ z h]
        cases (Atom.eval a env' : Nat) with
        | zero => rfl
        | succ k => exact Term.eval_rename G _ s (EnvRel.lift (σ := TyWf.prim .nat) h k)

/-- Take an 8-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint8))
    (b : Term Sg ((TyWf.prim (.bitvec 8)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint8_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt8).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt8).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 16-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint16))
    (b : Term Sg ((TyWf.prim (.bitvec 16)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint16_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt16).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt16).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint32))
    (b : Term Sg ((TyWf.prim (.bitvec 32)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt32).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt32).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit unsigned value apart: the branch binds its bit vector. -/
theorem Term.eval_uint64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint64))
    (b : Term Sg ((TyWf.prim (.bitvec 64)) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.uint64_casesOn' v b) env = Term.eval G b ((Term.eval G v env : UInt64).toBitVec, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : UInt64).toBitVec, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an 8-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int8))
    (b : Term Sg ((TyWf.prim .uint8) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int8_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int8).toUInt8, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int8).toUInt8, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 16-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int16))
    (b : Term Sg ((TyWf.prim .uint16) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int16_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int16).toUInt16, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int16).toUInt16, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int32))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int32).toUInt32, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int32).toUInt32, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit signed value apart: the branch binds the unsigned value. -/
theorem Term.eval_int64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int64))
    (b : Term Sg ((TyWf.prim .uint64) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int64_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Int64).toUInt64, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Int64).toUInt64, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a character apart: the branch binds its code point. -/
theorem Term.eval_char_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .char))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.char_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Char).val, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Char).val, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an unchecked position apart: the branch binds its byte index. -/
theorem Term.eval_stringPosRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .stringPosRaw))
    (b : Term Sg ((TyWf.prim .nat) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.stringPosRaw_casesOn' v b) env = Term.eval G b ((Term.eval G v env : String.Pos.Raw).byteIdx, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : String.Pos.Raw).byteIdx, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 64-bit float apart: the branch binds its model. -/
theorem Term.eval_float_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float))
    (b : Term Sg ((TyWf.prim .floatModel) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float).toModel, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float).toModel, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take a 32-bit float apart: the branch binds its model. -/
theorem Term.eval_float32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32))
    (b : Term Sg ((TyWf.prim .float32Model) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float32_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float32).toModel, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float32).toModel, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take the model of a 64-bit float apart: the branch binds its bits. -/
theorem Term.eval_floatModel_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .floatModel))
    (b : Term Sg ((TyWf.prim .uint64) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.floatModel_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float.Model).toBits, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float.Model).toBits, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take the model of a 32-bit float apart: the branch binds its bits. -/
theorem Term.eval_float32Model_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32Model))
    (b : Term Sg ((TyWf.prim .uint32) :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.float32Model_casesOn' v b) env = Term.eval G b ((Term.eval G v env : Float32.Model).toBits, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit (fun x => Term.eval G b ((x : Float32.Model).toBits, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- `match i with | .ofNat n => … | .negSucc n => …` takes the branch the value of `i`
    selects. -/
theorem Term.eval_int_casesOn' {Γ : Ctx} {τ : TyWf} (i : Term Sg Γ (.prim .int))
    (ofNat negSucc : Term Sg (TyWf.prim .nat :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.int_casesOn' i ofNat negSucc) env =
      Int.casesOn (motive := fun _ => TyWf.Den τ) (Term.eval G i env : Int)
        (fun k => Term.eval G ofNat (k, env)) (fun k => Term.eval G negSucc (k, env)) := by
  refine Term.evalJ_bindAtomOr G i _ _ env (J := []) PUnit.unit
    (fun v => Int.casesOn (motive := fun _ => TyWf.Den τ) (v : Int)
      (fun k => Term.eval G ofNat (k, env)) (fun k => Term.eval G negSucc (k, env))) ?_ ?_
  · intro a
    show (match (Atom.eval a env : Int) with
      | .ofNat k => Term.eval G ofNat (k, env) | .negSucc k => Term.eval G negSucc (k, env)) = _
    cases (Atom.eval a env : Int) <;> rfl
  · intro Δ ρ env' a h
    show (match (Atom.eval a env' : Int) with
      | .ofNat k => Term.eval G (ofNat.rename (Ren.lift ρ)) (k, env')
      | .negSucc k => Term.eval G (negSucc.rename (Ren.lift ρ)) (k, env')) = _
    cases (Atom.eval a env' : Int) with
    | ofNat k => exact Term.eval_rename G _ ofNat (EnvRel.lift (σ := TyWf.prim .nat) h k)
    | negSucc k => exact Term.eval_rename G _ negSucc (EnvRel.lift (σ := TyWf.prim .nat) h k)

/-- Take a checked position apart: the branch binds the unchecked position. -/
theorem Term.eval_stringPos_casesOn' {Γ : Ctx} {τ : TyWf} {str : String}
    (v : Term Sg Γ (.prim (.stringPos str))) (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) τ)
    (env : Env Γ) :
    Term.eval G (Term.stringPos_casesOn' v b) env =
      Term.eval G b ((Term.eval G v env : String.Pos str).offset, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G b ((x : String.Pos str).offset, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ b (h.lift _)

/-- Take an unchecked substring apart: the branch binds its string and its two ends. -/
theorem Term.eval_substringRaw_casesOn' {Γ : Ctx} {τ : TyWf}
    (v : Term Sg Γ (.prim .substringRaw))
    (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ)
    (env : Env Γ) :
    Term.eval G (Term.substringRaw_casesOn' v b) env =
      let x : Substring.Raw := Term.eval G v env
      Term.eval G b (x.str, x.startPos, x.stopPos, env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G b ((x : Substring.Raw).str, (x : Substring.Raw).startPos,
      (x : Substring.Raw).stopPos, env))
    (fun _ => rfl) fun _ _ _ h =>
      Term.eval_rename G _ b (EnvRel.lift (EnvRel.lift (EnvRel.lift h _) _) _)

/-- A spine that `Spine.atoms?` reads as atoms has the values of those atoms. -/
theorem Spine.eval_of_atoms? {Γ : Ctx} (env : Env Γ) :
    {σs : List TyWf} → (sp : Spine Sg Γ σs) → (bs : Args Sg Γ σs) → sp.atoms? = some bs →
    Args.eval G bs env = Spine.eval G sp env
  | _, .nil, bs, h => by
      cases h
      rfl
  | _, .cons t ts, bs, h => by
      cases t with
      | ret a =>
          simp only [Spine.atoms?] at h
          cases hts : ts.atoms? with
          | none => rw [hts] at h; cases h
          | some bs' =>
              rw [hts] at h
              cases h
              show (Atom.eval a env, Args.eval G bs' env) = (Atom.eval a env, Spine.eval G ts env)
              rw [Spine.eval_of_atoms? env ts bs' hts]
      | _ => simp [Spine.atoms?] at h

/-- **The fold of a natural number** (`Nat.rec` descending `k + 1` steps) is `natFoldK` of
    the values of its bases, at the value of its argument. -/
theorem Term.eval_nat_rec' {Γ : Ctx} {τ : TyWf} (k : Nat) (n : Term Sg Γ (.prim .nat))
    (base : Spine Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ) (env : Env Γ) :
    Term.eval G (Term.nat_rec' k n base branch) env =
      natFoldK (Spine.eval G base env)
        (fun m w => Term.eval G branch (m, Env.ofWin w env)) (Term.eval G n env : Nat) := by
  refine Term.evalJ_bindAtomOr G n _ _ env (J := []) PUnit.unit
    (fun v => natFoldK (Spine.eval G base env)
      (fun m w => Term.eval G branch (m, Env.ofWin w env)) (v : Nat)) ?_ ?_
  · intro a
    show Term.evalJ (J := []) G (match base.atoms? with
      | some bs => .nat_rec k a bs branch .ret
      | none => _) env PUnit.unit = _
    split
    next bs hb =>
        show natFoldK (Args.eval G bs env) _ _ = _
        rw [Spine.eval_of_atoms? G env base bs hb]
    next hb =>
        refine Spine.eval_bindArgs G base Ren.id env env (EnvRel.id' env) _
          (fun vs => natFoldK vs (fun m w => Term.eval G branch (m, Env.ofWin w env))
            (Atom.eval a env)) ?_
        intro Δ ρ' env' bs h'
        show natFoldK (Args.eval G bs env')
          (fun m w => Term.eval G (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) ρ')))
            (m, Env.ofWin w env'))
          (Atom.eval (a.rename ρ') env') = _
        rw [Atom.eval_rename h']
        congr 1
        funext m w
        exact Term.eval_rename G _ branch (EnvRel.lift (σ := TyWf.prim .nat) (EnvRel.liftNat h' _ _ w) m)
  · intro Δ ρ env' a h
    dsimp only
    refine Spine.eval_bindArgs G base ρ env env' h _
      (fun vs => natFoldK vs (fun m w => Term.eval G branch (m, Env.ofWin w env))
        (Atom.eval a env')) ?_
    intro Θ ρ' env'' bs h'
    show natFoldK (Args.eval G bs env'')
      (fun m w => Term.eval G (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) (Ren.comp ρ' ρ))))
        (m, Env.ofWin w env''))
      (Atom.eval (a.rename ρ') env'') = _
    rw [Atom.eval_rename h']
    congr 1
    funext m w
    exact Term.eval_rename G _ branch
      (EnvRel.lift (σ := TyWf.prim .nat) (EnvRel.liftNat (EnvRel.comp h' h) _ _ w) m)
end LeanScript

end
