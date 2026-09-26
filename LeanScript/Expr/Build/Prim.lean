module

public import LeanScript.Expr.Build.Bind
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# The direct-style forms: variables, primitives, functions and externs

The literals and the case analyses of the primitive types, `lam` / `ap`, and extern calls.
The forms of the structured types are in `LeanScript.Expr.Build`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-! ## The direct-style forms -/

/-- A variable of `Γ`. -/
abbrev Term.var {Γ : Ctx} {τ : TyWf} (v : Γ ∋ τ) : Term Sg Γ τ := .ret (.var v)

/-- A reference to a top-level declaration of the module's signature. -/
abbrev Term.global {Γ : Ctx} {τ : TyWf} (r : GlobalRef Sg.decls τ) : Term Sg Γ τ :=
  .ofComp (.global r)

/-- An atom, as a term. -/
abbrev Term.atom {Γ : Ctx} {τ : TyWf} (a : Atom Γ τ) : Term Sg Γ τ := .ret a

/-- A boolean literal. -/
abbrev Term.bool_mk {Γ : Ctx} (b : Bool) : Term Sg Γ (.prim .bool) := .ofComp (.bool_mk b)
/-- A natural number literal. -/
abbrev Term.nat_mk {Γ : Ctx} (n : Nat) : Term Sg Γ (.prim .nat) := .ofComp (.nat_mk n)
/-- An integer literal. -/
abbrev Term.int_mk {Γ : Ctx} (i : Int) : Term Sg Γ (.prim .int) := .ofComp (.int_mk i)
/-- A bit-vector literal, of a positive width. -/
abbrev Term.bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
    Term Sg Γ (.prim (.bitvec n h_positive)) := .ofComp (.bitvec_mk h_positive v)
/-- An 8-bit unsigned literal. -/
abbrev Term.uint8_mk {Γ : Ctx} (v : UInt8) : Term Sg Γ (.prim .uint8) := .ofComp (.uint8_mk v)
/-- A 16-bit unsigned literal. -/
abbrev Term.uint16_mk {Γ : Ctx} (v : UInt16) : Term Sg Γ (.prim .uint16) :=
  .ofComp (.uint16_mk v)
/-- A 32-bit unsigned literal. -/
abbrev Term.uint32_mk {Γ : Ctx} (v : UInt32) : Term Sg Γ (.prim .uint32) :=
  .ofComp (.uint32_mk v)
/-- A 64-bit unsigned literal. -/
abbrev Term.uint64_mk {Γ : Ctx} (v : UInt64) : Term Sg Γ (.prim .uint64) :=
  .ofComp (.uint64_mk v)
/-- An 8-bit signed literal. -/
abbrev Term.int8_mk {Γ : Ctx} (v : Int8) : Term Sg Γ (.prim .int8) := .ofComp (.int8_mk v)
/-- A 16-bit signed literal. -/
abbrev Term.int16_mk {Γ : Ctx} (v : Int16) : Term Sg Γ (.prim .int16) := .ofComp (.int16_mk v)
/-- A 32-bit signed literal. -/
abbrev Term.int32_mk {Γ : Ctx} (v : Int32) : Term Sg Γ (.prim .int32) := .ofComp (.int32_mk v)
/-- A 64-bit signed literal. -/
abbrev Term.int64_mk {Γ : Ctx} (v : Int64) : Term Sg Γ (.prim .int64) := .ofComp (.int64_mk v)
/-- A character literal. -/
abbrev Term.char_mk {Γ : Ctx} (c : Char) : Term Sg Γ (.prim .char) := .ofComp (.char_mk c)
/-- A string literal. -/
abbrev Term.string_mk {Γ : Ctx} (s : String) : Term Sg Γ (.prim .string) :=
  .ofComp (.string_mk s)
/-- A literal position into the string `s`. -/
abbrev Term.stringPos_mk {Γ : Ctx} (s : String) (p : String.Pos s) :
    Term Sg Γ (.prim (.stringPos s)) := .ofComp (.stringPos_mk s p)
/-- A literal unchecked byte position. -/
abbrev Term.stringPosRaw_mk {Γ : Ctx} (p : String.Pos.Raw) : Term Sg Γ (.prim .stringPosRaw) :=
  .ofComp (.stringPosRaw_mk p)
/-- A literal unchecked substring. -/
abbrev Term.substringRaw_mk {Γ : Ctx} (s : Substring.Raw) : Term Sg Γ (.prim .substringRaw) :=
  .ofComp (.substringRaw_mk s)
/-- A literal string slice. -/
abbrev Term.stringSlice_mk {Γ : Ctx} (s : String.Slice) : Term Sg Γ (.prim .stringSlice) :=
  .ofComp (.stringSlice_mk s)
/-- A 64-bit floating point literal. -/
abbrev Term.float_mk {Γ : Ctx} (x : Float) : Term Sg Γ (.prim .float) := .ofComp (.float_mk x)
/-- A 32-bit floating point literal. -/
abbrev Term.float32_mk {Γ : Ctx} (x : Float32) : Term Sg Γ (.prim .float32) :=
  .ofComp (.float32_mk x)
/-- A literal of the model of a 64-bit float. -/
abbrev Term.floatModel_mk {Γ : Ctx} (m : Float.Model) : Term Sg Γ (.prim .floatModel) :=
  .ofComp (.floatModel_mk m)
/-- A literal of the model of a 32-bit float. -/
abbrev Term.float32Model_mk {Γ : Ctx} (m : Float32.Model) : Term Sg Γ (.prim .float32Model) :=
  .ofComp (.float32Model_mk m)

/-- `fun x => body`. -/
abbrev Term.lam {Γ : Ctx} {σ τ : TyWf} (body : Term Sg (σ :: Γ) τ) : Term Sg Γ (σ ⇒ τ) :=
  .ofComp (.lam body)

/-- `f a`, for any terms `f` and `a`.  If `f` is an abstraction `fun x => body`, this is
    `let x = a; body` (a β-reduction: no closure is built).  Otherwise both are named, `f`
    first — unless `f` is a closed step (a declaration, typically), which is named last. -/
def Term.ap {Γ : Ctx} {σ τ : TyWf} (f : Term Sg Γ (σ ⇒ τ)) (a : Term Sg Γ σ) : Term Sg Γ τ :=
  match f.lamBody? with
  | some body => a.bind body
  | none =>
  match f.closedStep? with
  | some c =>
      a.bindAtom fun _ aa =>
        .letE (c.rename Ren.nil) (.ofComp (.ap (.var .head) (aa.rename Ren.wk)))
  | none =>
      f.bindAtomOr
        (fun fa => a.bindAtomOr (fun aa => .ofComp (.ap fa aa))
          fun ρ' aa => .ofComp (.ap (fa.rename ρ') aa))
        fun ρ fa => (a.rename ρ).bindAtom fun ρ' aa => .ofComp (.ap (fa.rename ρ') aa)

/-- A pure extern of `Init` applied to values. -/
abbrev Term.extern {Γ : Ctx} {τ : TyWf} (e : Extern τ) : Term Sg Γ τ := .ofComp (.extern e)

/-- A pure extern of `Init` applied to the terms of its arguments. -/
def Term.externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun _ as => .ofComp (.externCall as call)

/-- A pure extern of `Init` that takes a proof, applied to the terms of its arguments. -/
def Term.externCallChecked' {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun ρ as => (.externCallChecked as call .ret (fallback.rename ρ))

/-- `if c then t else e`; on a literal condition, the branch it selects. -/
def Term.bool_casesOn' {Γ : Ctx} {τ : TyWf} (c : Term Sg Γ (.prim .bool))
    (t e : Term Sg Γ τ) : Term Sg Γ τ :=
  match c.boolLit? with
  | some true => t
  | some false => e
  | none =>
      c.bindAtomOr (fun a => (.bool_casesOn a t e))
        fun ρ a => (.bool_casesOn a (t.rename ρ) (e.rename ρ))

/-- `match n with | 0 => … | k + 1 => …`; on a literal, the branch it selects. -/
def Term.nat_casesOn' {Γ : Ctx} {τ : TyWf} (n : Term Sg Γ (.prim .nat)) (z : Term Sg Γ τ)
    (s : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  match n.natLit? with
  | some 0 => z
  | some (m + 1) => .letE (.nat_mk m) s
  | none =>
      n.bindAtomOr (fun a => (.nat_casesOn a z s))
        fun ρ a => (.nat_casesOn a (z.rename ρ) (s.rename (Ren.lift ρ)))

/-- `Nat.rec` that descends `k + 1` steps. -/
def Term.nat_rec' {Γ : Ctx} {τ : TyWf} (k : Nat := 0) (n : Term Sg Γ (.prim .nat))
    (base : Spine Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  n.bindAtomOr
    (fun a => match base.atoms? with
      | some bs => .nat_rec k a bs branch .ret
      | none =>
          base.bindArgs Ren.id fun ρ' bs =>
            (.nat_rec k (a.rename ρ') bs
              (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) ρ'))) .ret))
    fun ρ a =>
    base.bindArgs ρ fun ρ' bs =>
      (.nat_rec k (a.rename ρ') bs
        (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) (Ren.comp ρ' ρ)))) .ret)

/-- `match i with | .ofNat n => … | .negSucc n => …`. -/
def Term.int_casesOn' {Γ : Ctx} {τ : TyWf} (i : Term Sg Γ (.prim .int))
    (ofNat negSucc : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  i.bindAtomOr (fun a =>
    (.int_casesOn a ofNat negSucc))
    fun ρ a =>
    (.int_casesOn a (ofNat.rename (Ren.lift ρ)) (negSucc.rename (Ren.lift ρ)))

/-- Take an 8-bit unsigned value apart. -/
def Term.uint8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint8))
    (b : Term Sg (TyWf.prim (.bitvec 8) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint8_casesOn a b))
    fun ρ a => (.uint8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit unsigned value apart. -/
def Term.uint16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint16))
    (b : Term Sg (TyWf.prim (.bitvec 16) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint16_casesOn a b))
    fun ρ a => (.uint16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit unsigned value apart. -/
def Term.uint32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint32))
    (b : Term Sg (TyWf.prim (.bitvec 32) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint32_casesOn a b))
    fun ρ a => (.uint32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit unsigned value apart. -/
def Term.uint64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint64))
    (b : Term Sg (TyWf.prim (.bitvec 64) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.uint64_casesOn a b))
    fun ρ a => (.uint64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an 8-bit signed value apart. -/
def Term.int8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int8))
    (b : Term Sg (TyWf.prim .uint8 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int8_casesOn a b))
    fun ρ a => (.int8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit signed value apart. -/
def Term.int16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int16))
    (b : Term Sg (TyWf.prim .uint16 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int16_casesOn a b))
    fun ρ a => (.int16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit signed value apart. -/
def Term.int32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int32))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int32_casesOn a b))
    fun ρ a => (.int32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit signed value apart. -/
def Term.int64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int64))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.int64_casesOn a b))
    fun ρ a => (.int64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a character apart. -/
def Term.char_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .char))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.char_casesOn a b))
    fun ρ a => (.char_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked position apart. -/
def Term.stringPosRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .stringPosRaw))
    (b : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.stringPosRaw_casesOn a b))
    fun ρ a => (.stringPosRaw_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a checked position apart. -/
def Term.stringPos_casesOn' {Γ : Ctx} {τ : TyWf} {s : String}
    (v : Term Sg Γ (.prim (.stringPos s)))
    (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.stringPos_casesOn a b))
    fun ρ a => (.stringPos_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked substring apart. -/
def Term.substringRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .substringRaw))
    (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.substringRaw_casesOn a b))
    fun ρ a =>
    (.substringRaw_casesOn a (b.rename (Ren.lift (Ren.lift (Ren.lift ρ)))))

/-- Take a 64-bit float apart. -/
def Term.float_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float))
    (b : Term Sg (TyWf.prim .floatModel :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float_casesOn a b))
    fun ρ a => (.float_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit float apart. -/
def Term.float32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32))
    (b : Term Sg (TyWf.prim .float32Model :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float32_casesOn a b))
    fun ρ a => (.float32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 64-bit float apart. -/
def Term.floatModel_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .floatModel))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.floatModel_casesOn a b))
    fun ρ a => (.floatModel_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 32-bit float apart. -/
def Term.float32Model_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32Model))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.float32Model_casesOn a b))
    fun ρ a => (.float32Model_casesOn a (b.rename (Ren.lift ρ)))

end LeanScript

end
