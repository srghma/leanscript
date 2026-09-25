module
public import LeanScript.Expr.Rename
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# Building A-normal terms

`LeanScript.Term` is in A-normal form by construction, so a term whose operands are
themselves computations cannot be written with its constructors directly: each operand has
to be named by a `let` first.  The functions of this file do that naming.  Each of them is
named like the constructor of the *direct-style* grammar it stands for (`Term.ap`,
`Term.nat_casesOn`, `Term.record_mk`, …) and takes arbitrary terms as operands; it binds
every operand that is not already an atom with `Term.letE`, left to right, and applies the
computation step to the atoms it got.  The branches and bodies it is given are moved under
those `let`s by renaming (`LeanScript.Expr.Rename`).

So a term written in direct style,

    .ap (.global f) (.ap (.global g) (.nat_mk 1))

*is* the A-normal term

    .letE (.ap (.global g) (.nat_mk 1)) (.ret (.ap (.global f) (.var .head)))

— an operand that is already an atom (`.global f`, `.nat_mk 1`, a variable) is used as
it is, and anything else is let-bound.

The lists of operands of the direct style — `LeanScript.Spine`, `LeanScript.Terms` and
`LeanScript.FamilyMemberValue` — are here too; the grammar itself holds lists of atoms
(`LeanScript.Args`, `List Atom`, `LeanScript.FamilyMemberArgs`).
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- Renamings compose. -/
def Ren.comp {Γ Δ Θ : Ctx} (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) : Ren Γ Θ := fun v => ρ' (ρ v)

variable {Sg : Sig}

/-! ## Sending the value of a term to a join point -/

/-- A join point of `J₀`, in the context of join points `J₀ ++ σ :: J`. -/
def JVar.embedL {x σ : TyWf} {J : JCtx} : {J₀ : JCtx} → J₀ ∋ x → (J₀ ++ σ :: J) ∋ x
  | _ :: _, .head => .head
  | _ :: _, .tail v => .tail (JVar.embedL v)

/-- The join point inserted after `J₀`, in the context `J₀ ++ σ :: J`. -/
def JVar.mid {σ : TyWf} {J : JCtx} : (J₀ : JCtx) → (J₀ ++ σ :: J) ∋ σ
  | [] => .head
  | _ :: J₀ => .tail (JVar.mid J₀)

/-- Where a fold's answer goes, once the value of the term it ends is sent to the join
    point `JVar.mid J₀`. -/
def Dest.toJump {ρ σ τ : TyWf} {J₀ J : JCtx} : Dest J₀ ρ σ → Dest (J₀ ++ σ :: J) ρ τ
  | .ret => .jump (JVar.mid J₀)
  | .jump j => .jump (JVar.embedL j)

mutual

/-- **Send the value of `t` to a join point.**  Every tail of `t` that gives the value of
    `t` — a last computation, or a fold that answers with it — is made to jump instead to
    the join point inserted after the join points `J₀` of `t`, whose parameter has the type
    `σ` of `t`.  The result answers with the type `τ` of that join point.  A dispatch sends
    each of its branches; the branches of a fold, and bodies of functions and delays, are
    left alone, since they do not give the value of `t`. -/
def Term.toJump {Γ : Ctx} {σ τ : TyWf} {J₀ J : JCtx} :
    Term Sg Γ σ J₀ → Term Sg Γ τ (J₀ ++ σ :: J)
  | .ret (.atom a) => .jump (JVar.mid J₀) a
  | .ret c => .letE c (.jump (JVar.mid J₀) (.var .head))
  | .letE c body => .letE c body.toJump
  | .letJ jp body => .letJ jp.toJump body.toJump
  | .jump j a => .jump (JVar.embedL j) a
  | .externCallChecked args call d fallback =>
      .externCallChecked args call d.toJump fallback.toJump
  | .bool_casesOn c t e => .bool_casesOn c t.toJump e.toJump
  | .nat_casesOn n z s => .nat_casesOn n z.toJump s.toJump
  | .nat_rec k n base branch d => .nat_rec k n base branch d.toJump
  | .int_casesOn i a b => .int_casesOn i a.toJump b.toJump
  | .uint8_casesOn v b => .uint8_casesOn v b.toJump
  | .uint16_casesOn v b => .uint16_casesOn v b.toJump
  | .uint32_casesOn v b => .uint32_casesOn v b.toJump
  | .uint64_casesOn v b => .uint64_casesOn v b.toJump
  | .int8_casesOn v b => .int8_casesOn v b.toJump
  | .int16_casesOn v b => .int16_casesOn v b.toJump
  | .int32_casesOn v b => .int32_casesOn v b.toJump
  | .int64_casesOn v b => .int64_casesOn v b.toJump
  | .char_casesOn v b => .char_casesOn v b.toJump
  | .stringPosRaw_casesOn v b => .stringPosRaw_casesOn v b.toJump
  | .stringPos_casesOn v b => .stringPos_casesOn v b.toJump
  | .substringRaw_casesOn v b => .substringRaw_casesOn v b.toJump
  | .float_casesOn v b => .float_casesOn v b.toJump
  | .float32_casesOn v b => .float32_casesOn v b.toJump
  | .floatModel_casesOn v b => .floatModel_casesOn v b.toJump
  | .float32Model_casesOn v b => .float32Model_casesOn v b.toJump
  | .array_casesOn a z s => .array_casesOn a z.toJump s.toJump
  | .array_rec k a bases branch d => .array_rec k a bases branch d.toJump
  | .enum_casesOn e cases => .enum_casesOn e cases.toJump
  | .enum_casesOnWithDefault e cases dflt hk =>
      .enum_casesOnWithDefault e cases.toJump dflt.toJump hk
  | .record_casesOn r body => .record_casesOn r body.toJump
  | .taggedUnion_casesOn v cases => .taggedUnion_casesOn v cases.toJump
  | .taggedUnion_casesOnWithDefault v cases dflt hk =>
      .taggedUnion_casesOnWithDefault v cases.toJump dflt.toJump hk
  | .recTaggedUnion_casesOn v cases => .recTaggedUnion_casesOn v cases.toJump
  | .recTaggedUnion_casesOnWithDefault v cases dflt hk =>
      .recTaggedUnion_casesOnWithDefault v cases.toJump dflt.toJump hk
  | .recTaggedUnion_rec k v cases d => .recTaggedUnion_rec k v cases d.toJump
  | .recObject_casesOn v body => .recObject_casesOn v body.toJump
  | .recObject_rec k v body d => .recObject_rec k v body d.toJump
  | .recAlias_casesOn v body => .recAlias_casesOn v body.toJump
  | .recAlias_rec k v body d => .recAlias_rec k v body d.toJump
  | .mutualRecursiveFamily_casesOn v cases => .mutualRecursiveFamily_casesOn v cases.toJump
  | .mutualRecursiveFamily_casesOnWithDefault v cases dflt =>
      .mutualRecursiveFamily_casesOnWithDefault v cases.toJump dflt.toJump
  | .mutualRecursiveFamily_rec k v cases d => .mutualRecursiveFamily_rec k v cases d.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on a tagged union. -/
def TaggedUnionSomeCases.toJump {Γ : Ctx} {l : LeanTaggedUnionSchema TyWf} {σ τ : TyWf}
    {k lo : Nat} {J₀ J : JCtx} :
    TaggedUnionSomeCases Sg Γ l σ k lo J₀ → TaggedUnionSomeCases Sg Γ l τ k lo (J₀ ++ σ :: J)
  | .last t ht branch hi => .last t ht branch.toJump hi
  | .cons t ht branch rest hi => .cons t ht branch.toJump rest.toJump hi

/-- `Term.toJump`, on each branch of a dispatch on an enum. -/
def EnumCases.toJump {Γ : Ctx} {σ τ : TyWf} {s : LeanEnumSchema} {J₀ J : JCtx} :
    EnumCases Sg Γ σ s J₀ → EnumCases Sg Γ τ s (J₀ ++ σ :: J)
  | .three b0 b1 b2 => .three b0.toJump b1.toJump b2.toJump
  | .cons b rest => .cons b.toJump rest.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on an enum. -/
def EnumSomeCases.toJump {Γ : Ctx} {σ τ : TyWf} {s : LeanEnumSchema} {k lo : Nat}
    {J₀ J : JCtx} : EnumSomeCases Sg Γ σ s k lo J₀ → EnumSomeCases Sg Γ τ s k lo (J₀ ++ σ :: J)
  | .last i branch hi => .last i branch.toJump hi
  | .cons i branch rest hi => .cons i branch.toJump rest.toJump hi

/-- `Term.toJump`, on each branch of a dispatch on a sum type. -/
def TaggedUnionFoldCases.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {l : LeanTaggedUnionSchema ι} {σ τ : TyWf} {J₀ J : JCtx} :
    TaggedUnionFoldCases Sg ι bind Γ l σ J₀ → TaggedUnionFoldCases Sg ι bind Γ l τ (J₀ ++ σ :: J)
  | .payloadFirst b0 b1 rest => .payloadFirst b0.toJump b1.toJump rest.toJump
  | .skip b0 rest => .skip b0.toJump rest.toJump

/-- `TaggedUnionFoldCases.toJump`, on the constructors a `CtorsWithPayload` holds. -/
def CtorsWithPayloadFoldCases.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {c : CtorsWithPayload ι} {σ τ : TyWf} {J₀ J : JCtx} :
    CtorsWithPayloadFoldCases Sg ι bind Γ c σ J₀ →
      CtorsWithPayloadFoldCases Sg ι bind Γ c τ (J₀ ++ σ :: J)
  | .here b rest => .here b.toJump rest.toJump
  | .skip b rest => .skip b.toJump rest.toJump

/-- `TaggedUnionFoldCases.toJump`, on a plain list of constructors. -/
def TaggedUnionFoldCasesRest.toJump {ι : Type} {bind : List ι → List TyWf} {Γ : Ctx}
    {cs : List (List ι)} {σ τ : TyWf} {J₀ J : JCtx} :
    TaggedUnionFoldCasesRest Sg ι bind Γ cs σ J₀ →
      TaggedUnionFoldCasesRest Sg ι bind Γ cs τ (J₀ ++ σ :: J)
  | .nil => .nil
  | .cons b rest => .cons b.toJump rest.toJump

/-- `Term.toJump`, on each branch of a dispatch on a member of a mutual family. -/
def FamilyMemberCases.toJump {Γ : Ctx} {σ τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J₀ J : JCtx} : FamilyMemberCases Sg Γ σ m J₀ → FamilyMemberCases Sg Γ τ m (J₀ ++ σ :: J)
  | .ctors cases => .ctors cases.toJump
  | .record body => .record body.toJump
  | .alias body => .alias body.toJump

/-- `Term.toJump`, on each branch of a partial dispatch on a member of a mutual family. -/
def FamilyMemberSomeCases.toJump {Γ : Ctx} {σ τ : TyWf} {m : LeanFamMemberSchema TyWf}
    {J₀ J : JCtx} :
    FamilyMemberSomeCases Sg Γ σ m J₀ → FamilyMemberSomeCases Sg Γ τ m (J₀ ++ σ :: J)
  | .ctors cases hk => .ctors cases.toJump hk

end

/-! ## Naming an operand -/

/-- **Name the value of `t`** and go on with an atom for it.  The continuation `k` is
    given the atom in a context `Δ` that extends `Γ`, together with the renaming from `Γ`
    into `Δ`, so that what it writes after can be moved there.

    * If `t` is already an atom nothing is bound and `k` gets it in `Γ` itself.
    * If `t` ends in a computation, its `let`s are floated out and the computation is
      bound by one more `let`.
    * If `t` ends in a dispatch or a fold — which cannot be bound by a `let` — what `k`
      writes becomes a **join point**, and every tail of `t` jumps to it with the value it
      gives (`Term.toJump`).  `k` is used once in every case, so nothing is duplicated. -/
def Term.bindAtom {Γ : Ctx} {σ τ : TyWf} {J : JCtx} :
    Term Sg Γ σ → (∀ {Δ : Ctx}, Ren Γ Δ → Atom Sg Δ σ → Term Sg Δ τ J) → Term Sg Γ τ J
  | .ret (.atom a), k => k Ren.id a
  | .ret c, k => .letE c (k Ren.wk (.var .head))
  | .letE c t, k => .letE c (t.bindAtom fun ρ a => k (Ren.comp ρ Ren.wk) a)
  | t, k => .letJ (k Ren.wk (.var .head)) (t.toJump (J₀ := []))

/-- **`let x = t; body`**, for any term `t`: the `let`s of `t` are floated out in front,
    and the computation it ends in is bound to `x`; if `t` ends in a dispatch or a fold,
    `body` becomes a join point that every tail of `t` jumps to. -/
def Term.bind {Γ : Ctx} {σ τ : TyWf} {J : JCtx} :
    Term Sg Γ σ → Term Sg (σ :: Γ) τ J → Term Sg Γ τ J
  | .ret c, body => .letE c body
  | .letE c t, body => .letE c (t.bind (body.rename (Ren.lift Ren.wk)))
  | t, body => .letJ body (t.toJump (J₀ := []))

/-! ## Lists of operands, in direct style -/

/-- The elements of an array, in direct style: any number of terms, all of one type. -/
inductive Terms (Sg : Sig) : Ctx → TyWf → Type 1
  /-- No more elements. -/
  | nil : ∀ {Γ τ}, Terms Sg Γ τ
  /-- One more element, at the front. -/
  | cons : ∀ {Γ τ}, Term Sg Γ τ → Terms Sg Γ τ → Terms Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    fields of a constructor, in direct style. -/
inductive Spine (Sg : Sig) : Ctx → List TyWf → Type 1
  /-- No more arguments. -/
  | nil : ∀ {Γ}, Spine Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- A value of one member of a mutual recursive family, in direct style: its fields (or
    its body) are terms. -/
inductive FamilyMemberValue (Sg : Sig) : Ctx → LeanFamMemberSchema TyWf → Type 1
  /-- A member with constructors: constructor `t` of it, and that constructor's
      fields. -/
  | ctors {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
      FamilyMemberValue Sg Γ (.ctors l)
  /-- A record member: its fields, in declaration order. -/
  | record {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Spine Sg Γ fs.toList) :
      FamilyMemberValue Sg Γ (.record fs)
  /-- A newtype member: a value of its body, whose wrapper is erased. -/
  | alias {Γ : Ctx} (b : TyWf) (value : Term Sg Γ b) : FamilyMemberValue Sg Γ (.alias b)

/-- Name every element of a list, left to right, after moving it along `ρ`, and go on with
    the atoms. -/
def Terms.bindAtoms {Γ Δ₀ : Ctx} {σ τ : TyWf} :
    Terms Sg Γ σ → Ren Γ Δ₀ →
    (∀ {Δ : Ctx}, Ren Δ₀ Δ → List (Atom Sg Δ σ) → Term Sg Δ τ) → Term Sg Δ₀ τ
  | .nil, _, k => k Ren.id []
  | .cons t ts, ρ, k =>
      (t.rename ρ).bindAtom fun ρ₁ a =>
        ts.bindAtoms (Ren.comp ρ₁ ρ) fun ρ₂ as => k (Ren.comp ρ₂ ρ₁) (a.rename ρ₂ :: as)

/-- Name every term of a spine, left to right, after moving it along `ρ`, and go on with
    the atoms. -/
def Spine.bindArgs {Γ Δ₀ : Ctx} {τ : TyWf} :
    {σs : List TyWf} → Spine Sg Γ σs → Ren Γ Δ₀ →
    (∀ {Δ : Ctx}, Ren Δ₀ Δ → Args Sg Δ σs → Term Sg Δ τ) → Term Sg Δ₀ τ
  | _, .nil, _, k => k Ren.id .nil
  | _, .cons t ts, ρ, k =>
      (t.rename ρ).bindAtom fun ρ₁ a =>
        ts.bindArgs (Ren.comp ρ₁ ρ) fun ρ₂ as => k (Ren.comp ρ₂ ρ₁) (.cons (a.rename ρ₂) as)

/-- Name the operands of a value of a member of a mutual family, and go on with them. -/
def FamilyMemberValue.bindArgs {Γ : Ctx} {m : LeanFamMemberSchema TyWf} {τ : TyWf} :
    FamilyMemberValue Sg Γ m →
    (∀ {Δ : Ctx}, Ren Γ Δ → FamilyMemberArgs Sg Δ m → Term Sg Δ τ) → Term Sg Γ τ
  | .ctors l t ht fields, k => fields.bindArgs Ren.id fun ρ as => k ρ (.ctors l t ht as)
  | .record fs fields, k => fields.bindArgs Ren.id fun ρ as => k ρ (.record fs as)
  | .alias b value, k => value.bindAtom fun ρ a => k ρ (.alias b a)

/-! ## The direct-style forms -/

/-- A variable of `Γ`. -/
abbrev Term.var {Γ : Ctx} {τ : TyWf} (v : Γ ∋ τ) : Term Sg Γ τ := .ret (.atom (.var v))

/-- A reference to a top-level declaration of the module's signature. -/
abbrev Term.global {Γ : Ctx} {τ : TyWf} (r : GlobalRef Sg.decls τ) : Term Sg Γ τ :=
  .ret (.atom (.global r))

/-- An atom, as a term. -/
abbrev Term.atom {Γ : Ctx} {τ : TyWf} (a : Atom Sg Γ τ) : Term Sg Γ τ := .ret (.atom a)

/-- A boolean literal. -/
abbrev Term.bool_mk {Γ : Ctx} (b : Bool) : Term Sg Γ (.prim .bool) := .atom (.bool_mk b)
/-- A natural number literal. -/
abbrev Term.nat_mk {Γ : Ctx} (n : Nat) : Term Sg Γ (.prim .nat) := .atom (.nat_mk n)
/-- An integer literal. -/
abbrev Term.int_mk {Γ : Ctx} (i : Int) : Term Sg Γ (.prim .int) := .atom (.int_mk i)
/-- A bit-vector literal, of a positive width. -/
abbrev Term.bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
    Term Sg Γ (.prim (.bitvec n h_positive)) := .atom (.bitvec_mk h_positive v)
/-- An 8-bit unsigned literal. -/
abbrev Term.uint8_mk {Γ : Ctx} (v : UInt8) : Term Sg Γ (.prim .uint8) := .atom (.uint8_mk v)
/-- A 16-bit unsigned literal. -/
abbrev Term.uint16_mk {Γ : Ctx} (v : UInt16) : Term Sg Γ (.prim .uint16) :=
  .atom (.uint16_mk v)
/-- A 32-bit unsigned literal. -/
abbrev Term.uint32_mk {Γ : Ctx} (v : UInt32) : Term Sg Γ (.prim .uint32) :=
  .atom (.uint32_mk v)
/-- A 64-bit unsigned literal. -/
abbrev Term.uint64_mk {Γ : Ctx} (v : UInt64) : Term Sg Γ (.prim .uint64) :=
  .atom (.uint64_mk v)
/-- An 8-bit signed literal. -/
abbrev Term.int8_mk {Γ : Ctx} (v : Int8) : Term Sg Γ (.prim .int8) := .atom (.int8_mk v)
/-- A 16-bit signed literal. -/
abbrev Term.int16_mk {Γ : Ctx} (v : Int16) : Term Sg Γ (.prim .int16) := .atom (.int16_mk v)
/-- A 32-bit signed literal. -/
abbrev Term.int32_mk {Γ : Ctx} (v : Int32) : Term Sg Γ (.prim .int32) := .atom (.int32_mk v)
/-- A 64-bit signed literal. -/
abbrev Term.int64_mk {Γ : Ctx} (v : Int64) : Term Sg Γ (.prim .int64) := .atom (.int64_mk v)
/-- A character literal. -/
abbrev Term.char_mk {Γ : Ctx} (c : Char) : Term Sg Γ (.prim .char) := .atom (.char_mk c)
/-- A string literal. -/
abbrev Term.string_mk {Γ : Ctx} (s : String) : Term Sg Γ (.prim .string) :=
  .atom (.string_mk s)
/-- A literal position into the string `s`. -/
abbrev Term.stringPos_mk {Γ : Ctx} (s : String) (p : String.Pos s) :
    Term Sg Γ (.prim (.stringPos s)) := .atom (.stringPos_mk s p)
/-- A literal unchecked byte position. -/
abbrev Term.stringPosRaw_mk {Γ : Ctx} (p : String.Pos.Raw) : Term Sg Γ (.prim .stringPosRaw) :=
  .atom (.stringPosRaw_mk p)
/-- A literal unchecked substring. -/
abbrev Term.substringRaw_mk {Γ : Ctx} (s : Substring.Raw) : Term Sg Γ (.prim .substringRaw) :=
  .atom (.substringRaw_mk s)
/-- A literal string slice. -/
abbrev Term.stringSlice_mk {Γ : Ctx} (s : String.Slice) : Term Sg Γ (.prim .stringSlice) :=
  .atom (.stringSlice_mk s)
/-- A 64-bit floating point literal. -/
abbrev Term.float_mk {Γ : Ctx} (x : Float) : Term Sg Γ (.prim .float) := .atom (.float_mk x)
/-- A 32-bit floating point literal. -/
abbrev Term.float32_mk {Γ : Ctx} (x : Float32) : Term Sg Γ (.prim .float32) :=
  .atom (.float32_mk x)
/-- A literal of the model of a 64-bit float. -/
abbrev Term.floatModel_mk {Γ : Ctx} (m : Float.Model) : Term Sg Γ (.prim .floatModel) :=
  .atom (.floatModel_mk m)
/-- A literal of the model of a 32-bit float. -/
abbrev Term.float32Model_mk {Γ : Ctx} (m : Float32.Model) : Term Sg Γ (.prim .float32Model) :=
  .atom (.float32Model_mk m)

/-- `fun x => body`. -/
abbrev Term.lam {Γ : Ctx} {σ τ : TyWf} (body : Term Sg (σ :: Γ) τ) : Term Sg Γ (σ ⇒ τ) :=
  .ret (.lam body)

/-- `f a`, for any terms `f` and `a`: both are named, `f` first. -/
def Term.ap {Γ : Ctx} {σ τ : TyWf} (f : Term Sg Γ (σ ⇒ τ)) (a : Term Sg Γ σ) : Term Sg Γ τ :=
  f.bindAtom fun ρ fa => (a.rename ρ).bindAtom fun ρ' aa => .ret (.ap (fa.rename ρ') aa)

/-- A pure extern of `Init` applied to values. -/
abbrev Term.extern {Γ : Ctx} {τ : TyWf} (e : Extern τ) : Term Sg Γ τ := .ret (.extern e)

/-- A pure extern of `Init` applied to the terms of its arguments. -/
def Term.externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun _ as => .ret (.externCall as call)

/-- A pure extern of `Init` that takes a proof, applied to the terms of its arguments. -/
def Term.externCallChecked' {Γ : Ctx} {σs : List TyWf} {τ : TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ τ) : Term Sg Γ τ :=
  args.bindArgs Ren.id fun ρ as => (.externCallChecked as call .ret (fallback.rename ρ))

/-- `if c then t else e`. -/
def Term.bool_casesOn' {Γ : Ctx} {τ : TyWf} (c : Term Sg Γ (.prim .bool))
    (t e : Term Sg Γ τ) : Term Sg Γ τ :=
  c.bindAtom fun ρ a => (.bool_casesOn a (t.rename ρ) (e.rename ρ))

/-- `match n with | 0 => … | k + 1 => …`. -/
def Term.nat_casesOn' {Γ : Ctx} {τ : TyWf} (n : Term Sg Γ (.prim .nat)) (z : Term Sg Γ τ)
    (s : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  n.bindAtom fun ρ a => (.nat_casesOn a (z.rename ρ) (s.rename (Ren.lift ρ)))

/-- `Nat.rec` that descends `k + 1` steps. -/
def Term.nat_rec' {Γ : Ctx} {τ : TyWf} (k : Nat := 0) (n : Term Sg Γ (.prim .nat))
    (base : Spine Sg Γ (natRecCtx τ (k + 1) []))
    (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  n.bindAtom fun ρ a =>
    base.bindArgs ρ fun ρ' bs =>
      (.nat_rec k (a.rename ρ') bs
        (branch.rename (Ren.lift (Ren.liftNat τ (k + 1) (Ren.comp ρ' ρ)))) .ret)

/-- `match i with | .ofNat n => … | .negSucc n => …`. -/
def Term.int_casesOn' {Γ : Ctx} {τ : TyWf} (i : Term Sg Γ (.prim .int))
    (ofNat negSucc : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  i.bindAtom fun ρ a =>
    (.int_casesOn a (ofNat.rename (Ren.lift ρ)) (negSucc.rename (Ren.lift ρ)))

/-- Take an 8-bit unsigned value apart. -/
def Term.uint8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint8))
    (b : Term Sg (TyWf.prim (.bitvec 8) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.uint8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit unsigned value apart. -/
def Term.uint16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint16))
    (b : Term Sg (TyWf.prim (.bitvec 16) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.uint16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit unsigned value apart. -/
def Term.uint32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint32))
    (b : Term Sg (TyWf.prim (.bitvec 32) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.uint32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit unsigned value apart. -/
def Term.uint64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .uint64))
    (b : Term Sg (TyWf.prim (.bitvec 64) :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.uint64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an 8-bit signed value apart. -/
def Term.int8_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int8))
    (b : Term Sg (TyWf.prim .uint8 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.int8_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 16-bit signed value apart. -/
def Term.int16_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int16))
    (b : Term Sg (TyWf.prim .uint16 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.int16_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit signed value apart. -/
def Term.int32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int32))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.int32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 64-bit signed value apart. -/
def Term.int64_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .int64))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.int64_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a character apart. -/
def Term.char_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .char))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.char_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked position apart. -/
def Term.stringPosRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .stringPosRaw))
    (b : Term Sg (TyWf.prim .nat :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.stringPosRaw_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a checked position apart. -/
def Term.stringPos_casesOn' {Γ : Ctx} {τ : TyWf} {s : String}
    (v : Term Sg Γ (.prim (.stringPos s)))
    (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.stringPos_casesOn a (b.rename (Ren.lift ρ)))

/-- Take an unchecked substring apart. -/
def Term.substringRaw_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .substringRaw))
    (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ) τ) :
    Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.substringRaw_casesOn a (b.rename (Ren.lift (Ren.lift (Ren.lift ρ)))))

/-- Take a 64-bit float apart. -/
def Term.float_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float))
    (b : Term Sg (TyWf.prim .floatModel :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.float_casesOn a (b.rename (Ren.lift ρ)))

/-- Take a 32-bit float apart. -/
def Term.float32_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32))
    (b : Term Sg (TyWf.prim .float32Model :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.float32_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 64-bit float apart. -/
def Term.floatModel_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .floatModel))
    (b : Term Sg (TyWf.prim .uint64 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.floatModel_casesOn a (b.rename (Ren.lift ρ)))

/-- Take the model of a 32-bit float apart. -/
def Term.float32Model_casesOn' {Γ : Ctx} {τ : TyWf} (v : Term Sg Γ (.prim .float32Model))
    (b : Term Sg (TyWf.prim .uint32 :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.float32Model_casesOn a (b.rename (Ren.lift ρ)))

/-- Delay a value, unmemoised. -/
abbrev Term.lazy_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.lazy τ) :=
  .ret (.lazy_mk e)

/-- Run a delayed value. -/
def Term.lazy_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.lazy τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ret (.lazy_force a)

/-- Delay a value and remember it: a `Thunk`. -/
abbrev Term.thunk_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.thunk τ) :=
  .ret (.thunk_mk e)

/-- Force a thunk. -/
def Term.thunk_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.thunk τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ret (.thunk_force a)

/-- An array, from its elements, in order. -/
def Term.array_mk {Γ : Ctx} {τ : TyWf} (ts : Terms Sg Γ τ) : Term Sg Γ (.array τ) :=
  ts.bindAtoms Ren.id fun _ as => .ret (.array_mk as)

/-- Take an array apart. -/
def Term.array_casesOn' {Γ : Ctx} {σ τ : TyWf} (a : Term Sg Γ (.array σ)) (z : Term Sg Γ τ)
    (s : Term Sg (σ :: TyWf.array σ :: Γ) τ) : Term Sg Γ τ :=
  a.bindAtom fun ρ x => (.array_casesOn x (z.rename ρ) (s.rename (Ren.lift (Ren.lift ρ))))

/-- The fold of an array that descends `k + 1` elements at a time. -/
def Term.array_rec' {Γ : Ctx} {σ τ : TyWf} (k : Nat := 0) (a : Term Sg Γ (.array σ))
    (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  a.bindAtom fun ρ x =>
    (.array_rec k x (bases.rename ρ)
      (branch.rename (Ren.lift (Ren.lift (Ren.liftNat τ (k + 1) ρ)))) .ret)

/-- A constructor of an enum. -/
abbrev Term.enum_mk {Γ : Ctx} (s : LeanEnumSchema) (i : Fin s.nOfConstructors) :
    Term Sg Γ (.enum s) := .ret (.enum_mk s i)

/-- A dispatch on an enum. -/
def Term.enum_casesOn' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} (e : Term Sg Γ (.enum s))
    (cases : EnumCases Sg Γ τ s) : Term Sg Γ τ :=
  e.bindAtom fun ρ a => (.enum_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of an enum, with a default. -/
def Term.enum_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {k : Nat}
    (e : Term Sg Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k) (dflt : Term Sg Γ τ)
    (hk : k < s.nOfConstructors := by ctor_lt) : Term Sg Γ τ :=
  e.bindAtom fun ρ a => (.enum_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A record, from its fields. -/
def Term.record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Spine Sg Γ fs.toList) :
    Term Sg Γ (.record fs) :=
  fields.bindArgs Ren.id fun _ as => .ret (.record_mk fs as)

/-- The eliminator of a record. -/
def Term.record_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf}
    (r : Term Sg Γ (.record fs)) (body : Term Sg (fs.toList ++ Γ) τ) : Term Sg Γ τ :=
  r.bindAtom fun ρ a => (.record_casesOn a (body.rename (Ren.liftN fs.toList ρ)))

/-- A tagged value. -/
def Term.taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
    (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
    Term Sg Γ (.taggedUnion l) :=
  fields.bindArgs Ren.id fun _ as => .ret (.taggedUnion_mk l t ht as)

/-- The eliminator of a tagged union. -/
def Term.taggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
    (v : Term Sg Γ (.taggedUnion l)) (cases : TaggedUnionFoldCases Sg TyWf id Γ l τ) :
    Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.taggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a tagged union, with a default. -/
def Term.taggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema TyWf} {k : Nat} (v : Term Sg Γ (.taggedUnion l))
    (cases : TaggedUnionSomeCases Sg Γ l τ k) (dflt : Term Sg Γ τ)
    (hk : k < l.length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.taggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A value of a recursive tagged union. -/
def Term.recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l) := by ty_wf) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_tag)
    (fields : Spine Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) :
    Term Sg Γ (.recTaggedUnion l hwf) :=
  fields.bindArgs Ren.id fun _ as => .ret (.recTaggedUnion_mk l hwf t ht as)

/-- The eliminator of a recursive tagged union. -/
def Term.recTaggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ) :
    Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.recTaggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a recursive tagged union, with a default. -/
def Term.recTaggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    {k : Nat} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k)
    (dflt : Term Sg Γ τ)
    (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.recTaggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- The fold of a recursive tagged union. -/
def Term.recTaggedUnion_rec' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat := 0)
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldKCases Sg l
      (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ l τ k []) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.recTaggedUnion_rec k a (cases.rename ρ) .ret)

/-- A value of a recursive record. -/
def Term.recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs) := by ty_wf)
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) :
    Term Sg Γ (.recObject fs hwf) :=
  fields.bindArgs Ren.id fun _ as => .ret (.recObject_mk fs hwf as)

/-- The eliminator of a recursive record. -/
def Term.recObject_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.recObject_casesOn a (body.rename (Ren.liftN (TyWf.recObjectUnfold fs hwf).toList ρ)))

/-- The fold of a recursive record. -/
def Term.recObject_rec' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat := 0) (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.recObject_rec k a (body.rename (Ren.liftN (TyWf.recObjectRecBinders fs hwf τ k) ρ)) .ret)

/-- A value of a recursive newtype. -/
def Term.recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b) := by ty_wf)
    (value : Term Sg Γ (TyWf.recAliasUnfold b hwf)) : Term Sg Γ (.recAlias b hwf) :=
  value.bindAtom fun _ a => .ret (.recAlias_mk b hwf a)

/-- The eliminator of a recursive newtype. -/
def Term.recAlias_casesOn' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.recAlias_casesOn a (body.rename (Ren.lift ρ)))

/-- The fold of a recursive newtype. -/
def Term.recAlias_rec' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
    (k : Nat := 0) (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.recAlias_rec k a (body.rename (Ren.liftN (TyWf.recAliasRecBinders b hwf τ k) ρ)) .ret)

/-- A value of one member of a mutual recursive family. -/
def Term.mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f) := by ty_wf)
    (value : FamilyMemberValue Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ (.mutualRecursiveFamily f hwf) :=
  value.bindArgs fun _ as => .ret (.mutualRecursiveFamily_mk f hwf as)

/-- The eliminator of a member of a mutual family. -/
def Term.mutualRecursiveFamily_casesOn' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.mutualRecursiveFamily_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a member of a mutual family, with a
    default. -/
def Term.mutualRecursiveFamily_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (dflt : Term Sg Γ τ) : Term Sg Γ τ :=
  v.bindAtom fun ρ a =>
    (.mutualRecursiveFamily_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ))

/-- The fold of a mutual family. -/
def Term.mutualRecursiveFamily_rec' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} (k : Nat := 0)
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ τ f.members k) :
    Term Sg Γ τ :=
  v.bindAtom fun ρ a => (.mutualRecursiveFamily_rec k a (cases.rename ρ) .ret)

end LeanScript

end
