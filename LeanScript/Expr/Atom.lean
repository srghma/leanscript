module
public import LeanScript.Expr.NatRecCtx
public import LeanScript.Expr.Extern
public import LeanScript.Ty.Unfold
public import LeanScript.Ty.TyWfIn
public import LeanScript.Ty.Wf
public meta import LeanScript.CtorTag

@[expose] public section

set_option autoImplicit false

/-!
# Atoms: the operands of an A-normal term

`LeanScript.Term` is in **A-normal form by construction**: every operand of a
computation — the function and the argument of an application, the value a `casesOn` or a
fold takes apart, the arguments of an extern, the fields of a constructor, the elements of
an array — is an **atom**, never a computation.  An intermediate value is always *named*
by a `let` (`LeanScript.Term.letE`) before it is used.

An atom is a variable, a reference to a top-level declaration, or a literal of a terminal
type: evaluating it does no work, so it may be duplicated or moved freely.  This file
holds atoms and the lists of them the grammar uses; it has no term in it, so it sits
before the `mutual` block of `LeanScript.Expr.Term`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- **An atom**: an operand that needs no computation — a variable of `Γ`, a reference to
    a top-level declaration of `Sg`, or a literal of a terminal type. -/
inductive Atom (Sg : Sig) : Ctx → TyWf → Type
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → Atom Sg Γ τ
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Atom Sg Γ τ
  /-- A boolean literal. -/
  | bool_mk : ∀ {Γ}, Bool → Atom Sg Γ (.prim .bool)
  /-- A natural number literal. -/
  | nat_mk : ∀ {Γ}, Nat → Atom Sg Γ (.prim .nat)
  /-- An integer literal. -/
  | int_mk : ∀ {Γ}, Int → Atom Sg Γ (.prim .int)
  /-- A bit-vector literal.  The width is positive, because `BitVec 0` is a unit type and
      unit types are erased. -/
  | bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
      Atom Sg Γ (.prim (.bitvec n h_positive))
  /-- An 8-bit unsigned literal. -/
  | uint8_mk : ∀ {Γ}, UInt8 → Atom Sg Γ (.prim .uint8)
  /-- A 16-bit unsigned literal. -/
  | uint16_mk : ∀ {Γ}, UInt16 → Atom Sg Γ (.prim .uint16)
  /-- A 32-bit unsigned literal. -/
  | uint32_mk : ∀ {Γ}, UInt32 → Atom Sg Γ (.prim .uint32)
  /-- A 64-bit unsigned literal. -/
  | uint64_mk : ∀ {Γ}, UInt64 → Atom Sg Γ (.prim .uint64)
  /-- An 8-bit signed literal. -/
  | int8_mk : ∀ {Γ}, Int8 → Atom Sg Γ (.prim .int8)
  /-- A 16-bit signed literal. -/
  | int16_mk : ∀ {Γ}, Int16 → Atom Sg Γ (.prim .int16)
  /-- A 32-bit signed literal. -/
  | int32_mk : ∀ {Γ}, Int32 → Atom Sg Γ (.prim .int32)
  /-- A 64-bit signed literal. -/
  | int64_mk : ∀ {Γ}, Int64 → Atom Sg Γ (.prim .int64)
  /-- A character literal. -/
  | char_mk : ∀ {Γ}, Char → Atom Sg Γ (.prim .char)
  /-- A string literal. -/
  | string_mk : ∀ {Γ}, String → Atom Sg Γ (.prim .string)
  /-- A literal position **into the string `s`**: the type of a checked position names
      the string it is into, so the string is part of the type. -/
  | stringPos_mk : ∀ {Γ} (s : String), String.Pos s → Atom Sg Γ (.prim (.stringPos s))
  /-- A literal unchecked byte position. -/
  | stringPosRaw_mk : ∀ {Γ}, String.Pos.Raw → Atom Sg Γ (.prim .stringPosRaw)
  /-- A literal unchecked substring. -/
  | substringRaw_mk : ∀ {Γ}, Substring.Raw → Atom Sg Γ (.prim .substringRaw)
  /-- A literal string slice. -/
  | stringSlice_mk : ∀ {Γ}, String.Slice → Atom Sg Γ (.prim .stringSlice)
  /-- A 64-bit floating point literal. -/
  | float_mk : ∀ {Γ}, Float → Atom Sg Γ (.prim .float)
  /-- A 32-bit floating point literal. -/
  | float32_mk : ∀ {Γ}, Float32 → Atom Sg Γ (.prim .float32)
  /-- A literal of the model of a 64-bit float: its bits, with their validity. -/
  | floatModel_mk : ∀ {Γ}, Float.Model → Atom Sg Γ (.prim .floatModel)
  /-- A literal of the model of a 32-bit float: its bits, with their validity. -/
  | float32Model_mk : ∀ {Γ}, Float32.Model → Atom Sg Γ (.prim .float32Model)

/-- A list of atoms, typed by the list of their types: the arguments of an extern, the
    fields of a constructor, the base values of a fold. -/
inductive Args (Sg : Sig) : Ctx → List TyWf → Type
  /-- No more arguments. -/
  | nil : ∀ {Γ}, Args Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Atom Sg Γ σ → Args Sg Γ σs → Args Sg Γ (σ :: σs)

/-- The operands of a value of one member of a mutual recursive family: the family has the
    same three cases as `LeanScript.LeanFamMemberSchema`, and the type says which of them
    a member is.  The member it is indexed by is the **unfolded** one, so a field written
    `Ty.familyMember i` is a value of member `i`. -/
inductive FamilyMemberArgs (Sg : Sig) : Ctx → LeanFamMemberSchema TyWf → Type
  /-- A member with constructors: constructor `t` of it, and that constructor's
      fields. -/
  | ctors {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Args Sg Γ (l.get t ht)) :
      FamilyMemberArgs Sg Γ (.ctors l)
  /-- A record member: its fields, in declaration order. -/
  | record {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Args Sg Γ fs.toList) :
      FamilyMemberArgs Sg Γ (.record fs)
  /-- A newtype member: a value of its body, whose wrapper is erased. -/
  | alias {Γ : Ctx} (b : TyWf) (value : Atom Sg Γ b) : FamilyMemberArgs Sg Γ (.alias b)

/-! ## Join points -/

/-- The join points in scope, by the type of their one parameter.  A join point is a
    continuation *inside* a function body — what follows a dispatch or a fold whose value
    is used — so it answers with the type of that body, and it lives in this context of its
    own, apart from the variables (`Ctx`): it is not a value, and it can only be jumped
    to, from tail position. -/
abbrev JCtx := List TyWf

/-- **Where the answer of a fold goes.**  A fold is a tail: it is the last thing its block
    does, so its answer is either the value of the whole term (`ret`, when the fold answers
    with the term's own type), or the argument of a jump to a join point (`jump`). -/
inductive Dest : JCtx → TyWf → TyWf → Type
  /-- The answer is the value of the term. -/
  | ret : ∀ {J : JCtx} {τ : TyWf}, Dest J τ τ
  /-- The answer is passed to the join point `j`. -/
  | jump : ∀ {J : JCtx} {ρ τ : TyWf}, J ∋ ρ → Dest J ρ τ

end LeanScript

end
