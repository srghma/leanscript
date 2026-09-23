module
public import LeanScript.ExprCtx
public meta import LeanScript.CtorTag

@[expose] public section

set_option autoImplicit false

/-!
# `Term`: the one grammar, terminating by construction

## The recursion discipline, and why four of the six kinds are unrepresentable

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | using specialized Term.natFix, arrayFix, etc |
| well-founded recursive | not supported yet |
| partial fixpoint | unrepresentable: there is no constructor for a fixpoint that does not descend |
| coinductive / inductive fixpoint | unrepresentable: `Ty` has no coinductive former and `Term` has no free fixpoint |
| `partial` | unrepresentable: same |
| `unsafe` | unrepresentable: same |

* **No `IO`, and no effect at all.**  `Ty` has no effectful former, so an `IO`-returning
  declaration has no image in this language.

* **No failure.**
  1. an exhausted recursion is not possible;
  2. an out-of-range index is not possible: a constructor is a *number with a proof* that
     the type has it, and a field is read by an eliminator that *binds* the fields of the
     constructor it matched, never by a lookup;
  3. a schema is never consulted for a default — there is no `Ty.dflt`.

* **A delay is not a memo cell.**  `Term.lazyForce (Term.lazyMk e)` runs `e`, and
  running it twice runs `e` twice: there is no memoisation.  `LeanScript.Den` makes
  `Ty.lazy` the identity on values — at this layer a delay carries nothing beyond the
  value, and the wrapper only decides what JavaScript is printed later.  `Ty.thunk`,
  which *is* memoised in JavaScript, has `Term.thunkMk` and `Term.thunkForce`: they
  denote the same identity, and the difference between the two wrappers is the code
  printed for them, not the value.  `task` and `promise` are commented out of
  `LeanPrimTyCovariant`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## Terms -/

/-
NOTE (the original sketch, kept verbatim but commented out).  It is superseded by the
`mutual` block that follows it, which is the same grammar with every `sorry` replaced by
a real type; the differences, and the constructors that are *not* expressible, are
documented there.

The `mutual` block below is work in progress: many constructors still carry `sorry`
in *type* position, some use default-argument syntax (`:= by decide`) inside a `∀`,
which the parser does not accept, and it refers to `TaggedUnionElimCases` /
`EnumElimCases`, which are never declared.  None of this elaborates, so it is
preserved here as a comment until the term language is finished.
-/
/-
mutual

inductive Term (Sg : Sig) : Ctx → Ty → Type 1
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → Term Sg Γ τ
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ σ τ}, Term Sg (σ :: Γ) τ → Term Sg Γ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap : ∀ {Γ σ τ}, Term Sg Γ (σ ⇒ τ) → Term Sg Γ σ → Term Sg Γ τ
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Term Sg Γ τ
  /-- `let x = e; body` — `x` is de Bruijn index `0` of `body`. -/
  | letE : ∀ {Γ σ τ}, Term Sg Γ σ → Term Sg (σ :: Γ) τ → Term Sg Γ τ
  -- LeanPrimTy intro
  | bool_mk : ∀ {Γ σ τ},  Bool
  | nat_mk : ∀ {Γ σ τ},  Nat
  | int_mk : ∀ {Γ σ τ},  Int
  | bitvec_mk : ∀ {Γ σ τ}, {n : Nat} (h_positive : 0 < n := by decide /- bc Unit-like types should be erased -/) -> BitVec n
  | uint8_mk : ∀ {Γ σ τ},  UInt8
  | uint16_mk : ∀ {Γ σ τ},  UInt16
  | uint32_mk : ∀ {Γ σ τ},  UInt32
  | uint64_mk : ∀ {Γ σ τ},  UInt64
  | int8_mk : ∀ {Γ σ τ},  Int8
  | int16_mk : ∀ {Γ σ τ},  Int16
  | int32_mk : ∀ {Γ σ τ},  Int32
  | int64_mk : ∀ {Γ σ τ},  Int64
  | char_mk : ∀ {Γ σ τ},  Char
  | string_mk : ∀ {Γ σ τ},  String
  | stringPos_mk s : ∀ {Γ σ τ},  String.Pos s
  | stringPosRaw_mk : ∀ {Γ σ τ},  String.Pos.Raw
  | substringRaw_mk : ∀ {Γ σ τ},  Substring.Raw
  | stringSlice_mk : ∀ {Γ σ τ},  String.Slice
  | float_mk : ∀ {Γ σ τ},  Float
  | float32_mk : ∀ {Γ σ τ},  Float32
  | floatModel_mk : ∀ {Γ σ τ},  Float.Model
  | float32Model_mk : ∀ {Γ σ τ},  Float32.Model
  -- LeanPrimTy recursors/eliminators
  /-- `if c then t else e`. -/
  | bool_rec : ∀ {Γ τ}, Term Sg Γ (.prim .bool) → Term Sg Γ τ → Term Sg Γ τ → Term Sg Γ τ
  | nat_rec : sorry -> Term -- recursor Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ) (t : Nat) : motive t
  | int_rec : sorry -> Term -- recursor Int.rec.{u} {motive : Int → Sort u} (ofNat : (a : Nat) → motive (Int.ofNat a)) (negSucc : (a : Nat) → motive (Int.negSucc a)) (t : Int) : motive t
  | bitvec_rec : sorry -> Term
  | uint8_rec : sorry -> Term
  | uint16_rec : sorry -> Term
  | uint32_rec : sorry -> Term
  | uint64_rec : sorry -> Term
  | int8_rec : sorry -> Term
  | int16_rec : sorry -> Term
  | int32_rec : sorry -> Term
  | int64_rec : sorry -> Term
  | char_rec : sorry -> Term
  | string_rec : sorry -> Term
  | stringPosRaw_rec : sorry -> Term
  | stringPos_rec : sorry -> Term
  | substringRaw_rec : sorry -> Term
  | stringSlice_rec : sorry -> Term
  | float_rec : sorry -> Term
  | float32_rec : sorry -> Term
  | floatModel_rec : sorry -> Term
  | float32Model_rec : sorry -> Term
  -- implement if makes sense. But the idea is to support `match ... with ...` using rec constructors (like bool_rec), not full recursors
  -- recursor BitVec.rec.{u} {w : Nat} {motive : BitVec w → Sort u} (ofFin : (toFin : Fin (2 ^ w)) → motive { toFin := toFin }) (t : BitVec w) : motive t
  -- recursor UInt8.rec.{u} {motive : UInt8 → Sort u} (ofBitVec : (toBitVec : BitVec 8) → motive { toBitVec := toBitVec }) (t : UInt8) : motive t
  -- recursor UInt16.rec.{u} {motive : UInt16 → Sort u} (ofBitVec : (toBitVec : BitVec 16) → motive { toBitVec := toBitVec }) (t : UInt16) : motive t
  -- recursor UInt32.rec.{u} {motive : UInt32 → Sort u} (ofBitVec : (toBitVec : BitVec 32) → motive { toBitVec := toBitVec }) (t : UInt32) : motive t
  -- recursor UInt64.rec.{u} {motive : UInt64 → Sort u} (ofBitVec : (toBitVec : BitVec 64) → motive { toBitVec := toBitVec }) (t : UInt64) : motive t
  -- recursor Int8.rec.{u} {motive : Int8 → Sort u} (ofUInt8 : (toUInt8 : UInt8) → motive { toUInt8 := toUInt8 }) (t : Int8) : motive t
  -- recursor Int16.rec.{u} {motive : Int16 → Sort u} (ofUInt16 : (toUInt16 : UInt16) → motive { toUInt16 := toUInt16 }) (t : Int16) : motive t
  -- recursor Int32.rec.{u} {motive : Int32 → Sort u} (ofUInt32 : (toUInt32 : UInt32) → motive { toUInt32 := toUInt32 }) (t : Int32) : motive t
  -- recursor Int64.rec.{u} {motive : Int64 → Sort u} (ofUInt64 : (toUInt64 : UInt64) → motive { toUInt64 := toUInt64 }) (t : Int64) : motive t
  -- recursor Char.rec.{u} {motive : Char → Sort u} (mk : (val : UInt32) → (valid : val.isValidChar) → motive { val := val, valid := valid }) (t : Char) : motive t
  -- recursor String.rec.{u} {motive : String → Sort u} (ofByteArray : (toByteArray : ByteArray) → (isValidUTF8 : toByteArray.IsValidUTF8) → motive { toByteArray := toByteArray, isValidUTF8 := isValidUTF8 }) (t : String) : motive t
  -- recursor String.Pos.Raw.rec.{u} {motive : String.Pos.Raw → Sort u} (mk : (byteIdx : Nat) → motive { byteIdx := byteIdx }) (t : String.Pos.Raw) : motive t
  -- recursor String.Pos.rec.{u} {s : String} {motive : s.Pos → Sort u} (mk : (offset : String.Pos.Raw) → (isValid : String.Pos.Raw.IsValid s offset) → motive { offset := offset, isValid := isValid }) (t : s.Pos) : motive t
  -- recursor Substring.Raw.rec.{u} {motive : Substring.Raw → Sort u} (mk : (str : String) → (startPos stopPos : String.Pos.Raw) → motive { str := str, startPos := startPos, stopPos := stopPos }) (t : Substring.Raw) : motive t
  -- recursor String.Slice.rec.{u} {motive : String.Slice → Sort u} (mk : (str : String) → (startInclusive endExclusive : str.Pos) → (startInclusive_le_endExclusive : startInclusive ≤ endExclusive) → motive { str := str, startInclusive := startInclusive, endExclusive := endExclusive, startInclusive_le_endExclusive := startInclusive_le_endExclusive }) (t : String.Slice) : motive t
  -- recursor Float.rec.{u} {motive : Float → Sort u} (ofModel : (toModel : Float.Model) → motive { toModel := toModel }) (t : Float) : motive t
  -- recursor Float32.rec.{u} {motive : Float32 → Sort u} (ofModel : (toModel : Float32.Model) → motive { toModel := toModel }) (t : Float32) : motive t
  -- recursor Float.Model.rec.{u} {motive : Float.Model → Sort u} (mk : (toBits : UInt64) → (valid : Float.Model.Format.binary64.Valid toBits.toBitVec) → motive { toBits := toBits, valid := valid }) (t : Float.Model) : motive t
  -- recursor Float32.Model.rec.{u} {motive : Float32.Model → Sort u} (mk : (toBits : UInt32) → (valid : Float.Model.Format.binary32.Valid toBits.toBitVec) → motive { toBits := toBits, valid := valid }) (t : Float32.Model) : motive t

  -- LeanPrimTyCovariant recursors/eliminators
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes once the one
      value of the unit type is erased.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazy_mk : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazy_rec : ∀ {Γ τ}, Term Sg Γ (.lazy τ) → Term Sg Γ τ
  /-- Delay a value and remember it: a `Thunk`.

      **Memoised**: the JavaScript printed for it runs the body at the first force and
      answers with the stored value afterwards.  Forcing it is `Term.thunkForce`.  At
      this layer the distinction from `Term.lazyMk` is not visible — a `Term` is a total
      Lean function of its environment, so running the body twice gives the same answer
      as running it once — and what it decides is the code that is printed. -/
  | thunk_mk : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ (.thunk τ)
  /-- Force a thunk: the value it stands for, computed at most once. -/
  | thunk_rec : ∀ {Γ τ}, Term Sg Γ (.thunk τ) → Term Sg Γ τ
  | array_mk : sorry → Term Sg Γ τ
  | array_rec : sorry → Term Sg Γ τ
  /-- A constructor of an enum: its **number**, which is what the runtime holds. -/
  | enum_mk : ∀ {Γ Ρ} (s : LeanEnumSchema), Fin s.nOfConstructors → Term Sg Γ (.enum s)
  /-- A dispatch on an enum: one branch per constructor, and no default, so it cannot
      fall off the end. -/
  | enum_rec : ∀ {Γ τ} {s : LeanEnumSchema},
      Term Sg Γ (.enum s) → EnumRecCases Sg Γ τ s.nOfConstructors → Term Sg Γ τ
  /-- A record, from its fields, in declaration order. -/
  | record_mk : ∀ {Γ Ρ} (fs : LeanRecordSchema Ty),
      Spine Sg Γ fs.toList → Term Sg Γ (.record fs)
  /-- The eliminator of a record: it **binds** every field, in declaration order, so de
      Bruijn index `0` of the body is the record's first field.  A projection is this
      node followed by a variable. -/
  | record_rec : ∀ {Γ τ} {fs : LeanRecordSchema Ty},
      Term Sg Γ (.record fs) → Term Sg (fs.toList ++ Γ) τ → Term Sg Γ τ
  /-- A tagged value: constructor `t` of the union — a number **with the proof that the
      union has it** — and exactly that constructor's fields. -/
  | taggedUnion_mk : ∀ {Γ Ρ} (l : LeanTaggedUnionSchema Ty) (t : Nat)
      (ht : t < l.toList.length),
      Spine Sg Γ (l.toList[t]'ht) → Term Sg Γ (.taggedUnion l)
  /-- The eliminator of a tagged union: one branch per constructor, each binding that
      constructor's fields, and no default. -/
  | taggedUnion_rec : ∀ {Γ τ} {l : LeanTaggedUnionSchema Ty},
      Term Sg Γ (.taggedUnion l) → TaggedUnionRecCases Sg Γ l τ → Term Sg Γ τ
  /-- **A block**: the one way a term uses labels.  Its tail is written in the *empty*
      label context, so a block is closed for jumps. -/
  | recTaggedUnion_mk : sorry → Term Sg Γ (.recTaggedUnion l)
  /-- The eliminator of a recursive tagged union: one branch per constructor, each
      binding that constructor's fields, and no default.  It takes the value **one level**
      apart; a recursion over the whole of one is `Term.fixAcc` descending at
      `Mu.size`. -/
  | recTaggedUnion_rec : sorry -> RecTaggedUnionRecCases -> Term Sg Γ τ
  | recObject_mk : sorry → Term Sg Γ (.recObject l)
  | recObject_rec : sorry -> RecTaggedUnionRecCases -> Term Sg Γ τ
  | recAlias_mk : sorry → Term Sg Γ (.recAlias l)
  | recAlias_rec : sorry -> sorry -> Term Sg Γ τ
  | mutualRecursiveFamily_mk : sorry → Term Sg Γ (.mutualRecursiveFamily l)
  | mutualRecursiveFamily_rec : sorry -> sorry -> Term Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    arguments of a jump, the arguments of a self call, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → List Ty → Type 1
  /-- No more arguments. -/
  | nil : ∀ {Γ Ρ}, Spine Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- The branches of a dispatch, one per constructor, in constructor order.  A branch
    **binds the fields** of its constructor, in declaration order, so de Bruijn index `0`
    of its body is that constructor's first field.  There is no default branch and no
    end-of-list before the constructors run out, so a dispatch is exhaustive by
    construction. -/
inductive TaggedUnionRecCases (Sg : Sig) : Ctx → LeanTaggedUnionSchema Ty → Ty → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ τ}, TaggedUnionRecCases Sg Γ sorry τ
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ fs rest τ},
      Term Sg (fs ++ Γ) τ → TaggedUnionRecCases Sg Γ rest τ → TaggedUnionElimCases Sg Γ sorry τ

/-- The branches of a dispatch on an enum: `n` of them, binding nothing. -/
inductive EnumRecCases (Sg : Sig) : Ctx → Ty → Nat → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ τ}, EnumRecCases Sg Γ τ 0
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ τ n},
      Term Sg Γ τ → EnumRecCases Sg Γ τ n → EnumElimCases Sg Γ τ (n + 1)

end
-/

/-! ## The grammar

The block below is the sketch above, made to elaborate.  Three things had to be decided
to get there.

**A literal is a literal *of its own type*.**  The sketch wrote `bool_mk : ∀ {Γ σ τ}, Bool`,
which says nothing about the term being built.  Here every introduction form ends in the
type it introduces: `bool_mk : Bool → Term Sg Γ (.prim .bool)`, and likewise for each leaf
of `LeanScript.LeanPrimTy`.  `bitvec_mk` carries the width's positivity proof, defaulted
by `by decide`, because `LeanPrimTy.bitvec` carries it; `stringPos_mk` carries the string
the position is into, because `LeanPrimTy.stringPos` is indexed by it.

**A `_casesOn` is a `match`; a `_rec` really is a recursor.**  The name of an eliminator
now says which of the two it is.

* `xxx_casesOn` is the *case analysis* of `xxx` — its `Xxx.casesOn`, with the fields of
  the matched constructor **bound** in the branch, no motive and no recursive value.
  So `nat_casesOn` has a zero branch and a successor branch binding the predecessor,
  `int_casesOn` has an `ofNat` branch and a `negSucc` branch each binding a `nat`, and
  the wrapper types (`uint8`, …, `int64`, `char`, `float`, `float32`, `floatModel`,
  `float32Model`, `stringPosRaw`, `stringPos`, `substringRaw`) each have the one branch
  that binds their representation, with the proof fields erased — they are propositions,
  so they carry nothing at runtime.
* `xxx_rec` is `Xxx.rec` with a **non-dependent motive**: a fold.  Its branch is given
  the value of the recursion on the smaller value, so it is not a call the branch can
  make on anything it likes, and a term is still terminating by construction.  Only the
  two recursive types of the language have one: `nat_rec` (`Nat.rec`) and `array_rec`
  (the fold of a list, `List.rec`).  For every other type here `Xxx.rec` and
  `Xxx.casesOn` are the same eliminator — the type is not recursive — and only the
  `_casesOn` name is given, since that is the one that describes what the constructor
  does.

Forcing a delay is not an eliminator of an inductive type at all — `Ty.lazy` is an erased
unit function and `Ty.thunk` is a `Thunk`, whose eliminator is `Thunk.get` — so the two
are called `lazy_force` and `thunk_force` rather than `_rec`.

**Three eliminators are deliberately absent**, because their fields have no type in this
language:

* `bitvec_casesOn` would bind a `Fin (2 ^ w)`, and `Fin` is not a `LeanPrimTy`;
* `string_casesOn` would bind a `ByteArray`, which is commented out of `LeanPrimTy` (a
  string is a leaf here, taken apart by the runtime operations rather than by a `match`);
* `stringSlice_casesOn` would bind two `String.Pos s` where `s` is the string bound by
  the *same* branch, and `Ctx` is a list of types, so it cannot express a binding whose
  type mentions an earlier binding of the same branch.

**The branches of a dispatch follow the *schema*, not a list.**  `TaggedUnionCases` is
indexed by the `LeanTaggedUnionSchema Ty` itself, so its constructors mirror that
schema's: `payloadFirst` wants the branch of constructor `0` (binding its fields), the
branch of the constructor that must follow it, and `TaggedUnionCasesRest` for the rest;
`skip` wants the branch of the field-less constructor `0` and then
`CtorsWithPayloadCases`, which mirrors `CtorsWithPayload` in the same way.  Nothing has
to be said about `toList` to write or to take apart a dispatch.  `EnumCases` is indexed
by the `LeanEnumSchema` itself in the same way: `three` is the branches of the three
constructors an enum has at minimum, and `cons` is one more branch for one more
constructor.

**A dispatch may name only some constructors, if it has a default.**
`enum_casesOnWithDefault` and `taggedUnion_casesOnWithDefault` take a *list* of branches
(`EnumSomeCases`, `TaggedUnionSomeCases`) — each naming its constructor by number, and,
for a union, binding that constructor's fields — plus the default branch every
unnamed constructor takes.  The term is still total: the default covers everything the
list leaves out.

Both lists are moreover **validated by their type**: `EnumSomeCases` and
`TaggedUnionSomeCases` each carry the smallest constructor number a branch may still
name, so the numbers strictly increase — they are in order and none is named twice —
and neither list has an empty case, so at least one constructor is named.

The four recursive shapes of `Ty` — `recTaggedUnion`, `recObject`, `recAlias` and
`mutualRecursiveFamily` — are left commented out at the end of the block, as asked.
-/

mutual

/-- A term of the language: a typed tree, in a context `Γ` of the types in scope and
    against the signature `Sg` of the module's top-level declarations.  It is total by
    construction — it has no fixpoint constructor, no effect and no partial operation. -/
inductive Term (Sg : Sig) : Ctx → Ty → Type 1
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ τ}, Γ ∋ τ → Term Sg Γ τ
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ σ τ}, Term Sg (σ :: Γ) τ → Term Sg Γ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap : ∀ {Γ σ τ}, Term Sg Γ (σ ⇒ τ) → Term Sg Γ σ → Term Sg Γ τ
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Term Sg Γ τ
  /-- `let x = e; body` — `x` is de Bruijn index `0` of `body`. -/
  | letE : ∀ {Γ σ τ}, Term Sg Γ σ → Term Sg (σ :: Γ) τ → Term Sg Γ τ
  -- LeanPrimTy intro
  /-- A boolean literal. -/
  | bool_mk : ∀ {Γ}, Bool → Term Sg Γ (.prim .bool)
  /-- A natural number literal. -/
  | nat_mk : ∀ {Γ}, Nat → Term Sg Γ (.prim .nat)
  /-- An integer literal. -/
  | int_mk : ∀ {Γ}, Int → Term Sg Γ (.prim .int)
  /-- A bit-vector literal.  The width is positive, because `BitVec 0` is a unit type and
      unit types are erased. -/
  | bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by decide) (v : BitVec n) :
      Term Sg Γ (.prim (.bitvec n h_positive))
  /-- An 8-bit unsigned literal. -/
  | uint8_mk : ∀ {Γ}, UInt8 → Term Sg Γ (.prim .uint8)
  /-- A 16-bit unsigned literal. -/
  | uint16_mk : ∀ {Γ}, UInt16 → Term Sg Γ (.prim .uint16)
  /-- A 32-bit unsigned literal. -/
  | uint32_mk : ∀ {Γ}, UInt32 → Term Sg Γ (.prim .uint32)
  /-- A 64-bit unsigned literal. -/
  | uint64_mk : ∀ {Γ}, UInt64 → Term Sg Γ (.prim .uint64)
  /-- An 8-bit signed literal. -/
  | int8_mk : ∀ {Γ}, Int8 → Term Sg Γ (.prim .int8)
  /-- A 16-bit signed literal. -/
  | int16_mk : ∀ {Γ}, Int16 → Term Sg Γ (.prim .int16)
  /-- A 32-bit signed literal. -/
  | int32_mk : ∀ {Γ}, Int32 → Term Sg Γ (.prim .int32)
  /-- A 64-bit signed literal. -/
  | int64_mk : ∀ {Γ}, Int64 → Term Sg Γ (.prim .int64)
  /-- A character literal. -/
  | char_mk : ∀ {Γ}, Char → Term Sg Γ (.prim .char)
  /-- A string literal. -/
  | string_mk : ∀ {Γ}, String → Term Sg Γ (.prim .string)
  /-- A literal position **into the string `s`**: the type of a checked position names
      the string it is into, so the string is part of the type. -/
  | stringPos_mk : ∀ {Γ} (s : String), String.Pos s → Term Sg Γ (.prim (.stringPos s))
  /-- A literal unchecked byte position. -/
  | stringPosRaw_mk : ∀ {Γ}, String.Pos.Raw → Term Sg Γ (.prim .stringPosRaw)
  /-- A literal unchecked substring. -/
  | substringRaw_mk : ∀ {Γ}, Substring.Raw → Term Sg Γ (.prim .substringRaw)
  /-- A literal string slice. -/
  | stringSlice_mk : ∀ {Γ}, String.Slice → Term Sg Γ (.prim .stringSlice)
  /-- A 64-bit floating point literal. -/
  | float_mk : ∀ {Γ}, Float → Term Sg Γ (.prim .float)
  /-- A 32-bit floating point literal. -/
  | float32_mk : ∀ {Γ}, Float32 → Term Sg Γ (.prim .float32)
  /-- A literal of the model of a 64-bit float: its bits, with their validity. -/
  | floatModel_mk : ∀ {Γ}, Float.Model → Term Sg Γ (.prim .floatModel)
  /-- A literal of the model of a 32-bit float: its bits, with their validity. -/
  | float32Model_mk : ∀ {Γ}, Float32.Model → Term Sg Γ (.prim .float32Model)
  -- LeanPrimTy recursors/eliminators
  /-- `if c then t else e`. -/
  | bool_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .bool) → Term Sg Γ τ → Term Sg Γ τ → Term Sg Γ τ
  /-- `match n with | 0 => … | k + 1 => …`: the successor branch **binds** the
      predecessor as de Bruijn index `0`.  There is no recursive value — this is
      `Nat.casesOn`, and the fold is `Term.nat_rec`. -/
  | nat_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .nat) →
      Term Sg Γ τ → Term Sg (Ty.prim .nat :: Γ) τ → Term Sg Γ τ
  /-- `Nat.rec` with a non-dependent motive: a fold over a natural number.  The
      successor branch **binds** the predecessor as de Bruijn index `0` and the value
      the fold gives for it as de Bruijn index `1` — the two arguments of `Nat.rec`'s
      successor branch, in order.

      It is terminating by construction: the branch is *given* the value at the
      predecessor, so there is no call it could make on anything larger. -/
  | nat_rec : ∀ {Γ τ}, Term Sg Γ (.prim .nat) →
      Term Sg Γ τ → Term Sg (Ty.prim .nat :: τ :: Γ) τ → Term Sg Γ τ
  /-- `match i with | .ofNat n => … | .negSucc n => …`: each branch binds its `nat`. -/
  | int_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .int) →
      Term Sg (Ty.prim .nat :: Γ) τ → Term Sg (Ty.prim .nat :: Γ) τ → Term Sg Γ τ
  /-- Take an 8-bit unsigned value apart: its branch binds the bit vector. -/
  | uint8_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .uint8) →
      Term Sg (Ty.prim (.bitvec 8) :: Γ) τ → Term Sg Γ τ
  /-- Take a 16-bit unsigned value apart: its branch binds the bit vector. -/
  | uint16_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .uint16) →
      Term Sg (Ty.prim (.bitvec 16) :: Γ) τ → Term Sg Γ τ
  /-- Take a 32-bit unsigned value apart: its branch binds the bit vector. -/
  | uint32_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .uint32) →
      Term Sg (Ty.prim (.bitvec 32) :: Γ) τ → Term Sg Γ τ
  /-- Take a 64-bit unsigned value apart: its branch binds the bit vector. -/
  | uint64_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .uint64) →
      Term Sg (Ty.prim (.bitvec 64) :: Γ) τ → Term Sg Γ τ
  /-- Take an 8-bit signed value apart: its branch binds the unsigned value. -/
  | int8_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .int8) →
      Term Sg (Ty.prim .uint8 :: Γ) τ → Term Sg Γ τ
  /-- Take a 16-bit signed value apart: its branch binds the unsigned value. -/
  | int16_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .int16) →
      Term Sg (Ty.prim .uint16 :: Γ) τ → Term Sg Γ τ
  /-- Take a 32-bit signed value apart: its branch binds the unsigned value. -/
  | int32_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .int32) →
      Term Sg (Ty.prim .uint32 :: Γ) τ → Term Sg Γ τ
  /-- Take a 64-bit signed value apart: its branch binds the unsigned value. -/
  | int64_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .int64) →
      Term Sg (Ty.prim .uint64 :: Γ) τ → Term Sg Γ τ
  /-- Take a character apart: its branch binds the code point, a `uint32`.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | char_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .char) →
      Term Sg (Ty.prim .uint32 :: Γ) τ → Term Sg Γ τ
  /-- Take an unchecked position apart: its branch binds the byte index. -/
  | stringPosRaw_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .stringPosRaw) →
      Term Sg (Ty.prim .nat :: Γ) τ → Term Sg Γ τ
  /-- Take a checked position apart: its branch binds the unchecked one.  The proof that
      it is valid is a proposition, so it is erased and is not bound. -/
  | stringPos_casesOn : ∀ {Γ τ} {s : String}, Term Sg Γ (.prim (.stringPos s)) →
      Term Sg (Ty.prim .stringPosRaw :: Γ) τ → Term Sg Γ τ
  /-- Take an unchecked substring apart: its branch binds the string and the two
      positions, in declaration order. -/
  | substringRaw_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .substringRaw) →
      Term Sg (Ty.prim .string :: Ty.prim .stringPosRaw :: Ty.prim .stringPosRaw :: Γ) τ →
      Term Sg Γ τ
  /-- Take a 64-bit float apart: its branch binds its model. -/
  | float_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .float) →
      Term Sg (Ty.prim .floatModel :: Γ) τ → Term Sg Γ τ
  /-- Take a 32-bit float apart: its branch binds its model. -/
  | float32_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .float32) →
      Term Sg (Ty.prim .float32Model :: Γ) τ → Term Sg Γ τ
  /-- Take the model of a 64-bit float apart: its branch binds its bits.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | floatModel_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .floatModel) →
      Term Sg (Ty.prim .uint64 :: Γ) τ → Term Sg Γ τ
  /-- Take the model of a 32-bit float apart: its branch binds its bits.  The validity
      field is a proposition, so it is erased and is not bound. -/
  | float32Model_casesOn : ∀ {Γ τ}, Term Sg Γ (.prim .float32Model) →
      Term Sg (Ty.prim .uint32 :: Γ) τ → Term Sg Γ τ
  -- `bitvec_casesOn`, `string_casesOn` and `stringSlice_casesOn` are not here: see this
  -- section's header for why their fields have no type in this language.
  -- LeanPrimTyCovariant intro and elimination
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes once the one
      value of the unit type is erased.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazy_mk : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazy_force : ∀ {Γ τ}, Term Sg Γ (.lazy τ) → Term Sg Γ τ
  /-- Delay a value and remember it: a `Thunk`.

      **Memoised**: the JavaScript printed for it runs the body at the first force and
      answers with the stored value afterwards.  Forcing it is `Term.thunk_force`.  At
      this layer the distinction from `Term.lazy_mk` is not visible — a `Term` is a total
      Lean function of its environment, so running the body twice gives the same answer
      as running it once — and what it decides is the code that is printed. -/
  | thunk_mk : ∀ {Γ τ}, Term Sg Γ τ → Term Sg Γ (.thunk τ)
  /-- Force a thunk: the value it stands for, computed at most once. -/
  | thunk_force : ∀ {Γ τ}, Term Sg Γ (.thunk τ) → Term Sg Γ τ
  /-- An array, from its elements, in order. -/
  | array_mk : ∀ {Γ τ}, Terms Sg Γ τ → Term Sg Γ (.array τ)
  /-- Take an array apart: an empty branch, and a non-empty branch that **binds** the
      first element and the rest of the array, in that order.  This is the case
      analysis — the branch gets the rest of the array, not the value of a fold over
      it; that is `Term.array_rec`. -/
  | array_casesOn : ∀ {Γ σ τ}, Term Sg Γ (.array σ) →
      Term Sg Γ τ → Term Sg (σ :: Ty.array σ :: Γ) τ → Term Sg Γ τ
  /-- The fold of an array, `List.rec` with a non-dependent motive: an empty branch, and
      a non-empty branch that **binds** the first element, the rest of the array, and
      the value of the fold over that rest, in that order — so the head is de Bruijn
      index `0`, the tail index `1` and the recursive value index `2`.

      As with `Term.nat_rec`, the recursive value is given rather than called, so a term
      is still terminating by construction. -/
  | array_rec : ∀ {Γ σ τ}, Term Sg Γ (.array σ) →
      Term Sg Γ τ → Term Sg (σ :: Ty.array σ :: τ :: Γ) τ → Term Sg Γ τ
  /-- A constructor of an enum: its **number**, which is what the runtime holds. -/
  | enum_mk : ∀ {Γ} (s : LeanEnumSchema), Fin s.nOfConstructors → Term Sg Γ (.enum s)
  /-- A dispatch on an enum: one branch per constructor, and no default, so it cannot
      fall off the end. -/
  | enum_casesOn : ∀ {Γ τ} {s : LeanEnumSchema},
      Term Sg Γ (.enum s) → EnumCases Sg Γ τ s → Term Sg Γ τ
  /-- A dispatch on an enum that branches on **some** of the constructors and sends the
      rest to a default branch.  The branches are given as a list of
      (constructor number, branch) pairs, in the order they are tried, and the last
      argument is the default.  Nothing is missing — the default catches every
      constructor that has no branch — so this is still total.

      The branches name their constructors in **strictly increasing** order and there is
      at least one of them, so no constructor can be named twice and the form is not a
      roundabout way of writing its own default. -/
  | enum_casesOnWithDefault : ∀ {Γ τ} {s : LeanEnumSchema},
      Term Sg Γ (.enum s) → EnumSomeCases Sg Γ τ s.nOfConstructors →
      Term Sg Γ τ → Term Sg Γ τ
  /-- A record, from its fields, in declaration order. -/
  | record_mk : ∀ {Γ} (fs : LeanRecordSchema Ty),
      Spine Sg Γ fs.toList → Term Sg Γ (.record fs)
  /-- The eliminator of a record: it **binds** every field, in declaration order, so de
      Bruijn index `0` of the body is the record's first field.  A projection is this
      node followed by a variable. -/
  | record_casesOn : ∀ {Γ τ} {fs : LeanRecordSchema Ty},
      Term Sg Γ (.record fs) → Term Sg (fs.toList ++ Γ) τ → Term Sg Γ τ
  /-- A tagged value: constructor `t` of the union — a number **with the proof that the
      union has it** — and exactly that constructor's fields.

      The bound is against `LeanTaggedUnionSchema.length`, the number of constructors,
      and it is written by `ctor_tag` unless one is given, so a concrete tag needs
      nothing written by hand. -/
  | taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema Ty) (t : Nat)
      (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
      Term Sg Γ (.taggedUnion l)
  /-- The eliminator of a tagged union: one branch per constructor, each binding that
      constructor's fields, and no default. -/
  | taggedUnion_casesOn : ∀ {Γ τ} {l : LeanTaggedUnionSchema Ty},
      Term Sg Γ (.taggedUnion l) → TaggedUnionCases Sg Γ l τ → Term Sg Γ τ
  /-- A dispatch on a tagged union that branches on **some** of the constructors and
      sends the rest to a default branch.  A branch names its constructor by number —
      with the same `t < l.length` bound, written by `ctor_tag` — and binds that
      constructor's fields; the last argument is the default.  Every constructor without
      a branch goes to the default, so this is still total.

      The branches name their constructors in **strictly increasing** order and there is
      at least one of them, so no constructor can be named twice and the form is not a
      roundabout way of writing its own default. -/
  | taggedUnion_casesOnWithDefault : ∀ {Γ τ} {l : LeanTaggedUnionSchema Ty},
      Term Sg Γ (.taggedUnion l) → TaggedUnionSomeCases Sg Γ l τ →
      Term Sg Γ τ → Term Sg Γ τ
  -- The four recursive shapes of `Ty` are left out on purpose, as asked:
  --
  -- | recTaggedUnion_mk : sorry → Term Sg Γ (.recTaggedUnion l)
  -- | recTaggedUnion_rec : sorry -> RecTaggedUnionRecCases -> Term Sg Γ τ
  -- | recObject_mk : sorry → Term Sg Γ (.recObject l)
  -- | recObject_rec : sorry -> RecTaggedUnionRecCases -> Term Sg Γ τ
  -- | recAlias_mk : sorry → Term Sg Γ (.recAlias l)
  -- | recAlias_rec : sorry -> sorry -> Term Sg Γ τ
  -- | mutualRecursiveFamily_mk : sorry → Term Sg Γ (.mutualRecursiveFamily l)
  -- | mutualRecursiveFamily_rec : sorry -> sorry -> Term Sg Γ τ
  --
  -- A value of one of them is a value of the shape the binder holds with the binder's
  -- occurrences (`Ty.self`, `Ty.familyMember i`) instantiated to the binder itself, so an
  -- introduction form for one needs the *unfolding* of a `Ty`, which is a substitution on
  -- trees this module does not have yet.

/-- The elements of an array: any number of terms, all of one type. -/
inductive Terms (Sg : Sig) : Ctx → Ty → Type 1
  /-- No more elements. -/
  | nil : ∀ {Γ τ}, Terms Sg Γ τ
  /-- One more element, at the front. -/
  | cons : ∀ {Γ τ}, Term Sg Γ τ → Terms Sg Γ τ → Terms Sg Γ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    arguments of a jump, the arguments of a self call, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → List Ty → Type 1
  /-- No more arguments. -/
  | nil : ∀ {Γ}, Spine Sg Γ []
  /-- One more argument. -/
  | cons : ∀ {Γ σ σs}, Term Sg Γ σ → Spine Sg Γ σs → Spine Sg Γ (σ :: σs)

/-- The branches of a dispatch on a tagged union: one per constructor, in constructor
    order, **indexed by the schema itself** rather than by the list of constructors it
    denotes.  So the family has the same shape as `LeanScript.LeanTaggedUnionSchema`: a
    schema whose first constructor carries fields wants that constructor's branch, the
    branch of the constructor that must follow it, and then the branches of the rest;
    a schema that starts with field-less constructors wants a branch for each of them,
    through `LeanScript.CtorsWithPayloadCases`.

    A branch **binds the fields** of its constructor, in declaration order, so de Bruijn
    index `0` of its body is that constructor's first field.  There is no default branch
    and no end-of-list before the constructors run out, so a dispatch is exhaustive by
    construction. -/
inductive TaggedUnionCases (Sg : Sig) : Ctx → LeanTaggedUnionSchema Ty → Ty → Type 1
  /-- The branch of constructor `0` (which carries fields, so it binds them), the branch
      of the constructor after it, and the branches of the remaining constructors. -/
  | payloadFirst : ∀ {Γ τ} {fields : NonEmptyList Ty} {next : List Ty}
      {rest : List (List Ty)},
      Term Sg (fields.toList ++ Γ) τ → Term Sg (next ++ Γ) τ →
      TaggedUnionCasesRest Sg Γ rest τ →
      TaggedUnionCases Sg Γ (.payloadFirst fields next rest) τ
  /-- The branch of constructor `0`, which carries no fields and so binds nothing, and
      the branches of the constructors after it. -/
  | skip : ∀ {Γ τ} {rest : CtorsWithPayload Ty},
      Term Sg Γ τ → CtorsWithPayloadCases Sg Γ rest τ →
      TaggedUnionCases Sg Γ (.skip rest) τ

/-- The branches of the constructors a `LeanScript.CtorsWithPayload` holds: the tail of
    `LeanScript.TaggedUnionCases`, with the same shape as that schema. -/
inductive CtorsWithPayloadCases (Sg : Sig) : Ctx → CtorsWithPayload Ty → Ty → Type 1
  /-- The branch of the first constructor that carries fields, which binds them, and the
      branches of the constructors after it. -/
  | here : ∀ {Γ τ} {fields : NonEmptyList Ty} {rest : List (List Ty)},
      Term Sg (fields.toList ++ Γ) τ → TaggedUnionCasesRest Sg Γ rest τ →
      CtorsWithPayloadCases Sg Γ (.here fields rest) τ
  /-- The branch of a field-less constructor, which binds nothing, and the branches of
      the constructors after it. -/
  | skip : ∀ {Γ τ} {rest : CtorsWithPayload Ty},
      Term Sg Γ τ → CtorsWithPayloadCases Sg Γ rest τ →
      CtorsWithPayloadCases Sg Γ (.skip rest) τ

/-- The branches of the constructors a schema leaves unconstrained: a plain list, one
    entry per constructor still to be given a branch, each as the list of its field
    types. -/
inductive TaggedUnionCasesRest (Sg : Sig) : Ctx → List (List Ty) → Ty → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ τ}, TaggedUnionCasesRest Sg Γ [] τ
  /-- The branch of the next constructor, which binds that constructor's fields. -/
  | cons : ∀ {Γ τ} {fs : List Ty} {rest : List (List Ty)},
      Term Sg (fs ++ Γ) τ → TaggedUnionCasesRest Sg Γ rest τ →
      TaggedUnionCasesRest Sg Γ (fs :: rest) τ

/-- The branches of a dispatch on **some** of the constructors of a tagged union, used
    with a default: a list of (constructor number, branch) pairs, in the order they are
    tried.  The number carries the same `t < l.length` bound as
    `LeanScript.Term.taggedUnion_mk`, written by `ctor_tag` unless it is given, and the
    branch binds that constructor's fields.  A constructor may be left out — that is the
    point — and `LeanScript.Term.taggedUnion_casesOnWithDefault` supplies the branch it
    then takes.

    The list is **validated by its type**, exactly as `LeanScript.EnumSomeCases` is, so a
    dispatch that is not well formed cannot be written at all:

    * the constructor numbers **strictly increase**, and so are in order and no number is
      named twice: the extra index `lo` is the smallest number a branch of the list may
      still name, and the tail after the branch of `t` starts at `t + 1`;
    * there is **at least one** branch: the list ends with `last`, not with an empty
      case, so a `LeanScript.Term.taggedUnion_casesOnWithDefault` that names nothing —
      which is just its default — is unwritable.

    `lo` is an `optParam` that starts at `0`, so `TaggedUnionSomeCases Sg Γ l τ` is the
    type of a whole list; and the bound `lo ≤ t` is the last argument of each
    constructor, with `ctor_ge` as its default, so a list of concrete numbers needs
    nothing written by hand. -/
inductive TaggedUnionSomeCases (Sg : Sig) :
    Ctx → LeanTaggedUnionSchema Ty → Ty → optParam Nat 0 → Type 1
  /-- The last branch: the constructor of number `t`, whose fields it binds, and no
      constructor after it has a branch. -/
  | last {Γ : Ctx} {l : LeanTaggedUnionSchema Ty} {τ : Ty} {lo : Nat} (t : Nat)
      (ht : t < l.length := by ctor_tag) (branch : Term Sg (l.get t ht ++ Γ) τ)
      (hi : lo ≤ t := by ctor_ge) : TaggedUnionSomeCases Sg Γ l τ lo
  /-- One more branch, for constructor `t`, binding that constructor's fields; every
      branch after it names a **bigger** constructor. -/
  | cons {Γ : Ctx} {l : LeanTaggedUnionSchema Ty} {τ : Ty} {lo : Nat} (t : Nat)
      (ht : t < l.length := by ctor_tag) (branch : Term Sg (l.get t ht ++ Γ) τ)
      (rest : TaggedUnionSomeCases Sg Γ l τ (t + 1))
      (hi : lo ≤ t := by ctor_ge) : TaggedUnionSomeCases Sg Γ l τ lo

/-- The branches of a dispatch on an enum: one per constructor, in constructor order,
    binding nothing, and **indexed by the schema itself** rather than by the number of
    constructors it denotes.  So the family has the same shape as
    `LeanScript.LeanEnumSchema`: an enum has three constructors at minimum, which is the
    base case `three`, and one more branch for each constructor beyond them.

    There is no end-of-list before the constructors run out and no default, so a
    dispatch is exhaustive by construction. -/
inductive EnumCases (Sg : Sig) : Ctx → Ty → LeanEnumSchema → Type 1
  /-- The branches of the three constructors an enum has at minimum, in constructor
      order. -/
  | three : ∀ {Γ τ} {shift : Int},
      Term Sg Γ τ → Term Sg Γ τ → Term Sg Γ τ → EnumCases Sg Γ τ ⟨0, shift⟩
  /-- The branch of the first constructor, and the branches of the ones after it — one
      constructor beyond the schema of the rest. -/
  | cons : ∀ {Γ τ} {extra : Nat} {shift : Int},
      Term Sg Γ τ → EnumCases Sg Γ τ ⟨extra, shift⟩ →
      EnumCases Sg Γ τ ⟨extra + 1, shift⟩

/-- The branches of a dispatch on **some** of the `n` constructors of an enum, used with
    a default: (constructor number, branch) pairs.  A constructor may be left out — that
    is the point — and `LeanScript.Term.enum_casesOnWithDefault` supplies the branch it
    then takes.

    The list is **validated by its type**, so a dispatch that is not well formed cannot
    be written at all:

    * the constructor numbers **strictly increase**, and so are in order and no number
      is named twice: the extra index `lo` is the smallest number a branch of the list
      may still name, and the tail after the branch of `i` starts at `i + 1`;
    * there is **at least one** branch: the list ends with `last`, not with an empty
      case, so a `LeanScript.Term.enum_casesOnWithDefault` that names nothing — which is
      just its default — is unwritable.

    `lo` is an `optParam` that starts at `0`, so `EnumSomeCases Sg Γ τ n` is the type of
    a whole list; and the bound `lo ≤ i` is the last argument of each constructor, with
    `ctor_ge` as its default, so a list of concrete numbers needs nothing written by
    hand. -/
inductive EnumSomeCases (Sg : Sig) : Ctx → Ty → Nat → optParam Nat 0 → Type 1
  /-- The last branch: the constructor of this number, and no constructor after it has a
      branch. -/
  | last {Γ : Ctx} {τ : Ty} {n lo : Nat} (i : Fin n) (branch : Term Sg Γ τ)
      (hi : lo ≤ i.val := by ctor_ge) : EnumSomeCases Sg Γ τ n lo
  /-- One more branch, for the constructor of this number; every branch after it names a
      **bigger** number. -/
  | cons {Γ : Ctx} {τ : Ty} {n lo : Nat} (i : Fin n) (branch : Term Sg Γ τ)
      (rest : EnumSomeCases Sg Γ τ n (i.val + 1))
      (hi : lo ≤ i.val := by ctor_ge) : EnumSomeCases Sg Γ τ n lo

end

end LeanScript

end
