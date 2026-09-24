module

/-!
# The design of `LeanScript.Term`

This module carries the prose of the grammar: why the recursion discipline is what it is,
the original sketch of the term language (kept verbatim, commented out), and the four
decisions that turned that sketch into the `mutual` block of `LeanScript.Expr.Term`.  It
declares nothing, so it costs nothing to import; the grammar itself is in
`LeanScript.Expr.Term`, and the context of `k` previous answers a fold is written in is in
`LeanScript.Expr.NatRecCtx`.
-/

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

The block below is the sketch above, made to elaborate.  Four things had to be decided
to get there.

**A term is indexed by a *type of the language*, not by a tree.**  `Ty` is a tree, and not
every tree is a type: a binder may mention itself nowhere, may mention itself in the
domain of a function, or may state an equation no value satisfies.  `Term` is therefore
indexed by `LeanScript.TyWf` — a tree **with** the proof that it is a type — and `Ctx` is a
list of those, so a tree that is not a type has no term of it at all, and the proof is
composed once where the type is written rather than checked again at each use.  A payload
written inside a binder is `LeanScript.TyWfIn n`, the same bundle for the scope the binder
opens, and the schemas of the grammar are schemas **of bundles**: the fields of a record
are a `LeanRecordSchema TyWf`, the payload of a recursive union a
`LeanTaggedUnionSchema (TyWfIn 1)`, the members of a mutual family a
`LeanMutualRecFamily (TyWfIn (n + 2))` — a family has at least two members.  The trees are
the `map` of the schema to `toTy`, so nothing is rechecked and nothing is carried twice.

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
indexed by the `LeanTaggedUnionSchema TyWf` itself, so its constructors mirror that
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

**The four recursive shapes of `Ty` have the same four forms as the others.**  A value of
`Ty.recTaggedUnion l` — and of `Ty.recObject`, `Ty.recAlias`,
`Ty.mutualRecursiveFamily` — is a value of the shape the binder holds with the binder's
own occurrences (`Ty.self`, `Ty.familyMember i`) instantiated to the binder itself, which
is the *unfolding* of `LeanScript.Ty.Unfold`.  So an introduction form takes the fields
**unfolded** (`TyWf.recTaggedUnionUnfold`, `TyWf.recObjectUnfold`, `TyWf.recAliasUnfold`),
and a `_casesOn` branches on the unfolded schema — which has the same constructors, in
the same order, as the one the binder holds, so the branch families above serve unchanged
and a dispatch is still exhaustive by construction.

Each of the four also has a `_rec`: the fold, `Xxx.rec` with a non-dependent motive.  Its
branches are `LeanScript.TaggedUnionFoldCases` (or the single branch of a record or a
newtype), which is the same family as `TaggedUnionCases` except for what a branch binds:
`LeanScript.TyWf.recBinders` binds every field, unfolded, and follows a field that *is* an
occurrence of the type being folded over by the value of the fold at that field.  As in
`nat_rec` and `array_rec` the recursive value is *given* to the branch, so a term is still
terminating by construction.  A field that mentions the type only inside another former
(an array of it, say) is bound as it is: folding it would be a map, which the grammar does
not have.

**An introduction form builds a value of a type, not of a tree.**  A `Ty` is a tree, and
not every tree is a type: a binder may mention itself nowhere, may mention itself in the
*domain* of a function — `μX. X ⇒ Nat`, at which a term language diverges — or may state
an equation no value satisfies, like `μX. Nat × X`.  `LeanScript.Ty.Wf` is the
proposition that rules all three out, and the four recursive introduction forms carry it
for the tree they build a value of, with `ty_wf` as its default, so a tree that is not a
type has no value in the grammar and nothing has to be written by hand for a schema
written out.  The eliminators do not carry it: a tree that is not a type has no value to
take apart in the first place.

The partial forms follow the same rule as elsewhere: `recTaggedUnion_casesOnWithDefault`
and `mutualRecursiveFamily_casesOnWithDefault` exist because those shapes have
constructors to leave out, while a recursive record and a recursive newtype have one
constructor each and so have no partial form at all.  A mutual family is dispatched on
member by member (`LeanScript.FamilyMemberValue`, `LeanScript.FamilyMemberCases`), and
its fold asks for the branches of **every** member (`LeanScript.FamilyFoldKCases`), with
one motive answering for all of them, and a branch of that fold may look one constructor
further down — into an occurrence of any member — as the fold of a recursive tagged union
may.
-/
