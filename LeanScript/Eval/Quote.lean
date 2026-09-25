module

public import Lean.ToExpr
public import LeanScript.Expr.Term
public import LeanScript.Eval.Extern

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# Writing a computed value back as a term

An extern called on values is a redex when its result type is `LeanScript.TyWf.quotable`
(`LeanScript.Expr.Quotable`) — when it holds no function: the translation computes the
value where the term is written and writes the value instead of the call.  `Ty.quote` is
the half of that which reads a value of the language: it describes the term that denotes
the value as a `LeanScript.Quoted`, a small tree whose leaves are the payloads of literals
as `Lean.Expr`s.  The translation runs it (compiled) on the value of the call and builds
the term from the tree.

A value is read through the container its type describes (`LeanScript.Ty.toPFunctor`):
`Ty.quoteIn t a k` reads a shape `a` of `t`, and `k` reads what sits in each of its holes
— the occurrences of the recursive binder `t` is written under.  A value of a recursive
tagged union (a `List`) is a W-tree, read node by node (`WType.elim`), each node's holes
being its subtrees.

`Ty.quote` answers with a tree for every value of a quotable type
(`LeanScript.Extern.quote_isSome`, proved below), so the translation can always write the
value the grammar asks for.
-/

namespace LeanScript

open Lean

/-- The term that denotes a computed value, as a tree whose leaves are the payloads of
    literals. -/
inductive Quoted where
  /-- The literal constructor `ctor` of the grammar (`Term.nat_mk`, …) applied to the
      payload. -/
  | lit (ctor : Name) (payload : Expr)
  /-- A bit-vector literal of width `w` (`Term.bitvec_mk`). -/
  | bitvec (w : Nat) (payload : Expr)
  /-- A checked position into the string of the type (`Term.stringPos_mk`), by its byte
      index; its validity is proved by `decide` when the term is built. -/
  | stringPos (byteIdx : Nat)
  /-- A string slice (`Term.stringSlice_mk`): the string and the byte indices of its
      start and end; the proofs are by `decide`. -/
  | stringSlice (str : String) (start stop : Nat)
  /-- The model of a float (`Term.floatModel_mk`, or `Term.float32Model_mk` if `single`),
      by its bits; that they are canonical is proved by `decide`. -/
  | floatModel (single : Bool) (bits : Nat)
  /-- The constructor number `i` of an enum (`Term.enum_mk`). -/
  | enum (i : Nat)
  /-- An array of these elements (`Term.array_mk`). -/
  | array (elems : List Quoted)
  /-- A delay of this value: a lazy value (`Term.lazy_mk`) if `lazy`, a thunk
      (`Term.thunk_mk`) otherwise. -/
  | delay (lazy : Bool) (value : Quoted)
  /-- Constructor number `t` with these fields: a record (`Term.record_mk`, and `t = 0`), a
      tagged value (`Term.taggedUnion_mk`) or a value of a recursive tagged union
      (`Term.recTaggedUnion_mk`), by the type it is written at. -/
  | ctor (t : Nat) (fields : List Quoted)
  deriving Inhabited

/-- A byte position, as an expression. -/
def quotePosRaw (p : String.Pos.Raw) : Expr :=
  mkApp (mkConst ``String.Pos.Raw.mk) (toExpr p.byteIdx)

/-- The literal of a value of a primitive type. -/
def LeanPrimTy.quote : (p : LeanPrimTy) → p.denote → Quoted
  | .bool, v => .lit ``Term.bool_mk (toExpr v)
  | .nat, v => .lit ``Term.nat_mk (toExpr v)
  | .int, v => .lit ``Term.int_mk (toExpr v)
  | .bitvec w _, v => .bitvec w (toExpr v)
  | .uint8, v => .lit ``Term.uint8_mk (toExpr v)
  | .uint16, v => .lit ``Term.uint16_mk (toExpr v)
  | .uint32, v => .lit ``Term.uint32_mk (toExpr v)
  | .uint64, v => .lit ``Term.uint64_mk (toExpr v)
  | .int8, v => .lit ``Term.int8_mk (toExpr v)
  | .int16, v => .lit ``Term.int16_mk (toExpr v)
  | .int32, v => .lit ``Term.int32_mk (toExpr v)
  | .int64, v => .lit ``Term.int64_mk (toExpr v)
  | .char, v => .lit ``Term.char_mk (toExpr v)
  | .string, v => .lit ``Term.string_mk (toExpr v)
  | .stringPosRaw, v => .lit ``Term.stringPosRaw_mk (quotePosRaw v)
  | .substringRaw, v => .lit ``Term.substringRaw_mk
      (mkApp3 (mkConst ``Substring.Raw.mk) (toExpr v.str) (quotePosRaw v.startPos)
        (quotePosRaw v.stopPos))
  -- a float is written by its bits, which is exact (a `NaN` keeps its payload)
  | .float, v => .lit ``Term.float_mk (mkApp (mkConst ``Float.ofBits) (toExpr v.toBits))
  | .float32, v => .lit ``Term.float32_mk (mkApp (mkConst ``Float32.ofBits) (toExpr v.toBits))
  | .stringPos _, v => .stringPos v.offset.byteIdx
  | .stringSlice, v =>
      .stringSlice v.str v.startInclusive.offset.byteIdx v.endExclusive.offset.byteIdx
  | .floatModel, v => .floatModel false v.toBits.toNat
  | .float32Model, v => .floatModel true v.toBits.toNat

/-- Read a list of shapes, each with the holes it has: `g` reads one shape, given what
    sits in its holes. -/
def Quoted.listPos {A : Type} {B : A → Type}
    (g : (x : A) → (B x → Option Quoted) → Option Quoted) :
    (xs : List A) → (PFunctor.ListPos B xs → Option Quoted) → Option (List Quoted)
  | [], _ => some []
  | x :: xs, k => do
      let q ← g x (fun h => k (.inl h))
      let qs ← Quoted.listPos g xs (fun h => k (.inr h))
      pure (q :: qs)

mutual

/-- The term that denotes the shape `a` of the tree `t`, where `k` gives the term of what
    sits in each hole of the shape (an occurrence `Ty.self` of the binder `t` is written
    under); `none` if the shape holds a function. -/
def Ty.quoteIn : (t : Ty) → (a : (Ty.toPFunctor t).A) →
    ((Ty.toPFunctor t).B a → Option Quoted) → Option Quoted
  | .self, _, k => k PUnit.unit
  | .familyMember _, a, _ => PEmpty.elim a
  | .shape s, a, k => Ty.quoteInShape s a k
  | .recTaggedUnion l, w, _ =>
      WType.elim (Option Quoted)
        (fun p => (Ty.quoteInAt l p.1.1.val p.1.2 p.2).map (Quoted.ctor p.1.1.val)) w
  | .recObject _, a, _ => PEmpty.elim a
  | .recAlias _, a, _ => PEmpty.elim a
  | .mutualRecursiveFamily _, a, _ => PEmpty.elim a

/-- `Ty.quoteIn`, on a node. -/
def Ty.quoteInShape : (s : TyShape Ty) → (a : (Ty.toPFunctorShape s).A) →
    ((Ty.toPFunctorShape s).B a → Option Quoted) → Option Quoted
  | .prim p, v, _ => some (p.quote v)
  | .fn _ _, _, _ => none
  | .primCovariant c, a, k => Ty.quoteInCov c a k
  | .enum _, v, _ => some (.enum v.val)
  | .record fs, a, k => (Ty.quoteInRecord fs a k).map (Quoted.ctor 0)
  | .taggedUnion l, a, k => (Ty.quoteInAt l a.1.val a.2 k).map (Quoted.ctor a.1.val)

/-- `Ty.quoteIn`, on an array, a thunk or a lazy value. -/
def Ty.quoteInCov : (c : LeanPrimTyCovariant Ty) → (a : (Ty.toPFunctorCov c).A) →
    ((Ty.toPFunctorCov c).B a → Option Quoted) → Option Quoted
  | .array t, xs, k =>
      (Quoted.listPos (fun x k' => Ty.quoteIn t x k') xs.toList k).map Quoted.array
  | .thunk t, a, k => (Ty.quoteIn t a k).map (Quoted.delay false)
  | .lazy t, a, k => (Ty.quoteIn t a k).map (Quoted.delay true)

/-- `Ty.quoteIn`, on the values of a list of types: one term each. -/
def Ty.quoteInList : (ts : List Ty) → (a : (Ty.toPFunctorList ts).A) →
    ((Ty.toPFunctorList ts).B a → Option Quoted) → Option (List Quoted)
  | [], _, _ => some []
  | t :: ts, a, k => do
      let q ← Ty.quoteIn t a.1 (fun h => k (.inl h))
      let qs ← Ty.quoteInList ts a.2 (fun h => k (.inr h))
      pure (q :: qs)

/-- `Ty.quoteInList`, on a non-empty list. -/
def Ty.quoteInNE : (xs : NonEmptyList Ty) → (a : (Ty.toPFunctorNE xs).A) →
    ((Ty.toPFunctorNE xs).B a → Option Quoted) → Option (List Quoted)
  | ⟨t, ts⟩, a, k => do
      let q ← Ty.quoteIn t a.1 (fun h => k (.inl h))
      let qs ← Ty.quoteInList ts a.2 (fun h => k (.inr h))
      pure (q :: qs)

/-- `Ty.quoteInList`, on the fields of a record. -/
def Ty.quoteInRecord : (fs : LeanRecordSchema Ty) → (a : (Ty.toPFunctorRecord fs).A) →
    ((Ty.toPFunctorRecord fs).B a → Option Quoted) → Option (List Quoted)
  | ⟨x, y, rest⟩, a, k => do
      let qx ← Ty.quoteIn x a.1 (fun h => k (.inl h))
      let qy ← Ty.quoteIn y a.2.1 (fun h => k (.inr (.inl h)))
      let qs ← Ty.quoteInList rest a.2.2 (fun h => k (.inr (.inr h)))
      pure (qx :: qy :: qs)

/-- `Ty.quoteInList`, on the fields of constructor number `t` of a tagged union. -/
def Ty.quoteInAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    (a : (Ty.toPFunctorAt l t).A) → ((Ty.toPFunctorAt l t).B a → Option Quoted) →
    Option (List Quoted)
  | .payloadFirst fields _ _, 0, a, k => Ty.quoteInNE fields a k
  | .payloadFirst _ next _, 1, a, k => Ty.quoteInList next a k
  | .payloadFirst _ _ rest, n + 2, a, k => Ty.quoteInAtList rest n a k
  | .skip _, 0, _, _ => some []
  | .skip rest, n + 1, a, k => Ty.quoteInAtCP rest n a k

/-- `Ty.quoteInAt`, on the constructors that follow a field-less one. -/
def Ty.quoteInAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    (a : (Ty.toPFunctorAtCP c t).A) → ((Ty.toPFunctorAtCP c t).B a → Option Quoted) →
    Option (List Quoted)
  | .here fields _, 0, a, k => Ty.quoteInNE fields a k
  | .here _ rest, n + 1, a, k => Ty.quoteInAtList rest n a k
  | .skip _, 0, _, _ => some []
  | .skip rest, n + 1, a, k => Ty.quoteInAtCP rest n a k

/-- `Ty.quoteInAt`, on a plain list of constructors. -/
def Ty.quoteInAtList : (cs : List (List Ty)) → (t : Nat) →
    (a : (Ty.toPFunctorAtList cs t).A) → ((Ty.toPFunctorAtList cs t).B a → Option Quoted) →
    Option (List Quoted)
  | [], _, a, _ => PEmpty.elim a
  | fs :: _, 0, a, k => Ty.quoteInList fs a k
  | _ :: rest, n + 1, a, k => Ty.quoteInAtList rest n a k

end

/-- The term that denotes a value of the (closed) type `t`; `none` if the value holds a
    function (`Ty.quotable`). -/
def Ty.quote (t : Ty) (v : Ty.Den t) : Option Quoted := Ty.quoteIn t v (fun _ => none)

/-- The term that denotes a value of type `τ`, when `τ` is quotable (`TyWf.quotable`). -/
def TyWf.quote (τ : TyWf) (v : τ.Den) : Option Quoted := Ty.quote τ.toTy v

/-- The term that denotes the value of an extern called on values, when its result type
    is quotable. -/
def Extern.quote {τ : TyWf} (e : Extern τ) : Option Quoted :=
  TyWf.quote τ (Extern.eval e)

/-- The same, for an extern that takes a proof and whose call decides it: nothing where
    the proposition does not hold, and otherwise the term that denotes the value, if
    the result type is quotable. -/
def Extern.quoteChecked {τ : TyWf} (e : Option (Extern τ)) : Option (Option Quoted) :=
  e.map Extern.quote

/-! ## Every value of a quotable type can be written

The translation relies on this: when the grammar asks for the value of an extern on
values (its result type is `TyWf.quotable`), `Ty.quote` always has a term for it. -/

/-- What a reader of holes must satisfy: every hole has a term, where holes are allowed. -/
abbrev HolesOk {H : Type} (sf : Bool) (k : H → Option Quoted) : Prop :=
  sf = true → ∀ h, (k h).isSome

theorem holesOk_comp {H H' : Type} {sf : Bool} {k : H → Option Quoted} (f : H' → H)
    (hk : HolesOk sf k) : HolesOk sf (fun h => k (f h)) := fun hs h => hk hs (f h)

theorem Quoted.listPos_isSome {A : Type} {B : A → Type} (sf : Bool)
    (g : (x : A) → (B x → Option Quoted) → Option Quoted)
    (hg : ∀ x k, HolesOk sf k → (g x k).isSome) :
    ∀ (xs : List A) (k : PFunctor.ListPos B xs → Option Quoted), HolesOk sf k →
      (Quoted.listPos g xs k).isSome
  | [], _, _ => rfl
  | x :: xs, k, hk => by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hg x _ (holesOk_comp Sum.inl hk))
      obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.mp
        (Quoted.listPos_isSome sf g hg xs _ (holesOk_comp Sum.inr hk))
      simp [Quoted.listPos, hq, hqs]

mutual

theorem Ty.quoteIn_isSome : ∀ (sf : Bool) (t : Ty), Ty.quotableIn sf t = true →
    ∀ (a : (Ty.toPFunctor t).A) (k : (Ty.toPFunctor t).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteIn t a k).isSome
  | sf, .self, hq, _, k, hk => hk hq _
  | _, .familyMember _, _, a, _, _ => PEmpty.elim a
  | sf, .shape s, hq, a, k, hk => Ty.quoteInShape_isSome sf s hq a k hk
  | _, .recTaggedUnion l, hq, w, _, _ => by
      induction w with
      | mk p f ih =>
        show ((Ty.quoteInAt l p.1.val p.2 _).map _).isSome
        rw [Option.isSome_map]
        exact Ty.quoteInAt_isSome true l hq p.1.val p.2 _
          (fun _ h => ih h (fun _ => none) (fun _ e => PEmpty.elim e))
  | _, .recObject _, _, a, _, _ => PEmpty.elim a
  | _, .recAlias _, _, a, _, _ => PEmpty.elim a
  | _, .mutualRecursiveFamily _, _, a, _, _ => PEmpty.elim a

theorem Ty.quoteInShape_isSome : ∀ (sf : Bool) (s : TyShape Ty), Ty.quotableShape sf s = true →
    ∀ (a : (Ty.toPFunctorShape s).A) (k : (Ty.toPFunctorShape s).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInShape s a k).isSome
  | _, .prim _, _, _, _, _ => rfl
  | _, .fn _ _, hq, _, _, _ => absurd hq (by simp [Ty.quotableShape])
  | sf, .primCovariant c, hq, a, k, hk => Ty.quoteInCov_isSome sf c hq a k hk
  | _, .enum _, _, _, _, _ => rfl
  | sf, .record fs, hq, a, k, hk => by
      simp only [Ty.quoteInShape, Option.isSome_map]
      exact Ty.quoteInRecord_isSome sf fs hq a k hk
  | sf, .taggedUnion l, hq, a, k, hk => by
      simp only [Ty.quoteInShape, Option.isSome_map]
      exact Ty.quoteInAt_isSome sf l hq a.1.val a.2 k hk

theorem Ty.quoteInCov_isSome : ∀ (sf : Bool) (c : LeanPrimTyCovariant Ty),
    Ty.quotableCov sf c = true →
    ∀ (a : (Ty.toPFunctorCov c).A) (k : (Ty.toPFunctorCov c).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInCov c a k).isSome
  | sf, .array t, hq, xs, k, hk => by
      simp only [Ty.quoteInCov, Option.isSome_map]
      exact Quoted.listPos_isSome sf _ (fun x k' hk' => Ty.quoteIn_isSome sf t hq x k' hk') xs.toList k hk
  | sf, .thunk t, hq, a, k, hk => by
      simp only [Ty.quoteInCov, Option.isSome_map]
      exact Ty.quoteIn_isSome sf t hq a k hk
  | sf, .lazy t, hq, a, k, hk => by
      simp only [Ty.quoteInCov, Option.isSome_map]
      exact Ty.quoteIn_isSome sf t hq a k hk

theorem Ty.quoteInList_isSome : ∀ (sf : Bool) (ts : List Ty), Ty.quotableList sf ts = true →
    ∀ (a : (Ty.toPFunctorList ts).A) (k : (Ty.toPFunctorList ts).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInList ts a k).isSome
  | _, [], _, _, _, _ => rfl
  | sf, t :: ts, hq, a, k, hk => by
      simp only [Ty.quotableList, Bool.and_eq_true] at hq
      obtain ⟨q, hq1⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteIn_isSome sf t hq.1 a.1 _ (holesOk_comp Sum.inl hk))
      obtain ⟨qs, hq2⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteInList_isSome sf ts hq.2 a.2 _ (holesOk_comp Sum.inr hk))
      simp [Ty.quoteInList, hq1, hq2]

theorem Ty.quoteInNE_isSome : ∀ (sf : Bool) (xs : NonEmptyList Ty), Ty.quotableNE sf xs = true →
    ∀ (a : (Ty.toPFunctorNE xs).A) (k : (Ty.toPFunctorNE xs).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInNE xs a k).isSome
  | sf, ⟨t, ts⟩, hq, a, k, hk => by
      simp only [Ty.quotableNE, Bool.and_eq_true] at hq
      obtain ⟨q, hq1⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteIn_isSome sf t hq.1 a.1 _ (holesOk_comp Sum.inl hk))
      obtain ⟨qs, hq2⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteInList_isSome sf ts hq.2 a.2 _ (holesOk_comp Sum.inr hk))
      simp [Ty.quoteInNE, hq1, hq2]

theorem Ty.quoteInRecord_isSome : ∀ (sf : Bool) (fs : LeanRecordSchema Ty),
    Ty.quotableRecord sf fs = true →
    ∀ (a : (Ty.toPFunctorRecord fs).A) (k : (Ty.toPFunctorRecord fs).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInRecord fs a k).isSome
  | sf, ⟨x, y, rest⟩, hq, a, k, hk => by
      simp only [Ty.quotableRecord, Bool.and_eq_true] at hq
      obtain ⟨qx, h1⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteIn_isSome sf x hq.1.1 a.1 _ (holesOk_comp Sum.inl hk))
      obtain ⟨qy, h2⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteIn_isSome sf y hq.1.2 a.2.1 _
          (holesOk_comp (fun h => Sum.inr (Sum.inl h)) hk))
      obtain ⟨qs, h3⟩ := Option.isSome_iff_exists.mp
        (Ty.quoteInList_isSome sf rest hq.2 a.2.2 _
          (holesOk_comp (fun h => Sum.inr (Sum.inr h)) hk))
      simp [Ty.quoteInRecord, h1, h2, h3]

theorem Ty.quoteInAt_isSome : ∀ (sf : Bool) (l : LeanTaggedUnionSchema Ty),
    Ty.quotableTU sf l = true → ∀ (t : Nat)
    (a : (Ty.toPFunctorAt l t).A) (k : (Ty.toPFunctorAt l t).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInAt l t a k).isSome
  | sf, .payloadFirst fields _ _, hq, 0, a, k, hk => by
      simp only [Ty.quotableTU, Bool.and_eq_true] at hq
      exact Ty.quoteInNE_isSome sf fields hq.1.1 a k hk
  | sf, .payloadFirst _ next _, hq, 1, a, k, hk => by
      simp only [Ty.quotableTU, Bool.and_eq_true] at hq
      exact Ty.quoteInList_isSome sf next hq.1.2 a k hk
  | sf, .payloadFirst _ _ rest, hq, n + 2, a, k, hk => by
      simp only [Ty.quotableTU, Bool.and_eq_true] at hq
      exact Ty.quoteInAtList_isSome sf rest hq.2 n a k hk
  | _, .skip _, _, 0, _, _, _ => rfl
  | sf, .skip rest, hq, n + 1, a, k, hk =>
      Ty.quoteInAtCP_isSome sf rest hq n a k hk

theorem Ty.quoteInAtCP_isSome : ∀ (sf : Bool) (c : CtorsWithPayload Ty),
    Ty.quotableCP sf c = true → ∀ (t : Nat)
    (a : (Ty.toPFunctorAtCP c t).A) (k : (Ty.toPFunctorAtCP c t).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInAtCP c t a k).isSome
  | sf, .here fields _, hq, 0, a, k, hk => by
      simp only [Ty.quotableCP, Bool.and_eq_true] at hq
      exact Ty.quoteInNE_isSome sf fields hq.1 a k hk
  | sf, .here _ rest, hq, n + 1, a, k, hk => by
      simp only [Ty.quotableCP, Bool.and_eq_true] at hq
      exact Ty.quoteInAtList_isSome sf rest hq.2 n a k hk
  | _, .skip _, _, 0, _, _, _ => rfl
  | sf, .skip rest, hq, n + 1, a, k, hk =>
      Ty.quoteInAtCP_isSome sf rest hq n a k hk

theorem Ty.quoteInAtList_isSome : ∀ (sf : Bool) (cs : List (List Ty)),
    Ty.quotableCtors sf cs = true → ∀ (t : Nat)
    (a : (Ty.toPFunctorAtList cs t).A) (k : (Ty.toPFunctorAtList cs t).B a → Option Quoted),
      HolesOk sf k → (Ty.quoteInAtList cs t a k).isSome
  | _, [], _, _, a, _, _ => PEmpty.elim a
  | sf, fs :: _, hq, 0, a, k, hk => by
      simp only [Ty.quotableCtors, Bool.and_eq_true] at hq
      exact Ty.quoteInList_isSome sf fs hq.1 a k hk
  | sf, _ :: rest, hq, n + 1, a, k, hk => by
      simp only [Ty.quotableCtors, Bool.and_eq_true] at hq
      exact Ty.quoteInAtList_isSome sf rest hq.2 n a k hk

end

/-- **Every value of a quotable type has a term.** -/
theorem Ty.quote_isSome (t : Ty) (h : t.quotable = true) (v : Ty.Den t) :
    (Ty.quote t v).isSome :=
  Ty.quoteIn_isSome false t h v _ (fun hs => absurd hs Bool.false_ne_true)

/-- **The translation can always write the value the grammar asks for**: an extern on
    values whose result type is quotable has a term for its value. -/
theorem Extern.quote_isSome {τ : TyWf} (e : Extern τ) (h : TyWf.quotable τ = true) :
    (Extern.quote e).isSome :=
  Ty.quote_isSome τ.toTy h _

end LeanScript

end
