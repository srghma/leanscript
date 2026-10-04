module

public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.EnumSchema

@[expose] public section

set_option autoImplicit false

/-!
# `Ty`: closed types that name their recursive datatypes

The one grammar of types of the language (designed in `proposals/NominalTyProposal.md`).

A closed type `Ty ks` has **no binder, no hole and no grounding index**.  A recursive type is
not written inside the type: it is *declared once*, in a datatype signature
(`LeanScript.DSig`, in `LeanScript.Ty.Syntax.Decl`), and a type refers to it by its
name, `Ty.data r`, where `r : Ref ks` is a typed de Bruijn name.  `ks` lists the sizes of
the declared blocks, newest first: a block of `k + 1` mutually recursive datatypes
contributes `k` to `ks`.

Because a recursive type is a name, two occurrences of the same datatype are the same tree:
canonical forms are free, and equality of types is the derived `DecidableEq`.

What cannot be written:

* a union of fewer than two constructors (`Ctors` has at least two), or one none of whose
  constructors has fields (`UnionShape`: two points are only ever `bool`, three or more
  field-less constructors only ever an `enum`);
* a record of fewer than two fields (`Ty.record` takes a first field and at least one more);
* a constructor with an explicit `PUnit` payload (a constructor without fields is
  `Ctor.nullary`, and a union with one denotes `Option`/`Bool`, never `PUnit ⊕ _`);
* a leaf with fewer than three values other than `bool`: there is no `unit`, and the
  constructors of `LeanPrimTy` themselves refuse `BitVec 0`, `BitVec 1` (`LeanPrimTy.bitvec`
  takes a proof of `2 ≤ n`) and `String.Pos s` for `s` of fewer than two characters
  (`LeanPrimTy.stringPos` takes a proof of `2 ≤ s.length`);
* a delay inside a delay: `Ty.thunk` / `Ty.lazy` (a `Thunk τ` / `Unit → τ`, which print as a
  JavaScript thunk / `() => …`) take a `Ty ks false`, the index `false` excluding the two
  delays, so `Unit → Unit → τ`, `Unit → Thunk τ`, `Thunk (Unit → τ)` and `Thunk (Thunk τ)` are
  read with one delay (`Ty.mkThunk`, `Ty.mkLazy`; `lazy_not_in_lazy` and the other
  `…_not_in_…` theorems).

A delay denotes the value it holds (`Ty.den` of `.thunk τ` is `Ty.den` of `τ`), so it is the
one exception to *one type per set of points*: `bool`, `Thunk Bool` and `Unit → Bool` all denote
`Bool`.  The delays only matter for printing; terms evaluate them as the identity.
-/

namespace LeanScript


/-! ## Names of declared datatypes -/

/-- A reference to member `j` of one block of a signature whose block sizes are `ks`
    (newest block first, as de Bruijn indices).  A block of size `k` has `k + 1` members. -/
inductive Ref : List Nat → Type where
  /-- Member `j` of the newest block. -/
  | here {k : Nat} {ks : List Nat} (j : Fin (k + 1)) : Ref (k :: ks)
  /-- A datatype of an older block. -/
  | there {k : Nat} {ks : List Nat} : Ref ks → Ref (k :: ks)
  deriving DecidableEq, Repr, Hashable

/-- A reference to a whole block of a signature (without choosing a member). -/
inductive BRef : List Nat → Type where
  /-- The newest block. -/
  | here {k : Nat} {ks : List Nat} : BRef (k :: ks)
  /-- An older block. -/
  | there {k : Nat} {ks : List Nat} : BRef ks → BRef (k :: ks)
  deriving DecidableEq, Repr, Hashable

/-- The size `k` of a block (it has `k + 1` members). -/
def BRef.size : {ks : List Nat} → BRef ks → Nat
  | k :: _, .here => k
  | _ :: _, .there b => b.size

/-- Member `j` of a block, as a name. -/
def BRef.ref : {ks : List Nat} → (b : BRef ks) → Fin (b.size + 1) → Ref ks
  | _ :: _, .here, j => .here j
  | _ :: _, .there b, j => .there (b.ref j)

/-! ## Closed types -/

/-- The shape of a union: which of its constructors have fields.  A union must have at least
    one constructor with fields: a sum of field-less constructors is `bool` (two values) or an
    `enum` (three or more), never a union, so each finite set of points has exactly one type
    (up to the delays `thunk` / `lazy`, which denote their contents). -/
class inductive UnionShape : List Bool → Prop where
  /-- The first constructor has fields. -/
  | here {bs : List Bool} : UnionShape (true :: bs)
  /-- The first constructor has no fields; one of the others has. -/
  | there {bs : List Bool} (h : UnionShape bs) : UnionShape (false :: bs)

attribute [instance] UnionShape.here

/-- A union whose first constructor has no fields: the rest must be a union shape. -/
instance UnionShape.instThere {bs : List Bool} [h : UnionShape bs] : UnionShape (false :: bs) :=
  .there h

mutual
/-- A closed type over a signature with block sizes `ks`.

    The second index says whether the type may be a *delay* (`thunk` / `lazy`).  It is an
    optional argument: `Ty ks` is `Ty ks true`, any type.  `Ty ks false` is a type that is
    **not** a delay; it is what a delay holds, so a delay directly inside a delay cannot be
    written (`Ty.lazy_not_in_lazy`, `Ty.thunk_not_in_lazy`, `Ty.lazy_not_in_thunk`).  Every
    other constructor builds a type at either index, and its children are any type. -/
inductive Ty : List Nat → optParam Bool true → Type where
  /-- A leaf (`bool`, or a leaf with at least three values: `LeanPrimTy` has no other). -/
  | prim {ks : List Nat} {d : Bool} (p : LeanPrimTy) : Ty ks d
  /-- A function type. -/
  | fn {ks : List Nat} {d : Bool} : Ty ks → Ty ks → Ty ks d
  /-- A Lean `Array`. -/
  | array {ks : List Nat} {d : Bool} : Ty ks → Ty ks d
  /-- A Lean `List`.  A built-in type former, like `array`: a list is recursive, so it could
      not be an abbreviation of the other constructors (as `option` is); it denotes Lean's
      own `List`, the type the externs over lists (`Array.toList`, `String.toList`, …) take
      and answer. -/
  | list {ks : List Nat} {d : Bool} : Ty ks → Ty ks d
  /-- A Lean `Std.HashMap String τ`: a hash map whose keys are strings (with the `BEq` and
      `Hashable` instances of `String`).  A built-in type former, like `array`: it denotes Lean's
      own hash map (`Ty.den`), the type the externs over string-keyed hash maps
      (`StrMapExtern`: `get?`, `get!`, `contains`, `keys`, …) take and answer.  In JavaScript it
      is an object whose own properties are the keys (`Object.keys`, `Object.hasOwn`). -/
  | strMap {ks : List Nat} {d : Bool} : Ty ks → Ty ks d
  /-- A field-less sum of at least three constructors. -/
  | enum {ks : List Nat} {d : Bool} : LeanEnumSchema → Ty ks d
  /-- A record: a first field and at least one more. -/
  | record {ks : List Nat} {d : Bool} : Ty ks → Fields ks → Ty ks d
  /-- A union: at least two constructors, at least one of which has fields. -/
  | union {ks : List Nat} {d : Bool} {bs : List Bool} (cs : Ctors ks bs) [h : UnionShape bs] :
      Ty ks d
  /-- A declared (recursive) datatype, by name. -/
  | data {ks : List Nat} {d : Bool} : Ref ks → Ty ks d
  /-- A memoised delay (in JS, a thunk that caches its value).  It denotes the value it
      holds: it only matters for printing.  Its contents are not a delay. -/
  | thunk {ks : List Nat} : Ty ks false → Ty ks
  /-- A delay that is recomputed every time (in JS, `() => …`; in Lean, `Unit → τ`).  It
      denotes the value it holds: it only matters for printing.  Its contents are not a
      delay. -/
  | lazy {ks : List Nat} : Ty ks false → Ty ks
/-- One or more fields. -/
inductive Fields : List Nat → Type where
  | one {ks : List Nat} : Ty ks → Fields ks
  | cons {ks : List Nat} : Ty ks → Fields ks → Fields ks
/-- A constructor: no fields (index `false`), or one or more fields (index `true`). -/
inductive Ctor : List Nat → Bool → Type where
  | nullary {ks : List Nat} : Ctor ks false
  | fields {ks : List Nat} : Fields ks → Ctor ks true
/-- Two or more constructors; the index lists which of them have fields. -/
inductive Ctors : List Nat → List Bool → Type where
  | two {ks : List Nat} {a b : Bool} : Ctor ks a → Ctor ks b → Ctors ks [a, b]
  | cons {ks : List Nat} {a : Bool} {bs : List Bool} : Ctor ks a → Ctors ks bs → Ctors ks (a :: bs)
end

deriving instance DecidableEq for Ty, Fields, Ctor, Ctors
deriving instance Repr for Ty, Fields, Ctor, Ctors
deriving instance Hashable for Ty, Fields, Ctor, Ctors

section Instances
variable {ks : List Nat}

instance {d : Bool} : BEq (Ty ks d) := instBEqOfDecidableEq
instance : BEq (Fields ks) := instBEqOfDecidableEq
instance {b : Bool} : BEq (Ctor ks b) := instBEqOfDecidableEq
instance {bs : List Bool} : BEq (Ctors ks bs) := instBEqOfDecidableEq
instance : BEq (Ref ks) := instBEqOfDecidableEq
instance : BEq (BRef ks) := instBEqOfDecidableEq

/-! `ReflBEq`, `LawfulBEq` and `LawfulHashable` follow from the `BEq` instances above, which
    are `decide (a = b)` (`instLawfulBEqInstBEqOfDecidableEq`,
    `instLawfulHashableOfLawfulBEq`). -/

instance {d : Bool} : Inhabited (Ty ks d) := ⟨.prim .bool⟩
instance : Inhabited (Fields ks) := ⟨.one default⟩
instance : Inhabited (Ctor ks false) := ⟨.nullary⟩
instance : Inhabited (Ctor ks true) := ⟨.fields default⟩
instance {a b : Bool} [Inhabited (Ctor ks a)] [Inhabited (Ctor ks b)] :
    Inhabited (Ctors ks [a, b]) := ⟨.two default default⟩
instance {a : Bool} {bs : List Bool} [Inhabited (Ctor ks a)] [Inhabited (Ctors ks bs)] :
    Inhabited (Ctors ks (a :: bs)) := ⟨.cons default default⟩
instance {k : Nat} : Inhabited (Ref (k :: ks)) := ⟨.here 0⟩
instance {k : Nat} : Inhabited (BRef (k :: ks)) := ⟨.here⟩

example : LawfulBEq (Ty ks) := inferInstance
example {bs : List Bool} : ReflBEq (Ctors ks bs) := inferInstance
example : LawfulHashable (Ty ks) := inferInstance

end Instances

namespace Ty

/-- The pair type: a record of two fields. -/
abbrev pair {ks : List Nat} (a b : Ty ks) : Ty ks := .record a (.one b)

/-- `Bool`. -/
abbrev bool {ks : List Nat} : Ty ks := .prim .bool
/-- `Nat`. -/
abbrev nat {ks : List Nat} : Ty ks := .prim .nat
/-- `Int`. -/
abbrev int {ks : List Nat} : Ty ks := .prim .int
/-- `String`. -/
abbrev string {ks : List Nat} : Ty ks := .prim .string
/-- One component of a `Lean.Name`: a union of a string (`Name.str`) and a number
    (`Name.num`).  It denotes `String ⊕ Nat`. -/
abbrev nameComponent {ks : List Nat} : Ty ks :=
  .union (.two (.fields (.one .string)) (.fields (.one .nat)))

/-- `Lean.Name`: the list of its components, root first (`` `a.b.3 `` is `[a, b, 3]`).

    `Lean.Name` is the recursive union
    `anonymous | str (pre : Name) (s : String) | num (pre : Name) (i : Nat)`.  A closed `Ty`
    cannot write that recursion itself (a recursive type is a declared datatype, `Ty.data`,
    which only exists in a signature that declares it), but it is the built-in recursion of
    `Ty.list`: a name is a list of components.  So, like `Ty.ordering` (an `Ordering` is the
    enum `Fin 3`), it is an abbreviation of the other constructors and not a leaf of its own;
    its values are `List (String ⊕ Nat)`, converted from and to `Lean.Name` by
    `LeanScript.nameToComponents` / `LeanScript.nameOfComponents` (`LeanScript.Term.Extern.Catalogue`). -/
abbrev leanName {ks : List Nat} : Ty ks := .list nameComponent

/-- `Option t`: a union of a constructor without fields and one with the field `t`. -/
abbrev option {ks : List Nat} (t : Ty ks) : Ty ks :=
  .union (.two .nullary (.fields (.one t)))

/-- `a ⊕ b`. -/
abbrev sum {ks : List Nat} (a b : Ty ks) : Ty ks :=
  .union (.two (.fields (.one a)) (.fields (.one b)))

end Ty

/-! ## Delays

`Ty.thunk t` and `Ty.lazy t` hold a type `t : Ty ks false` that is not a delay.  A Lean type
with several delays around it (`Unit → Unit → τ`, `Thunk (Unit → τ)`, `Unit → Thunk τ`, …)
is read as **one** delay: `mkLazy` and `mkThunk` below collapse them, a `thunk` absorbing a
`lazy` (`Ty.mkLazy_mkLazy`, `Ty.mkLazy_mkThunk`, `Ty.mkThunk_mkLazy`, `Ty.mkThunk_mkThunk`). -/

namespace Ty
variable {ks : List Nat}

/-- A type that is not a delay, as a type (the same constructor, at the index `true`). -/
def relax : Ty ks false → Ty ks
  | .prim p => .prim p
  | .fn a b => .fn a b
  | .array t => .array t
  | .list t => .list t
  | .strMap t => .strMap t
  | .enum s => .enum s
  | .record t fs => .record t fs
  | .union cs (h := h) => .union cs (h := h)
  | .data r => .data r

/-- Is the type a delay (`thunk` or `lazy`)? -/
def isDelay : Ty ks → Bool
  | .thunk _ | .lazy _ => true
  | _ => false

/-- The type with its delay removed: the contents of a `thunk` / `lazy`, otherwise the type
    itself (at the index `false`). -/
def undelay : Ty ks → Ty ks false
  | .prim p => .prim p
  | .fn a b => .fn a b
  | .array t => .array t
  | .list t => .list t
  | .strMap t => .strMap t
  | .enum s => .enum s
  | .record t fs => .record t fs
  | .union cs (h := h) => .union cs (h := h)
  | .data r => .data r
  | .thunk t => t
  | .lazy t => t

/-- `Thunk t`: a `thunk` of `t` with its delay removed (a `thunk` absorbs a `lazy`). -/
def mkThunk (t : Ty ks) : Ty ks := .thunk t.undelay

/-- `Unit → t`: `t` itself if it already is a delay, otherwise a `lazy` of it. -/
def mkLazy : Ty ks → Ty ks
  | .thunk t => .thunk t
  | .lazy t => .lazy t
  | t => .lazy t.undelay

/-- A type that is not a delay is never a delay. -/
@[simp] theorem isDelay_relax (t : Ty ks false) : t.relax.isDelay = false := by
  cases t <;> rfl

@[simp] theorem undelay_relax (t : Ty ks false) : t.relax.undelay = t := by
  cases t <;> rfl

/-- A type that is not a delay is its own contents. -/
theorem relax_undelay (t : Ty ks) (h : t.isDelay = false) : t.undelay.relax = t := by
  cases t <;> first | rfl | cases h

/-- The contents of a `lazy` are never a `lazy`. -/
theorem lazy_not_in_lazy (t : Ty ks false) (u : Ty ks false) : t.relax ≠ .lazy u := by
  cases t <;> nofun

/-- The contents of a `lazy` are never a `thunk`. -/
theorem thunk_not_in_lazy (t : Ty ks false) (u : Ty ks false) : t.relax ≠ .thunk u := by
  cases t <;> nofun

/-- The contents of a `thunk` are never a `lazy`. -/
theorem lazy_not_in_thunk (t : Ty ks false) (u : Ty ks false) : t.relax ≠ .lazy u :=
  lazy_not_in_lazy t u

/-- The contents of a `thunk` are never a `thunk`. -/
theorem thunk_not_in_thunk (t : Ty ks false) (u : Ty ks false) : t.relax ≠ .thunk u :=
  thunk_not_in_lazy t u

/-- The delay a type is, if it is one: `.lazy u` or `.thunk u` is the whole type, so its
    contents `u` are not a delay. -/
theorem undelay_of_lazy {t : Ty ks} {u : Ty ks false} (h : t = .lazy u) :
    t.undelay = u ∧ u.relax.isDelay = false := by
  subst h; exact ⟨rfl, isDelay_relax u⟩

/-- `Unit → Unit → τ` is `Unit → τ`. -/
@[simp] theorem mkLazy_mkLazy (t : Ty ks) : mkLazy (mkLazy t) = mkLazy t := by
  cases t <;> rfl

/-- `Unit → Thunk τ` is `Thunk τ`. -/
@[simp] theorem mkLazy_mkThunk (t : Ty ks) : mkLazy (mkThunk t) = mkThunk t := rfl

/-- `Thunk (Unit → τ)` is `Thunk τ`. -/
@[simp] theorem mkThunk_mkLazy (t : Ty ks) : mkThunk (mkLazy t) = mkThunk t := by
  cases t <;> rfl

/-- `Thunk (Thunk τ)` is `Thunk τ`. -/
@[simp] theorem mkThunk_mkThunk (t : Ty ks) : mkThunk (mkThunk t) = mkThunk t := rfl

/-- `mkLazy` of a type that is not a delay is `lazy`. -/
@[simp] theorem mkLazy_relax (t : Ty ks false) : mkLazy t.relax = .lazy t := by
  cases t <;> rfl

/-- `mkThunk` of a type that is not a delay is `thunk`. -/
@[simp] theorem mkThunk_relax (t : Ty ks false) : mkThunk t.relax = .thunk t := by
  simp [mkThunk]

/-- The result of `mkLazy` is a delay, whose contents are not. -/
theorem isDelay_mkLazy (t : Ty ks) : (mkLazy t).isDelay = true := by
  cases t <;> rfl

/-- The result of `mkThunk` is a `thunk`. -/
theorem isDelay_mkThunk (t : Ty ks) : (mkThunk t).isDelay = true := rfl

/-- Is the type `bool`, possibly under a delay (`Bool`, `Thunk Bool`, `Unit → Bool`)?  These
    are the closed types with two values (`Ty.eq_bool_of_two_points`). -/
def isBool {d : Bool} : Ty ks d → Bool
  | .prim .bool => true
  | .thunk t => t.isBool
  | .lazy t => t.isBool
  | _ => false

theorem isBool_iff (t : Ty ks) :
    t.isBool = true ↔ t = .bool ∨ t = .thunk (.prim .bool) ∨ t = .lazy (.prim .bool) := by
  cases t with
  | prim p => cases p <;> simp_all [isBool]
  | thunk s => cases s with
    | prim p => cases p <;> simp_all [isBool]
    | _ => simp [isBool]
  | lazy s => cases s with
    | prim p => cases p <;> simp_all [isBool]
    | _ => simp [isBool]
  | _ => simp [isBool]

end Ty

/-! ## Renaming (weakening) -/

mutual
/-- Rename the declared datatypes a type mentions. -/
def Ty.map {ks ks' : List Nat} (f : Ref ks → Ref ks') {d : Bool} : Ty ks d → Ty ks' d
  | .prim p => .prim p
  | .fn a b => .fn (Ty.map f a) (Ty.map f b)
  | .array t => .array (Ty.map f t)
  | .list t => .list (Ty.map f t)
  | .strMap t => .strMap (Ty.map f t)
  | .enum s => .enum s
  | .record t fs => .record (Ty.map f t) (Fields.map f fs)
  | .union cs (h := h) => .union (Ctors.map f cs) (h := h)
  | .data r => .data (f r)
  | .thunk t => .thunk (Ty.map f t)
  | .lazy t => .lazy (Ty.map f t)
/-- `Ty.map` on fields. -/
def Fields.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Fields ks → Fields ks'
  | .one t => .one (Ty.map f t)
  | .cons t fs => .cons (Ty.map f t) (Fields.map f fs)
/-- `Ty.map` on a constructor. -/
def Ctor.map {ks ks' : List Nat} {b : Bool} (f : Ref ks → Ref ks') : Ctor ks b → Ctor ks' b
  | .nullary => .nullary
  | .fields fs => .fields (Fields.map f fs)
/-- `Ty.map` on constructors. -/
def Ctors.map {ks ks' : List Nat} {bs : List Bool} (f : Ref ks → Ref ks') :
    Ctors ks bs → Ctors ks' bs
  | .two c d => .two (Ctor.map f c) (Ctor.map f d)
  | .cons c cs => .cons (Ctor.map f c) (Ctors.map f cs)
end

/-- Weakening a closed type into a signature with one more (newest) block. -/
abbrev Ty.weaken {k : Nat} {ks : List Nat} {d : Bool} (t : Ty ks d) : Ty (k :: ks) d :=
  Ty.map .there t

/-- Renaming commutes with forgetting that a type is not a delay. -/
theorem Ty.map_relax {ks ks' : List Nat} (f : Ref ks → Ref ks') (t : Ty ks false) :
    Ty.map f t.relax = (Ty.map f t).relax := by
  cases t <;> rfl

mutual
/-- Renaming by the identity is the identity. -/
theorem Ty.map_id {ks : List Nat} {d : Bool} : (t : Ty ks d) → Ty.map (fun r => r) t = t
  | .prim _ => rfl
  | .fn a b => by simp only [Ty.map, Ty.map_id a, Ty.map_id b]
  | .array t => by simp only [Ty.map, Ty.map_id t]
  | .list t => by simp only [Ty.map, Ty.map_id t]
  | .strMap t => by simp only [Ty.map, Ty.map_id t]
  | .enum _ => rfl
  | .record t fs => by simp only [Ty.map, Ty.map_id t, Fields.map_id fs]
  | .union cs (h := _) => by simp only [Ty.map, Ctors.map_id cs]
  | .data _ => rfl
  | .thunk t => by simp only [Ty.map, Ty.map_id t]
  | .lazy t => by simp only [Ty.map, Ty.map_id t]
theorem Fields.map_id {ks : List Nat} : (fs : Fields ks) → Fields.map (fun r => r) fs = fs
  | .one t => by simp only [Fields.map, Ty.map_id t]
  | .cons t fs => by simp only [Fields.map, Ty.map_id t, Fields.map_id fs]
theorem Ctor.map_id {ks : List Nat} {b : Bool} : (c : Ctor ks b) → Ctor.map (fun r => r) c = c
  | .nullary => rfl
  | .fields fs => by simp only [Ctor.map, Fields.map_id fs]
theorem Ctors.map_id {ks : List Nat} {bs : List Bool} :
    (cs : Ctors ks bs) → Ctors.map (fun r => r) cs = cs
  | .two c d => by simp only [Ctors.map, Ctor.map_id c, Ctor.map_id d]
  | .cons c cs => by simp only [Ctors.map, Ctor.map_id c, Ctors.map_id cs]
end

mutual
/-- Renaming twice is renaming by the composite. -/
theorem Ty.map_map {ks ks' ks'' : List Nat} {d : Bool} (f : Ref ks → Ref ks')
    (g : Ref ks' → Ref ks'') :
    (t : Ty ks d) → Ty.map g (Ty.map f t) = Ty.map (fun r => g (f r)) t
  | .prim _ => rfl
  | .fn a b => by simp only [Ty.map, Ty.map_map f g a, Ty.map_map f g b]
  | .array t => by simp only [Ty.map, Ty.map_map f g t]
  | .list t => by simp only [Ty.map, Ty.map_map f g t]
  | .strMap t => by simp only [Ty.map, Ty.map_map f g t]
  | .enum _ => rfl
  | .record t fs => by simp only [Ty.map, Ty.map_map f g t, Fields.map_map f g fs]
  | .union cs (h := _) => by simp only [Ty.map, Ctors.map_map f g cs]
  | .data _ => rfl
  | .thunk t => by simp only [Ty.map, Ty.map_map f g t]
  | .lazy t => by simp only [Ty.map, Ty.map_map f g t]
theorem Fields.map_map {ks ks' ks'' : List Nat} (f : Ref ks → Ref ks') (g : Ref ks' → Ref ks'') :
    (fs : Fields ks) → Fields.map g (Fields.map f fs) = Fields.map (fun r => g (f r)) fs
  | .one t => by simp only [Fields.map, Ty.map_map f g t]
  | .cons t fs => by simp only [Fields.map, Ty.map_map f g t, Fields.map_map f g fs]
theorem Ctor.map_map {ks ks' ks'' : List Nat} {b : Bool} (f : Ref ks → Ref ks')
    (g : Ref ks' → Ref ks'') :
    (c : Ctor ks b) → Ctor.map g (Ctor.map f c) = Ctor.map (fun r => g (f r)) c
  | .nullary => rfl
  | .fields fs => by simp only [Ctor.map, Fields.map_map f g fs]
theorem Ctors.map_map {ks ks' ks'' : List Nat} {bs : List Bool} (f : Ref ks → Ref ks')
    (g : Ref ks' → Ref ks'') :
    (cs : Ctors ks bs) → Ctors.map g (Ctors.map f cs) = Ctors.map (fun r => g (f r)) cs
  | .two c d => by simp only [Ctors.map, Ctor.map_map f g c, Ctor.map_map f g d]
  | .cons c cs => by simp only [Ctors.map, Ctor.map_map f g c, Ctors.map_map f g cs]
end


end LeanScript

end
