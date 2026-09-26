module

public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

/-!
# No unit-like and no empty-like types

Every closed type over every signature has two values that a Boolean test tells apart
(`Ty.twoDen`), hence it is inhabited (`Ty.den_nonempty`) and has two different values
(`Ty.den_exists_ne`, `Ty.den_not_subsingleton`).

The proof is data computed by structural recursion, in two layers:

* `DSig.two Δ : ∀ r, Two (DSig.refDen Δ r)`, by recursion on the signature.  Inside a
  block it works member by member with `IW.build` on a `Nat` bound, first with `inh`
  (grounded holes suffice), then with `two`.
* `Ty.pick E TE : (t : Ty ks) → Two (Ty.den E t)`, by recursion on a closed type, given two
  values of every datatype.  It needs no grounding: every closed type has values.

The leaves (`LeanPrimTy.two`) are settled one by one, each by `decide` on two literals (the
float types included: `Float` and `Float32` have a decidable equality through their model).
-/

namespace LeanScript



/-- Two values of `α` that a Boolean test tells apart.  Structural data, not a proof search. -/
structure Two (α : Type) where
  x : α
  y : α
  d : α → Bool
  dx : d x = true
  dy : d y = false

theorem Two.ne {α : Type} (T : Two α) : T.x ≠ T.y := fun h => by
  have := T.dx; rw [h, T.dy] at this; exact Bool.noConfusion this

/-- Two different values of a type with decidable equality. -/
def Two.ofNe {α : Type} [DecidableEq α] (a b : α) (h : a ≠ b) : Two α :=
  ⟨a, b, fun v => decide (v = a), by simp, by simpa using fun e => h e.symm⟩

theorem bitVec_zero_ne_one (n : Nat) (h : 0 < n) : (0#n) ≠ 1#n := by
  intro e
  have := congrArg BitVec.toNat e
  simp [BitVec.toNat_ofNat] at this
  omega

/-- Two told-apart values of every leaf with at least two values. -/
def LeanPrimTy.two : (p : LeanPrimTy) → p.Nondeg = true → Two p.denote
  | .bool, _ => ⟨true, false, id, rfl, rfl⟩
  | .nat, _ => ⟨(0 : Nat), (1 : Nat), fun n => Nat.beq n 0, rfl, rfl⟩
  | .int, _ => Two.ofNe (0 : Int) 1 (by decide)
  | .bitvec n h, _ => Two.ofNe (0#n) (1#n) (bitVec_zero_ne_one n h)
  | .uint8, _ => Two.ofNe (0 : UInt8) 1 (by decide)
  | .uint16, _ => Two.ofNe (0 : UInt16) 1 (by decide)
  | .uint32, _ => Two.ofNe (0 : UInt32) 1 (by decide)
  | .uint64, _ => Two.ofNe (0 : UInt64) 1 (by decide)
  | .int8, _ => Two.ofNe (0 : Int8) 1 (by decide)
  | .int16, _ => Two.ofNe (0 : Int16) 1 (by decide)
  | .int32, _ => Two.ofNe (0 : Int32) 1 (by decide)
  | .int64, _ => Two.ofNe (0 : Int64) 1 (by decide)
  | .char, _ => Two.ofNe 'a' 'b' (by decide)
  | .string, _ => Two.ofNe "" "a" (by decide)
  | .stringPos s, h =>
      ⟨s.startPos, s.endPos, fun q => q.offset.byteIdx == 0, rfl, by
        have hs : s ≠ "" := fun e => by subst e; simp [LeanPrimTy.Nondeg] at h
        have : s.utf8ByteSize ≠ 0 := fun e => hs (String.utf8ByteSize_eq_zero_iff.mp e)
        simpa [String.endPos, String.rawEndPos] using this⟩
  | .stringPosRaw, _ => Two.ofNe (⟨0⟩ : String.Pos.Raw) ⟨1⟩ (by decide)
  | .substringRaw, _ =>
      ⟨⟨"", ⟨0⟩, ⟨0⟩⟩, ⟨"", ⟨0⟩, ⟨1⟩⟩, fun s => s.stopPos.byteIdx == 0, rfl, rfl⟩
  | .stringSlice, _ =>
      ⟨"".toSlice, "a".toSlice, fun s => s.str == "", by decide, by decide⟩
  | .float, _ => Two.ofNe (0.0 : Float) 1.0 (by decide)
  | .float32, _ => Two.ofNe (0.0 : Float32) 1.0 (by decide)
  | .floatModel, _ =>
      ⟨Float.Model.nan, Float.Model.inf, fun f => f.toBits == Float.Model.nan.toBits,
        by simp, by decide⟩
  | .float32Model, _ =>
      ⟨Float32.Model.nan, Float32.Model.inf, fun f => f.toBits == Float32.Model.nan.toBits,
        by simp, by decide⟩

section ClosedTwo
variable {ks : List Nat} (E : Ref ks → Type) (TE : (r : Ref ks) → Two (E r))

/-- Two constructors: the tag tells them apart (payloads from `inh`). -/
def twoTwo : (A B : Option Type) → (A.elim PUnit id) → (B.elim PUnit id) → Two (twoT A B)
  | none, none, _, _ => ⟨true, false, id, rfl, rfl⟩
  | none, some _, _, b => ⟨none, some b, Option.isNone, rfl, rfl⟩
  | some _, none, a, _ => ⟨some a, none, Option.isSome, rfl, rfl⟩
  | some _, some _, a, b => ⟨.inl a, .inr b, Sum.isLeft, rfl, rfl⟩

/-- A constructor in front of an inhabited rest: the tag tells them apart. -/
def twoCons : (A : Option Type) → {R : Type} → (A.elim PUnit id) → R → Two (consT A R)
  | none, _, _, r => ⟨none, some r, Option.isNone, rfl, rfl⟩
  | some _, _, a, r => ⟨.inl a, .inr r, Sum.isLeft, rfl, rfl⟩

mutual
/-- Two told-apart values of a closed type, given two of every declared datatype.
    Structural recursion on the type: closed types need no grounding. -/
def Ty.pick : (t : Ty ks) → Two (Ty.den E t)
  | .prim p h => LeanPrimTy.two p h
  | .fn a b =>
      let e := (Ty.pick a).x
      let T := Ty.pick b
      ⟨fun _ => T.x, fun _ => T.y, fun f => T.d (f e), T.dx, T.dy⟩
  | .array t =>
      let v := (Ty.pick t).x
      ⟨#[], #[v], fun a => a.isEmpty, rfl, rfl⟩
  | .enum s =>
      ⟨⟨0, by simp [LeanEnumSchema.nOfConstructors]⟩, ⟨1, by simp [LeanEnumSchema.nOfConstructors]⟩,
        fun i => i.val == 0, rfl, rfl⟩
  | .record t fs =>
      let T := Ty.pick t
      let v := (Fields.pick fs).x
      ⟨(T.x, v), (T.y, v), fun p => T.d p.1, T.dx, T.dy⟩
  | .union cs (h := _) => Ctors.pick cs
  | .data r => TE r
def Fields.pick : (fs : Fields ks) → Two (Fields.den E fs)
  | .one t => Ty.pick t
  | .cons t fs =>
      let T := Ty.pick t
      let v := (Fields.pick fs).x
      ⟨(T.x, v), (T.y, v), fun p => T.d p.1, T.dx, T.dy⟩
def Ctor.pick {b : Bool} : (c : Ctor ks b) → (Ctor.den E c).elim PUnit id
  | .nullary => PUnit.unit
  | .fields fs => (Fields.pick fs).x
def Ctors.pick {bs : List Bool} : (cs : Ctors ks bs) → Two (Ctors.den E cs)
  | .two c d => twoTwo _ _ (Ctor.pick c) (Ctor.pick d)
  | .cons c cs => twoCons _ (Ctor.pick c) (Ctors.pick cs).x
end
end ClosedTwo

section BodyTwo
variable {ks : List Nat} (E : Ref ks → Type) (TE : (r : Ref ks) → Two (E r))

/-- A value of a field, given values of the holes it is grounded on. -/
def Fld.inh {n g : Nat} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (f : Fld ks n g) → (Fld.toIPF E f).Obj X
  | .hole i h => ⟨PUnit.unit, fun _ => w i h⟩
  | .old t => .ofConst (Ty.pick E TE t).x
  | .array _ => ⟨#[], fun p => nomatch p⟩
  | .fn _ f => let o := Fld.inh X w f; ⟨fun _ => o.1, fun p => o.2 p.2⟩

def Flds.inh {n g : Nat} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (fs : Flds ks n g) → (Flds.toIPF E fs).Obj X
  | .one f => Fld.inh E TE X w f
  | .cons f fs => .pair (Fld.inh E TE X w f) (Flds.inh X w fs)

/-- Two told-apart values of a field, given a value of every hole and two of every grounded one. -/
def Fld.two {n g : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (tw : (i : Fin n) → i.val < g → Two (X i)) : (f : Fld ks n g) → Two ((Fld.toIPF E f).Obj X)
  | .hole i h =>
      let T := tw i h
      ⟨⟨PUnit.unit, fun _ => T.x⟩, ⟨PUnit.unit, fun _ => T.y⟩, fun o => T.d (o.2 PUnit.unit),
        T.dx, T.dy⟩
  | .old t =>
      let T := Ty.pick E TE t
      ⟨.ofConst T.x, .ofConst T.y, fun o => T.d o.1, T.dx, T.dy⟩
  | .array f =>
      let o := Fld.inh E TE X (fun i _ => all i) f
      ⟨⟨#[], fun p => nomatch p⟩, ⟨#[o.1], fun | .inl q => o.2 q⟩,
        fun o' => o'.1.isEmpty, rfl, rfl⟩
  | .fn a f =>
      let e := (Ty.pick E TE a).x
      let T := Fld.two X all tw f
      ⟨⟨fun _ => T.x.1, fun p => T.x.2 p.2⟩, ⟨fun _ => T.y.1, fun p => T.y.2 p.2⟩,
        fun o => T.d ⟨o.1 e, fun q => o.2 ⟨e, q⟩⟩, T.dx, T.dy⟩

def Flds.two {n g : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (tw : (i : Fin n) → i.val < g → Two (X i)) : (fs : Flds ks n g) → Two ((Flds.toIPF E fs).Obj X)
  | .one f => Fld.two E TE X all tw f
  | .cons f fs =>
      let T := Fld.two E TE X all tw f
      let os := Flds.inh E TE X (fun i _ => all i) fs
      ⟨.pair T.x os, .pair T.y os, fun o => T.d o.fst, T.dx, T.dy⟩

/-- With every hole inhabited, any list of constructors is inhabited (take the first). -/
def BCtors.inh {n : Nat} {bs : List Bool} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (cs : BCtors ks n bs) → (BCtors.toIPF E cs).Obj X
  | .two .nullary .nullary => .ofConst true
  | .two .nullary (.fields _) => .none
  | .two (.fields fc) .nullary => .some (Flds.inh E TE X (fun i _ => all i) fc)
  | .two (.fields fc) (.fields _) => .inl (Flds.inh E TE X (fun i _ => all i) fc)
  | .cons .nullary _ => .none
  | .cons (.fields fc) _ => .inl (Flds.inh E TE X (fun i _ => all i) fc)

/-- A union is inhabited through its base constructor. -/
def Alts.inh {n g : Nat} {bs : List Bool} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (u : Alts ks n g bs) → (Alts.toIPF E u).Obj X
  | .two₁ .nullary .nullary => .ofConst true
  | .two₁ .nullary (.fields _) => .none
  | .two₁ (.fields fc) .nullary => .some (Flds.inh E TE X w fc)
  | .two₁ (.fields fc) (.fields _) => .inl (Flds.inh E TE X w fc)
  | .two₂ .nullary .nullary => .ofConst true
  | .two₂ .nullary (.fields fd) => .some (Flds.inh E TE X w fd)
  | .two₂ (.fields _) .nullary => .none
  | .two₂ (.fields _) (.fields fd) => .inr (Flds.inh E TE X w fd)
  | .here .nullary _ => .none
  | .here (.fields fc) _ => .inl (Flds.inh E TE X w fc)
  | .there .nullary u => .some (Alts.inh X w u)
  | .there (.fields _) u => .inr (Alts.inh X w u)

def BCtor.twoTwo {n g g' : Nat} {a b : Bool} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (c : BCtor ks n g a) → (d : BCtor ks n g' b) →
    Two ((IPF.twoC (BCtor.toIPF E c) (BCtor.toIPF E d)).Obj X)
  | .nullary, .nullary => ⟨.ofConst true, .ofConst false, fun o => o.1, rfl, rfl⟩
  | .nullary, .fields fd =>
      ⟨.none, .some (Flds.inh E TE X (fun i _ => all i) fd), fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc, .nullary =>
      ⟨.some (Flds.inh E TE X (fun i _ => all i) fc), .none, fun o => o.1.isSome, rfl, rfl⟩
  | .fields fc, .fields fd =>
      ⟨.inl (Flds.inh E TE X (fun i _ => all i) fc), .inr (Flds.inh E TE X (fun i _ => all i) fd),
        fun o => o.1.isLeft, rfl, rfl⟩

def BCtor.consTwo {n g : Nat} {a : Bool} {R : IPF n} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (r : R.Obj X) : (c : BCtor ks n g a) → Two ((IPF.consC (BCtor.toIPF E c) R).Obj X)
  | .nullary => ⟨.none, .some r, fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc =>
      ⟨.inl (Flds.inh E TE X (fun i _ => all i) fc), .inr r, fun o => o.1.isLeft, rfl, rfl⟩

def Alts.two {n g : Nat} {bs : List Bool} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (u : Alts ks n g bs) → Two ((Alts.toIPF E u).Obj X)
  | .two₁ c d => BCtor.twoTwo E TE X all c d
  | .two₂ c d => BCtor.twoTwo E TE X all c d
  | .here c cs => BCtor.consTwo E TE X all (BCtors.inh E TE X all cs) c
  | .there c u => BCtor.consTwo E TE X all (Alts.inh E TE X (fun i _ => all i) u) c

def Decl.inh {n g : Nat} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (d : Decl ks n g) → (Decl.toIPF E d).Obj X
  | .wrap f _ => Fld.inh E TE X w f
  | .record f fs => .pair (Fld.inh E TE X w f) (Flds.inh E TE X w fs)
  | .union u (h := _) => Alts.inh E TE X w u

def Decl.two {n g : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (tw : (i : Fin n) → i.val < g → Two (X i)) : (d : Decl ks n g) → Two ((Decl.toIPF E d).Obj X)
  | .wrap f _ => Fld.two E TE X all tw f
  | .record f fs =>
      let T := Fld.two E TE X all tw f
      let os := Flds.inh E TE X (fun i _ => all i) fs
      ⟨.pair T.x os, .pair T.y os, fun o => T.d o.fst, T.dx, T.dy⟩
  | .union u (h := _) => Alts.two E TE X all u

def Mems.inhMember {n g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (X : Fin n → Type) → ((j : Fin n) → j.val < g + i → X j) → (Mems.member E bs i h).Obj X
  | .nil, _, h, _, _ => absurd h (by omega)
  | .cons d _, 0, _, X, w => Decl.inh E TE X w d
  | .cons _ bs, i + 1, _, X, w => Mems.inhMember bs i (by omega) X (fun j hj => w j (by omega))

def Mems.twoMember {n g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (X : Fin n → Type) → ((j : Fin n) → X j) → ((j : Fin n) → j.val < g + i → Two (X j)) →
    Two ((Mems.member E bs i h).Obj X)
  | .nil, _, h, _, _, _ => absurd h (by omega)
  | .cons d _, 0, _, X, all, tw => Decl.two E TE X all tw d
  | .cons _ bs, i + 1, _, X, all, tw =>
      Mems.twoMember bs i (by omega) X all (fun j hj => tw j (by omega))
end BodyTwo

/-- Two told-apart trees of a W-type from two told-apart layers. -/
def Two.ofIW {k : Nat} {P : Fin k → IPF k} {j : Fin k} (T : Two ((P j).Obj (IW P))) :
    Two (IW P j) where
  x := IW.mk j T.x.1 T.x.2
  y := IW.mk j T.y.1 T.y.2
  d v := T.d v.dest
  dx := T.dx
  dy := T.dy

/-- Two told-apart values of every declared datatype.  Structural recursion on the signature;
    inside a block, member by member in grounding order. -/
def DSig.two : {ks : List Nat} → (Δ : DSig ks) → (r : Ref ks) → Two (DSig.refDen Δ r)
  | _, .cons Δ _ bs, .here j =>
      let E := DSig.refDen Δ
      let TE := DSig.two Δ
      let all : (i : Fin _) → IW (Mems.fam E bs) i := IW.build (fun j acc =>
        IW.ofObj (Mems.inhMember E TE bs j.val (Fin.zero_add_lt' j) (IW (Mems.fam E bs))
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _)))))
      IW.build (C := fun i => Two (IW (Mems.fam E bs) i)) (fun j acc =>
        Two.ofIW (Mems.twoMember E TE bs j.val (Fin.zero_add_lt' j) (IW (Mems.fam E bs)) all
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _))))) j
  | _, .cons Δ _ _, .there r => DSig.two Δ r

/-- **Every closed type over every signature has two values that a Boolean test tells
    apart.**  No fuel, no measure, no proof search. -/
def Ty.twoDen {ks : List Nat} (Δ : DSig ks) (t : Ty ks) : Two (Ty.Den Δ t) :=
  Ty.pick (DSig.refDen Δ) (DSig.two Δ) t

/-- No closed type is empty-like. -/
theorem Ty.den_nonempty {ks : List Nat} (Δ : DSig ks) (t : Ty ks) : Nonempty (Ty.Den Δ t) :=
  ⟨(Ty.twoDen Δ t).x⟩

/-- No closed type is unit-like (or empty-like). -/
theorem Ty.den_not_subsingleton {ks : List Nat} (Δ : DSig ks) (t : Ty ks) :
    ¬ ∀ x y : Ty.Den Δ t, x = y :=
  fun h => (Ty.twoDen Δ t).ne (h _ _)

/-- Every closed type has two different values. -/
theorem Ty.den_exists_ne {ks : List Nat} (Δ : DSig ks) (t : Ty ks) :
    ∃ x y : Ty.Den Δ t, x ≠ y :=
  ⟨_, _, (Ty.twoDen Δ t).ne⟩



end LeanScript

end
