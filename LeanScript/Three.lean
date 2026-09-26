module

public import LeanScript.Two

@[expose] public section

set_option autoImplicit false

/-!
# Two points are only ever `bool`

Every closed type over every signature **other than `Ty.bool`** has three values that a test
tells apart (`Ty.threeDen`), hence three pairwise different values (`Ty.den_exists_three`).
So a type whose values are at most two points is `Ty.bool` (`Ty.eq_bool_of_two_points`):
the grammar has no other way to write a type of two values (`Option Unit`, `BitVec 1`,
`Bool × Unit`, a copy of `Bool` under a new name, a union of two field-less constructors, …
cannot be written).

As for `LeanScript.Two`, the proof is data computed by structural recursion:

* `LeanPrimTy.three`: every leaf other than `bool` allowed by `LeanPrimTy.Nondeg`;
* `Ty.three E TE TE3`: a closed type other than `bool`, given two told-apart values
  (`TE`) and three told-apart values (`TE3`) of every declared datatype;
* `DSig.three Δ`: every declared datatype, block by block and, inside a block, member by
  member in grounding order (`IW.build`), using the two values of every member that
  `DSig.two` already gives.
-/

namespace LeanScript



/-- Three values of `α` that a test tells apart. -/
structure Three (α : Type) where
  x : α
  y : α
  z : α
  d : α → Nat
  dx : d x = 0
  dy : d y = 1
  dz : d z = 2

theorem Three.distinct {α : Type} (T : Three α) : T.x ≠ T.y ∧ T.y ≠ T.z ∧ T.x ≠ T.z := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := T.dx; rw [h, T.dy] at this; exact Nat.noConfusion this
  · have := T.dy; rw [h, T.dz] at this; exact Nat.noConfusion (Nat.succ.inj this)
  · have := T.dx; rw [h, T.dz] at this; exact Nat.noConfusion this

/-- Three different values of a type with decidable equality. -/
def Three.ofNe {α : Type} [DecidableEq α] (a b c : α) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : Three α :=
  ⟨a, b, c, fun v => if v = a then 0 else if v = b then 1 else 2, by simp,
    by simp [Ne.symm hab], by simp [Ne.symm hac, Ne.symm hbc]⟩

/-- Three values of a pair, from two told-apart values of each component. -/
def Three.prod {α β : Type} (A : Two α) (B : Two β) : Three (α × β) where
  x := (A.x, B.x)
  y := (A.y, B.x)
  z := (A.x, B.y)
  d p := if A.d p.1 then (if B.d p.2 then 0 else 2) else 1
  dx := by simp [A.dx, B.dx]
  dy := by simp [A.dy]
  dz := by simp [A.dx, B.dy]

/-- Three functions, from two told-apart values of the domain and of the codomain: the two
    constant functions and the function that tells the two points of the domain apart. -/
def Three.fn {α β : Type} (A : Two α) (B : Two β) : Three (α → β) where
  x := fun _ => B.x
  y := fun _ => B.y
  z := fun v => if A.d v then B.x else B.y
  d f := if B.d (f A.x) then (if B.d (f A.y) then 0 else 2) else 1
  dx := by simp [B.dx]
  dy := by simp [B.dy]
  dz := by simp [A.dx, A.dy, B.dx, B.dy]

/-- Three arrays: of length `0`, `1` and `2`. -/
def Three.array {α : Type} (v : α) : Three (Array α) :=
  ⟨#[], #[v], #[v, v], Array.size, rfl, rfl, rfl⟩

/-- Three values of an `Option`: `none` and two told-apart `some`s. -/
def Three.opt {α : Type} (A : Two α) : Three (Option α) where
  x := none
  y := some A.x
  z := some A.y
  d | none => 0 | some a => if A.d a then 1 else 2
  dx := rfl
  dy := by simp [A.dx]
  dz := by simp [A.dy]

/-- Three values of a sum: two told-apart on the left, one on the right. -/
def Three.sumL {α β : Type} (A : Two α) (b : β) : Three (α ⊕ β) where
  x := .inl A.x
  y := .inl A.y
  z := .inr b
  d | .inl a => if A.d a then 0 else 1 | .inr _ => 2
  dx := by simp [A.dx]
  dy := by simp [A.dy]
  dz := rfl

/-- Three values of a sum: one on the left, two told-apart on the right. -/
def Three.sumR {α β : Type} (a : α) (B : Two β) : Three (α ⊕ β) where
  x := .inl a
  y := .inr B.x
  z := .inr B.y
  d | .inl _ => 0 | .inr b => if B.d b then 1 else 2
  dx := rfl
  dy := by simp [B.dx]
  dz := by simp [B.dy]

/-! ## Leaves -/

theorem bitVec_toNat_small (n k : Nat) (hn : 2 ≤ n) (hk : k < 4) : (BitVec.ofNat n k).toNat = k := by
  have h4 : 4 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hn
    simpa using this
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem String.startPos_ne_endPos_of_two_le (s : String) (h : 2 ≤ s.length) :
    s.startPos ≠ s.endPos := by
  intro e
  have := String.startPos_eq_endPos_iff.mp e
  subst this
  simp at h

theorem String.next_startPos_ne_endPos (s : String) (h : 2 ≤ s.length)
    (h0 : s.startPos ≠ s.endPos) : s.startPos.next h0 ≠ s.endPos := by
  intro e
  have hs := s.startPos.splits_next h0
  have h2 := hs.eq_endPos_iff.mp e
  have := hs.eq_append
  rw [h2] at this
  have hl := congrArg String.length this
  simp [String.length_singleton] at hl
  omega

theorem String.startPos_ne_next (s : String) (h0 : s.startPos ≠ s.endPos) :
    s.startPos ≠ s.startPos.next h0 := by
  intro e
  have := String.Pos.lt_next (p := s.startPos) (h := h0)
  rw [← e] at this
  simp at this

/-- Three told-apart values of every leaf other than `bool` (the leaves of two values other
    than `bool` are refused by `LeanPrimTy.Nondeg`). -/
def LeanPrimTy.three : (p : LeanPrimTy) → p.Nondeg = true → p ≠ .bool → Three p.denote
  | .bool, _, h => absurd rfl h
  | .nat, _, _ => ⟨(0 : Nat), (1 : Nat), (2 : Nat), id, rfl, rfl, rfl⟩
  | .int, _, _ => Three.ofNe (0 : Int) 1 2 (by decide) (by decide) (by decide)
  | .bitvec n hn, h, _ =>
      have h2 : 2 ≤ n := by simp [LeanPrimTy.Nondeg] at h; omega
      ⟨0#n, 1#n, 2#n, BitVec.toNat, bitVec_toNat_small n 0 h2 (by decide),
        bitVec_toNat_small n 1 h2 (by decide), bitVec_toNat_small n 2 h2 (by decide)⟩
  | .uint8, _, _ => Three.ofNe (0 : UInt8) 1 2 (by decide) (by decide) (by decide)
  | .uint16, _, _ => Three.ofNe (0 : UInt16) 1 2 (by decide) (by decide) (by decide)
  | .uint32, _, _ => Three.ofNe (0 : UInt32) 1 2 (by decide) (by decide) (by decide)
  | .uint64, _, _ => Three.ofNe (0 : UInt64) 1 2 (by decide) (by decide) (by decide)
  | .int8, _, _ => Three.ofNe (0 : Int8) 1 2 (by decide) (by decide) (by decide)
  | .int16, _, _ => Three.ofNe (0 : Int16) 1 2 (by decide) (by decide) (by decide)
  | .int32, _, _ => Three.ofNe (0 : Int32) 1 2 (by decide) (by decide) (by decide)
  | .int64, _, _ => Three.ofNe (0 : Int64) 1 2 (by decide) (by decide) (by decide)
  | .char, _, _ => Three.ofNe 'a' 'b' 'c' (by decide) (by decide) (by decide)
  | .string, _, _ => Three.ofNe "" "a" "b" (by decide) (by decide) (by decide)
  | .stringPos s, h, _ =>
      have h2 : 2 ≤ s.length := by simpa [LeanPrimTy.Nondeg] using h
      have h0 := String.startPos_ne_endPos_of_two_le s h2
      Three.ofNe s.startPos (s.startPos.next h0) s.endPos (String.startPos_ne_next s h0)
        (String.next_startPos_ne_endPos s h2 h0) h0
  | .stringPosRaw, _, _ =>
      ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, String.Pos.Raw.byteIdx, rfl, rfl, rfl⟩
  | .substringRaw, _, _ =>
      ⟨⟨"", ⟨0⟩, ⟨0⟩⟩, ⟨"", ⟨0⟩, ⟨1⟩⟩, ⟨"", ⟨0⟩, ⟨2⟩⟩, fun s => s.stopPos.byteIdx, rfl, rfl, rfl⟩
  | .stringSlice, _, _ =>
      ⟨"".toSlice, "a".toSlice, "ab".toSlice, fun s => s.str.length, by decide, by decide,
        by decide⟩
  | .float, _, _ => Three.ofNe (0.0 : Float) 1.0 2.0 (by decide) (by decide) (by decide)
  | .float32, _, _ => Three.ofNe (0.0 : Float32) 1.0 2.0 (by decide) (by decide) (by decide)
  | .floatModel, _, _ =>
      Three.ofNe Float.Model.nan Float.Model.inf (-Float.Model.inf) (by decide) (by decide)
        (by decide)
  | .float32Model, _, _ =>
      Three.ofNe Float32.Model.nan Float32.Model.inf (-Float32.Model.inf) (by decide)
        (by decide) (by decide)

/-! ## Closed types -/

section ClosedThree
variable {ks : List Nat} (E : Ref ks → Type) (TE : (r : Ref ks) → Two (E r))

/-- Two constructors, one of which has fields. -/
def Ctor.threeTwo {a b : Bool} (c : Ctor ks a) (d : Ctor ks b) (h : UnionShape [a, b]) :
    Three (twoT (Ctor.den E c) (Ctor.den E d)) :=
  match a, b, c, d, h with
  | _, _, .nullary, .nullary, h => absurd h.some_fields (by decide)
  | _, _, .nullary, .fields fd, _ => Three.opt (Fields.pick E TE fd)
  | _, _, .fields fc, .nullary, _ => Three.opt (Fields.pick E TE fc)
  | _, _, .fields fc, .fields fd, _ => Three.sumL (Fields.pick E TE fc) (Fields.pick E TE fd).x

/-- A constructor in front of a rest of two told-apart values. -/
def Ctor.threeCons {a : Bool} {R : Type} (c : Ctor ks a) (TR : Two R) :
    Three (consT (Ctor.den E c) R) :=
  match a, c with
  | _, .nullary => Three.opt TR
  | _, .fields fc => Three.sumL (Fields.pick E TE fc) TR.x

/-- A union has three told-apart values. -/
def Ctors.three {bs : List Bool} (cs : Ctors ks bs) (h : UnionShape bs) : Three (Ctors.den E cs) :=
  match bs, cs, h with
  | _, .two c d, h => Ctor.threeTwo E TE c d h
  | _, .cons c cs, _ => Ctor.threeCons E TE c (Ctors.pick E TE cs)

variable (TE3 : (r : Ref ks) → Three (E r))

/-- Three told-apart values of a closed type other than `bool`, given two and three
    told-apart values of every declared datatype. -/
def Ty.three : (t : Ty ks) → t ≠ .bool → Three (Ty.den E t)
  | .prim p hp, h => LeanPrimTy.three p hp (fun e => h (by subst e; rfl))
  | .fn a b, _ => Three.fn (Ty.pick E TE a) (Ty.pick E TE b)
  | .array t, _ => Three.array (Ty.pick E TE t).x
  | .enum s, _ =>
      ⟨⟨0, by simp [LeanEnumSchema.nOfConstructors]⟩, ⟨1, by simp [LeanEnumSchema.nOfConstructors]⟩,
        ⟨2, by simp [LeanEnumSchema.nOfConstructors]⟩, Fin.val, rfl, rfl, rfl⟩
  | .record t fs, _ => Three.prod (Ty.pick E TE t) (Fields.pick E TE fs)
  | .union cs (h := hu), _ => Ctors.three E TE cs hu
  | .data r, _ => TE3 r

end ClosedThree

/-! ## One layer of a declared datatype -/

section ObjThree
variable {n : Nat} {X : Fin n → Type}

/-- An element of a hole. -/
def IPF.Obj.ofHole {i : Fin n} (x : X i) : (IPF.hole i).Obj X := ⟨PUnit.unit, fun _ => x⟩

/-- A layer from a function into layers. -/
def IPF.Obj.ofFn {D : Type} {c : IPF n} (g : D → c.Obj X) : (IPF.fn D c).Obj X :=
  ⟨fun v => (g v).1, fun p => (g p.1).2 p.2⟩

/-- Apply a function layer. -/
def IPF.Obj.app {D : Type} {c : IPF n} (o : (IPF.fn D c).Obj X) (v : D) : c.Obj X :=
  ⟨o.1 v, fun q => o.2 ⟨v, q⟩⟩

theorem IPF.Obj.app_ofFn {D : Type} {c : IPF n} (g : D → c.Obj X) (v : D) :
    IPF.Obj.app (IPF.Obj.ofFn g) v = g v := rfl

/-- Three layers of a hole, from three told-apart subtrees. -/
def Three.hole {i : Fin n} (T : Three (X i)) : Three ((IPF.hole i).Obj X) :=
  ⟨.ofHole T.x, .ofHole T.y, .ofHole T.z, fun o => T.d (o.2 PUnit.unit), T.dx, T.dy, T.dz⟩

/-- Three array layers: of length `0`, `1` and `2`. -/
def Three.arrayObj {c : IPF n} (o : c.Obj X) : Three ((IPF.array c).Obj X) :=
  ⟨⟨⟨[]⟩, fun b => nomatch b⟩, ⟨⟨[o.1]⟩, fun | .inl q => o.2 q⟩,
    ⟨⟨[o.1, o.1]⟩, fun | .inl q => o.2 q | .inr (.inl q) => o.2 q⟩,
    fun o' => o'.1.size, rfl, rfl, rfl⟩

/-- Three function layers, from two told-apart values of the domain and two told-apart
    layers of the codomain. -/
def Three.fnObj {D : Type} {c : IPF n} (A : Two D) (T : Two (c.Obj X)) :
    Three ((IPF.fn D c).Obj X) where
  x := .ofFn fun _ => T.x
  y := .ofFn fun _ => T.y
  z := .ofFn fun v => if A.d v then T.x else T.y
  d o := if T.d (o.app A.x) then (if T.d (o.app A.y) then 0 else 2) else 1
  dx := by simp [IPF.Obj.app_ofFn, T.dx]
  dy := by simp [IPF.Obj.app_ofFn, T.dy]
  dz := by simp [IPF.Obj.app_ofFn, A.dx, A.dy, T.dx, T.dy]

/-- Three pair layers. -/
def Three.prodObj {c d : IPF n} (A : Two (c.Obj X)) (B : Two (d.Obj X)) :
    Three ((IPF.prod c d).Obj X) where
  x := .pair A.x B.x
  y := .pair A.y B.x
  z := .pair A.x B.y
  d o := if A.d o.fst then (if B.d o.snd then 0 else 2) else 1
  dx := by show (if A.d A.x = true then (if B.d B.x = true then 0 else 2) else 1) = 0; simp [A.dx, B.dx]
  dy := by show (if A.d A.y = true then (if B.d B.x = true then 0 else 2) else 1) = 1; simp [A.dy]
  dz := by show (if A.d A.x = true then (if B.d B.y = true then 0 else 2) else 1) = 2; simp [A.dx, B.dy]

/-- Three layers with an extra field-less constructor. -/
def Three.optObj {c : IPF n} (A : Two (c.Obj X)) : Three ((IPF.opt c).Obj X) where
  x := .none
  y := .some A.x
  z := .some A.y
  d o := match o.caseOpt with | none => 0 | some a => if A.d a then 1 else 2
  dx := rfl
  dy := by show (if A.d A.x = true then 1 else 2) = 1; simp [A.dx]
  dz := by show (if A.d A.y = true then 1 else 2) = 2; simp [A.dy]

/-- Three layers of a choice: two told-apart on the left, one on the right. -/
def Three.sumObj {c d : IPF n} (A : Two (c.Obj X)) (b : d.Obj X) : Three ((IPF.sum c d).Obj X) where
  x := .inl A.x
  y := .inl A.y
  z := .inr b
  d o := match o.caseSum with | .inl a => if A.d a then 0 else 1 | .inr _ => 2
  dx := by show (if A.d A.x = true then 0 else 1) = 0; simp [A.dx]
  dy := by show (if A.d A.y = true then 0 else 1) = 1; simp [A.dy]
  dz := rfl

end ObjThree

section BodyThree
variable {ks : List Nat} (E : Ref ks → Type) (TE : (r : Ref ks) → Two (E r))
variable {n : Nat} (X : Fin n → Type) (tw : (i : Fin n) → Two (X i))

/-- Two told-apart layers of a list of guarded constructors. -/
def BCtors.twoOf {bs : List Bool} : (cs : BCtors ks n bs) → Two ((BCtors.toIPF E cs).Obj X)
  | .two c d => BCtor.twoTwo E TE X (fun i => (tw i).x) c d
  | .cons c cs => BCtor.consTwo E TE X (fun i => (tw i).x)
      (BCtors.inh E TE X (fun i => (tw i).x) cs) c

/-- Two constructors, one of which has fields: three told-apart layers. -/
def BCtor.threeTwo {g g' : Nat} {a b : Bool} (c : BCtor ks n g a) (d : BCtor ks n g' b)
    (h : UnionShape [a, b]) : Three ((IPF.twoC (BCtor.toIPF E c) (BCtor.toIPF E d)).Obj X) :=
  match a, b, c, d, h with
  | _, _, .nullary, .nullary, h => absurd h.some_fields (by decide)
  | _, _, .nullary, .fields fd, _ => Three.optObj (Flds.two E TE X (fun i => (tw i).x) (fun i _ => tw i) fd)
  | _, _, .fields fc, .nullary, _ => Three.optObj (Flds.two E TE X (fun i => (tw i).x) (fun i _ => tw i) fc)
  | _, _, .fields fc, .fields fd, _ =>
      Three.sumObj (Flds.two E TE X (fun i => (tw i).x) (fun i _ => tw i) fc)
        (Flds.inh E TE X (fun i _ => (tw i).x) fd)

/-- A constructor in front of a rest with two told-apart layers: three told-apart layers. -/
def BCtor.threeCons {g : Nat} {a : Bool} {R : IPF n} (c : BCtor ks n g a) (TR : Two (R.Obj X)) :
    Three ((IPF.consC (BCtor.toIPF E c) R).Obj X) :=
  match a, c with
  | _, .nullary => Three.optObj TR
  | _, .fields fc => Three.sumObj (Flds.two E TE X (fun i => (tw i).x) (fun i _ => tw i) fc) TR.x

/-- The constructors of a union: three told-apart layers. -/
def Alts.three {g : Nat} {bs : List Bool} (u : Alts ks n g bs) (h : UnionShape bs) :
    Three ((Alts.toIPF E u).Obj X) :=
  match bs, u, h with
  | _, .two₁ c d, h => BCtor.threeTwo E TE X tw c d h
  | _, .two₂ c d, h => BCtor.threeTwo E TE X tw c d h
  | _, .here c cs, _ => BCtor.threeCons E TE X tw c (BCtors.twoOf E TE X tw cs)
  | _, .there c u, _ => BCtor.threeCons E TE X tw c (Alts.two E TE X (fun i => (tw i).x) u)

/-- A field that is not an older type as it is: three told-apart layers, given three
    told-apart values of every grounded member. -/
def Fld.three {g : Nat} (tw3 : (i : Fin n) → i.val < g → Three (X i)) :
    (f : Fld ks n g) → f.isOld = false → Three ((Fld.toIPF E f).Obj X)
  | .hole i hi, _ => Three.hole (tw3 i hi)
  | .old _, h => absurd h (by simp [Fld.isOld])
  | .array f, _ => Three.arrayObj (Fld.inh E TE X (fun i _ => (tw i).x) f)
  | .fn a f, _ => Three.fnObj (Ty.pick E TE a) (Fld.two E TE X (fun i => (tw i).x) (fun i _ => tw i) f)

/-- A member of a block: three told-apart layers. -/
def Decl.three {g : Nat} (tw3 : (i : Fin n) → i.val < g → Three (X i)) :
    (d : Decl ks n g) → Three ((Decl.toIPF E d).Obj X)
  | .wrap f h => Fld.three E TE X tw tw3 f h
  | .record f fs => Three.prodObj (Fld.two E TE X (fun i => (tw i).x) (fun i _ => tw i) f)
      (Flds.two E TE X (fun i => (tw i).x) (fun i _ => tw i) fs)
  | .union u (h := hu) => Alts.three E TE X tw u hu

end BodyThree

section MemsThree
variable {ks : List Nat} (E : Ref ks → Type) (TE : (r : Ref ks) → Two (E r))

def Mems.threeMember {n g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (X : Fin n → Type) → ((j : Fin n) → Two (X j)) → ((j : Fin n) → j.val < g + i → Three (X j)) →
    Three ((Mems.member E bs i h).Obj X)
  | .nil, _, h, _, _, _ => absurd h (by omega)
  | .cons d _, 0, _, X, tw, tw3 => Decl.three E TE X tw tw3 d
  | .cons _ bs, i + 1, _, X, tw, tw3 =>
      Mems.threeMember bs i (by omega) X tw (fun j hj => tw3 j (by omega))

end MemsThree

/-- Three told-apart trees of a W-type from three told-apart layers. -/
def Three.ofIW {k : Nat} {P : Fin k → IPF k} {j : Fin k} (T : Three ((P j).Obj (IW P))) :
    Three (IW P j) where
  x := IW.mk j T.x.1 T.x.2
  y := IW.mk j T.y.1 T.y.2
  z := IW.mk j T.z.1 T.z.2
  d v := T.d v.dest
  dx := T.dx
  dy := T.dy
  dz := T.dz

/-- Three told-apart values of every declared datatype.  Structural recursion on the
    signature; inside a block, member by member in grounding order. -/
def DSig.three : {ks : List Nat} → (Δ : DSig ks) → (r : Ref ks) → Three (DSig.refDen Δ r)
  | _, .cons Δ k bs, .here j =>
      let E := DSig.refDen Δ
      let TE := DSig.two Δ
      let tw : (i : Fin (k + 1)) → Two (IW (Mems.fam E bs) i) :=
        fun i => DSig.two (.cons Δ k bs) (.here i)
      IW.build (C := fun i => Three (IW (Mems.fam E bs) i)) (fun j acc =>
        Three.ofIW (Mems.threeMember E TE bs j.val (Fin.zero_add_lt' j) (IW (Mems.fam E bs)) tw
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _))))) j
  | _, .cons Δ _ _, .there r => DSig.three Δ r

/-- **Every closed type other than `bool` has three values that a test tells apart.** -/
def Ty.threeDen {ks : List Nat} (Δ : DSig ks) (t : Ty ks) (h : t ≠ .bool) : Three (Ty.Den Δ t) :=
  Ty.three (DSig.refDen Δ) (DSig.two Δ) (DSig.three Δ) t h

/-- Every closed type other than `bool` has three pairwise different values. -/
theorem Ty.den_exists_three {ks : List Nat} (Δ : DSig ks) (t : Ty ks) (h : t ≠ .bool) :
    ∃ x y z : Ty.Den Δ t, x ≠ y ∧ y ≠ z ∧ x ≠ z :=
  ⟨_, _, _, (Ty.threeDen Δ t h).distinct⟩

/-- **Two points are only ever `bool`**: a closed type with at most two values (among any
    three values two are equal) is `Ty.bool`. -/
theorem Ty.eq_bool_of_two_points {ks : List Nat} (Δ : DSig ks) (t : Ty ks)
    (h : ∀ x y z : Ty.Den Δ t, x = y ∨ y = z ∨ x = z) : t = .bool := by
  apply Classical.byContradiction
  intro hb
  let T := Ty.threeDen Δ t hb
  have ⟨h1, h2, h3⟩ := T.distinct
  rcases h T.x T.y T.z with e | e | e
  · exact h1 e
  · exact h2 e
  · exact h3 e



end LeanScript

end
