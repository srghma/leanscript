module

/-!
# Toy model for `proposals/NominalTyProposal.md`: declared datatypes instead of a `mu` binder

Self-contained (no imports, not part of the Lake build).  Check it with the bare compiler:

```
lean proposals/NomTyToy.lean
```

The design, at toy scale:

* **Closed types `Ty ks` have no binder and no holes.**  A recursive type is a *name*,
  `data r`, pointing into a *datatype signature* `Δ : DSig ks`: a list of declaration blocks,
  newest first (`ks` lists the block sizes).  `Ty ks` has no grounding index; a union is any
  two or more constructors.
* **Declaration bodies are a separate, flat grammar** (`Fld`, `Decl`, `Mems`): a member is a
  record (≥ 2 fields), a union (≥ 2 constructors, one of them the grounded *base*) or a
  wrapper of one field.  A field is a hole (member of the block being declared), an older
  closed type (`old`), an `array` of a field (guarded) or a function from an older closed type
  to a field.  The grounding index `g` lives only here, exactly as in `WTyToy`.
* **Canonical forms are free**: a Lean type is one `Ty` because a recursive type is referred
  to by its name, never by its structure.  There is no `Ty.fix`, no inlining rule and no rule
  about where `closed` goes.
* **`Ty.twoDen Δ t`**: every closed type over every signature has two values told apart by a
  Boolean test.  Structural recursion (on the type for closed types; on the signature, then
  member by member by a `Nat` bound, for declared types).
* `data_in`/`data_out`/`data_rec` (`dataIn`, `dataOut`, `dataRec`) are structural, need no
  cast, and compute by `rfl`; the old-type fields go through the structural transports
  `Ty.lift`/`Ty.lower` (weakening), which also compute.
* Rejected by the type checker (pinned with `#guard_msgs`): `μX. X`, `μX. Nat × X`, a
  one-constructor union.
-/

@[expose] public section

namespace NomTyToy

/-! ## Names of declared datatypes -/

/-- A reference to member `j` of one block of a signature whose block sizes are `ks`
    (newest block first, as de Bruijn indices). -/
inductive Ref : List Nat → Type where
  | here {k : Nat} {ks : List Nat} (j : Fin (k + 1)) : Ref (k :: ks)
  | there {k : Nat} {ks : List Nat} : Ref ks → Ref (k :: ks)
  deriving DecidableEq

/-! ## Closed types: no binder, no hole, no grounding -/

mutual
/-- A closed type over a signature with block sizes `ks`. -/
inductive Ty : List Nat → Type where
  | nat {ks : List Nat} : Ty ks
  | bool {ks : List Nat} : Ty ks
  | fn {ks : List Nat} : Ty ks → Ty ks → Ty ks
  | array {ks : List Nat} : Ty ks → Ty ks
  /-- At least two fields. -/
  | record {ks : List Nat} : Ty ks → Fields ks → Ty ks
  /-- At least two constructors. -/
  | union {ks : List Nat} : Ctors ks → Ty ks
  /-- A declared (recursive) datatype, by name. -/
  | data {ks : List Nat} : Ref ks → Ty ks
/-- One or more fields. -/
inductive Fields : List Nat → Type where
  | one {ks : List Nat} : Ty ks → Fields ks
  | cons {ks : List Nat} : Ty ks → Fields ks → Fields ks
/-- A constructor: no fields, or one or more fields. -/
inductive Ctor : List Nat → Type where
  | nullary {ks : List Nat} : Ctor ks
  | fields {ks : List Nat} : Fields ks → Ctor ks
/-- Two or more constructors. -/
inductive Ctors : List Nat → Type where
  | two {ks : List Nat} : Ctor ks → Ctor ks → Ctors ks
  | cons {ks : List Nat} : Ctor ks → Ctors ks → Ctors ks
end

deriving instance DecidableEq for Ty, Fields, Ctor, Ctors

example : DecidableEq (Ty [0, 1]) := inferInstance

/-- Two constructors: a constructor without fields adds `Option`, never `PUnit ⊕ _`. -/
def twoT : Option Type → Option Type → Type
  | none, none => Bool
  | none, some B => Option B
  | some A, none => Option A
  | some A, some B => A ⊕ B

/-- A constructor in front of the others. -/
def consT : Option Type → Type → Type
  | none, R => Option R
  | some A, R => A ⊕ R

mutual
/-- The meaning of a closed type, given the meaning `E` of the declared datatypes. -/
def Ty.den {ks : List Nat} (E : Ref ks → Type) : Ty ks → Type
  | .nat => Nat
  | .bool => Bool
  | .fn a b => Ty.den E a → Ty.den E b
  | .array t => (m : Nat) × (Fin m → Ty.den E t)
  | .record t fs => Ty.den E t × Fields.den E fs
  | .union cs => Ctors.den E cs
  | .data r => E r
def Fields.den {ks : List Nat} (E : Ref ks → Type) : Fields ks → Type
  | .one t => Ty.den E t
  | .cons t fs => Ty.den E t × Fields.den E fs
def Ctor.den {ks : List Nat} (E : Ref ks → Type) : Ctor ks → Option Type
  | .nullary => none
  | .fields fs => some (Fields.den E fs)
def Ctors.den {ks : List Nat} (E : Ref ks → Type) : Ctors ks → Type
  | .two c d => twoT (Ctor.den E c) (Ctor.den E d)
  | .cons c cs => consT (Ctor.den E c) (Ctors.den E cs)
end

/-! ## Renaming (weakening) and its transports -/

mutual
def Ty.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ty ks → Ty ks'
  | .nat => .nat
  | .bool => .bool
  | .fn a b => .fn (Ty.map f a) (Ty.map f b)
  | .array t => .array (Ty.map f t)
  | .record t fs => .record (Ty.map f t) (Fields.map f fs)
  | .union cs => .union (Ctors.map f cs)
  | .data r => .data (f r)
def Fields.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Fields ks → Fields ks'
  | .one t => .one (Ty.map f t)
  | .cons t fs => .cons (Ty.map f t) (Fields.map f fs)
def Ctor.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ctor ks → Ctor ks'
  | .nullary => .nullary
  | .fields fs => .fields (Fields.map f fs)
def Ctors.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ctors ks → Ctors ks'
  | .two c d => .two (Ctor.map f c) (Ctor.map f d)
  | .cons c cs => .cons (Ctor.map f c) (Ctors.map f cs)
end

/-- Weakening a closed type into a signature with one more (newest) block. -/
abbrev Ty.weaken {k : Nat} {ks : List Nat} (t : Ty ks) : Ty (k :: ks) := Ty.map .there t

section Transport
variable {ks ks' : List Nat} (f : Ref ks → Ref ks') (E : Ref ks' → Type)

mutual
/-- A value of `t` (datatypes read through `f`) is a value of the renamed type.  Structural,
    the identity on declared datatypes. -/
def Ty.lift : (t : Ty ks) → Ty.den (fun r => E (f r)) t → Ty.den E (Ty.map f t)
  | .nat, x => x
  | .bool, x => x
  | .fn a b, x => fun y => Ty.lift b (x (Ty.lower a y))
  | .array t, x => ⟨x.1, fun i => Ty.lift t (x.2 i)⟩
  | .record t fs, x => (Ty.lift t x.1, Fields.lift fs x.2)
  | .union cs, x => Ctors.lift cs x
  | .data _, x => x
def Ty.lower : (t : Ty ks) → Ty.den E (Ty.map f t) → Ty.den (fun r => E (f r)) t
  | .nat, x => x
  | .bool, x => x
  | .fn a b, x => fun y => Ty.lower b (x (Ty.lift a y))
  | .array t, x => ⟨x.1, fun i => Ty.lower t (x.2 i)⟩
  | .record t fs, x => (Ty.lower t x.1, Fields.lower fs x.2)
  | .union cs, x => Ctors.lower cs x
  | .data _, x => x
def Fields.lift : (fs : Fields ks) → Fields.den (fun r => E (f r)) fs → Fields.den E (Fields.map f fs)
  | .one t, x => Ty.lift t x
  | .cons t fs, x => (Ty.lift t x.1, Fields.lift fs x.2)
def Fields.lower : (fs : Fields ks) → Fields.den E (Fields.map f fs) → Fields.den (fun r => E (f r)) fs
  | .one t, x => Ty.lower t x
  | .cons t fs, x => (Ty.lower t x.1, Fields.lower fs x.2)
def Ctors.lift : (cs : Ctors ks) → Ctors.den (fun r => E (f r)) cs → Ctors.den E (Ctors.map f cs)
  | .two .nullary .nullary, x => x
  | .two .nullary (.fields fd), x => x.map (Fields.lift fd)
  | .two (.fields fc) .nullary, x => x.map (Fields.lift fc)
  | .two (.fields fc) (.fields fd), x =>
      match x with | .inl a => .inl (Fields.lift fc a) | .inr b => .inr (Fields.lift fd b)
  | .cons .nullary cs, x => x.map (Ctors.lift cs)
  | .cons (.fields fc) cs, x =>
      match x with | .inl a => .inl (Fields.lift fc a) | .inr b => .inr (Ctors.lift cs b)
def Ctors.lower : (cs : Ctors ks) → Ctors.den E (Ctors.map f cs) → Ctors.den (fun r => E (f r)) cs
  | .two .nullary .nullary, x => x
  | .two .nullary (.fields fd), x => x.map (Fields.lower fd)
  | .two (.fields fc) .nullary, x => x.map (Fields.lower fc)
  | .two (.fields fc) (.fields fd), x =>
      match x with | .inl a => .inl (Fields.lower fc a) | .inr b => .inr (Fields.lower fd b)
  | .cons .nullary cs, x => x.map (Ctors.lower cs)
  | .cons (.fields fc) cs, x =>
      match x with | .inl a => .inl (Fields.lower fc a) | .inr b => .inr (Ctors.lower cs b)
end

end Transport

/-! ## Declaration bodies: the only place with holes and grounding

A block declares `n` members over the older signature `ks`.  `Fld ks n g`: a field type in
which holes `< g` are grounded (known to have values). -/

/-- A field of a constructor of a declared datatype. -/
inductive Fld : List Nat → Nat → Nat → Type where
  /-- A member of the block being declared, used directly: must be grounded. -/
  | hole {ks : List Nat} {n g : Nat} (i : Fin n) : i.val < g → Fld ks n g
  /-- An older closed type (it cannot mention the block being declared). -/
  | old {ks : List Nat} {n g : Nat} : Ty ks → Fld ks n g
  /-- Guarded: the empty array is always a value. -/
  | array {ks : List Nat} {n g : Nat} : Fld ks n n → Fld ks n g
  /-- The domain is an older closed type (strict positivity, by typing). -/
  | fn {ks : List Nat} {n g : Nat} : Ty ks → Fld ks n g → Fld ks n g
  deriving DecidableEq

/-- One or more fields. -/
inductive Flds : List Nat → Nat → Nat → Type where
  | one {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g
  | cons {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g → Flds ks n g
  deriving DecidableEq

/-- A constructor: no fields, or one or more fields. -/
inductive BCtor : List Nat → Nat → Nat → Type where
  | nullary {ks : List Nat} {n g : Nat} : BCtor ks n g
  | fields {ks : List Nat} {n g : Nat} : Flds ks n g → BCtor ks n g
  deriving DecidableEq

/-- Two or more guarded constructors. -/
inductive BCtors : List Nat → Nat → Type where
  | two {ks : List Nat} {n : Nat} : BCtor ks n n → BCtor ks n n → BCtors ks n
  | cons {ks : List Nat} {n : Nat} : BCtor ks n n → BCtors ks n → BCtors ks n
  deriving DecidableEq

/-- Two or more constructors, exactly one of which (the base) is grounded. -/
inductive Alts : List Nat → Nat → Nat → Type where
  | two₁ {ks : List Nat} {n g : Nat} : BCtor ks n g → BCtor ks n n → Alts ks n g
  | two₂ {ks : List Nat} {n g : Nat} : BCtor ks n n → BCtor ks n g → Alts ks n g
  | here {ks : List Nat} {n g : Nat} : BCtor ks n g → BCtors ks n → Alts ks n g
  | there {ks : List Nat} {n g : Nat} : BCtor ks n n → Alts ks n g → Alts ks n g
  deriving DecidableEq

/-- One member of a block. -/
inductive Decl : List Nat → Nat → Nat → Type where
  /-- One constructor with one field (e.g. `Rose.node : Array Rose → Rose`). -/
  | wrap {ks : List Nat} {n g : Nat} : Fld ks n g → Decl ks n g
  /-- One constructor with at least two fields, all grounded. -/
  | record {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g → Decl ks n g
  /-- At least two constructors, the base grounded. -/
  | union {ks : List Nat} {n g : Nat} : Alts ks n g → Decl ks n g
  deriving DecidableEq

/-- The members `g, g+1, …, n-1` of a block; member `g` may use members `< g` directly. -/
inductive Mems : List Nat → Nat → Nat → Type where
  | nil {ks : List Nat} {n : Nat} : Mems ks n n
  | cons {ks : List Nat} {n g : Nat} : Decl ks n g → Mems ks n (g + 1) → Mems ks n g
  deriving DecidableEq

/-- A datatype signature: blocks of mutually recursive datatypes, newest first.  Each block
    may use the older blocks as closed types. -/
inductive DSig : List Nat → Type where
  | nil : DSig []
  | cons {ks : List Nat} (Δ : DSig ks) (k : Nat) (bs : Mems ks (k + 1) 0) : DSig (k :: ks)

/-! ## Containers (as in `WTyToy`) -/

structure IPF (n : Nat) : Type 1 where
  A : Type
  B : A → Type
  tgt : (a : A) → B a → Fin n

def IPF.Obj {n : Nat} (P : IPF n) (X : Fin n → Type) : Type :=
  (a : P.A) × ((b : P.B a) → X (P.tgt a b))

inductive IW {k : Nat} (P : Fin k → IPF k) : Fin k → Type where
  | mk (i : Fin k) (a : (P i).A) (f : (b : (P i).B a) → IW P ((P i).tgt a b)) : IW P i

def IW.ofObj {k : Nat} {P : Fin k → IPF k} {i : Fin k} (o : (P i).Obj (IW P)) : IW P i :=
  IW.mk i o.1 o.2

def IW.dest {k : Nat} {P : Fin k → IPF k} {i : Fin k} : IW P i → (P i).Obj (IW P)
  | .mk _ a f => ⟨a, f⟩

def IPF.const {n : Nat} (A : Type) : IPF n := ⟨A, fun _ => PEmpty, fun _ b => nomatch b⟩
def IPF.prod {n : Nat} (c d : IPF n) : IPF n :=
  ⟨c.A × d.A, fun p => c.B p.1 ⊕ d.B p.2, fun p => Sum.elim (c.tgt p.1) (d.tgt p.2)⟩
def IPF.sum {n : Nat} (c d : IPF n) : IPF n :=
  ⟨c.A ⊕ d.A, Sum.elim c.B d.B, fun | .inl a => c.tgt a | .inr a => d.tgt a⟩
def IPF.opt {n : Nat} (c : IPF n) : IPF n :=
  ⟨Option c.A, fun | none => PEmpty | some a => c.B a,
    fun | none, b => nomatch b | some a, b => c.tgt a b⟩
def IPF.fn {n : Nat} (D : Type) (c : IPF n) : IPF n :=
  ⟨D → c.A, fun f => (x : D) × c.B (f x), fun f p => c.tgt (f p.1) p.2⟩
def IPF.array {n : Nat} (c : IPF n) : IPF n :=
  ⟨(m : Nat) × (Fin m → c.A), fun s => (i : Fin s.1) × c.B (s.2 i), fun s p => c.tgt (s.2 p.1) p.2⟩
def IPF.hole {n : Nat} (i : Fin n) : IPF n := ⟨PUnit, fun _ => PUnit, fun _ _ => i⟩
def IPF.consC {n : Nat} : Option (IPF n) → IPF n → IPF n
  | none, d => .opt d
  | some c, d => .sum c d
def IPF.twoC {n : Nat} : Option (IPF n) → Option (IPF n) → IPF n
  | none, none => .const Bool
  | none, some d => .opt d
  | some c, none => .opt c
  | some c, some d => .sum c d

section BodyDen
variable {ks : List Nat} (E : Ref ks → Type)

def Fld.toIPF {n g : Nat} : Fld ks n g → IPF n
  | .hole i _ => .hole i
  | .old t => .const (Ty.den E t)
  | .array f => .array (Fld.toIPF f)
  | .fn a f => .fn (Ty.den E a) (Fld.toIPF f)
def Flds.toIPF {n g : Nat} : Flds ks n g → IPF n
  | .one f => Fld.toIPF E f
  | .cons f fs => .prod (Fld.toIPF E f) (Flds.toIPF fs)
def BCtor.toIPF {n g : Nat} : BCtor ks n g → Option (IPF n)
  | .nullary => none
  | .fields fs => some (Flds.toIPF E fs)
def BCtors.toIPF {n : Nat} : BCtors ks n → IPF n
  | .two c d => .twoC (BCtor.toIPF E c) (BCtor.toIPF E d)
  | .cons c cs => .consC (BCtor.toIPF E c) (BCtors.toIPF cs)
def Alts.toIPF {n g : Nat} : Alts ks n g → IPF n
  | .two₁ c d => .twoC (BCtor.toIPF E c) (BCtor.toIPF E d)
  | .two₂ c d => .twoC (BCtor.toIPF E c) (BCtor.toIPF E d)
  | .here c cs => .consC (BCtor.toIPF E c) (BCtors.toIPF E cs)
  | .there c u => .consC (BCtor.toIPF E c) (Alts.toIPF u)
def Decl.toIPF {n g : Nat} : Decl ks n g → IPF n
  | .wrap f => Fld.toIPF E f
  | .record f fs => .prod (Fld.toIPF E f) (Flds.toIPF E fs)
  | .union u => Alts.toIPF E u
/-- The container of member `g + i` of a block. -/
def Mems.member {n g : Nat} : Mems ks n g → (i : Nat) → g + i < n → IPF n
  | .nil, _, h => absurd h (by omega)
  | .cons d _, 0, _ => Decl.toIPF E d
  | .cons _ bs, i + 1, h => Mems.member bs i (by omega)
end BodyDen

theorem Fin.zero_add_lt {k : Nat} (j : Fin k) : 0 + j.val < k := by
  have := j.isLt; omega

/-- The members of a block, as one indexed container. -/
abbrev Mems.fam {ks : List Nat} {k : Nat} (E : Ref ks → Type) (bs : Mems ks (k + 1) 0) :
    Fin (k + 1) → IPF (k + 1) :=
  fun j => Mems.member E bs j.val (Fin.zero_add_lt j)

/-- The meaning of each declared datatype: an indexed W-type over its block, whose older
    fields mean what the older signature says.  Structural recursion on the signature. -/
def DSig.refDen : {ks : List Nat} → DSig ks → Ref ks → Type
  | _, .cons Δ _ bs, .here j => IW (Mems.fam (DSig.refDen Δ) bs) j
  | _, .cons Δ _ _, .there r => DSig.refDen Δ r

/-- The meaning of a closed type over a signature. -/
abbrev Ty.Den {ks : List Nat} (Δ : DSig ks) (t : Ty ks) : Type := Ty.den (DSig.refDen Δ) t

example {ks : List Nat} (Δ : DSig ks) (k : Nat) (bs : Mems ks (k + 1) 0) (r : Ref ks) :
    Ty.Den (.cons Δ k bs) (.data (.there r)) = Ty.Den Δ (.data r) := rfl

/-! ## Unfolding: filling the holes of a body with closed types

The older closed types of a body are renamed into the target signature by `w` (weakening). -/

section Inst
variable {ks K : List Nat} (w : Ref ks → Ref K)

def Fld.inst {n g : Nat} (σ : Fin n → Ty K) : Fld ks n g → Ty K
  | .hole i _ => σ i
  | .old t => Ty.map w t
  | .array f => .array (Fld.inst σ f)
  | .fn a f => .fn (Ty.map w a) (Fld.inst σ f)
def Flds.inst {n g : Nat} (σ : Fin n → Ty K) : Flds ks n g → Fields K
  | .one f => .one (Fld.inst w σ f)
  | .cons f fs => .cons (Fld.inst w σ f) (Flds.inst σ fs)
def BCtor.inst {n g : Nat} (σ : Fin n → Ty K) : BCtor ks n g → Ctor K
  | .nullary => .nullary
  | .fields fs => .fields (Flds.inst w σ fs)
def BCtors.inst {n : Nat} (σ : Fin n → Ty K) : BCtors ks n → Ctors K
  | .two c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .cons c cs => .cons (BCtor.inst w σ c) (BCtors.inst σ cs)
def Alts.inst {n g : Nat} (σ : Fin n → Ty K) : Alts ks n g → Ctors K
  | .two₁ c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .two₂ c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .here c cs => .cons (BCtor.inst w σ c) (BCtors.inst w σ cs)
  | .there c u => .cons (BCtor.inst w σ c) (Alts.inst σ u)
def Decl.inst {n g : Nat} (σ : Fin n → Ty K) : Decl ks n g → Ty K
  | .wrap f => Fld.inst w σ f
  | .record f fs => .record (Fld.inst w σ f) (Flds.inst w σ fs)
  | .union u => .union (Alts.inst w σ u)
def Mems.instMember {n g : Nat} (σ : Fin n → Ty K) : Mems ks n g → (i : Nat) → g + i < n → Ty K
  | .nil, _, h => absurd h (by omega)
  | .cons d _, 0, _ => Decl.inst w σ d
  | .cons _ bs, i + 1, h => Mems.instMember σ bs i (by omega)
end Inst

/-- The unfolded body of member `j` of the newest block: its holes are the members themselves
    (by name), its older types are weakened. -/
abbrev Ty.unfold {ks : List Nat} {k : Nat} (bs : Mems ks (k + 1) 0) (j : Fin (k + 1)) :
    Ty (k :: ks) :=
  Mems.instMember .there (fun i => .data (.here i)) bs j.val (Fin.zero_add_lt j)

/-! ## One layer in, one layer out -/

section ObjOps
variable {n : Nat} {c d : IPF n} {X : Fin n → Type}
def IPF.Obj.inl (o : c.Obj X) : (IPF.sum c d).Obj X := ⟨.inl o.1, o.2⟩
def IPF.Obj.inr (o : d.Obj X) : (IPF.sum c d).Obj X := ⟨.inr o.1, o.2⟩
def IPF.Obj.some (o : c.Obj X) : (IPF.opt c).Obj X := ⟨.some o.1, o.2⟩
def IPF.Obj.none : (IPF.opt c).Obj X := ⟨.none, fun b => nomatch b⟩
def IPF.Obj.pair (o : c.Obj X) (o' : d.Obj X) : (IPF.prod c d).Obj X :=
  ⟨(o.1, o'.1), fun | .inl b => o.2 b | .inr b => o'.2 b⟩
def IPF.Obj.fst (o : (IPF.prod c d).Obj X) : c.Obj X := ⟨o.1.1, fun b => o.2 (.inl b)⟩
def IPF.Obj.snd (o : (IPF.prod c d).Obj X) : d.Obj X := ⟨o.1.2, fun b => o.2 (.inr b)⟩
def IPF.Obj.ofConst {A : Type} (a : A) : (IPF.const (n := n) A).Obj X := ⟨a, fun b => b.elim⟩
def IPF.Obj.caseSum : (IPF.sum c d).Obj X → c.Obj X ⊕ d.Obj X
  | ⟨.inl a, f⟩ => .inl ⟨a, f⟩
  | ⟨.inr a, f⟩ => .inr ⟨a, f⟩
def IPF.Obj.caseOpt : (IPF.opt c).Obj X → Option (c.Obj X)
  | ⟨.none, _⟩ => .none
  | ⟨.some a, f⟩ => .some ⟨a, f⟩
end ObjOps

section Roll
variable {ks K : List Nat} (w : Ref ks → Ref K) (E' : Ref K → Type) {n : Nat} (σ : Fin n → Ty K)

def Fld.roll {g : Nat} : (f : Fld ks n g) → Ty.den E' (Fld.inst w σ f) →
    (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i))
  | .hole _ _, x => ⟨PUnit.unit, fun _ => x⟩
  | .old t, x => ⟨Ty.lower w E' t x, fun b => nomatch b⟩
  | .array f, x => ⟨⟨x.1, fun i => (Fld.roll f (x.2 i)).1⟩, fun p => (Fld.roll f (x.2 p.1)).2 p.2⟩
  | .fn a f, x => ⟨fun y => (Fld.roll f (x (Ty.lift w E' a y))).1,
      fun p => (Fld.roll f (x (Ty.lift w E' a p.1))).2 p.2⟩

def Fld.unroll {g : Nat} : (f : Fld ks n g) →
    (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i)) → Ty.den E' (Fld.inst w σ f)
  | .hole _ _, x => x.2 PUnit.unit
  | .old t, x => Ty.lift w E' t x.1
  | .array f, x => ⟨x.1.1, fun i => Fld.unroll f ⟨x.1.2 i, fun q => x.2 ⟨i, q⟩⟩⟩
  | .fn a f, x => fun y => Fld.unroll f ⟨x.1 (Ty.lower w E' a y), fun q => x.2 ⟨Ty.lower w E' a y, q⟩⟩

def Flds.roll {g : Nat} : (fs : Flds ks n g) → Fields.den E' (Flds.inst w σ fs) →
    (Flds.toIPF (fun r => E' (w r)) fs).Obj (fun i => Ty.den E' (σ i))
  | .one f, x => Fld.roll w E' σ f x
  | .cons f fs, x => .pair (Fld.roll w E' σ f x.1) (Flds.roll fs x.2)

def Flds.unroll {g : Nat} : (fs : Flds ks n g) →
    (Flds.toIPF (fun r => E' (w r)) fs).Obj (fun i => Ty.den E' (σ i)) → Fields.den E' (Flds.inst w σ fs)
  | .one f, x => Fld.unroll w E' σ f x
  | .cons f fs, x => (Fld.unroll w E' σ f x.fst, Flds.unroll fs x.snd)

/-- Two constructors. -/
def BCtor.rollTwo {g g' : Nat} : (c : BCtor ks n g) → (d : BCtor ks n g') →
    twoT (Ctor.den E' (BCtor.inst w σ c)) (Ctor.den E' (BCtor.inst w σ d)) →
    (IPF.twoC (BCtor.toIPF (fun r => E' (w r)) c) (BCtor.toIPF (fun r => E' (w r)) d)).Obj
      (fun i => Ty.den E' (σ i))
  | .nullary, .nullary, x => .ofConst x
  | .nullary, .fields fd, x => match x with | .none => .none | .some a => .some (Flds.roll w E' σ fd a)
  | .fields fc, .nullary, x => match x with | .none => .none | .some a => .some (Flds.roll w E' σ fc a)
  | .fields fc, .fields fd, x =>
      match x with | .inl a => .inl (Flds.roll w E' σ fc a) | .inr b => .inr (Flds.roll w E' σ fd b)

def BCtor.unrollTwo {g g' : Nat} : (c : BCtor ks n g) → (d : BCtor ks n g') →
    (IPF.twoC (BCtor.toIPF (fun r => E' (w r)) c) (BCtor.toIPF (fun r => E' (w r)) d)).Obj
      (fun i => Ty.den E' (σ i)) →
    twoT (Ctor.den E' (BCtor.inst w σ c)) (Ctor.den E' (BCtor.inst w σ d))
  | .nullary, .nullary, x => x.1
  | .nullary, .fields fd, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Flds.unroll w E' σ fd o)
  | .fields fc, .nullary, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Flds.unroll w E' σ fc o)
  | .fields fc, .fields fd, x =>
      match x.caseSum with
      | .inl o => .inl (Flds.unroll w E' σ fc o) | .inr o => .inr (Flds.unroll w E' σ fd o)

/-- A constructor in front of the others. -/
def BCtor.rollCons {g : Nat} {R : IPF n} {RT : Type} (rest : RT → R.Obj (fun i => Ty.den E' (σ i))) :
    (c : BCtor ks n g) → consT (Ctor.den E' (BCtor.inst w σ c)) RT →
    (IPF.consC (BCtor.toIPF (fun r => E' (w r)) c) R).Obj (fun i => Ty.den E' (σ i))
  | .nullary, x => match x with | .none => .none | .some a => .some (rest a)
  | .fields fc, x => match x with | .inl a => .inl (Flds.roll w E' σ fc a) | .inr b => .inr (rest b)

def BCtor.unrollCons {g : Nat} {R : IPF n} {RT : Type} (rest : R.Obj (fun i => Ty.den E' (σ i)) → RT) :
    (c : BCtor ks n g) → (IPF.consC (BCtor.toIPF (fun r => E' (w r)) c) R).Obj (fun i => Ty.den E' (σ i)) →
    consT (Ctor.den E' (BCtor.inst w σ c)) RT
  | .nullary, x => match x.caseOpt with | .none => .none | .some o => .some (rest o)
  | .fields fc, x => match x.caseSum with
      | .inl o => .inl (Flds.unroll w E' σ fc o) | .inr o => .inr (rest o)

def BCtors.roll : (cs : BCtors ks n) → Ctors.den E' (BCtors.inst w σ cs) →
    (BCtors.toIPF (fun r => E' (w r)) cs).Obj (fun i => Ty.den E' (σ i))
  | .two c d, x => BCtor.rollTwo w E' σ c d x
  | .cons c cs, x => BCtor.rollCons w E' σ (BCtors.roll cs) c x

def BCtors.unroll : (cs : BCtors ks n) → (BCtors.toIPF (fun r => E' (w r)) cs).Obj (fun i => Ty.den E' (σ i)) →
    Ctors.den E' (BCtors.inst w σ cs)
  | .two c d, x => BCtor.unrollTwo w E' σ c d x
  | .cons c cs, x => BCtor.unrollCons w E' σ (BCtors.unroll cs) c x

def Alts.roll {g : Nat} : (u : Alts ks n g) → Ctors.den E' (Alts.inst w σ u) →
    (Alts.toIPF (fun r => E' (w r)) u).Obj (fun i => Ty.den E' (σ i))
  | .two₁ c d, x => BCtor.rollTwo w E' σ c d x
  | .two₂ c d, x => BCtor.rollTwo w E' σ c d x
  | .here c cs, x => BCtor.rollCons w E' σ (BCtors.roll w E' σ cs) c x
  | .there c u, x => BCtor.rollCons w E' σ (Alts.roll u) c x

def Alts.unroll {g : Nat} : (u : Alts ks n g) → (Alts.toIPF (fun r => E' (w r)) u).Obj (fun i => Ty.den E' (σ i)) →
    Ctors.den E' (Alts.inst w σ u)
  | .two₁ c d, x => BCtor.unrollTwo w E' σ c d x
  | .two₂ c d, x => BCtor.unrollTwo w E' σ c d x
  | .here c cs, x => BCtor.unrollCons w E' σ (BCtors.unroll w E' σ cs) c x
  | .there c u, x => BCtor.unrollCons w E' σ (Alts.unroll u) c x

def Decl.roll {g : Nat} : (d : Decl ks n g) → Ty.den E' (Decl.inst w σ d) →
    (Decl.toIPF (fun r => E' (w r)) d).Obj (fun i => Ty.den E' (σ i))
  | .wrap f, x => Fld.roll w E' σ f x
  | .record f fs, x => .pair (Fld.roll w E' σ f x.1) (Flds.roll w E' σ fs x.2)
  | .union u, x => Alts.roll w E' σ u x

def Decl.unroll {g : Nat} : (d : Decl ks n g) → (Decl.toIPF (fun r => E' (w r)) d).Obj (fun i => Ty.den E' (σ i)) →
    Ty.den E' (Decl.inst w σ d)
  | .wrap f, x => Fld.unroll w E' σ f x
  | .record f fs, x => (Fld.unroll w E' σ f x.fst, Flds.unroll w E' σ fs x.snd)
  | .union u, x => Alts.unroll w E' σ u x

def Mems.rollMember {g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    Ty.den E' (Mems.instMember w σ bs i h) →
    (Mems.member (fun r => E' (w r)) bs i h).Obj (fun j => Ty.den E' (σ j))
  | .nil, _, h, _ => absurd h (by omega)
  | .cons d _, 0, _, x => Decl.roll w E' σ d x
  | .cons _ bs, i + 1, h, x => Mems.rollMember bs i (by omega) x

def Mems.unrollMember {g : Nat} : (bs : Mems ks n g) → (i : Nat) → (h : g + i < n) →
    (Mems.member (fun r => E' (w r)) bs i h).Obj (fun j => Ty.den E' (σ j)) →
    Ty.den E' (Mems.instMember w σ bs i h)
  | .nil, _, h, _ => absurd h (by omega)
  | .cons d _, 0, _, x => Decl.unroll w E' σ d x
  | .cons _ bs, i + 1, h, x => Mems.unrollMember bs i (by omega) x
end Roll

section DataOps
variable {ks : List Nat} (Δ : DSig ks) {k : Nat} (bs : Mems ks (k + 1) 0)

/-- `Comp.data_in`: the one introduction form of every declared datatype. -/
def dataIn (j : Fin (k + 1)) (x : Ty.Den (.cons Δ k bs) (Ty.unfold bs j)) :
    Ty.Den (.cons Δ k bs) (.data (.here j)) :=
  match Mems.rollMember .there (DSig.refDen (.cons Δ k bs)) (fun i => .data (.here i)) bs j.val
      (Fin.zero_add_lt j) x with
  | ⟨a, f⟩ => IW.mk j a f

/-- `Comp.data_out`: take one layer off. -/
def dataOut (j : Fin (k + 1)) (v : Ty.Den (.cons Δ k bs) (.data (.here j))) :
    Ty.Den (.cons Δ k bs) (Ty.unfold bs j) :=
  Mems.unrollMember .there (DSig.refDen (.cons Δ k bs)) (fun i => .data (.here i)) bs j.val
    (Fin.zero_add_lt j) v.dest

def IW.fold {k : Nat} {P : Fin k → IPF k} {C : Fin k → Type}
    (alg : (i : Fin k) → (P i).Obj (fun j => IW P j × C j) → C i) :
    {i : Fin k} → IW P i → C i
  | _, .mk i a f => alg i ⟨a, fun b => (f b, IW.fold alg (f b))⟩

/-- The pair type: a record of two fields. -/
def pairTy {ks : List Nat} (a b : Ty ks) : Ty ks := .record a (.one b)

/-- `Term.data_rec`: one branch per member `j`, binding member `j`'s body with every hole `i`
    filled by the pair of the subvalue and the answer at it.  Structural recursion on the tree. -/
def dataRec (ρ : Fin (k + 1) → Ty (k :: ks))
    (branch : (j : Fin (k + 1)) →
      Ty.Den (.cons Δ k bs) (Mems.instMember .there (fun i => pairTy (.data (.here i)) (ρ i)) bs j.val
        (Fin.zero_add_lt j)) →
      Ty.Den (.cons Δ k bs) (ρ j))
    {j : Fin (k + 1)} (v : Ty.Den (.cons Δ k bs) (.data (.here j))) : Ty.Den (.cons Δ k bs) (ρ j) :=
  IW.fold (C := fun i => Ty.Den (.cons Δ k bs) (ρ i))
    (fun i x => branch i (Mems.unrollMember .there (DSig.refDen (.cons Δ k bs)) _ bs i.val
      (Fin.zero_add_lt i) ⟨x.1, x.2⟩)) v
end DataOps

/-! ## Every closed type has two distinguishable values -/

/-- Two values of `α` that a Boolean test tells apart.  Structural data, not a proof search. -/
structure Two (α : Type) where
  x : α
  y : α
  d : α → Bool
  dx : d x = true
  dy : d y = false

theorem Two.ne {α : Type} (T : Two α) : T.x ≠ T.y := fun h => by
  have := T.dx; rw [h, T.dy] at this; exact Bool.noConfusion this

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
  | .nat => ⟨(0 : Nat), (1 : Nat), fun n => Nat.beq n 0, rfl, rfl⟩
  | .bool => ⟨true, false, id, rfl, rfl⟩
  | .fn a b =>
      let e := (Ty.pick a).x
      let T := Ty.pick b
      ⟨fun _ => T.x, fun _ => T.y, fun f => T.d (f e), T.dx, T.dy⟩
  | .array t =>
      let v := (Ty.pick t).x
      ⟨⟨0, Fin.elim0⟩, ⟨1, fun _ => v⟩, fun a => Nat.beq a.1 0, rfl, rfl⟩
  | .record t fs =>
      let T := Ty.pick t
      let v := (Fields.pick fs).x
      ⟨(T.x, v), (T.y, v), fun p => T.d p.1, T.dx, T.dy⟩
  | .union cs => Ctors.pick cs
  | .data r => TE r
def Fields.pick : (fs : Fields ks) → Two (Fields.den E fs)
  | .one t => Ty.pick t
  | .cons t fs =>
      let T := Ty.pick t
      let v := (Fields.pick fs).x
      ⟨(T.x, v), (T.y, v), fun p => T.d p.1, T.dx, T.dy⟩
def Ctor.pick : (c : Ctor ks) → (Ctor.den E c).elim PUnit id
  | .nullary => PUnit.unit
  | .fields fs => (Fields.pick fs).x
def Ctors.pick : (cs : Ctors ks) → Two (Ctors.den E cs)
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
  | .array _ => ⟨⟨0, Fin.elim0⟩, fun p => p.1.elim0⟩
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
      ⟨⟨⟨0, Fin.elim0⟩, fun p => p.1.elim0⟩, ⟨⟨1, fun _ => o.1⟩, fun p => o.2 p.2⟩,
        fun o' => Nat.beq o'.1.1 0, rfl, rfl⟩
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
def BCtors.inh {n : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (cs : BCtors ks n) → (BCtors.toIPF E cs).Obj X
  | .two .nullary .nullary => .ofConst true
  | .two .nullary (.fields _) => .none
  | .two (.fields fc) .nullary => .some (Flds.inh E TE X (fun i _ => all i) fc)
  | .two (.fields fc) (.fields _) => .inl (Flds.inh E TE X (fun i _ => all i) fc)
  | .cons .nullary _ => .none
  | .cons (.fields fc) _ => .inl (Flds.inh E TE X (fun i _ => all i) fc)

/-- A union is inhabited through its base constructor. -/
def Alts.inh {n g : Nat} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (u : Alts ks n g) → (Alts.toIPF E u).Obj X
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

def BCtor.twoTwo {n g g' : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (c : BCtor ks n g) → (d : BCtor ks n g') →
    Two ((IPF.twoC (BCtor.toIPF E c) (BCtor.toIPF E d)).Obj X)
  | .nullary, .nullary => ⟨.ofConst true, .ofConst false, fun o => o.1, rfl, rfl⟩
  | .nullary, .fields fd =>
      ⟨.none, .some (Flds.inh E TE X (fun i _ => all i) fd), fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc, .nullary =>
      ⟨.some (Flds.inh E TE X (fun i _ => all i) fc), .none, fun o => o.1.isSome, rfl, rfl⟩
  | .fields fc, .fields fd =>
      ⟨.inl (Flds.inh E TE X (fun i _ => all i) fc), .inr (Flds.inh E TE X (fun i _ => all i) fd),
        fun o => o.1.isLeft, rfl, rfl⟩

def BCtor.consTwo {n g : Nat} {R : IPF n} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (r : R.Obj X) : (c : BCtor ks n g) → Two ((IPF.consC (BCtor.toIPF E c) R).Obj X)
  | .nullary => ⟨.none, .some r, fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc =>
      ⟨.inl (Flds.inh E TE X (fun i _ => all i) fc), .inr r, fun o => o.1.isLeft, rfl, rfl⟩

def Alts.two {n g : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i) :
    (u : Alts ks n g) → Two ((Alts.toIPF E u).Obj X)
  | .two₁ c d => BCtor.twoTwo E TE X all c d
  | .two₂ c d => BCtor.twoTwo E TE X all c d
  | .here c cs => BCtor.consTwo E TE X all (BCtors.inh E TE X all cs) c
  | .there c u => BCtor.consTwo E TE X all (Alts.inh E TE X (fun i _ => all i) u) c

def Decl.inh {n g : Nat} (X : Fin n → Type) (w : (i : Fin n) → i.val < g → X i) :
    (d : Decl ks n g) → (Decl.toIPF E d).Obj X
  | .wrap f => Fld.inh E TE X w f
  | .record f fs => .pair (Fld.inh E TE X w f) (Flds.inh E TE X w fs)
  | .union u => Alts.inh E TE X w u

def Decl.two {n g : Nat} (X : Fin n → Type) (all : (i : Fin n) → X i)
    (tw : (i : Fin n) → i.val < g → Two (X i)) : (d : Decl ks n g) → Two ((Decl.toIPF E d).Obj X)
  | .wrap f => Fld.two E TE X all tw f
  | .record f fs =>
      let T := Fld.two E TE X all tw f
      let os := Flds.inh E TE X (fun i _ => all i) fs
      ⟨.pair T.x os, .pair T.y os, fun o => T.d o.fst, T.dx, T.dy⟩
  | .union u => Alts.two E TE X all u

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

/-- Build a value of every member of a block, member by member, from a step that may use the
    members before it.  Structural recursion on a `Nat` bound. -/
def IW.build {k : Nat} {C : Fin k → Type}
    (step : (j : Fin k) → ((i : Fin k) → i.val < j.val → C i) → C j) : (j : Fin k) → C j :=
  fun j => go (j.val + 1) j (Nat.lt_succ_self _)
where
  go : (m : Nat) → (i : Fin k) → i.val < m → C i
    | 0, _, h => absurd h (Nat.not_lt_zero _)
    | m + 1, i, h => step i (fun i' h' => go m i' (by omega))

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
        IW.ofObj (Mems.inhMember E TE bs j.val (Fin.zero_add_lt j) (IW (Mems.fam E bs))
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _)))))
      IW.build (C := fun i => Two (IW (Mems.fam E bs) i)) (fun j acc =>
        Two.ofIW (Mems.twoMember E TE bs j.val (Fin.zero_add_lt j) (IW (Mems.fam E bs)) all
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

theorem Ty.den_exists_ne {ks : List Nat} (Δ : DSig ks) (t : Ty ks) :
    ∃ x y : Ty.Den Δ t, x ≠ y :=
  ⟨_, _, (Ty.twoDen Δ t).ne⟩

/-! ## Examples -/

/-- `Bool`-like and `Option Nat` closed types (no signature needed). -/
example : Ty.Den .nil (.union (.two .nullary .nullary)) = Bool := rfl
example : Ty.Den .nil (.union (.two .nullary (.fields (.one .nat)))) = Option Nat := rfl

/-! ### Block 1: `List Nat` -/

/-- `List Nat := nil | cons Nat List`; `nil` is the base constructor. -/
def listBody : Mems [] 1 0 :=
  .cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil

/-- The signature with one block. -/
def Δ₁ : DSig [0] := .cons .nil 0 listBody

/-- `List Nat` is a name. -/
def listNat : Ty [0] := .data (.here 0)

example : Ty.Den Δ₁ (Ty.unfold listBody 0) = Option (Nat × Ty.Den Δ₁ listNat) := rfl

def nil' : Ty.Den Δ₁ listNat := dataIn .nil listBody 0 none
def cons' (x : Nat) (xs : Ty.Den Δ₁ listNat) : Ty.Den Δ₁ listNat :=
  dataIn .nil listBody 0 (some (x, xs))

def sum' (v : Ty.Den Δ₁ listNat) : Nat :=
  dataRec .nil listBody (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × (Ty.Den Δ₁ listNat × Nat))) with
        | none => 0
        | some (n, _, r) => Nat.add n r
      r) v

example : sum' (cons' 1 (cons' 2 (cons' 3 nil'))) = 6 := rfl

def head? (v : Ty.Den Δ₁ listNat) : Option Nat :=
  match (dataOut .nil listBody 0 v : Option (Nat × Ty.Den Δ₁ listNat)) with
  | none => none
  | some (n, _) => some n

example : head? (cons' 7 nil') = some 7 := rfl
example : head? nil' = none := rfl

/-- The two values the structural proof picks for `List Nat`: `[]` and `[0]`. -/
example : head? (Ty.twoDen Δ₁ listNat).x = none := rfl
example : head? (Ty.twoDen Δ₁ listNat).y = some 0 := rfl

/-! ### Block 2: `LitExprS` with `swap`, and a rose tree that stores `List Nat`s

Member `0` is `LitExprS (Nat × Bool)`, member `1` is `LitExprS (Bool × Nat)`, member `2` is
`Rose := node (List Nat) (Array Rose)`.  The older `List Nat` is used by name through `old`. -/

def block₂ : Mems [0] 3 0 :=
  .cons (.union (.here (.fields (.one (.old (pairTy .nat .bool))))
          (.two (.fields (.cons (.old .nat) (.one (.old .bool)))) (.fields (.one (.hole 1 (by decide)))))))
  (.cons (.union (.here (.fields (.one (.old (pairTy .bool .nat))))
          (.two (.fields (.cons (.old .bool) (.one (.old .nat)))) (.fields (.one (.hole 0 (by decide)))))))
  (.cons (.record (.old listNat) (.one (.array (.hole 2 (by decide)))))
  .nil))

def Δ₂ : DSig [2, 0] := .cons Δ₁ 2 block₂

/-- Names in the bigger signature. -/
def litSNB : Ty [2, 0] := .data (.here 0)
def litSBN : Ty [2, 0] := .data (.here 1)
def rose : Ty [2, 0] := .data (.here 2)
def listNat₂ : Ty [2, 0] := .data (.there (.here 0))

/-- **Canonical by name**: `List Nat` weakened into the bigger signature is literally the
    name `List Nat` there, and the rose tree's field has that type. -/
example : (Ty.weaken listNat : Ty [2, 0]) = listNat₂ := rfl
example : Ty.unfold block₂ 2 = .record listNat₂ (.one (.array rose)) := rfl
/-- …and old values are values in the bigger signature, with no conversion. -/
example : Ty.Den Δ₂ listNat₂ = Ty.Den Δ₁ listNat := rfl

example : Ty.Den Δ₂ (Ty.unfold block₂ 0) =
    ((Nat × Bool) ⊕ ((Nat × Bool) ⊕ Ty.Den Δ₂ litSBN)) := rfl
example : Ty.Den Δ₂ (Ty.unfold block₂ 2) =
    (Ty.Den Δ₁ listNat × ((m : Nat) × (Fin m → Ty.Den Δ₂ rose))) := rfl

/-- The answer type of each member (`eval : LitExprS α → α`; the rose tree's sum). -/
def answer₂ : Fin 3 → Ty [2, 0]
  | ⟨0, _⟩ => pairTy .nat .bool
  | ⟨1, _⟩ => pairTy .bool .nat
  | ⟨2, _⟩ => .nat

def litS_litBN (b : Bool) (a : Nat) : Ty.Den Δ₂ litSBN := dataIn Δ₁ block₂ 1 (.inl (b, a))
def litS_swap (e : Ty.Den Δ₂ litSBN) : Ty.Den Δ₂ litSNB := dataIn Δ₁ block₂ 0 (.inr (.inr e))
def rose_node (xs : Ty.Den Δ₁ listNat) (m : Nat) (cs : Fin m → Ty.Den Δ₂ rose) : Ty.Den Δ₂ rose :=
  dataIn Δ₁ block₂ 2 (xs, ⟨m, cs⟩)

/-- Sum over `Fin m`, by `Nat` recursion. -/
def finSum : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => Nat.add (f ⟨m, Nat.lt_succ_self m⟩) (finSum m (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))

/-- One fold for the whole block, answering a different type at each member; the rose tree's
    branch calls the *older* block's fold `sum'` on its `List Nat` field. -/
def eval₂ {j : Fin 3} (v : Ty.Den Δ₂ (.data (.here j))) : Ty.Den Δ₂ (answer₂ j) :=
  dataRec Δ₁ block₂ answer₂ (fun
    | ⟨0, _⟩, x =>
      let r : Nat × Bool :=
        match (x : (Nat × Bool) ⊕ ((Nat × Bool) ⊕ (Ty.Den Δ₂ litSBN × (Bool × Nat)))) with
        | .inl p => p
        | .inr (.inl p) => p
        | .inr (.inr (_, (b, a))) => (a, b)
      r
    | ⟨1, _⟩, x =>
      let r : Bool × Nat :=
        match (x : (Bool × Nat) ⊕ ((Bool × Nat) ⊕ (Ty.Den Δ₂ litSNB × (Nat × Bool)))) with
        | .inl p => p
        | .inr (.inl p) => p
        | .inr (.inr (_, (a, b))) => (b, a)
      r
    | ⟨2, _⟩, x =>
      let r : Nat :=
        match (x : Ty.Den Δ₁ listNat × ((m : Nat) × (Fin m → Ty.Den Δ₂ rose × Nat))) with
        | (xs, ⟨m, cs⟩) => Nat.add (sum' xs) (finSum m (fun i => (cs i).2))
      r) v

example : eval₂ (j := 0) (litS_swap (litS_litBN true 3)) = ((3, true) : Nat × Bool) := rfl
example :
    eval₂ (j := 2) (rose_node (cons' 1 nil') 2 (fun
      | ⟨0, _⟩ => rose_node (cons' 10 (cons' 20 nil')) 0 Fin.elim0
      | ⟨1, _⟩ => rose_node nil' 0 Fin.elim0)) = (31 : Nat) := rfl

/-- `Ty.twoDen` in the bigger signature: the rose tree's two values differ in their list. -/
example : head? (Ty.twoDen Δ₂ rose).x.dest.1.1 = none := rfl
example : head? (Ty.twoDen Δ₂ rose).y.dest.1.1 = some 0 := rfl

/-! ## What can no longer be written

Each attempt below is rejected by the type checker; `#guard_msgs` pins the error. -/

-- `μX. X`: member `0` may use no hole outside a guard.
/--
error: Tactic `decide` proved that the proposition
  ↑0 < 0
is false
-/
#guard_msgs in
example : Mems [] 1 0 := .cons (.wrap (.hole 0 (by decide))) .nil

-- `μX. Nat × X` (no base case): every field of a record is a grounded position.
/--
error: Tactic `decide` proved that the proposition
  ↑0 < 0
is false
-/
#guard_msgs in
example : Mems [] 1 0 := .cons (.record (.old .nat) (.one (.hole 0 (by decide)))) .nil

-- A one-constructor union, closed or declared: there is no such form.
/--
error: Unknown constant `NomTyToy.Ctors.one`

Note: Inferred this name from the expected resulting type of `.one`:
  Ctors []
-/
#guard_msgs in
example : Ty [] := .union (.one .nullary)

-- A declared type cannot use itself as a closed type: the block is not in its own signature.
/--
error: Application type mismatch: The argument
  listNat
has type
  Ty [0]
but is expected to have type
  Ty []
in the application
  Fld.old listNat
-/
#guard_msgs in
example : Mems [] 1 0 := .cons (.wrap (.old listNat)) .nil

end NomTyToy
end
