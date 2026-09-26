module

public import LeanScript.Nominal.Decl
public import LeanScript.Nominal.Container

@[expose] public section

set_option autoImplicit false

/-!
# The meaning of closed types and of declared datatypes

Step 3 of design **N** of `proposals/NominalTyProposal.md` (§2.3, §2.5).

* `Ty.den E t` — the Lean type a closed type denotes, given the meaning `E` of the declared
  datatypes.  Structural recursion on the type.
* `DSig.refDen Δ r` — the meaning of a declared datatype: an indexed W-type over its block,
  whose older fields mean what the older signature says.  Structural recursion on the
  signature.
* `Ty.Den Δ t := Ty.den (DSig.refDen Δ) t`.

A value of an older datatype is a value in every extension of the signature, with no
conversion: `Ty.Den (.cons Δ k bs) (.data (.there r)) = Ty.Den Δ (.data r)` by `rfl`.

The three operations on declared datatypes are here too, at every block of the signature
(not only the newest one): `DSig.dataIn` (one layer in), `DSig.dataOut` (one layer out)
and `DSig.dataRec` (the fold, with a different answer type per member).  They are
structural, need no cast and compute by `rfl`.  The older fields of a body are read through
the structural transports `Ty.lift`/`Ty.lower`, which are the identity on datatype values.
-/

namespace LeanScript

namespace Nominal

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
  | .prim p _ => p.denote
  | .fn a b => Ty.den E a → Ty.den E b
  | .array t => Array (Ty.den E t)
  | .thunk t => Ty.den E t
  | .lazy t => Ty.den E t
  | .enum s => Fin s.nOfConstructors
  | .record t fs => Ty.den E t × Fields.den E fs
  | .union cs => Ctors.den E cs
  | .data r => E r
/-- The meaning of fields: a nested product. -/
def Fields.den {ks : List Nat} (E : Ref ks → Type) : Fields ks → Type
  | .one t => Ty.den E t
  | .cons t fs => Ty.den E t × Fields.den E fs
/-- The payload of a constructor, if it has fields. -/
def Ctor.den {ks : List Nat} (E : Ref ks → Type) : Ctor ks → Option Type
  | .nullary => none
  | .fields fs => some (Fields.den E fs)
/-- The meaning of constructors: a nested sum, `Option` for a constructor without fields. -/
def Ctors.den {ks : List Nat} (E : Ref ks → Type) : Ctors ks → Type
  | .two c d => twoT (Ctor.den E c) (Ctor.den E d)
  | .cons c cs => consT (Ctor.den E c) (Ctors.den E cs)
end

/-! ## Renaming and its transports -/

section Transport
variable {ks ks' : List Nat} (f : Ref ks → Ref ks') (E : Ref ks' → Type)

mutual
/-- A value of `t` (datatypes read through `f`) is a value of the renamed type.  Structural,
    the identity on declared datatypes. -/
def Ty.lift : (t : Ty ks) → Ty.den (fun r => E (f r)) t → Ty.den E (Ty.map f t)
  | .prim _ _, x => x
  | .fn a b, x => fun y => Ty.lift b (x (Ty.lower a y))
  | .array t, x => x.map (Ty.lift t)
  | .thunk t, x => Ty.lift t x
  | .lazy t, x => Ty.lift t x
  | .enum _, x => x
  | .record t fs, x => (Ty.lift t x.1, Fields.lift fs x.2)
  | .union cs, x => Ctors.lift cs x
  | .data _, x => x
/-- The inverse of `Ty.lift`. -/
def Ty.lower : (t : Ty ks) → Ty.den E (Ty.map f t) → Ty.den (fun r => E (f r)) t
  | .prim _ _, x => x
  | .fn a b, x => fun y => Ty.lower b (x (Ty.lift a y))
  | .array t, x => x.map (Ty.lower t)
  | .thunk t, x => Ty.lower t x
  | .lazy t, x => Ty.lower t x
  | .enum _, x => x
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

/-! ## Bodies as containers -/

section BodyDen
variable {ks : List Nat} (E : Ref ks → Type)

/-- The container of a field. -/
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

/-- The members of a block, as one indexed container. -/
abbrev Mems.fam {ks : List Nat} {k : Nat} (E : Ref ks → Type) (bs : Mems ks (k + 1) 0) :
    Fin (k + 1) → IPF (k + 1) :=
  fun j => Mems.member E bs j.val (Fin.zero_add_lt' j)

/-- The meaning of each declared datatype: an indexed W-type over its block, whose older
    fields mean what the older signature says.  Structural recursion on the signature. -/
def DSig.refDen : {ks : List Nat} → DSig ks → Ref ks → Type
  | _, .cons Δ _ bs, .here j => IW (Mems.fam (DSig.refDen Δ) bs) j
  | _, .cons Δ _ _, .there r => DSig.refDen Δ r

/-- The meaning of a closed type over a signature. -/
abbrev Ty.Den {ks : List Nat} (Δ : DSig ks) (t : Ty ks) : Type := Ty.den (DSig.refDen Δ) t

example {ks : List Nat} (Δ : DSig ks) (k : Nat) (bs : Mems ks (k + 1) 0) (r : Ref ks) :
    Ty.Den (.cons Δ k bs) (.data (.there r)) = Ty.Den Δ (.data r) := rfl

/-! ## Rolling and unrolling one layer -/

section Roll
variable {ks K : List Nat} (w : Ref ks → Ref K) (E' : Ref K → Type) {n : Nat} (σ : Fin n → Ty K)

def Fld.roll {g : Nat} : (f : Fld ks n g) → Ty.den E' (Fld.inst w σ f) →
    (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i))
  | .hole _ _, x => ⟨PUnit.unit, fun _ => x⟩
  | .old t, x => ⟨Ty.lower w E' t x, fun b => nomatch b⟩
  | .array f, x =>
      let o := listRoll (fun d => Fld.roll f d) x.toList
      ⟨⟨o.1⟩, o.2⟩
  | .fn a f, x => ⟨fun y => (Fld.roll f (x (Ty.lift w E' a y))).1,
      fun p => (Fld.roll f (x (Ty.lift w E' a p.1))).2 p.2⟩

def Fld.unroll {g : Nat} : (f : Fld ks n g) →
    (Fld.toIPF (fun r => E' (w r)) f).Obj (fun i => Ty.den E' (σ i)) → Ty.den E' (Fld.inst w σ f)
  | .hole _ _, x => x.2 PUnit.unit
  | .old t, x => Ty.lift w E' t x.1
  | .array f, x => ⟨listUnroll (fun o => Fld.unroll f o) x.1.toList x.2⟩
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

/-! ## Finding a block in a signature

`DSig.block Δ b` finds block `b` of `Δ` together with the renaming `w` of its own names into
the whole signature, and the two (identity) transports between the whole signature's reading
of its members and the block's W-type.  Each step of the recursion is the identity function:
the transports type-check by unfolding `DSig.refDen`, so nothing is cast. -/

/-- Block `b` of a signature `Δ`, seen from `Δ`. -/
structure DSig.Block {ks : List Nat} (Δ : DSig ks) where
  /-- The signature the block was declared over. -/
  ks' : List Nat
  /-- The block has `k + 1` members. -/
  k : Nat
  /-- The member declarations. -/
  bs : Mems ks' (k + 1) 0
  /-- The block's own names (its members, then the older datatypes), in `Δ`. -/
  w : Ref (k :: ks') → Ref ks
  /-- A value of member `i`, as a tree of the block's W-type. -/
  toIW : (i : Fin (k + 1)) → DSig.refDen Δ (w (.here i)) →
    IW (Mems.fam (fun r => DSig.refDen Δ (w (.there r))) bs) i
  /-- A tree of the block's W-type, as a value of member `i`. -/
  ofIW : (i : Fin (k + 1)) → IW (Mems.fam (fun r => DSig.refDen Δ (w (.there r))) bs) i →
    DSig.refDen Δ (w (.here i))

/-- Find a block of a signature.  Structural recursion on the signature. -/
def DSig.block : {ks : List Nat} → (Δ : DSig ks) → BRef ks → Δ.Block
  | _, .cons _ k bs, .here => ⟨_, k, bs, id, fun _ x => x, fun _ x => x⟩
  | _, .cons Δ _ _, .there b =>
      let B := DSig.block Δ b
      ⟨B.ks', B.k, B.bs, fun r => .there (B.w r), B.toIW, B.ofIW⟩

namespace DSig.Block
variable {ks : List Nat} {Δ : DSig ks} (B : Δ.Block)

/-- Member `i` of the block, as a name in `Δ`. -/
abbrev ref (i : Fin (B.k + 1)) : Ref ks := B.w (.here i)

/-- The renaming of the block's older datatypes into `Δ`. -/
abbrev old : Ref B.ks' → Ref ks := fun r => B.w (.there r)

/-- Member `j`'s body instantiated by `σ`, in `Δ`. -/
abbrev inst (σ : Fin (B.k + 1) → Ty ks) (j : Fin (B.k + 1)) : Ty ks := Mems.inst B.old σ B.bs j

/-- The unfolded body of member `j`: its holes are the members, by name. -/
abbrev unfold (j : Fin (B.k + 1)) : Ty ks := B.inst (fun i => .data (B.ref i)) j

/-- The body of member `j` for a fold with answer types `ρ`: each hole `i` is the pair of the
    subvalue and the answer at it. -/
abbrev recBody (ρ : Fin (B.k + 1) → Ty ks) (j : Fin (B.k + 1)) : Ty ks :=
  B.inst (fun i => Ty.pair (.data (B.ref i)) (ρ i)) j

end DSig.Block

section DataOps
variable {ks : List Nat} (Δ : DSig ks)

/-- One layer in: the introduction form of every declared datatype. -/
def DSig.dataIn (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (x : Ty.Den Δ ((Δ.block b).unfold j)) : Ty.Den Δ (.data ((Δ.block b).ref j)) :=
  let B := Δ.block b
  let o := Mems.rollMember B.old (DSig.refDen Δ) (fun i => .data (B.ref i)) B.bs j.val
    (Fin.zero_add_lt' j) x
  B.ofIW j (IW.mk j o.1 (fun p => B.toIW _ (o.2 p)))

/-- One layer out. -/
def DSig.dataOut (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (v : Ty.Den Δ (.data ((Δ.block b).ref j))) : Ty.Den Δ ((Δ.block b).unfold j) :=
  let B := Δ.block b
  Mems.unrollMember B.old (DSig.refDen Δ) (fun i => .data (B.ref i)) B.bs j.val
    (Fin.zero_add_lt' j) ((B.toIW j v).dest.map (fun i y => B.ofIW i y))

/-- The fold over a block: one branch per member `j`, given member `j`'s body with every hole
    `i` filled by the pair of the subvalue and the answer at it.  Structural recursion on the
    tree. -/
def DSig.dataRec (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
    (branch : (j : Fin ((Δ.block b).k + 1)) → Ty.Den Δ ((Δ.block b).recBody ρ j) → Ty.Den Δ (ρ j))
    (j : Fin ((Δ.block b).k + 1)) (v : Ty.Den Δ (.data ((Δ.block b).ref j))) : Ty.Den Δ (ρ j) :=
  let B := Δ.block b
  IW.fold (C := fun i => Ty.Den Δ (ρ i))
    (fun i x => branch i (Mems.unrollMember B.old (DSig.refDen Δ)
      (fun i' => Ty.pair (.data (B.ref i')) (ρ i')) B.bs i.val (Fin.zero_add_lt' i)
      (x.map (fun i' y => (B.ofIW i' y.1, y.2)))))
    (B.toIW j v)

end DataOps

end Nominal

end LeanScript

end
