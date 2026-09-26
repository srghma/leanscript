module

public import Init

@[expose] public section

set_option autoImplicit false

/-!
# Indexed containers and indexed W-types

The meaning of a block of declared datatypes (`LeanScript.Nominal.DSig.refDen`) is an
indexed W-type `IW P` over an indexed container `P : Fin n → IPF n`: one shape per layer,
and one subtree per position of the shape.  Everything here is structural recursion and
computes by `rfl`; there is no quotient, no `cast` and no fuel.
-/

namespace LeanScript

namespace Nominal

/-- An indexed polynomial functor over `n` sorts: shapes, positions of a shape, and the sort
    of the subtree at each position. -/
structure IPF (n : Nat) : Type 1 where
  A : Type
  B : A → Type
  tgt : (a : A) → B a → Fin n

/-- The functor applied to a family of types: a shape and one value per position. -/
def IPF.Obj {n : Nat} (P : IPF n) (X : Fin n → Type) : Type :=
  (a : P.A) × ((b : P.B a) → X (P.tgt a b))

/-- The indexed W-type: finite trees of layers. -/
inductive IW {k : Nat} (P : Fin k → IPF k) : Fin k → Type where
  | mk (i : Fin k) (a : (P i).A) (f : (b : (P i).B a) → IW P ((P i).tgt a b)) : IW P i

/-- Put one layer on. -/
def IW.ofObj {k : Nat} {P : Fin k → IPF k} {i : Fin k} (o : (P i).Obj (IW P)) : IW P i :=
  IW.mk i o.1 o.2

/-- Take one layer off. -/
def IW.dest {k : Nat} {P : Fin k → IPF k} {i : Fin k} : IW P i → (P i).Obj (IW P)
  | .mk _ a f => ⟨a, f⟩

/-- The fold (a recursor with a non-dependent motive that also sees the subtrees). -/
def IW.fold {k : Nat} {P : Fin k → IPF k} {C : Fin k → Type}
    (alg : (i : Fin k) → (P i).Obj (fun j => IW P j × C j) → C i) :
    {i : Fin k} → IW P i → C i
  | _, .mk i a f => alg i ⟨a, fun b => (f b, IW.fold alg (f b))⟩

/-- Build a value of every sort, sort by sort, from a step that may use the sorts before
    it.  Structural recursion on a `Nat` bound. -/
def IW.build {k : Nat} {C : Fin k → Type}
    (step : (j : Fin k) → ((i : Fin k) → i.val < j.val → C i) → C j) : (j : Fin k) → C j :=
  fun j => go (j.val + 1) j (Nat.lt_succ_self _)
where
  go : (m : Nat) → (i : Fin k) → i.val < m → C i
    | 0, _, h => absurd h (Nat.not_lt_zero _)
    | m + 1, i, h => step i (fun i' h' => go m i' (by omega))

/-! ## Building containers -/

/-- A constant: no position. -/
def IPF.const {n : Nat} (A : Type) : IPF n := ⟨A, fun _ => PEmpty, fun _ b => nomatch b⟩
/-- A pair of layers. -/
def IPF.prod {n : Nat} (c d : IPF n) : IPF n :=
  ⟨c.A × d.A, fun p => c.B p.1 ⊕ d.B p.2, fun p => Sum.elim (c.tgt p.1) (d.tgt p.2)⟩
/-- A choice of layers. -/
def IPF.sum {n : Nat} (c d : IPF n) : IPF n :=
  ⟨c.A ⊕ d.A, Sum.elim c.B d.B, fun | .inl a => c.tgt a | .inr a => d.tgt a⟩
/-- One extra constructor with no fields: `Option`, not `PUnit ⊕ _`. -/
def IPF.opt {n : Nat} (c : IPF n) : IPF n :=
  ⟨Option c.A, fun | none => PEmpty | some a => c.B a,
    fun | none, b => nomatch b | some a, b => c.tgt a b⟩
/-- A function from a fixed domain. -/
def IPF.fn {n : Nat} (D : Type) (c : IPF n) : IPF n :=
  ⟨D → c.A, fun f => (x : D) × c.B (f x), fun f p => c.tgt (f p.1) p.2⟩
/-- A subtree of sort `i`. -/
def IPF.hole {n : Nat} (i : Fin n) : IPF n := ⟨PUnit, fun _ => PUnit, fun _ _ => i⟩

/-- The positions of a list of shapes: the positions of its elements, one after the other.
    Structural recursion on the list, so it computes on a list built with `::`. -/
def ListPos {n : Nat} (c : IPF n) : List c.A → Type
  | [] => PEmpty
  | a :: as => c.B a ⊕ ListPos c as

/-- The sort at a position of a list of shapes. -/
def ListPos.tgt {n : Nat} (c : IPF n) : (s : List c.A) → ListPos c s → Fin n
  | [], b => nomatch b
  | a :: _, .inl b => c.tgt a b
  | _ :: as, .inr b => ListPos.tgt c as b

/-- `Array`: the shape is the array of the elements' shapes. -/
def IPF.array {n : Nat} (c : IPF n) : IPF n :=
  ⟨Array c.A, fun s => ListPos c s.toList, fun s => ListPos.tgt c s.toList⟩

/-- A constructor in front of the others; a constructor with no fields adds `Option`. -/
def IPF.consC {n : Nat} : Option (IPF n) → IPF n → IPF n
  | none, d => .opt d
  | some c, d => .sum c d
/-- Exactly two constructors. -/
def IPF.twoC {n : Nat} : Option (IPF n) → Option (IPF n) → IPF n
  | none, none => .const Bool
  | none, some d => .opt d
  | some c, none => .opt c
  | some c, some d => .sum c d

/-! ## One layer: building and taking apart -/

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
/-- Change the values at the positions. -/
def IPF.Obj.map {Y : Fin n → Type} (g : (i : Fin n) → X i → Y i) (o : c.Obj X) : c.Obj Y :=
  ⟨o.1, fun b => g _ (o.2 b)⟩
end ObjOps

section ListOps
variable {n : Nat} {c : IPF n} {X : Fin n → Type} {D : Type}

/-- Take a list of values apart into a list of shapes and its positions. -/
def listRoll (f : D → c.Obj X) : List D → ((s : List c.A) × ((b : ListPos c s) → X (ListPos.tgt c s b)))
  | [] => ⟨[], fun b => nomatch b⟩
  | d :: ds =>
      let o := f d
      let os := listRoll f ds
      ⟨o.1 :: os.1, fun | .inl b => o.2 b | .inr b => os.2 b⟩

/-- Put a list of values back together from its shapes and positions. -/
def listUnroll (f : c.Obj X → D) : (s : List c.A) → ((b : ListPos c s) → X (ListPos.tgt c s b)) →
    List D
  | [], _ => []
  | a :: as, g => f ⟨a, fun b => g (.inl b)⟩ :: listUnroll f as (fun b => g (.inr b))

end ListOps

end Nominal

end LeanScript

end
