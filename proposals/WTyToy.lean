module

/-!
# Toy model for `proposals/WTypeTyProposal.md` (hardened: no unit-like, no empty-like types)

Self-contained (no imports, not part of the Lake build).  Check it with the bare compiler:

```
lean proposals/WTyToy.lean
```

What it checks, at toy scale:

* **`Ty n g`**: a type in a scope of `n` recursive holes, of which the first `g` are
  *grounded* (already known to have values).  A hole may appear directly (`var i (h : i < g)`)
  only if it is grounded; any hole may appear under a *guard*: an `array` element or a
  constructor other than the union's base constructor (fields of type `Ty n n`).
* **Three different containers**: `array` (Lean's `Array`), `list` (Lean's `List`) and
  `finFn` (`(m : Nat) × (Fin m → A)`).  A closed `array nat` means `Array Nat`; the rose trees
  `node : List Rose → Rose`, `node : Array Rose → Rose` and
  `node : (m : Nat) → (Fin m → Rose) → Rose` are three different accepted types, whose
  unfoldings are `List Rose`, `Array Rose` and `(m : Nat) × (Fin m → Rose)`, and whose node
  counts by `muRec` compute by `rfl`.
* **No unit-like and no empty-like type can be written**, by construction:
  - a record has at least two fields, a union at least two constructors (`Alts`, `Ctors`), and
    there is no unit type at all; a constructor without fields adds `Option`, not `PUnit ⊕ _`;
  - a union names a *base constructor* whose fields only use grounded holes;
  - member `j` of a `mu` is a `Ty (k+1) j`: it may use members `< j` directly, members `≥ j`
    only under a guard.  So `μX. X`, `μX. Nat × X`, and the old `unitTy` do not typecheck
    (pinned below with `#guard_msgs`).
* **`Ty.twoDen : (t : Ty 0 0) → Two (Ty.Den t)`**: two values of every closed type and a Boolean
  test that tells them apart, by structural recursion on the type (for a `mu`, member by member,
  by structural recursion on a `Nat` bound).  No fuel, no measure, no well-formedness predicate.
  Consequences: `Ty.den_nonempty`, `Ty.den_not_subsingleton`, `Ty.den_exists_ne`.
* The kernel accepts the indexed mutual `Ty` and `DecidableEq` derives for it.
* `Ty.Den`, instantiation, `muIn`, `muOut` and the one fold `muRec` are structurally recursive,
  need no cast, and compute by `rfl` (`List Nat`: `sum [1,2,3] = 6`, `head? [7] = some 7`; the
  two-member `LitExprS` family with `swap`: `eval (swap (lit (true, 3))) = (3, true)`).
-/

@[expose] public section

namespace WTyToy

mutual
/-- A type in a scope with `n` recursive holes, the first `g` of which are grounded. -/
inductive Ty : Nat → Nat → Type where
  /-- A grounded hole: member `i` of the innermost `mu`, with `i < g`. -/
  | var {n g : Nat} (i : Fin n) : i.val < g → Ty n g
  /-- A closed type used inside a scope (weakening as a constructor). -/
  | closed {n g : Nat} : Ty 0 0 → Ty n g
  | nat {n g : Nat} : Ty n g
  | bool {n g : Nat} : Ty n g
  /-- The domain is closed (strict positivity, by typing); the codomain stays grounded. -/
  | fn {n g : Nat} : Ty 0 0 → Ty n g → Ty n g
  /-- A Lean `Array`.  The element is guarded (the empty array is always a value), so it sees
      every hole.  Denotes `Array A`, and unfolds to an honest `Array` of the recursive type. -/
  | array {n g : Nat} : Ty n n → Ty n g
  /-- A Lean `List`, guarded like `array`.  Denotes `List A`. -/
  | list {n g : Nat} : Ty n n → Ty n g
  /-- A length and a function on `Fin length`, guarded like `array`: `(m : Nat) × (Fin m → A)`.
      This is what a constructor `node : (m : Nat) → (Fin m → T) → T` becomes.  It is a
      different type from `array`, on purpose. -/
  | finFn {n g : Nat} : Ty n n → Ty n g
  /-- At least two fields. -/
  | record {n g : Nat} : Ty n g → Fields n g → Ty n g
  /-- At least two constructors, one of them grounded. -/
  | union {n g : Nat} : Alts n g → Ty n g
  /-- An indexed W-type with `k + 1` members; member `j`'s body is a `Ty (k + 1) j`. -/
  | mu {n g : Nat} (k : Nat) : Mems (k + 1) 0 → Fin (k + 1) → Ty n g
/-- One or more fields. -/
inductive Fields : Nat → Nat → Type where
  | one {n g : Nat} : Ty n g → Fields n g
  | cons {n g : Nat} : Ty n g → Fields n g → Fields n g
/-- A constructor: no fields, or one or more fields. -/
inductive Ctor : Nat → Nat → Type where
  | nullary {n g : Nat} : Ctor n g
  | fields {n g : Nat} : Fields n g → Ctor n g
/-- Two or more constructors, all guarded. -/
inductive Ctors : Nat → Type where
  | two {n : Nat} : Ctor n n → Ctor n n → Ctors n
  | cons {n : Nat} : Ctor n n → Ctors n → Ctors n
/-- Two or more constructors, one of which (the base) is grounded. -/
inductive Alts : Nat → Nat → Type where
  | two₁ {n g : Nat} : Ctor n g → Ctor n n → Alts n g
  | two₂ {n g : Nat} : Ctor n n → Ctor n g → Alts n g
  | here {n g : Nat} : Ctor n g → Ctors n → Alts n g
  | there {n g : Nat} : Ctor n n → Alts n g → Alts n g
/-- The bodies of members `g, g+1, …, n-1`; member `g` may use members `< g` directly. -/
inductive Mems : Nat → Nat → Type where
  | nil {n : Nat} : Mems n n
  | cons {n g : Nat} : Ty n g → Mems n (g + 1) → Mems n g
end

deriving instance DecidableEq for Ty, Fields, Ctor, Ctors, Alts, Mems

example : DecidableEq (Ty 0 0) := inferInstance

/-! ## Containers -/

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
/-- One extra constructor with no fields: `Option`, not `PUnit ⊕ _`. -/
def IPF.opt {n : Nat} (c : IPF n) : IPF n :=
  ⟨Option c.A, fun | none => PEmpty | some a => c.B a,
    fun | none, b => nomatch b | some a, b => c.tgt a b⟩
def IPF.fn {n : Nat} (D : Type) (c : IPF n) : IPF n :=
  ⟨D → c.A, fun f => (x : D) × c.B (f x), fun f p => c.tgt (f p.1) p.2⟩
def IPF.finFn {n : Nat} (c : IPF n) : IPF n :=
  ⟨(m : Nat) × (Fin m → c.A), fun s => (i : Fin s.1) × c.B (s.2 i), fun s p => c.tgt (s.2 p.1) p.2⟩

/-- The positions of a list of shapes: the positions of its elements, one after the other.
    Structural recursion on the list, so it computes on a list built with `::` and needs no cast. -/
def ListPos {n : Nat} (c : IPF n) : List c.A → Type
  | [] => PEmpty
  | a :: as => c.B a ⊕ ListPos c as

def ListPos.tgt {n : Nat} (c : IPF n) : (s : List c.A) → ListPos c s → Fin n
  | [], b => nomatch b
  | a :: _, .inl b => c.tgt a b
  | _ :: as, .inr b => ListPos.tgt c as b

/-- `List`: the shape is the list of the elements' shapes. -/
def IPF.list {n : Nat} (c : IPF n) : IPF n := ⟨List c.A, ListPos c, ListPos.tgt c⟩
/-- `Array`: the shape is the array of the elements' shapes. -/
def IPF.array {n : Nat} (c : IPF n) : IPF n :=
  ⟨Array c.A, fun s => ListPos c s.toList, fun s => ListPos.tgt c s.toList⟩

section ListOps
variable {n : Nat} {c : IPF n} {X : Fin n → Type} {D : Type}

/-- Take a list of values apart into a list of shapes and its positions. -/
def listRoll (f : D → c.Obj X) : List D → (IPF.list c).Obj X
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
/-- Put a constructor in front of the others; a constructor with no fields adds `Option`. -/
def IPF.consC {n : Nat} : Option (IPF n) → IPF n → IPF n
  | none, d => .opt d
  | some c, d => .sum c d
/-- Exactly two constructors. -/
def IPF.twoC {n : Nat} : Option (IPF n) → Option (IPF n) → IPF n
  | none, none => .const Bool
  | none, some d => .opt d
  | some c, none => .opt c
  | some c, some d => .sum c d

theorem Fin.zero_add_lt {k : Nat} (j : Fin k) : 0 + j.val < k := by
  have := j.isLt; omega

mutual
def Ty.toIPF : {n g : Nat} → Ty n g → IPF n
  | _, _, .var i _ => ⟨PUnit, fun _ => PUnit, fun _ _ => i⟩
  | _, _, .closed t => .const (Ty.toIPF t).A
  | _, _, .nat => .const Nat
  | _, _, .bool => .const Bool
  | _, _, .fn a b => .fn (Ty.toIPF a).A (Ty.toIPF b)
  | _, _, .array t => .array (Ty.toIPF t)
  | _, _, .list t => .list (Ty.toIPF t)
  | _, _, .finFn t => .finFn (Ty.toIPF t)
  | _, _, .record t fs => .prod (Ty.toIPF t) (Fields.toIPF fs)
  | _, _, .union u => Alts.toIPF u
  | _, _, .mu k bs s => .const (IW (fun j : Fin (k + 1) => Mems.member bs j.val (Fin.zero_add_lt j)) s)
def Fields.toIPF : {n g : Nat} → Fields n g → IPF n
  | _, _, .one t => Ty.toIPF t
  | _, _, .cons t fs => .prod (Ty.toIPF t) (Fields.toIPF fs)
def Ctor.toIPF : {n g : Nat} → Ctor n g → Option (IPF n)
  | _, _, .nullary => none
  | _, _, .fields fs => some (Fields.toIPF fs)
def Ctors.toIPF : {n : Nat} → Ctors n → IPF n
  | _, .two c d => .twoC (Ctor.toIPF c) (Ctor.toIPF d)
  | _, .cons c cs => .consC (Ctor.toIPF c) (Ctors.toIPF cs)
def Alts.toIPF : {n g : Nat} → Alts n g → IPF n
  | _, _, .two₁ c d => .twoC (Ctor.toIPF c) (Ctor.toIPF d)
  | _, _, .two₂ c d => .twoC (Ctor.toIPF c) (Ctor.toIPF d)
  | _, _, .here c cs => .consC (Ctor.toIPF c) (Ctors.toIPF cs)
  | _, _, .there c u => .consC (Ctor.toIPF c) (Alts.toIPF u)
/-- Member `g + i` of a family whose members `g, g+1, …` are listed. -/
def Mems.member : {n g : Nat} → Mems n g → (i : Nat) → g + i < n → IPF n
  | _, _, .nil, _, h => absurd h (by omega)
  | _, _, .cons b _, 0, _ => Ty.toIPF b
  | _, _, .cons _ bs, i + 1, h => Mems.member bs i (by omega)
end

abbrev Ty.Den (t : Ty 0 0) : Type := (Ty.toIPF t).A

example : Ty.Den (.fn .nat .bool) = (Nat → Bool) := rfl

/-! ## Instantiating the holes with closed types -/

mutual
def Ty.inst : {n g : Nat} → Ty n g → (Fin n → Ty 0 0) → Ty 0 0
  | _, _, .var i _, σ => σ i
  | _, _, .closed t, _ => t
  | _, _, .nat, _ => .nat
  | _, _, .bool, _ => .bool
  | _, _, .fn a b, σ => .fn a (Ty.inst b σ)
  | _, _, .array t, σ => .array (Ty.inst t σ)
  | _, _, .list t, σ => .list (Ty.inst t σ)
  | _, _, .finFn t, σ => .finFn (Ty.inst t σ)
  | _, _, .record t fs, σ => .record (Ty.inst t σ) (Fields.inst fs σ)
  | _, _, .union u, σ => .union (Alts.inst u σ)
  | _, _, .mu k bs s, _ => .mu k bs s
def Fields.inst : {n g : Nat} → Fields n g → (Fin n → Ty 0 0) → Fields 0 0
  | _, _, .one t, σ => .one (Ty.inst t σ)
  | _, _, .cons t fs, σ => .cons (Ty.inst t σ) (Fields.inst fs σ)
def Ctor.inst : {n g : Nat} → Ctor n g → (Fin n → Ty 0 0) → Ctor 0 0
  | _, _, .nullary, _ => .nullary
  | _, _, .fields fs, σ => .fields (Fields.inst fs σ)
def Ctors.inst : {n : Nat} → Ctors n → (Fin n → Ty 0 0) → Ctors 0
  | _, .two c d, σ => .two (Ctor.inst c σ) (Ctor.inst d σ)
  | _, .cons c cs, σ => .cons (Ctor.inst c σ) (Ctors.inst cs σ)
def Alts.inst : {n g : Nat} → Alts n g → (Fin n → Ty 0 0) → Alts 0 0
  | _, _, .two₁ c d, σ => .two₁ (Ctor.inst c σ) (Ctor.inst d σ)
  | _, _, .two₂ c d, σ => .two₂ (Ctor.inst c σ) (Ctor.inst d σ)
  | _, _, .here c cs, σ => .here (Ctor.inst c σ) (Ctors.inst cs σ)
  | _, _, .there c u, σ => .there (Ctor.inst c σ) (Alts.inst u σ)
end

/-- The body of member `g + i`, with its holes filled. -/
def Mems.instMember : {n g : Nat} → Mems n g → (i : Nat) → g + i < n → (Fin n → Ty 0 0) → Ty 0 0
  | _, _, .nil, _, h, _ => absurd h (by omega)
  | _, _, .cons b _, 0, _, σ => Ty.inst b σ
  | _, _, .cons _ bs, i + 1, h, σ => Mems.instMember bs i (by omega) σ

/-- The members of a family, as one indexed container. -/
abbrev Mems.fam {k : Nat} (bs : Mems (k + 1) 0) : Fin (k + 1) → IPF (k + 1) :=
  fun j => Mems.member bs j.val (Fin.zero_add_lt j)

/-- The unfolded body of member `j`: its holes filled with the members themselves. -/
abbrev Ty.unfold {k : Nat} (bs : Mems (k + 1) 0) (j : Fin (k + 1)) : Ty 0 0 :=
  Mems.instMember bs j.val (Fin.zero_add_lt j) (fun i => .mu k bs i)

example {k : Nat} (bs : Mems (k + 1) 0) (j : Fin (k + 1)) :
    Ty.Den (.mu k bs j) = IW bs.fam j := rfl

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
def IPF.Obj.ofConst {A : Type} (a : A) : (IPF.const (n := n) A).Obj X := ⟨a, fun b => b.elim⟩
def IPF.Obj.caseSum : (IPF.sum c d).Obj X → c.Obj X ⊕ d.Obj X
  | ⟨.inl a, f⟩ => .inl ⟨a, f⟩
  | ⟨.inr a, f⟩ => .inr ⟨a, f⟩
def IPF.Obj.caseOpt : (IPF.opt c).Obj X → Option (c.Obj X)
  | ⟨.none, _⟩ => .none
  | ⟨.some a, f⟩ => .some ⟨a, f⟩
end ObjOps

mutual
def Ty.roll : {n g : Nat} → (t : Ty n g) → (σ : Fin n → Ty 0 0) →
    Ty.Den (Ty.inst t σ) → (Ty.toIPF t).Obj (fun i => Ty.Den (σ i))
  | _, _, .var _ _, _, x => ⟨PUnit.unit, fun _ => x⟩
  | _, _, .closed _, _, x => ⟨x, fun b => nomatch b⟩
  | _, _, .nat, _, x => ⟨x, fun b => nomatch b⟩
  | _, _, .bool, _, x => ⟨x, fun b => nomatch b⟩
  | _, _, .fn _ b, σ, f => ⟨fun y => (Ty.roll b σ (f y)).1, fun p => (Ty.roll b σ (f p.1)).2 p.2⟩
  | _, _, .array t, σ, x =>
      let o := listRoll (fun d => Ty.roll t σ d) x.toList
      ⟨⟨o.1⟩, o.2⟩
  | _, _, .list t, σ, x => listRoll (fun d => Ty.roll t σ d) x
  | _, _, .finFn t, σ, x =>
      ⟨⟨x.1, fun i => (Ty.roll t σ (x.2 i)).1⟩, fun p => (Ty.roll t σ (x.2 p.1)).2 p.2⟩
  | _, _, .record t fs, σ, x =>
      let r := Ty.roll t σ x.1
      let rs := Fields.roll fs σ x.2
      ⟨(r.1, rs.1), fun | .inl b => r.2 b | .inr b => rs.2 b⟩
  | _, _, .union u, σ, x => Alts.roll u σ x
  | _, _, .mu _ _ _, _, x => ⟨x, fun b => nomatch b⟩
def Fields.roll : {n g : Nat} → (fs : Fields n g) → (σ : Fin n → Ty 0 0) →
    (Fields.toIPF (Fields.inst fs σ)).A → (Fields.toIPF fs).Obj (fun i => Ty.Den (σ i))
  | _, _, .one t, σ, x => Ty.roll t σ x
  | _, _, .cons t fs, σ, x =>
      let r := Ty.roll t σ x.1
      let rs := Fields.roll fs σ x.2
      ⟨(r.1, rs.1), fun | .inl b => r.2 b | .inr b => rs.2 b⟩
def Ctors.roll : {n : Nat} → (cs : Ctors n) → (σ : Fin n → Ty 0 0) →
    (Ctors.toIPF (Ctors.inst cs σ)).A → (Ctors.toIPF cs).Obj (fun i => Ty.Den (σ i))
  | _, .two .nullary .nullary, _, x => ⟨x, fun b => nomatch b⟩
  | _, .two .nullary (.fields fd), σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fd σ a)
  | _, .two (.fields fc) .nullary, σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fc σ a)
  | _, .two (.fields fc) (.fields fd), σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Fields.roll fd σ a)
  | _, .cons .nullary cs, σ, x =>
      match x with | .none => .none | .some a => .some (Ctors.roll cs σ a)
  | _, .cons (.fields fc) cs, σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Ctors.roll cs σ a)
def Alts.roll : {n g : Nat} → (u : Alts n g) → (σ : Fin n → Ty 0 0) →
    (Alts.toIPF (Alts.inst u σ)).A → (Alts.toIPF u).Obj (fun i => Ty.Den (σ i))
  | _, _, .two₁ .nullary .nullary, _, x => ⟨x, fun b => nomatch b⟩
  | _, _, .two₁ .nullary (.fields fd), σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fd σ a)
  | _, _, .two₁ (.fields fc) .nullary, σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fc σ a)
  | _, _, .two₁ (.fields fc) (.fields fd), σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Fields.roll fd σ a)
  | _, _, .two₂ .nullary .nullary, _, x => ⟨x, fun b => nomatch b⟩
  | _, _, .two₂ .nullary (.fields fd), σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fd σ a)
  | _, _, .two₂ (.fields fc) .nullary, σ, x =>
      match x with | .none => .none | .some a => .some (Fields.roll fc σ a)
  | _, _, .two₂ (.fields fc) (.fields fd), σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Fields.roll fd σ a)
  | _, _, .here .nullary cs, σ, x =>
      match x with | .none => .none | .some a => .some (Ctors.roll cs σ a)
  | _, _, .here (.fields fc) cs, σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Ctors.roll cs σ a)
  | _, _, .there .nullary u, σ, x =>
      match x with | .none => .none | .some a => .some (Alts.roll u σ a)
  | _, _, .there (.fields fc) u, σ, x =>
      match x with | .inl a => .inl (Fields.roll fc σ a) | .inr a => .inr (Alts.roll u σ a)
end

mutual
def Ty.unroll : {n g : Nat} → (t : Ty n g) → (σ : Fin n → Ty 0 0) →
    (Ty.toIPF t).Obj (fun i => Ty.Den (σ i)) → Ty.Den (Ty.inst t σ)
  | _, _, .var _ _, _, x => x.2 PUnit.unit
  | _, _, .closed _, _, x => x.1
  | _, _, .nat, _, x => x.1
  | _, _, .bool, _, x => x.1
  | _, _, .fn _ b, σ, x => fun a => Ty.unroll b σ ⟨x.1 a, fun q => x.2 ⟨a, q⟩⟩
  | _, _, .array t, σ, x => ⟨listUnroll (fun o => Ty.unroll t σ o) x.1.toList x.2⟩
  | _, _, .list t, σ, x => listUnroll (fun o => Ty.unroll t σ o) x.1 x.2
  | _, _, .finFn t, σ, x => ⟨x.1.1, fun i => Ty.unroll t σ ⟨x.1.2 i, fun q => x.2 ⟨i, q⟩⟩⟩
  | _, _, .record t fs, σ, x =>
      (Ty.unroll t σ ⟨x.1.1, fun b => x.2 (.inl b)⟩, Fields.unroll fs σ ⟨x.1.2, fun b => x.2 (.inr b)⟩)
  | _, _, .union u, σ, x => Alts.unroll u σ x
  | _, _, .mu _ _ _, _, x => x.1
def Fields.unroll : {n g : Nat} → (fs : Fields n g) → (σ : Fin n → Ty 0 0) →
    (Fields.toIPF fs).Obj (fun i => Ty.Den (σ i)) → (Fields.toIPF (Fields.inst fs σ)).A
  | _, _, .one t, σ, x => Ty.unroll t σ x
  | _, _, .cons t fs, σ, x =>
      (Ty.unroll t σ ⟨x.1.1, fun b => x.2 (.inl b)⟩, Fields.unroll fs σ ⟨x.1.2, fun b => x.2 (.inr b)⟩)
def Ctors.unroll : {n : Nat} → (cs : Ctors n) → (σ : Fin n → Ty 0 0) →
    (Ctors.toIPF cs).Obj (fun i => Ty.Den (σ i)) → (Ctors.toIPF (Ctors.inst cs σ)).A
  | _, .two .nullary .nullary, _, x => x.1
  | _, .two .nullary (.fields fd), σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fd σ o)
  | _, .two (.fields fc) .nullary, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fc σ o)
  | _, .two (.fields fc) (.fields fd), σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Fields.unroll fd σ o)
  | _, .cons .nullary cs, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Ctors.unroll cs σ o)
  | _, .cons (.fields fc) cs, σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Ctors.unroll cs σ o)
def Alts.unroll : {n g : Nat} → (u : Alts n g) → (σ : Fin n → Ty 0 0) →
    (Alts.toIPF u).Obj (fun i => Ty.Den (σ i)) → (Alts.toIPF (Alts.inst u σ)).A
  | _, _, .two₁ .nullary .nullary, _, x => x.1
  | _, _, .two₁ .nullary (.fields fd), σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fd σ o)
  | _, _, .two₁ (.fields fc) .nullary, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fc σ o)
  | _, _, .two₁ (.fields fc) (.fields fd), σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Fields.unroll fd σ o)
  | _, _, .two₂ .nullary .nullary, _, x => x.1
  | _, _, .two₂ .nullary (.fields fd), σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fd σ o)
  | _, _, .two₂ (.fields fc) .nullary, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Fields.unroll fc σ o)
  | _, _, .two₂ (.fields fc) (.fields fd), σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Fields.unroll fd σ o)
  | _, _, .here .nullary cs, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Ctors.unroll cs σ o)
  | _, _, .here (.fields fc) cs, σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Ctors.unroll cs σ o)
  | _, _, .there .nullary u, σ, x =>
      match x.caseOpt with | .none => .none | .some o => .some (Alts.unroll u σ o)
  | _, _, .there (.fields fc) u, σ, x =>
      match x.caseSum with | .inl o => .inl (Fields.unroll fc σ o) | .inr o => .inr (Alts.unroll u σ o)
end

def Mems.rollMember : {n g : Nat} → (bs : Mems n g) → (i : Nat) → (h : g + i < n) →
    (σ : Fin n → Ty 0 0) → Ty.Den (Mems.instMember bs i h σ) →
    (Mems.member bs i h).Obj (fun j => Ty.Den (σ j))
  | _, _, .nil, _, h, _, _ => absurd h (by omega)
  | _, _, .cons b _, 0, _, σ, x => Ty.roll b σ x
  | _, _, .cons _ bs, i + 1, h, σ, x => Mems.rollMember bs i (by omega) σ x

def Mems.unrollMember : {n g : Nat} → (bs : Mems n g) → (i : Nat) → (h : g + i < n) →
    (σ : Fin n → Ty 0 0) → (Mems.member bs i h).Obj (fun j => Ty.Den (σ j)) →
    Ty.Den (Mems.instMember bs i h σ)
  | _, _, .nil, _, h, _, _ => absurd h (by omega)
  | _, _, .cons b _, 0, _, σ, x => Ty.unroll b σ x
  | _, _, .cons _ bs, i + 1, h, σ, x => Mems.unrollMember bs i (by omega) σ x

/-- `Comp.mu_in`: the one introduction form of every recursive type. -/
def muIn {k : Nat} (bs : Mems (k + 1) 0) (j : Fin (k + 1)) (x : Ty.Den (Ty.unfold bs j)) :
    Ty.Den (.mu k bs j) :=
  match Mems.rollMember bs j.val (Fin.zero_add_lt j) (fun i => .mu k bs i) x with
  | ⟨a, f⟩ => IW.mk j a f

/-- `Comp.mu_out`: take one layer off. -/
def muOut {k : Nat} (bs : Mems (k + 1) 0) (j : Fin (k + 1)) (v : Ty.Den (.mu k bs j)) :
    Ty.Den (Ty.unfold bs j) :=
  Mems.unrollMember bs j.val (Fin.zero_add_lt j) (fun i => .mu k bs i) v.dest

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

/-- Build a value of every member of an indexed W-type, member by member, from a step that may
    use the members before it.  Structural recursion on a `Nat` bound. -/
def IW.build {k : Nat} {C : Fin k → Type}
    (step : (j : Fin k) → ((i : Fin k) → i.val < j.val → C i) → C j) : (j : Fin k) → C j :=
  fun j => go (j.val + 1) j (Nat.lt_succ_self _)
where
  go : (m : Nat) → (i : Fin k) → i.val < m → C i
    | 0, _, h => absurd h (Nat.not_lt_zero _)
    | m + 1, i, h => step i (fun i' h' => go m i' (by omega))

theorem IPF.Obj.eq_of_fin0 {P : IPF 0} {X : Fin 0 → Type} (o : P.Obj X) :
    (⟨o.1, fun b => (P.tgt o.1 b).elim0⟩ : P.Obj X) = o := by
  cases o with
  | mk a f => exact congrArg (Sigma.mk a) (funext fun b => (P.tgt a b).elim0)

def Two.ofObj0 {P : IPF 0} {X : Fin 0 → Type} (T : Two (P.Obj X)) : Two P.A where
  x := T.x.1
  y := T.y.1
  d a := T.d ⟨a, fun b => (P.tgt a b).elim0⟩
  dx := by rw [IPF.Obj.eq_of_fin0]; exact T.dx
  dy := by rw [IPF.Obj.eq_of_fin0]; exact T.dy

def Two.ofIW {k : Nat} {P : Fin k → IPF k} {j : Fin k} (T : Two ((P j).Obj (IW P))) :
    Two (IW P j) where
  x := IW.mk j T.x.1 T.x.2
  y := IW.mk j T.y.1 T.y.2
  d v := T.d v.dest
  dx := T.dx
  dy := T.dy

/-- The empty context of holes. -/
abbrev X0 : Fin 0 → Type := fun i => i.elim0

mutual
/-- A value of `t`, given values of the holes `t` is grounded on (`i < g`).  Holes `≥ g` are
    only reached under a guard (an `array`, a non-base constructor), so they are never needed. -/
def Ty.inh : {n g : Nat} → (t : Ty n g) → (X : Fin n → Type) →
    ((i : Fin n) → i.val < g → X i) → (Ty.toIPF t).Obj X
  | _, _, .var i h, _, w => ⟨PUnit.unit, fun _ => w i h⟩
  | _, _, .closed t, _, _ =>
      ⟨(Ty.inh t X0 (fun i => i.elim0)).1, fun b => b.elim⟩
  | _, _, .nat, _, _ => ⟨(0 : Nat), fun b => nomatch b⟩
  | _, _, .bool, _, _ => ⟨false, fun b => nomatch b⟩
  | _, _, .fn _ b, X, w => let o := Ty.inh b X w; ⟨fun _ => o.1, fun p => o.2 p.2⟩
  | _, _, .array _, _, _ => ⟨#[], fun b => nomatch b⟩
  | _, _, .list _, _, _ => ⟨[], fun b => nomatch b⟩
  | _, _, .finFn _, _, _ => ⟨⟨0, Fin.elim0⟩, fun p => p.1.elim0⟩
  | _, _, .record t fs, X, w =>
      let o := Ty.inh t X w
      let os := Fields.inh fs X w
      ⟨(o.1, os.1), fun | .inl b => o.2 b | .inr b => os.2 b⟩
  | _, _, .union u, X, w => Alts.inh u X w
  | _, _, .mu _ bs s, _, _ =>
      ⟨IW.build (C := IW bs.fam)
        (fun j acc => IW.ofObj (Mems.inhMember bs j.val (Fin.zero_add_lt j)
            (IW bs.fam) (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _))))) s,
        fun b => b.elim⟩
def Fields.inh : {n g : Nat} → (fs : Fields n g) → (X : Fin n → Type) →
    ((i : Fin n) → i.val < g → X i) → (Fields.toIPF fs).Obj X
  | _, _, .one t, X, w => Ty.inh t X w
  | _, _, .cons t fs, X, w =>
      let o := Ty.inh t X w
      let os := Fields.inh fs X w
      ⟨(o.1, os.1), fun | .inl b => o.2 b | .inr b => os.2 b⟩
/-- A union is inhabited through its base constructor. -/
def Alts.inh : {n g : Nat} → (u : Alts n g) → (X : Fin n → Type) →
    ((i : Fin n) → i.val < g → X i) → (Alts.toIPF u).Obj X
  | _, _, .two₁ .nullary .nullary, _, _ => ⟨true, fun b => nomatch b⟩
  | _, _, .two₁ .nullary (.fields _), _, _ => .none
  | _, _, .two₁ (.fields fc) .nullary, X, w => .some (Fields.inh fc X w)
  | _, _, .two₁ (.fields fc) (.fields _), X, w => .inl (Fields.inh fc X w)
  | _, _, .two₂ .nullary .nullary, _, _ => ⟨true, fun b => nomatch b⟩
  | _, _, .two₂ .nullary (.fields fd), X, w => .some (Fields.inh fd X w)
  | _, _, .two₂ (.fields _) .nullary, _, _ => .none
  | _, _, .two₂ (.fields _) (.fields fd), X, w => .inr (Fields.inh fd X w)
  | _, _, .here .nullary _, _, _ => .none
  | _, _, .here (.fields fc) _, X, w => .inl (Fields.inh fc X w)
  | _, _, .there .nullary u, X, w => .some (Alts.inh u X w)
  | _, _, .there (.fields _) u, X, w => .inr (Alts.inh u X w)
def Mems.inhMember : {n g : Nat} → (bs : Mems n g) → (i : Nat) → (h : g + i < n) →
    (X : Fin n → Type) → ((j : Fin n) → j.val < g + i → X j) → (Mems.member bs i h).Obj X
  | _, _, .nil, _, h, _, _ => absurd h (by omega)
  | _, _, .cons b _, 0, _, X, w => Ty.inh b X w
  | _, _, .cons _ bs, i + 1, _, X, w => Mems.inhMember bs i (by omega) X (fun j hj => w j (by omega))
end

/-- With every hole inhabited, any list of constructors is inhabited (take the first). -/
def Ctors.inh {n : Nat} : (cs : Ctors n) → (X : Fin n → Type) → ((i : Fin n) → X i) →
    (Ctors.toIPF cs).Obj X
  | .two .nullary .nullary, _, _ => .ofConst true
  | .two .nullary (.fields _), _, _ => .none
  | .two (.fields fc) .nullary, X, all => .some (Fields.inh fc X (fun i _ => all i))
  | .two (.fields fc) (.fields _), X, all => .inl (Fields.inh fc X (fun i _ => all i))
  | .cons .nullary _, _, _ => .none
  | .cons (.fields fc) _, X, all => .inl (Fields.inh fc X (fun i _ => all i))

/-- Two constructors: the tag tells them apart. -/
def Ctor.twoTwo {n g g' : Nat} : (c : Ctor n g) → (d : Ctor n g') → (X : Fin n → Type) →
    ((i : Fin n) → X i) → Two ((IPF.twoC (Ctor.toIPF c) (Ctor.toIPF d)).Obj X)
  | .nullary, .nullary, _, _ => ⟨.ofConst true, .ofConst false, fun o => o.1, rfl, rfl⟩
  | .nullary, .fields fd, X, all =>
      ⟨.none, .some (Fields.inh fd X (fun i _ => all i)), fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc, .nullary, X, all =>
      ⟨.some (Fields.inh fc X (fun i _ => all i)), .none, fun o => o.1.isSome, rfl, rfl⟩
  | .fields fc, .fields fd, X, all =>
      ⟨.inl (Fields.inh fc X (fun i _ => all i)), .inr (Fields.inh fd X (fun i _ => all i)),
        fun o => o.1.isLeft, rfl, rfl⟩

/-- A constructor in front of an inhabited rest: the tag tells them apart. -/
def Ctor.consTwo {n g : Nat} {R : IPF n} : (c : Ctor n g) → (X : Fin n → Type) →
    ((i : Fin n) → X i) → R.Obj X → Two ((IPF.consC (Ctor.toIPF c) R).Obj X)
  | .nullary, _, _, r => ⟨.none, .some r, fun o => o.1.isNone, rfl, rfl⟩
  | .fields fc, X, all, r =>
      ⟨.inl (Fields.inh fc X (fun i _ => all i)), .inr r, fun o => o.1.isLeft, rfl, rfl⟩

/-- A union has two told-apart values: it has at least two constructors, all inhabited. -/
def Alts.two {n g : Nat} : (u : Alts n g) → (X : Fin n → Type) → ((i : Fin n) → X i) →
    Two ((Alts.toIPF u).Obj X)
  | .two₁ c d, X, all => Ctor.twoTwo c d X all
  | .two₂ c d, X, all => Ctor.twoTwo c d X all
  | .here c cs, X, all => Ctor.consTwo c X all (Ctors.inh cs X all)
  | .there c u, X, all => Ctor.consTwo c X all (Alts.inh u X (fun i _ => all i))

mutual
/-- Two values of `t` told apart by a test, given a value of every hole and two told-apart values
    of every hole `t` is grounded on. -/
def Ty.two : {n g : Nat} → (t : Ty n g) → (X : Fin n → Type) → ((i : Fin n) → X i) →
    ((i : Fin n) → i.val < g → Two (X i)) → Two ((Ty.toIPF t).Obj X)
  | _, _, .var i h, _, _, tw =>
      let T := tw i h
      ⟨⟨PUnit.unit, fun _ => T.x⟩, ⟨PUnit.unit, fun _ => T.y⟩, fun o => T.d (o.2 PUnit.unit),
        T.dx, T.dy⟩
  | _, _, .closed t, _, _, _ =>
      let T := Two.ofObj0 (Ty.two t X0 (fun i => i.elim0) (fun i => i.elim0))
      ⟨.ofConst T.x, .ofConst T.y, fun o => T.d o.1, T.dx, T.dy⟩
  | _, _, .nat, _, _, _ =>
      ⟨.ofConst (0 : Nat), .ofConst (1 : Nat), fun o => Nat.beq o.1 0, rfl, rfl⟩
  | _, _, .bool, _, _, _ => ⟨.ofConst true, .ofConst false, fun o => o.1, rfl, rfl⟩
  | _, _, .fn a b, X, all, tw =>
      let e := (Ty.inh a X0 (fun i => i.elim0)).1
      let T := Ty.two b X all tw
      ⟨⟨fun _ => T.x.1, fun p => T.x.2 p.2⟩, ⟨fun _ => T.y.1, fun p => T.y.2 p.2⟩,
        fun o => T.d ⟨o.1 e, fun q => o.2 ⟨e, q⟩⟩, T.dx, T.dy⟩
  | _, _, .array t, X, all, _ =>
      let o := Ty.inh t X (fun i _ => all i)
      ⟨⟨#[], fun b => nomatch b⟩, ⟨#[o.1], fun | .inl b => o.2 b⟩,
        fun o' => o'.1.toList.isEmpty, rfl, rfl⟩
  | _, _, .list t, X, all, _ =>
      let o := Ty.inh t X (fun i _ => all i)
      ⟨⟨[], fun b => nomatch b⟩, ⟨[o.1], fun | .inl b => o.2 b⟩,
        fun o' => o'.1.isEmpty, rfl, rfl⟩
  | _, _, .finFn t, X, all, _ =>
      let o := Ty.inh t X (fun i _ => all i)
      ⟨⟨⟨0, Fin.elim0⟩, fun p => p.1.elim0⟩, ⟨⟨1, fun _ => o.1⟩, fun p => o.2 p.2⟩,
        fun o' => Nat.beq o'.1.1 0, rfl, rfl⟩
  | _, _, .record t fs, X, all, tw =>
      let T := Ty.two t X all tw
      let os := Fields.inh fs X (fun i _ => all i)
      ⟨.pair T.x os, .pair T.y os, fun o => T.d o.fst, T.dx, T.dy⟩
  | _, _, .union u, X, all, _ => Alts.two u X all
  | _, _, .mu _ bs s, _, _, _ =>
      let all : (i : Fin _) → IW bs.fam i := IW.build (fun j acc =>
        IW.ofObj (Mems.inhMember bs j.val (Fin.zero_add_lt j) (IW bs.fam)
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _)))))
      let T := IW.build (C := fun i => Two (IW bs.fam i)) (fun j acc =>
        Two.ofIW (Mems.twoMember bs j.val (Fin.zero_add_lt j) (IW bs.fam) all
          (fun i hi => acc i (Nat.lt_of_lt_of_eq hi (Nat.zero_add _))))) s
      ⟨.ofConst T.x, .ofConst T.y, fun o => T.d o.1, T.dx, T.dy⟩
def Fields.two : {n g : Nat} → (fs : Fields n g) → (X : Fin n → Type) → ((i : Fin n) → X i) →
    ((i : Fin n) → i.val < g → Two (X i)) → Two ((Fields.toIPF fs).Obj X)
  | _, _, .one t, X, all, tw => Ty.two t X all tw
  | _, _, .cons t fs, X, all, tw =>
      let T := Ty.two t X all tw
      let os := Fields.inh fs X (fun i _ => all i)
      ⟨.pair T.x os, .pair T.y os, fun o => T.d o.fst, T.dx, T.dy⟩
def Mems.twoMember : {n g : Nat} → (bs : Mems n g) → (i : Nat) → (h : g + i < n) →
    (X : Fin n → Type) → ((j : Fin n) → X j) → ((j : Fin n) → j.val < g + i → Two (X j)) →
    Two ((Mems.member bs i h).Obj X)
  | _, _, .nil, _, h, _, _, _ => absurd h (by omega)
  | _, _, .cons b _, 0, _, X, all, tw => Ty.two b X all tw
  | _, _, .cons _ bs, i + 1, _, X, all, tw =>
      Mems.twoMember bs i (by omega) X all (fun j hj => tw j (by omega))
end

/-- **Every closed type has two values that a Boolean test tells apart.**  Structural recursion
    on the type; no fuel, no measure, no proof search. -/
def Ty.twoDen (t : Ty 0 0) : Two (Ty.Den t) :=
  Two.ofObj0 (Ty.two t X0 (fun i => i.elim0) (fun i => i.elim0))

/-- No closed type is empty-like. -/
theorem Ty.den_nonempty (t : Ty 0 0) : Nonempty (Ty.Den t) := ⟨(Ty.twoDen t).x⟩

/-- No closed type is unit-like (or empty-like). -/
theorem Ty.den_not_subsingleton (t : Ty 0 0) : ¬ ∀ x y : Ty.Den t, x = y :=
  fun h => (Ty.twoDen t).ne (h _ _)

theorem Ty.den_exists_ne (t : Ty 0 0) : ∃ x y : Ty.Den t, x ≠ y :=
  ⟨_, _, (Ty.twoDen t).ne⟩

/-! ## The one fold -/

def IW.fold {k : Nat} {P : Fin k → IPF k} {C : Fin k → Type}
    (alg : (i : Fin k) → (P i).Obj (fun j => IW P j × C j) → C i) :
    {i : Fin k} → IW P i → C i
  | _, .mk i a f => alg i ⟨a, fun b => (f b, IW.fold alg (f b))⟩

/-- The pair type: a record of two fields. -/
def pairTy (a b : Ty 0 0) : Ty 0 0 := .record a (.one b)

example (a b : Ty 0 0) : Ty.Den (pairTy a b) = (Ty.Den a × Ty.Den b) := rfl

/-- `Term.mu_rec`: one branch per member `j`, binding member `j`'s body with every hole `i`
    filled by the pair of the subvalue and the answer at it.  Structural recursion on the tree. -/
def muRec {k : Nat} (bs : Mems (k + 1) 0) (ρ : Fin (k + 1) → Ty 0 0)
    (branch : (j : Fin (k + 1)) →
      Ty.Den (Mems.instMember bs j.val (Fin.zero_add_lt j) (fun i => pairTy (.mu k bs i) (ρ i))) →
      Ty.Den (ρ j))
    {j : Fin (k + 1)} (v : Ty.Den (.mu k bs j)) : Ty.Den (ρ j) :=
  IW.fold (C := fun i => Ty.Den (ρ i))
    (fun i x => branch i (Mems.unrollMember bs i.val (Fin.zero_add_lt i) _ ⟨x.1, x.2⟩)) v

/-! ## Examples: what `Ty.Den` returns -/

/-- `Bool`-like: two constructors without fields. -/
example : Ty.Den (.union (.two₁ .nullary .nullary) : Ty 0 0) = Bool := rfl
/-- `Option Nat`: a constructor without fields is `Option`, not `PUnit ⊕ _`. -/
example : Ty.Den (.union (.two₁ .nullary (.fields (.one .nat))) : Ty 0 0) = Option Nat := rfl

/-! ## `List Nat` -/

/-- `nil` is the base constructor (grounded, `Ctor 1 0`); `cons` may mention the list. -/
def listBody : Mems 1 0 :=
  .cons (.union (.two₁ .nullary (.fields (.cons .nat (.one (.var 0 (by decide))))))) .nil
def listNat : Ty 0 0 := .mu 0 listBody 0

example : Ty.Den (Ty.unfold listBody 0) = Option (Nat × Ty.Den listNat) := rfl

def nil' : Ty.Den listNat := muIn listBody 0 none
def cons' (x : Nat) (xs : Ty.Den listNat) : Ty.Den listNat := muIn listBody 0 (some (x, xs))

def sum' (v : Ty.Den listNat) : Nat :=
  muRec listBody (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × (Ty.Den listNat × Nat))) with
        | none => 0
        | some (n, _, r) => Nat.add n r
      r) v

example : sum' (cons' 1 (cons' 2 (cons' 3 nil'))) = 6 := rfl

def head? (v : Ty.Den listNat) : Option Nat :=
  match (muOut listBody 0 v : Option (Nat × Ty.Den listNat)) with
  | none => none
  | some (n, _) => some n

example : head? (cons' 7 nil') = some 7 := rfl
example : head? nil' = none := rfl

/-! ## Rose trees: three different types

```
inductive RoseL | node : List RoseL → RoseL
inductive RoseA | node : Array RoseA → RoseA
inductive RoseF | node : (m : Nat) → (Fin m → RoseF) → RoseF
```

None of them has a constructor without recursive fields, but `list`, `array` and `finFn` guard
their element (the empty list / array / `m = 0` is a value), so all three are accepted.  They
are three different `Ty`s, and each unfolds to exactly what its Lean constructor takes. -/

def roseLBody : Mems 1 0 := .cons (.list (.var 0 (by decide))) .nil
def roseABody : Mems 1 0 := .cons (.array (.var 0 (by decide))) .nil
def roseFBody : Mems 1 0 := .cons (.finFn (.var 0 (by decide))) .nil
abbrev RoseL : Type := Ty.Den (.mu 0 roseLBody 0)
abbrev RoseA : Type := Ty.Den (.mu 0 roseABody 0)
abbrev RoseF : Type := Ty.Den (.mu 0 roseFBody 0)

example : Ty.Den (Ty.unfold roseLBody 0) = List RoseL := rfl
example : Ty.Den (Ty.unfold roseABody 0) = Array RoseA := rfl
example : Ty.Den (Ty.unfold roseFBody 0) = ((m : Nat) × (Fin m → RoseF)) := rfl

example : (Ty.mu 0 roseLBody 0 : Ty 0 0) ≠ .mu 0 roseABody 0 := by decide
example : (Ty.mu 0 roseABody 0 : Ty 0 0) ≠ .mu 0 roseFBody 0 := by decide
example : (Ty.array .nat : Ty 0 0) ≠ .finFn .nat := by decide

/-- A closed `array` is Lean's `Array`, not a function on `Fin`. -/
example : Ty.Den (.array .nat) = Array Nat := rfl
example : Ty.Den (.list .nat) = List Nat := rfl

def RoseL.node (cs : List RoseL) : RoseL := muIn roseLBody 0 cs
def RoseA.node (cs : Array RoseA) : RoseA := muIn roseABody 0 cs
def RoseF.node (m : Nat) (cs : Fin m → RoseF) : RoseF := muIn roseFBody 0 ⟨m, cs⟩

theorem listUnroll_listRoll {n : Nat} {c : IPF n} {X : Fin n → Type} {D : Type}
    (f : c.Obj X → D) (g : D → c.Obj X) (h : ∀ d, f (g d) = d) :
    (xs : List D) → listUnroll f (listRoll g xs).1 (listRoll g xs).2 = xs
  | [] => rfl
  | d :: ds => by
    show f (g d) :: listUnroll f (listRoll g ds).1 (listRoll g ds).2 = d :: ds
    rw [h d]
    exact congrArg (d :: ·) (listUnroll_listRoll f g h ds)

/-- Taking a layer off gives back the same `List` of children. -/
example (cs : List RoseL) : muOut roseLBody 0 (RoseL.node cs) = cs :=
  listUnroll_listRoll _ _ (fun _ => rfl) cs

/-- The same `Array` of children. -/
example (cs : Array RoseA) : muOut roseABody 0 (RoseA.node cs) = cs :=
  congrArg Array.mk (listUnroll_listRoll _ _ (fun _ => rfl) cs.toList)

/-- `Σ i < m, f i`, by structural recursion on `m`. -/
def finSum : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => f ⟨m, Nat.lt_succ_self m⟩ + finSum m (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

/-- The number of nodes, by the one fold: each branch receives the honest `List` (or `Array`)
    of pairs (child, answer at the child). -/
def RoseL.size (t : RoseL) : Nat :=
  muRec roseLBody (fun _ => .nat) (fun
    | ⟨0, _⟩, cs =>
      let r : Nat := ((cs : List (RoseL × Nat)).map Prod.snd).foldl Nat.add 1
      r) t

def RoseA.size (t : RoseA) : Nat :=
  muRec roseABody (fun _ => .nat) (fun
    | ⟨0, _⟩, cs =>
      let r : Nat := ((cs : Array (RoseA × Nat)).toList.map Prod.snd).foldl Nat.add 1
      r) t

def RoseF.size (t : RoseF) : Nat :=
  muRec roseFBody (fun _ => .nat) (fun
    | ⟨0, _⟩, cs =>
      let cs : (m : Nat) × (Fin m → RoseF × Nat) := cs
      let r : Nat := 1 + finSum cs.1 (fun i => (cs.2 i).2)
      r) t

example : RoseL.size (.node [.node [], .node [.node []]]) = 4 := rfl
example : RoseA.size (.node #[.node #[], .node #[.node #[]]]) = 4 := rfl
example : RoseF.size (.node 2 fun i => if i.val = 0 then .node 0 Fin.elim0 else
    .node 1 fun _ => .node 0 Fin.elim0) = 4 := rfl

/-- The two values the structural proof picks for `List Nat`: `[]` and `[0]`. -/
example : head? (Ty.twoDen listNat).x = none := rfl
example : head? (Ty.twoDen listNat).y = some 0 := rfl

/-! ## `LitExpr` at a closed index: no recursion left

`LitExpr (Nat × Bool)`: `lit` at `Nat × Bool` (one field, the pair) and `pair` (fields
`LitExpr Nat`, `LitExpr Bool`).  At `Nat` and `Bool` only `lit` survives, and a type with one
constructor and one field is that field, so `LitExpr Nat` is `nat` and `LitExpr Bool` is
`bool`. -/

def litExprNatBool : Ty 0 0 :=
  .union (.two₁ (.fields (.one (pairTy .nat .bool))) (.fields (.cons .nat (.one .bool))))

example : Ty.Den litExprNatBool = ((Nat × Bool) ⊕ (Nat × Bool)) := rfl

/-- `eval : LitExpr (Nat × Bool) → Nat × Bool`, with no recursion at all. -/
def evalNB (v : Ty.Den litExprNatBool) : Nat × Bool :=
  match (v : (Nat × Bool) ⊕ (Nat × Bool)) with
  | .inl p => p
  | .inr p => p

/-! ## `LitExpr` with `swap`: a cycle of indices, one `mu` with two members

Member `0` is `LitExprS (Nat × Bool)`, member `1` is `LitExprS (Bool × Nat)`.  Each member's
base constructor is `lit`, whose field is closed. -/

def litSBody : Mems 2 0 :=
  .cons (.union (.here (.fields (.one (.closed (pairTy .nat .bool))))
          (.two (.fields (.cons .nat (.one .bool))) (.fields (.one (.var 1 (by decide)))))))
  (.cons (.union (.here (.fields (.one (.closed (pairTy .bool .nat))))
          (.two (.fields (.cons .bool (.one .nat))) (.fields (.one (.var 0 (by decide)))))))
  .nil)

def litSNB : Ty 0 0 := .mu 1 litSBody 0

example : Ty.Den (Ty.unfold litSBody 0) =
    ((Nat × Bool) ⊕ ((Nat × Bool) ⊕ Ty.Den (.mu 1 litSBody 1))) := rfl

/-- The answer type of each member: `eval : LitExprS α → α`. -/
def litSAnswer : Fin 2 → Ty 0 0
  | ⟨0, _⟩ => pairTy .nat .bool
  | ⟨1, _⟩ => pairTy .bool .nat

def litS_lit (a : Nat) (b : Bool) : Ty.Den litSNB := muIn litSBody 0 (.inl (a, b))
def litS_litBN (b : Bool) (a : Nat) : Ty.Den (.mu 1 litSBody 1) := muIn litSBody 1 (.inl (b, a))
def litS_swap (e : Ty.Den (.mu 1 litSBody 1)) : Ty.Den litSNB := muIn litSBody 0 (.inr (.inr e))

/-- `eval`, by the one fold, answering a different type at each member. -/
def litSEval {j : Fin 2} (v : Ty.Den (.mu 1 litSBody j)) : Ty.Den (litSAnswer j) :=
  muRec litSBody litSAnswer (fun
    | ⟨0, _⟩, x =>
      let r : Nat × Bool :=
        match (x : (Nat × Bool) ⊕ ((Nat × Bool) ⊕ (Ty.Den (.mu 1 litSBody 1) × (Bool × Nat)))) with
        | .inl p => p
        | .inr (.inl p) => p
        | .inr (.inr (_, (b, a))) => (a, b)
      r
    | ⟨1, _⟩, x =>
      let r : Bool × Nat :=
        match (x : (Bool × Nat) ⊕ ((Bool × Nat) ⊕ (Ty.Den (.mu 1 litSBody 0) × (Nat × Bool)))) with
        | .inl p => p
        | .inr (.inl p) => p
        | .inr (.inr (_, (a, b))) => (b, a)
      r) v

example : litSEval (j := 0) (litS_swap (litS_litBN true 3)) = ((3, true) : Nat × Bool) := rfl

/-! ## What can no longer be written

Each attempt below is rejected by the type checker; `#guard_msgs` pins the error. -/

-- `μX. X`: member `0` may use no hole outside a guard (only holes `< 0`).
/--
error: Tactic `decide` proved that the proposition
  ↑0 < 0
is false
-/
#guard_msgs in
example : Ty 0 0 := .mu 0 (.cons (.var 0 (by decide)) .nil) 0

-- `μX. Nat × X` (no base case): every field of a record is a grounded position.
/--
error: Tactic `decide` proved that the proposition
  ↑0 < 0
is false
-/
#guard_msgs in
example : Ty 0 0 := .mu 0 (.cons (.record .nat (.one (.var 0 (by decide)))) .nil) 0

-- The old `unitTy` (one constructor without fields): a union has no one-constructor form.
/--
error: Unknown constant `WTyToy.Alts.one`

Note: Inferred this name from the expected resulting type of `.one`:
  Alts 0 0
-/
#guard_msgs in
example : Ty 0 0 := .union (.one .nullary)

end WTyToy
end
