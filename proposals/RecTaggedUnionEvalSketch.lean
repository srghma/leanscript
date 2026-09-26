module

public import LeanScript.Ty.Unfold
public import LeanScript.Den
public import LeanScript.Ty.WfFacts

@[expose] public section

/-!
Sketch that goes with `proposals/RecTaggedUnionEvalProposal.md`.  It is NOT part of the Lake build
(no library glob matches `proposals/`); check it with

    lake build LeanScript.Den LeanScript.Ty.Unfold LeanScript.Ty.WfFacts
    lake env lean proposals/RecTaggedUnionEvalSketch.lean

Everything lives in `LeanScript.Proto`, so it does not clash with the real definitions.
It shows that
* `Ty.Den` can be computed from a container per tree, with every equation of today's
  `Ty.Den` still holding by `rfl`, and a recursive tagged union denoting a W-tree;
* `roll` / `unroll` (unfolded fields <-> shape + holes) need no `cast` once substitution
  leaves the domain of an arrow alone;
* values of `List Nat` can be built, taken apart and folded, and the kernel computes the
  results (`rfl`, `decide`);
* `roll` and `unroll` are mutually inverse (`unroll_roll`, `roll_unroll`, at the end of
  the file), with no extra hypothesis: only `funext`, list induction and re-typing a
  goal at the container it unfolds to;
* the positivity check is *strict* positivity: `Ty.self` is refused anywhere in the domain
  of an arrow, positive (`(self → Nat) → Nat`) or negative (`(Nat → self) → Nat`).
-/

open NonEmpty.ListCorrectByConstruction (NonEmptyList)
namespace LeanScript.Proto

structure Cont where
  S : Type
  P : S → Type

inductive WTree (S : Type) (P : S → Type) : Type
  | mk (s : S) (f : P s → WTree S P)

def Cont.const (A : Type) : Cont := ⟨A, fun _ => PEmpty⟩
def Cont.prod (c d : Cont) : Cont := ⟨c.S × d.S, fun p => c.P p.1 ⊕ d.P p.2⟩
def Cont.sigma (I : Type) (c : I → Cont) : Cont := ⟨(i : I) × (c i).S, fun p => (c p.1).P p.2⟩
def Cont.pi (A : Type) (c : Cont) : Cont := ⟨A → c.S, fun f => (a : A) × c.P (f a)⟩
def ListPos {S : Type} (P : S → Type) : List S → Type
  | [] => PEmpty
  | s :: ss => P s ⊕ ListPos P ss
def Cont.list (c : Cont) : Cont := ⟨List c.S, ListPos c.P⟩
def Cont.mu (c : Cont) : Cont := Cont.const (WTree c.S c.P)
/-- The extension of a container: a shape, and a value of `X` in each hole. -/
def Cont.Ext (c : Cont) (X : Type) : Type := (s : c.S) × (c.P s → X)

mutual
def Ty.Cont : Ty → Cont
  | .self => ⟨PUnit, fun _ => PUnit⟩
  | .familyMember _ => Cont.const PEmpty
  | .shape s => Ty.ContShape s
  | .recTaggedUnion l => Cont.mu (Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t.val))
  | .recObject _ => Cont.const PEmpty
  | .recAlias _ => Cont.const PEmpty
  | .mutualRecursiveFamily _ => Cont.const PEmpty
def Ty.ContShape : TyShape Ty → Cont
  | .prim p => Cont.const p.denote
  | .fn a b => Cont.pi (Ty.Cont a).S (Ty.Cont b)
  | .primCovariant c => Ty.ContCov c
  | .enum s => Cont.const (Fin s.nOfConstructors)
  | .record fs => Ty.ContRecord fs
  | .taggedUnion l => Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t.val)
def Ty.ContCov : LeanPrimTyCovariant Ty → Cont
  | .array a => Cont.list (Ty.Cont a)
  | .thunk a => Ty.Cont a
  | .lazy a => Ty.Cont a
def Ty.ContNE : NonEmptyList Ty → Cont
  | ⟨a, as⟩ => Cont.prod (Ty.Cont a) (Ty.ContList as)
def Ty.ContRecord : LeanRecordSchema Ty → Cont
  | ⟨a, b, rest⟩ => Cont.prod (Ty.Cont a) (Cont.prod (Ty.Cont b) (Ty.ContList rest))
def Ty.ContList : List Ty → Cont
  | [] => Cont.const PUnit
  | τ :: ts => Cont.prod (Ty.Cont τ) (Ty.ContList ts)
def Ty.ContAt : LeanTaggedUnionSchema Ty → Nat → Cont
  | .payloadFirst fields _ _, 0 => Ty.ContNE fields
  | .payloadFirst _ next _, 1 => Ty.ContList next
  | .payloadFirst _ _ rest, n + 2 => Ty.ContAtList rest n
  | .skip _, 0 => Cont.const PUnit
  | .skip rest, n + 1 => Ty.ContAtCP rest n
def Ty.ContAtCP : CtorsWithPayload Ty → Nat → Cont
  | .here fields _, 0 => Ty.ContNE fields
  | .here _ rest, n + 1 => Ty.ContAtList rest n
  | .skip _, 0 => Cont.const PUnit
  | .skip rest, n + 1 => Ty.ContAtCP rest n
def Ty.ContAtList : List (List Ty) → Nat → Cont
  | [], _ => Cont.const PEmpty
  | fs :: _, 0 => Ty.ContList fs
  | _ :: rest, n + 1 => Ty.ContAtList rest n
end

@[reducible] def Ty.Den (t : Ty) : Type := (Ty.Cont t).S
@[reducible] def Ty.DenList (ts : List Ty) : Type := (Ty.ContList ts).S
@[reducible] def Ty.DenAt (l : LeanTaggedUnionSchema Ty) (t : Nat) : Type := (Ty.ContAt l t).S

-- the equations of today's `Ty.Den` still hold by `rfl`
example : Ty.Den .self = PUnit := rfl
example (a b : Ty) : Ty.Den (.fn a b) = (Ty.Den a → Ty.Den b) := rfl
example (a : Ty) : Ty.Den (.array a) = List (Ty.Den a) := rfl
example (a : Ty) : Ty.Den (.thunk a) = Ty.Den a := rfl
example (a b : Ty) (r : List Ty) :
    Ty.Den (.record ⟨a, b, r⟩) = (Ty.Den a × Ty.Den b × Ty.DenList r) := rfl
example (p : LeanPrimTy) : Ty.Den (.prim p) = p.denote := rfl
example (t : Ty) (ts : List Ty) : Ty.DenList (t :: ts) = (Ty.Den t × Ty.DenList ts) := rfl
example (l : LeanTaggedUnionSchema Ty) :
    Ty.Den (.taggedUnion l) = ((t : Fin l.length) × Ty.DenAt l t.val) := rfl
example (l : LeanTaggedUnionSchema Ty) : Ty.Den (.recTaggedUnion l) =
    WTree ((t : Fin l.length) × Ty.DenAt l t.val) (fun p => (Ty.ContAt l p.1.val).P p.2) := rfl

/-! Substitution that leaves the domain of an arrow alone (`Ty.Wf` keeps occurrences out
of it anyway), so that the unfolded domain *is* the domain, definitionally. -/
mutual
def subst (s : Ty) : Ty → Ty
  | .self => s
  | .familyMember i => .familyMember i
  | .shape sh => .shape (substShape s sh)
  | .recTaggedUnion l => .recTaggedUnion l
  | .recObject fs => .recObject fs
  | .recAlias b => .recAlias b
  | .mutualRecursiveFamily f => .mutualRecursiveFamily f
def substShape (s : Ty) : TyShape Ty → TyShape Ty
  | .prim p => .prim p
  | .fn a b => .fn a (subst s b)
  | .primCovariant c => .primCovariant (substCov s c)
  | .enum e => .enum e
  | .record fs => .record (substRecord s fs)
  | .taggedUnion l => .taggedUnion (substTU s l)
def substCov (s : Ty) : LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty
  | .array a => .array (subst s a)
  | .thunk a => .thunk (subst s a)
  | .lazy a => .lazy (subst s a)
def substList (s : Ty) : List Ty → List Ty
  | [] => []
  | a :: as => subst s a :: substList s as
def substCtors (s : Ty) : List (List Ty) → List (List Ty)
  | [] => []
  | a :: as => substList s a :: substCtors s as
def substNE (s : Ty) : NonEmptyList Ty → NonEmptyList Ty
  | ⟨a, as⟩ => ⟨subst s a, substList s as⟩
def substRecord (s : Ty) : LeanRecordSchema Ty → LeanRecordSchema Ty
  | ⟨a, b, rest⟩ => ⟨subst s a, subst s b, substList s rest⟩
def substTU (s : Ty) : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty
  | .payloadFirst f n r => .payloadFirst (substNE s f) (substList s n) (substCtors s r)
  | .skip c => .skip (substCP s c)
def substCP (s : Ty) : CtorsWithPayload Ty → CtorsWithPayload Ty
  | .here f r => .here (substNE s f) (substCtors s r)
  | .skip c => .skip (substCP s c)
end

theorem length_substCtors (s : Ty) : ∀ l, (substCtors s l).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (length_substCtors s l)
theorem length_substCP (s : Ty) : ∀ c, (substCP s c).length = c.length
  | .here _ r => by simp [substCP, CtorsWithPayload.length, length_substCtors]
  | .skip c => by simp [substCP, CtorsWithPayload.length, length_substCP s c]
theorem length_substTU (s : Ty) (l : LeanTaggedUnionSchema Ty) :
    (substTU s l).length = l.length := by
  cases l <;> simp [substTU, LeanTaggedUnionSchema.length, length_substCtors, length_substCP]

/-! `roll`: a value of an unfolded field is a shape of the payload with a value of the
binder in each hole.  Every clause is definitional — no `cast` anywhere. -/
section
variable (R : Ty)
local notation "X" => Ty.Den R

def Cont.Ext.pair {c d : Cont} {Y : Type} (x : c.Ext Y) (y : d.Ext Y) : (Cont.prod c d).Ext Y :=
  ⟨(x.1, y.1), fun | .inl p => x.2 p | .inr q => y.2 q⟩

def Cont.Ext.list {c : Cont} {Y α : Type} (f : α → c.Ext Y) : List α → (Cont.list c).Ext Y
  | [] => ⟨[], fun p => PEmpty.elim p⟩
  | x :: xs =>
      let h := f x
      let t := Cont.Ext.list f xs
      ⟨h.1 :: t.1, fun | .inl p => h.2 p | .inr q => t.2 q⟩

def Cont.Ext.pi {A : Type} {c : Cont} {Y : Type} (g : A → c.Ext Y) : (Cont.pi A c).Ext Y :=
  ⟨fun y => (g y).1, fun q => (g q.1).2 q.2⟩

mutual
def roll : (a : Ty) → Ty.Den (subst R a) → (Ty.Cont a).Ext X
  | .self, x => ⟨PUnit.unit, fun _ => x⟩
  | .familyMember _, x => PEmpty.elim x
  | .shape s, x => rollShape s x
  | .recTaggedUnion _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .recObject _, x => PEmpty.elim x
  | .recAlias _, x => PEmpty.elim x
  | .mutualRecursiveFamily _, x => PEmpty.elim x
def rollShape : (s : TyShape Ty) → Ty.Den (.shape (substShape R s)) → (Ty.ContShape s).Ext X
  | .prim _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .fn _ b, f => Cont.Ext.pi (fun y => roll b (f y))
  | .primCovariant c, x => rollCov c x
  | .enum _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .record ⟨a, b, rest⟩, ⟨x, y, zs⟩ =>
      Cont.Ext.pair (roll a x) (Cont.Ext.pair (roll b y) (rollList rest zs))
  | .taggedUnion l, ⟨t, v⟩ =>
      let r := rollAt l t.val v
      ⟨⟨⟨t.val, length_substTU R l ▸ t.isLt⟩, r.1⟩, r.2⟩
def rollCov : (c : LeanPrimTyCovariant Ty) →
    Ty.Den (.primCovariant (substCov R c)) → (Ty.ContCov c).Ext X
  | .array a, xs => Cont.Ext.list (fun x => roll a x) xs
  | .thunk a, x => roll a x
  | .lazy a, x => roll a x
def rollList : (ts : List Ty) → Ty.DenList (substList R ts) → (Ty.ContList ts).Ext X
  | [], _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | a :: as, ⟨x, xs⟩ => Cont.Ext.pair (roll a x) (rollList as xs)
def rollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    Ty.DenAt (substTU R l) t → (Ty.ContAt l t).Ext X
  | .payloadFirst ⟨a, as⟩ _ _, 0, ⟨x, xs⟩ => Cont.Ext.pair (roll a x) (rollList as xs)
  | .payloadFirst _ next _, 1, v => rollList next v
  | .payloadFirst _ _ rest, n + 2, v => rollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => rollAtCP rest n v
def rollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    (Ty.ContAtCP (substCP R c) t).S → (Ty.ContAtCP c t).Ext X
  | .here ⟨a, as⟩ _, 0, ⟨x, xs⟩ => Cont.Ext.pair (roll a x) (rollList as xs)
  | .here _ rest, n + 1, v => rollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => rollAtCP rest n v
def rollAtList : (cs : List (List Ty)) → (t : Nat) →
    (Ty.ContAtList (substCtors R cs) t).S → (Ty.ContAtList cs t).Ext X
  | [], _, v => PEmpty.elim v
  | fs :: _, 0, v => rollList fs v
  | _ :: rest, n + 1, v => rollAtList rest n v
end
end

/-- The introduction form: constructor `t` of `recTaggedUnion l`, from its unfolded
fields. -/
def mkRec (l : LeanTaggedUnionSchema Ty) (t : Fin l.length)
    (v : Ty.DenAt (substTU (.recTaggedUnion l) l) t.val) : Ty.Den (.recTaggedUnion l) :=
  let r := rollAt (.recTaggedUnion l) l t.val v
  WTree.mk ⟨t, r.1⟩ r.2

/-! A list of naturals, built and folded. -/
def natL : LeanTaggedUnionSchema Ty := .skip (.here ⟨.prim .nat, [.self]⟩ [])
def nil' : Ty.Den (.recTaggedUnion natL) := mkRec natL ⟨0, by decide⟩ PUnit.unit
def cons' (n : Nat) (xs : Ty.Den (.recTaggedUnion natL)) : Ty.Den (.recTaggedUnion natL) :=
  mkRec natL ⟨1, by decide⟩ (show Nat from n, xs, PUnit.unit)

def WTree.fold {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → WTree S P) → (P s → β) → β) : WTree S P → β
  | .mk s f => step s f (fun p => WTree.fold step (f p))

def sum' : Ty.Den (.recTaggedUnion natL) → Nat := WTree.fold fun s _ ih =>
  match s, ih with
  | ⟨⟨0, _⟩, _⟩, _ => 0
  | ⟨⟨1, _⟩, (n, _)⟩, ih => (show Nat from n) + ih (.inr (.inl PUnit.unit))

example : sum' (cons' 3 (cons' 4 nil')) = 7 := by decide
example : sum' (cons' 3 (cons' 4 nil')) = 7 := rfl

/-! `unroll`: the inverse direction, what the eliminators use. -/
section
variable (R : Ty)
local notation "X" => Ty.Den R

def Cont.Ext.fst {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) : c.Ext Y :=
  ⟨x.1.1, fun p => x.2 (.inl p)⟩
def Cont.Ext.snd {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) : d.Ext Y :=
  ⟨x.1.2, fun p => x.2 (.inr p)⟩
def Cont.Ext.unlist {c : Cont} {Y α : Type} (h : c.Ext Y → α) :
    (xs : List c.S) → (ListPos c.P xs → Y) → List α
  | [], _ => []
  | s :: ss, g => h ⟨s, fun p => g (.inl p)⟩ :: Cont.Ext.unlist h ss (fun q => g (.inr q))

mutual
def unroll : (a : Ty) → (Ty.Cont a).Ext X → Ty.Den (subst R a)
  | .self, x => x.2 PUnit.unit
  | .familyMember _, x => PEmpty.elim x.1
  | .shape s, x => unrollShape s x
  | .recTaggedUnion _, x => x.1
  | .recObject _, x => PEmpty.elim x.1
  | .recAlias _, x => PEmpty.elim x.1
  | .mutualRecursiveFamily _, x => PEmpty.elim x.1
def unrollShape : (s : TyShape Ty) → (Ty.ContShape s).Ext X → Ty.Den (.shape (substShape R s))
  | .prim _, x => x.1
  | .fn _ b, x => fun y => unroll b ⟨x.1 y, fun p => x.2 ⟨y, p⟩⟩
  | .primCovariant c, x => unrollCov c x
  | .enum _, x => x.1
  | .record ⟨a, b, rest⟩, x =>
      (unroll a x.fst, unroll b x.snd.fst, unrollList rest x.snd.snd)
  | .taggedUnion l, x =>
      ⟨⟨x.1.1.val, (length_substTU R l).symm ▸ x.1.1.isLt⟩,
        unrollAt l x.1.1.val ⟨x.1.2, x.2⟩⟩
def unrollCov : (c : LeanPrimTyCovariant Ty) →
    (Ty.ContCov c).Ext X → Ty.Den (.primCovariant (substCov R c))
  | .array a, x => Cont.Ext.unlist (fun y => unroll a y) x.1 x.2
  | .thunk a, x => unroll a x
  | .lazy a, x => unroll a x
def unrollList : (ts : List Ty) → (Ty.ContList ts).Ext X → Ty.DenList (substList R ts)
  | [], _ => PUnit.unit
  | a :: as, x => (unroll a x.fst, unrollList as x.snd)
def unrollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    (Ty.ContAt l t).Ext X → Ty.DenAt (substTU R l) t
  | .payloadFirst ⟨a, as⟩ _ _, 0, x => (unroll a x.fst, unrollList as x.snd)
  | .payloadFirst _ next _, 1, x => unrollList next x
  | .payloadFirst _ _ rest, n + 2, x => unrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => unrollAtCP rest n x
def unrollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    (Ty.ContAtCP c t).Ext X → (Ty.ContAtCP (substCP R c) t).S
  | .here ⟨a, as⟩ _, 0, x => (unroll a x.fst, unrollList as x.snd)
  | .here _ rest, n + 1, x => unrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => unrollAtCP rest n x
def unrollAtList : (cs : List (List Ty)) → (t : Nat) →
    (Ty.ContAtList cs t).Ext X → (Ty.ContAtList (substCtors R cs) t).S
  | [], _, x => PEmpty.elim x.1
  | fs :: _, 0, x => unrollList fs x
  | _ :: rest, n + 1, x => unrollAtList rest n x
end
end

/-- One level of a value of `recTaggedUnion l`: its tag and its unfolded fields, which is
what `recTaggedUnion_casesOn` dispatches on. -/
def unfoldRec (l : LeanTaggedUnionSchema Ty) :
    Ty.Den (.recTaggedUnion l) → (t : Fin l.length) × Ty.DenAt (substTU (.recTaggedUnion l) l) t.val
  | .mk ⟨t, s⟩ f => ⟨t, unrollAt (.recTaggedUnion l) l t.val ⟨s, f⟩⟩

def head' (xs : Ty.Den (.recTaggedUnion natL)) : Nat :=
  match unfoldRec natL xs with
  | ⟨⟨0, _⟩, _⟩ => 0
  | ⟨⟨1, _⟩, (n, _)⟩ => (show Nat from n)

example : head' (cons' 5 nil') = 5 := rfl
example : head' nil' = 0 := rfl

/-! Round trip `unroll ∘ roll = id`. -/
section
variable (R : Ty)

theorem unlist_list {c : Cont} {Y α : Type} (f : α → c.Ext Y) (h : c.Ext Y → α)
    (hr : ∀ x, h (f x) = x) : ∀ xs : List α,
    Cont.Ext.unlist h (Cont.Ext.list f xs).1 (Cont.Ext.list f xs).2 = xs
  | [] => rfl
  | x :: xs => by
      show h ⟨(f x).1, fun p => (f x).2 p⟩ :: _ = x :: xs
      rw [List.cons.injEq]
      exact ⟨hr x, unlist_list f h hr xs⟩

mutual
theorem unroll_roll : ∀ (a : Ty) (x : Ty.Den (subst R a)), unroll R a (roll R a x) = x
  | .self, _ => rfl
  | .familyMember _, x => PEmpty.elim x
  | .shape s, x => unroll_rollShape s x
  | .recTaggedUnion _, _ => rfl
  | .recObject _, x => PEmpty.elim x
  | .recAlias _, x => PEmpty.elim x
  | .mutualRecursiveFamily _, x => PEmpty.elim x
theorem unroll_rollShape : ∀ (s : TyShape Ty) (x : Ty.Den (.shape (substShape R s))),
    unrollShape R s (rollShape R s x) = x
  | .prim _, _ => rfl
  | .fn _ b, f => funext fun y => unroll_roll b (f y)
  | .primCovariant c, x => unroll_rollCov c x
  | .enum _, _ => rfl
  | .record ⟨a, b, rest⟩, ⟨x, y, zs⟩ => by
      show (unroll R a (roll R a x), unroll R b (roll R b y), unrollList R rest (rollList R rest zs)) = _
      rw [unroll_roll a x, unroll_roll b y, unroll_rollList rest zs]
      rfl
  | .taggedUnion l, ⟨t, v⟩ => by
      show (⟨⟨t.val, _⟩, unrollAt R l t.val (rollAt R l t.val v)⟩ : Ty.Den (.shape (substShape R (.taggedUnion l)))) = _
      rw [unroll_rollAt l t.val v]
theorem unroll_rollCov : ∀ (c : LeanPrimTyCovariant Ty) (x : Ty.Den (.primCovariant (substCov R c))),
    unrollCov R c (rollCov R c x) = x
  | .array a, xs => unlist_list _ _ (fun x => unroll_roll a x) xs
  | .thunk a, x => unroll_roll a x
  | .lazy a, x => unroll_roll a x
theorem unroll_rollList : ∀ (ts : List Ty) (x : Ty.DenList (substList R ts)),
    unrollList R ts (rollList R ts x) = x
  | [], _ => rfl
  | a :: as, ⟨x, xs⟩ => by
      show (unroll R a (roll R a x), unrollList R as (rollList R as xs)) = _
      rw [unroll_roll a x, unroll_rollList as xs]
theorem unroll_rollAt : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat) (v : Ty.DenAt (substTU R l) t),
    unrollAt R l t (rollAt R l t v) = v
  | .payloadFirst ⟨a, as⟩ _ _, 0, ⟨x, xs⟩ => by
      show (unroll R a (roll R a x), unrollList R as (rollList R as xs)) = _
      rw [unroll_roll a x, unroll_rollList as xs]
  | .payloadFirst _ next _, 1, v => unroll_rollList next v
  | .payloadFirst _ _ rest, n + 2, v => unroll_rollAtList rest n v
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, v => unroll_rollAtCP rest n v
theorem unroll_rollAtCP : ∀ (c : CtorsWithPayload Ty) (t : Nat) (v : (Ty.ContAtCP (substCP R c) t).S),
    unrollAtCP R c t (rollAtCP R c t v) = v
  | .here ⟨a, as⟩ _, 0, ⟨x, xs⟩ => by
      show (unroll R a (roll R a x), unrollList R as (rollList R as xs)) = _
      rw [unroll_roll a x, unroll_rollList as xs]
  | .here _ rest, n + 1, v => unroll_rollAtList rest n v
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, v => unroll_rollAtCP rest n v
theorem unroll_rollAtList : ∀ (cs : List (List Ty)) (t : Nat) (v : (Ty.ContAtList (substCtors R cs) t).S),
    unrollAtList R cs t (rollAtList R cs t v) = v
  | [], _, v => PEmpty.elim v
  | fs :: _, 0, v => unroll_rollList fs v
  | _ :: rest, n + 1, v => unroll_rollAtList rest n v
end
end

/-! Round trip `roll ∘ unroll = id` on `Cont.Ext`. -/
section
variable (R : Ty)

theorem Cont.Ext.pair_fst_snd {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) :
    Cont.Ext.pair x.fst x.snd = x := by
  obtain ⟨⟨s, t⟩, f⟩ := x
  exact congrArg (Sigma.mk (s, t)) (funext fun | .inl _ => rfl | .inr _ => rfl)

theorem Cont.Ext.const_eta {A Y : Type} (s : A) (f : (Cont.const A).P s → Y) :
    (⟨s, fun p => PEmpty.elim p⟩ : (Cont.const A).Ext Y) = ⟨s, f⟩ :=
  congrArg (Sigma.mk s) (funext fun p => PEmpty.elim p)

theorem list_unlist {c : Cont} {Y α : Type} (f : α → c.Ext Y) (h : c.Ext Y → α)
    (hr : ∀ e, f (h e) = e) : ∀ (ss : List c.S) (g : ListPos c.P ss → Y),
    Cont.Ext.list f (Cont.Ext.unlist h ss g) = ⟨ss, g⟩
  | [], g => congrArg (Sigma.mk []) (funext fun p => PEmpty.elim p)
  | s :: ss, g => by
      have ih := list_unlist f h hr ss (fun q => g (.inr q))
      have hx := hr ⟨s, fun p => g (.inl p)⟩
      show (⟨_, _⟩ : (Cont.list c).Ext Y) = _
      generalize f (h ⟨s, fun p => g (.inl p)⟩) = A at hx ⊢
      generalize Cont.Ext.list f (Cont.Ext.unlist h ss fun q => g (.inr q)) = B at ih ⊢
      subst hx ih
      exact congrArg (Sigma.mk (s :: ss)) (funext fun | .inl _ => rfl | .inr _ => rfl)

mutual
theorem roll_unroll : ∀ (a : Ty) (x : (Ty.Cont a).Ext (Ty.Den R)), roll R a (unroll R a x) = x
  | .self, _ => rfl
  | .familyMember _, x => PEmpty.elim x.1
  | .shape s, x => roll_unrollShape s x
  | .recTaggedUnion _, ⟨s, f⟩ => Cont.Ext.const_eta s f
  | .recObject _, x => PEmpty.elim x.1
  | .recAlias _, x => PEmpty.elim x.1
  | .mutualRecursiveFamily _, x => PEmpty.elim x.1
theorem roll_unrollShape : ∀ (s : TyShape Ty) (x : (Ty.ContShape s).Ext (Ty.Den R)),
    rollShape R s (unrollShape R s x) = x
  | .prim _, ⟨s, f⟩ => Cont.Ext.const_eta s f
  | .fn a b, x => by
      revert x
      show ∀ x : (Cont.pi (Ty.Cont a).S (Ty.Cont b)).Ext (Ty.Den R),
        Cont.Ext.pi (fun y => roll R b (unroll R b ⟨x.1 y, fun p => x.2 ⟨y, p⟩⟩)) = x
      intro ⟨s, f⟩
      have hb : (fun y => roll R b (unroll R b ⟨s y, fun p => f ⟨y, p⟩⟩))
          = fun y => ⟨s y, fun p => f ⟨y, p⟩⟩ := funext fun y => roll_unroll b _
      show Cont.Ext.pi (fun y => roll R b (unroll R b ⟨s y, fun p => f ⟨y, p⟩⟩)) = _
      rw [hb]
      rfl
  | .primCovariant c, x => roll_unrollCov c x
  | .enum _, ⟨s, f⟩ => Cont.Ext.const_eta s f
  | .record ⟨a, b, rest⟩, x => by
      revert x
      show ∀ x : (Cont.prod (Ty.Cont a) (Cont.prod (Ty.Cont b) (Ty.ContList rest))).Ext (Ty.Den R),
        Cont.Ext.pair (roll R a (unroll R a x.fst))
          (Cont.Ext.pair (roll R b (unroll R b x.snd.fst)) (rollList R rest (unrollList R rest x.snd.snd))) = x
      intro x
      rw [roll_unroll a, roll_unroll b, roll_unrollList rest, Cont.Ext.pair_fst_snd,
        Cont.Ext.pair_fst_snd]
  | .taggedUnion l, x => by
      revert x
      show ∀ x : (Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t.val)).Ext (Ty.Den R),
        rollShape R (.taggedUnion l) (unrollShape R (.taggedUnion l) x) = x
      intro ⟨⟨t, s⟩, f⟩
      exact congrArg (fun r : (Ty.ContAt l t.val).Ext (Ty.Den R) =>
        (⟨⟨t, r.1⟩, r.2⟩ : (Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t.val)).Ext (Ty.Den R)))
        (roll_unrollAt l t.val ⟨s, f⟩)
theorem roll_unrollCov : ∀ (c : LeanPrimTyCovariant Ty) (x : (Ty.ContCov c).Ext (Ty.Den R)),
    rollCov R c (unrollCov R c x) = x
  | .array a, ⟨ss, g⟩ => list_unlist _ _ (fun e => roll_unroll a e) ss g
  | .thunk a, x => roll_unroll a x
  | .lazy a, x => roll_unroll a x
theorem roll_unrollList : ∀ (ts : List Ty) (x : (Ty.ContList ts).Ext (Ty.Den R)),
    rollList R ts (unrollList R ts x) = x
  | [], ⟨s, f⟩ => Cont.Ext.const_eta s f
  | a :: as, x => by
      revert x
      show ∀ x : (Cont.prod (Ty.Cont a) (Ty.ContList as)).Ext (Ty.Den R),
        Cont.Ext.pair (roll R a (unroll R a x.fst)) (rollList R as (unrollList R as x.snd)) = x
      intro x
      rw [roll_unroll a, roll_unrollList as, Cont.Ext.pair_fst_snd]
theorem roll_unrollAt : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat) (x : (Ty.ContAt l t).Ext (Ty.Den R)),
    rollAt R l t (unrollAt R l t x) = x
  | .payloadFirst ⟨a, as⟩ _ _, 0, x => by
      revert x
      show ∀ x : (Cont.prod (Ty.Cont a) (Ty.ContList as)).Ext (Ty.Den R),
        Cont.Ext.pair (roll R a (unroll R a x.fst)) (rollList R as (unrollList R as x.snd)) = x
      intro x
      rw [roll_unroll a, roll_unrollList as, Cont.Ext.pair_fst_snd]
  | .payloadFirst _ next _, 1, x => roll_unrollList next x
  | .payloadFirst _ _ rest, n + 2, x => roll_unrollAtList rest n x
  | .skip _, 0, ⟨s, f⟩ => Cont.Ext.const_eta s f
  | .skip rest, n + 1, x => roll_unrollAtCP rest n x
theorem roll_unrollAtCP : ∀ (c : CtorsWithPayload Ty) (t : Nat) (x : (Ty.ContAtCP c t).Ext (Ty.Den R)),
    rollAtCP R c t (unrollAtCP R c t x) = x
  | .here ⟨a, as⟩ _, 0, x => by
      revert x
      show ∀ x : (Cont.prod (Ty.Cont a) (Ty.ContList as)).Ext (Ty.Den R),
        Cont.Ext.pair (roll R a (unroll R a x.fst)) (rollList R as (unrollList R as x.snd)) = x
      intro x
      rw [roll_unroll a, roll_unrollList as, Cont.Ext.pair_fst_snd]
  | .here _ rest, n + 1, x => roll_unrollAtList rest n x
  | .skip _, 0, ⟨s, f⟩ => Cont.Ext.const_eta s f
  | .skip rest, n + 1, x => roll_unrollAtCP rest n x
theorem roll_unrollAtList : ∀ (cs : List (List Ty)) (t : Nat) (x : (Ty.ContAtList cs t).Ext (Ty.Den R)),
    rollAtList R cs t (unrollAtList R cs t x) = x
  | [], _, x => PEmpty.elim x.1
  | fs :: _, 0, x => roll_unrollList fs x
  | _ :: rest, n + 1, x => roll_unrollAtList rest n x
end
end

/-! Positivity is *strict* positivity (checked against the real `Ty.WfIn`). -/
/-- `(self → Nat) → Nat`: a positive but not strictly positive occurrence, refused. -/
example : ¬ LeanScript.Ty.WfIn 1 (.fn (.fn .self (.prim .nat)) (.prim .nat)) := fun h =>
  LeanScript.Ty.not_wf_self
    (LeanScript.Ty.wfIn_domain_of_wfIn_fn (LeanScript.Ty.wfIn_domain_of_wfIn_fn h))
/-- `(Nat → self) → Nat`: a negative occurrence, refused. -/
example : ¬ LeanScript.Ty.WfIn 1 (.fn (.fn (.prim .nat) .self) (.prim .nat)) := fun h => by
  have h0 := LeanScript.Ty.wfIn_domain_of_wfIn_fn h
  have hs : LeanScript.Ty.WfShapeIn 0 (.fn (.prim .nat) .self) ∨
      LeanScript.Ty.WfShapeIn 0 (.fn (.prim .nat) .self) := LeanScript.Ty.wfHere_of_wfIn h0
  rcases hs with hs | hs <;> cases hs with | fn _ hb => exact LeanScript.Ty.not_wf_self hb

end LeanScript.Proto
