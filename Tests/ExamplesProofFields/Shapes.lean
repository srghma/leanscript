/-
# Seven user-defined types whose fields contain proofs — one per shape of `Ty`

For each of the seven shapes a *user-defined* type can have in the backend's type
language (`enum`, `record`, `taggedUnion`, `recTaggedUnion`, `recObject`, `recAlias`,
`mutualRecursiveFamily`) this file writes down

* a Lean declaration of that shape **that has proof fields**,
* the *erased twin*: the same declaration with every `Prop`-typed field deleted, which
  is what the backend sees and what `ExamplesProofFields/ShapesTy.lean` writes down as a
  `Ty`,
* the erasure map from the first to the second, and a proof that it is **injective**.

The injectivity proofs are the point of the file.  They say that deleting the proof
fields loses *no* information: two values of the proof-carrying type that erase to the
same runtime value are equal, because their data fields are equal and their proof fields
are equal by proof irrelevance.  So a schema (`LeanEnumSchema`, `LeanRecordSchema`, …)
that also recorded the proof fields would record something already determined by what it
holds.

What erasure is *not* is surjective: `Status 5` has no `error` value, but `StatusE.error`
exists.  That asymmetry — the erased type has values the proof-carrying one does not — is
the whole content of the termination question, and it is the subject of
`ExamplesProofFields/Countdown.lean`.

Nothing here is compiled to JavaScript; this is a specimen of erased proof fields.
-/

namespace ExamplesProofFields

/-! ## Two lemmas used by the recursive cases -/

/-- A `List.map` by an elementwise-injective function is injective. -/
theorem listMapInj {α β : Type} (f : α → β) : ∀ (l₁ l₂ : List α),
    (∀ x ∈ l₁, ∀ y, f x = f y → x = y) → l₁.map f = l₂.map f → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h; cases l₂ <;> simp_all
  | cons a as ih =>
      intro l₂ hinj h
      cases l₂ with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hab : a = b := hinj a (by simp) b h.1
          have hrest : as = bs := ih bs (fun x hx y hxy => hinj x (by simp [hx]) y hxy) h.2
          simp [hab, hrest]

/-- The same for `Array.map`. -/
theorem arrayMapInj {α β : Type} (f : α → β) (a b : Array α)
    (hinj : ∀ x ∈ a, ∀ y, f x = f y → x = y) (h : a.map f = b.map f) : a = b := by
  have h' : a.toList.map f = b.toList.map f := by
    simpa using congrArg Array.toList h
  have := listMapInj f a.toList b.toList
    (fun x hx y hxy => hinj x (by simpa using hx) y hxy) h'
  exact Array.toList_inj.mp this

/-! ## 1. `enum` — a sum of three constructors that carry nothing but proofs

The question's own example.  Every field is a proof, so every constructor has zero
runtime fields and three constructors remain: an `enum`. -/

inductive Status (n : Nat) where
  | ok                               -- 0 fields
  | warn  (h : n > 0)                -- 1 proof field
  | error (h1 : n = 0) (h2 : n ≠ 1)  -- 2 proof fields

/-- What is left of `Status` once the proof fields are deleted: three constructors, no
    fields — which is exactly what the backend sees. -/
inductive StatusE where
  | ok
  | warn
  | error

/-- Erasure: the constructor, and nothing else. -/
def Status.erase {n : Nat} : Status n → StatusE
  | .ok => .ok
  | .warn _ => .warn
  | .error _ _ => .error

theorem Status.erase_injective {n : Nat} :
    ∀ a b : Status n, a.erase = b.erase → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Status.erase]

/-- The converse fails, and not by accident: `StatusE` has three values for every `n`,
    while `Status 5` has only two — no `error`.  The erased type is the *larger* one, and
    `StatusE.error` is a runtime value with no proof-carrying counterpart. -/
theorem Status.erase_not_surjective : ¬ ∃ s : Status 5, s.erase = StatusE.error := by
  intro ⟨s, h⟩
  cases s with
  | ok => simp [Status.erase] at h
  | warn _ => simp [Status.erase] at h
  | error h1 _ => exact absurd h1 (by decide)

/-! ## 2. `record` — one constructor, two data fields and two proof fields -/

structure Window (cap : Nat) where
  lo : Nat
  hi : Nat
  hlo : lo ≤ hi
  hcap : hi ≤ cap

/-- The erased twin: two `Nat` fields, so a `record` of two fields. -/
structure WindowE where
  lo : Nat
  hi : Nat

def Window.erase {cap : Nat} (w : Window cap) : WindowE := ⟨w.lo, w.hi⟩

theorem Window.erase_injective {cap : Nat} :
    ∀ a b : Window cap, a.erase = b.erase → a = b := by
  intro ⟨lo₁, hi₁, _, _⟩ ⟨lo₂, hi₂, _, _⟩ h
  simp only [Window.erase, WindowE.mk.injEq] at h
  simp [h.1, h.2]

/-! ## 3. `taggedUnion` — two constructors, one of which keeps a data field -/

inductive Reading (cap : Nat) where
  | missing (h : 0 < cap)
  | value (v : Nat) (h : v ≤ cap)

/-- The erased twin: `[[], [nat]]`, the shape of `Option Nat`. -/
inductive ReadingE where
  | missing
  | value (v : Nat)

def Reading.erase {cap : Nat} : Reading cap → ReadingE
  | .missing _ => .missing
  | .value v _ => .value v

theorem Reading.erase_injective {cap : Nat} :
    ∀ a b : Reading cap, a.erase = b.erase → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Reading.erase]

/-! ## 4. `recTaggedUnion` — a recursive sum with a proof field in one constructor -/

inductive NTree where
  | leaf
  | node (n : Nat) (h : 0 < n) (l r : NTree)

/-- The erased twin: `[[], [nat, self 0, self 0]]`. -/
inductive NTreeE where
  | leaf
  | node (n : Nat) (l r : NTreeE)

def NTree.erase : NTree → NTreeE
  | .leaf => .leaf
  | .node n _ l r => .node n l.erase r.erase

theorem NTree.erase_injective : ∀ a b : NTree, a.erase = b.erase → a = b := by
  intro a
  induction a with
  | leaf => intro b h; cases b <;> simp_all [NTree.erase]
  | node n hn l r ihl ihr =>
      intro b h
      cases b with
      | leaf => simp [NTree.erase] at h
      | node m hm l' r' =>
          simp only [NTree.erase, NTreeE.node.injEq] at h
          obtain ⟨hnm, hl, hr⟩ := h
          subst hnm
          simp [ihl l' hl, ihr r' hr]

/-! ### The rank survives erasure too

A kind-S recursion over `NTree` is ranked by the *size* of its argument, and the backend
has to compute that size from the erased value.  It gets the same number: proof fields
contribute no nodes, so the structural rank of a proof-carrying value and of its erased
twin agree.  (This is what makes a runtime `sizeOf` primitive a sound rank for kind S.) -/

def NTree.size : NTree → Nat
  | .leaf => 1
  | .node _ _ l r => 1 + l.size + r.size

def NTreeE.size : NTreeE → Nat
  | .leaf => 1
  | .node _ l r => 1 + l.size + r.size

theorem NTree.size_erase : ∀ t : NTree, t.erase.size = t.size := by
  intro t
  induction t with
  | leaf => rfl
  | node n hn l r ihl ihr => simp [NTree.erase, NTree.size, NTreeE.size, ihl, ihr]

/-! ## 5. `recObject` — a recursive single-constructor type with a proof field

Lean accepts a recursive `structure`; the recursive occurrence is nested inside an
`Array`.  A proof field may mention the earlier *scalar* fields (`0 < n`); it may not
mention the nested field itself, since the nested occurrence is not yet available when
the field's type is elaborated (`h : kids.size < 4` is rejected by the kernel). -/

structure Tag where
  n : Nat
  h : 0 < n
  kids : Array Tag

/-- The erased twin: two fields, `nat` and `array (self 0)`. -/
structure TagE where
  n : Nat
  kids : Array TagE

def Tag.erase (t : Tag) : TagE := ⟨t.n, t.kids.map Tag.erase⟩
decreasing_by
  rename_i x hx
  have h1 := Array.sizeOf_lt_of_mem hx
  cases t
  simp_all
  omega

theorem Tag.erase_injective : ∀ a b : Tag, a.erase = b.erase → a = b := by
  intro a
  induction hs : sizeOf a using Nat.strongRecOn generalizing a with
  | _ m ih =>
    intro b hab
    subst hs
    obtain ⟨n₁, hn₁, k₁⟩ := a
    obtain ⟨n₂, hn₂, k₂⟩ := b
    simp only [Tag.erase, TagE.mk.injEq] at hab
    obtain ⟨hn, hk⟩ := hab
    subst hn
    have hkids : k₁ = k₂ := by
      refine arrayMapInj _ k₁ k₂ ?_ hk
      intro x hx y hxy
      have hlt : sizeOf x < sizeOf (Tag.mk n₁ hn₁ k₁) := by
        have := Array.sizeOf_lt_of_mem hx
        simp
        omega
      exact ih (sizeOf x) hlt x rfl y hxy
    simp [hkids]

/-! ## 6. `recAlias` — a recursive **newtype** that does not look like one

`Rose` is written with two fields, so it reads as a `recObject`; one of them is a proof,
so at run time it has a single field and is a *newtype*: the wrapper is erased and its
`Ty` is `recAlias (array (self 0))`.  A `Rose` is `[[], [[]]]` in JavaScript — an array
of arrays, with no object anywhere.  This is the shape-changing effect of proof fields in
its clearest form. -/

structure Rose (cap : Nat) where
  kids : Array (Rose cap)
  h : 0 < cap

/-- The erased twin: a newtype over `Array (self 0)`, i.e. nothing but nested arrays. -/
inductive RoseE where
  | mk (kids : Array RoseE)

def Rose.erase {cap : Nat} (r : Rose cap) : RoseE := .mk (r.kids.map Rose.erase)
decreasing_by
  rename_i x hx
  have h1 := Array.sizeOf_lt_of_mem hx
  cases r
  simp_all
  omega

theorem Rose.erase_injective {cap : Nat} :
    ∀ a b : Rose cap, a.erase = b.erase → a = b := by
  intro a
  induction hs : sizeOf a using Nat.strongRecOn generalizing a with
  | _ m ih =>
    intro b hab
    subst hs
    obtain ⟨k₁, hc₁⟩ := a
    obtain ⟨k₂, hc₂⟩ := b
    simp only [Rose.erase, RoseE.mk.injEq] at hab
    have hkids : k₁ = k₂ := by
      refine arrayMapInj _ k₁ k₂ ?_ hab
      intro x hx y hxy
      have hlt : sizeOf x < sizeOf (Rose.mk (cap := cap) k₁ hc₁) := by
        have := Array.sizeOf_lt_of_mem hx
        simp
        omega
      exact ih (sizeOf x) hlt x rfl y hxy
    simp [hkids]

/-! ## 7. `mutualRecursiveFamily` — a genuinely mutual pair, both members with proofs -/

mutual

inductive PNode (cap : Nat) where
  | node (label : Nat) (h : label < cap) (kids : PForest cap)

inductive PForest (cap : Nat) where
  | nil (h : 0 < cap)
  | cons (hd : PNode cap) (tl : PForest cap)

end

mutual

/-- The erased twin of `PNode`: a record of `nat` and member `1`. -/
inductive PNodeE where
  | node (label : Nat) (kids : PForestE)

/-- The erased twin of `PForest`: `[[], [self 0, self 1]]`. -/
inductive PForestE where
  | nil
  | cons (hd : PNodeE) (tl : PForestE)

end

mutual

def PNode.erase {cap : Nat} : PNode cap → PNodeE
  | .node l _ ks => .node l ks.erase

def PForest.erase {cap : Nat} : PForest cap → PForestE
  | .nil _ => .nil
  | .cons hd tl => .cons hd.erase tl.erase

end

mutual

theorem PNode.erase_injective {cap : Nat} :
    ∀ a b : PNode cap, a.erase = b.erase → a = b := by
  intro a b h
  cases a with
  | node l₁ h₁ k₁ =>
    cases b with
    | node l₂ h₂ k₂ =>
      simp only [PNode.erase, PNodeE.node.injEq] at h
      obtain ⟨hl, hk⟩ := h
      subst hl
      simp [PForest.erase_injective k₁ k₂ hk]

theorem PForest.erase_injective {cap : Nat} :
    ∀ a b : PForest cap, a.erase = b.erase → a = b := by
  intro a b h
  cases a with
  | nil h₁ =>
    cases b with
    | nil h₂ => rfl
    | cons _ _ => simp [PForest.erase] at h
  | cons hd₁ tl₁ =>
    cases b with
    | nil _ => simp [PForest.erase] at h
    | cons hd₂ tl₂ =>
      simp only [PForest.erase, PForestE.cons.injEq] at h
      simp [PNode.erase_injective hd₁ hd₂ h.1, PForest.erase_injective tl₁ tl₂ h.2]

end

/-! ## What a proof field can and cannot carry

All seven erasure maps are injective for one reason, worth stating on its own: a function
of a proof is constant, so **no run-time quantity can depend on a proof field**.  That is
why preserving the proof fields inside `LeanEnumSchema` and the other schemas would not
make a single measure computable that is not computable now. -/

theorem measure_indep_of_proof {p : Prop} (f : p → Nat) (h₁ h₂ : p) : f h₁ = f h₂ := by
  rw [proof_irrel h₁ h₂]

/-- The same fact for a proof-carrying *field*: a measure over `Window cap` is a measure
    over the two numbers, however it is written. -/
theorem window_measure_indep {cap : Nat} (f : Window cap → Nat)
    (lo hi : Nat) (h₁ h₁' : lo ≤ hi) (h₂ h₂' : hi ≤ cap) :
    f ⟨lo, hi, h₁, h₂⟩ = f ⟨lo, hi, h₁', h₂'⟩ := by
  rw [proof_irrel h₁ h₁', proof_irrel h₂ h₂']

end ExamplesProofFields
