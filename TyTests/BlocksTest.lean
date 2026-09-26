module

public import LeanScript.Two

@[expose] public section

set_option autoImplicit false

/-!
# Design N: declared datatypes (`LeanScript`)

The examples of `proposals/NomTyToy.lean`, on the real type language: `List Nat` as a
block, then a second block holding `LitExprS` with `swap` and a rose tree that stores an
older `List Nat`.  Everything is checked by `rfl`/`decide`, and the forms that cannot be
written are pinned with `#guard_msgs`.
-/

namespace BlocksTest

open LeanScript

/-! ## Closed types without a signature -/

example : Ty.Den .nil .bool = Bool := rfl
example : Ty.Den .nil (Ty.option .nat) = Option Nat := rfl
example : Ty.Den .nil (.array (.prim .string)) = Array String := rfl
example : Ty.Den .nil (.enum {}) = Fin 3 := rfl
example : Ty.Den .nil (.prim (.stringPos "ab")) = String.Pos "ab" := rfl

/-- Equality of types is decided. -/
example : (Ty.option (.nat : Ty []) == Ty.option .nat) = true := by decide
example : (Ty.option (.nat : Ty []) == Ty.option .bool) = false := by decide

/-! ## Block 1: `List Nat` -/

/-- `List Nat := nil | cons Nat List`; `nil` is the base constructor. -/
def listBody : Mems [] 1 0 :=
  .cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil

/-- The signature with one block. -/
def Δ₁ : DSig [0] := .cons .nil 0 listBody

/-- `List Nat` is a name. -/
def listNat : Ty [0] := .data (.here 0)

example : (Δ₁.block .here).unfold 0 = .union (.two .nullary (.fields (.cons .nat (.one listNat)))) :=
  rfl
example : Ty.Den Δ₁ ((Δ₁.block .here).unfold 0) = Option (Nat × Ty.Den Δ₁ listNat) := rfl

def nil' : Ty.Den Δ₁ listNat := Δ₁.dataIn .here 0 none
def cons' (x : Nat) (xs : Ty.Den Δ₁ listNat) : Ty.Den Δ₁ listNat := Δ₁.dataIn .here 0 (some (x, xs))

def sum' (v : Ty.Den Δ₁ listNat) : Nat :=
  Δ₁.dataRec .here (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × (Ty.Den Δ₁ listNat × Nat))) with
        | none => 0
        | some (n, _, r) => Nat.add n r
      r) 0 v

example : sum' (cons' 1 (cons' 2 (cons' 3 nil'))) = 6 := rfl

def head? (v : Ty.Den Δ₁ listNat) : Option Nat :=
  match (Δ₁.dataOut .here 0 v : Option (Nat × Ty.Den Δ₁ listNat)) with
  | none => none
  | some (n, _) => some n

example : head? (cons' 7 nil') = some 7 := rfl
example : head? nil' = none := rfl

/-- The two values the structural proof picks for `List Nat`: `[]` and `[0]`. -/
example : head? (Ty.twoDen Δ₁ listNat).x = none := rfl
example : head? (Ty.twoDen Δ₁ listNat).y = some 0 := rfl

/-! ## Block 2: `LitExprS` with `swap`, and a rose tree that stores `List Nat`s

Member `0` is `LitExprS (Nat × Bool)`, member `1` is `LitExprS (Bool × Nat)`, member `2` is
`Rose := node (List Nat) (Array Rose)`.  The older `List Nat` is used by name through `old`. -/

def block₂ : Mems [0] 3 0 :=
  .cons (.union (.here (.fields (.one (.old (.pair .nat .bool))))
          (.two (.fields (.cons (.old .nat) (.one (.old .bool)))) (.fields (.one (.hole 1 (by decide)))))))
  (.cons (.union (.here (.fields (.one (.old (.pair .bool .nat))))
          (.two (.fields (.cons (.old .bool) (.one (.old .nat)))) (.fields (.one (.hole 0 (by decide)))))))
  (.cons (.record (.old listNat) (.one (.array (.hole 2 (by decide)))))
  .nil))

def Δ₂ : DSig [2, 0] := .cons Δ₁ 2 block₂

def litSNB : Ty [2, 0] := .data (.here 0)
def litSBN : Ty [2, 0] := .data (.here 1)
def rose : Ty [2, 0] := .data (.here 2)
def listNat₂ : Ty [2, 0] := .data (.there (.here 0))

/-- **Canonical by name**: `List Nat` weakened into the bigger signature is literally the name
    `List Nat` there, and the rose tree's field has that type. -/
example : (Ty.weaken listNat : Ty [2, 0]) = listNat₂ := rfl
example : (Δ₂.block .here).unfold 2 = .record listNat₂ (.one (.array rose)) := rfl
/-- …and old values are values in the bigger signature, with no conversion. -/
example : Ty.Den Δ₂ listNat₂ = Ty.Den Δ₁ listNat := rfl
/-- The older block is found from the bigger signature, with its names renamed. -/
example : (Δ₂.block (.there .here)).unfold 0 =
    .union (.two .nullary (.fields (.cons .nat (.one listNat₂)))) := rfl

example : Ty.Den Δ₂ ((Δ₂.block .here).unfold 0) =
    ((Nat × Bool) ⊕ ((Nat × Bool) ⊕ Ty.Den Δ₂ litSBN)) := rfl
example : Ty.Den Δ₂ ((Δ₂.block .here).unfold 2) =
    (Ty.Den Δ₁ listNat × Array (Ty.Den Δ₂ rose)) := rfl

/-- The answer type of each member (`eval : LitExprS α → α`; the rose tree's sum). -/
def answer₂ : Fin 3 → Ty [2, 0]
  | ⟨0, _⟩ => .pair .nat .bool
  | ⟨1, _⟩ => .pair .bool .nat
  | ⟨2, _⟩ => .nat

def litS_litBN (b : Bool) (a : Nat) : Ty.Den Δ₂ litSBN := Δ₂.dataIn .here 1 (.inl (b, a))
def litS_swap (e : Ty.Den Δ₂ litSBN) : Ty.Den Δ₂ litSNB := Δ₂.dataIn .here 0 (.inr (.inr e))
def rose_node (xs : Ty.Den Δ₁ listNat) (cs : Array (Ty.Den Δ₂ rose)) : Ty.Den Δ₂ rose :=
  Δ₂.dataIn .here 2 (xs, cs)

/-- One fold for the whole block, answering a different type at each member; the rose
    tree's branch calls the *older* block's fold `sum'` on its `List Nat` field. -/
def eval₂ (j : Fin 3) (v : Ty.Den Δ₂ (.data (.here j))) : Ty.Den Δ₂ (answer₂ j) :=
  Δ₂.dataRec .here answer₂ (fun
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
        match (x : Ty.Den Δ₁ listNat × Array (Ty.Den Δ₂ rose × Nat)) with
        | (xs, cs) => Nat.add (sum' xs) (cs.foldl (fun acc c => Nat.add acc c.2) 0)
      r) j v

example : eval₂ 0 (litS_swap (litS_litBN true 3)) = ((3, true) : Nat × Bool) := rfl
example :
    eval₂ 2 (rose_node (cons' 1 nil')
      #[rose_node (cons' 10 (cons' 20 nil')) #[], rose_node nil' #[]]) = (31 : Nat) := rfl

/-- The older block, folded from the bigger signature, with an answer in the bigger one. -/
def length₂ (v : Ty.Den Δ₂ listNat₂) : Nat :=
  Δ₂.dataRec (.there .here) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × (Ty.Den Δ₂ listNat₂ × Nat))) with
        | none => 0
        | some (_, _, r) => Nat.succ r
      r) 0 v

example : length₂ (cons' 5 (cons' 6 nil')) = 2 := rfl

/-- `Ty.twoDen` in the bigger signature: the rose tree's two values differ in their list. -/
example : head? (Δ₂.dataOut .here 2 (Ty.twoDen Δ₂ rose).x).1 = none := rfl
example : head? (Δ₂.dataOut .here 2 (Ty.twoDen Δ₂ rose).y).1 = some 0 := rfl

/-! ## What can no longer be written -/

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
error: Unknown constant `LeanScript.Ctors.one`

Note: Inferred this name from the expected resulting type of `.one`:
  Ctors [] ?m.3
-/
#guard_msgs in
example : Ty [] := .union (.one .nullary) (h := .here)

-- Two points are only ever `bool`: a union none of whose constructors has fields is refused,
-- closed or declared (and three or more field-less constructors are only ever an `enum`).
/--
error: failed to synthesize instance of type class
  UnionShape [false, false]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Ty [] := .union (.two .nullary .nullary)

/--
error: failed to synthesize instance of type class
  UnionShape [false, false, false]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Ty [] := .union (.cons .nullary (.two .nullary .nullary))

/--
error: failed to synthesize instance of type class
  UnionShape [false, false]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Mems [] 1 0 := .cons (.union (.two₁ .nullary .nullary)) .nil

-- A member that wraps an older type as it is would be a copy of it under a new name (a copy
-- of `bool` would be a second type of two points).
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (Fld.old Ty.bool).isOld = false
is false
-/
#guard_msgs in
example : Mems [] 1 0 := .cons (.wrap (.old .bool)) .nil

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
example : Mems [] 1 0 := .cons (.wrap (.array (.old listNat))) .nil

-- The other leaves of two values are refused: two points are only ever `bool`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (LeanPrimTy.bitvec 1 ⋯).Nondeg = true
is false
-/
#guard_msgs in
example : Ty [] := .prim (.bitvec 1)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (LeanPrimTy.stringPos "a").Nondeg = true
is false
-/
#guard_msgs in
example : Ty [] := .prim (.stringPos "a")

-- `String.Pos ""` has one value: it is not a leaf.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (LeanPrimTy.stringPos "").Nondeg = true
is false
-/
#guard_msgs in
example : Ty [] := .prim (.stringPos "")

end BlocksTest

end
