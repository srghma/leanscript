module
public import LeanScript.Expr.Term
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# Writing a `Term` with the flat constructors

`LeanScript.Term` is split into the syntactic categories of A-normal form —
`LeanScript.Ref`, `LeanScript.Callee`, `LeanScript.Atom`, `LeanScript.Comp` and
`LeanScript.Term` itself — so where only an atom may stand, the grammar only has atoms.

This module gives back the **flat** way of writing a term, one function per constructor of
the categories, each returning a `Term`: `Term.var x`, `Term.ap f a`, `Term.bool_casesOn c t
e`, `Term.record_mk fs fields`, …  Their operands are given as *terms*, together with a proof
that each is in the category the grammar asks for (`hAnf`, written by the default tactic
`head_ok`): that a scrutinee is a name (`Head.isName`), that an argument is an atom
(`Head.isAtom`), that a callee is a name or an application (`Head.isCallee`).  The proof is
what lets the operand be read in its category (`Term.toRef`, `Term.toAtom`,
`Term.toCallee`), and the node lands in the category of its head (`Term.ofComp`: a closed
value is an atom).  So a term can be written exactly as it reads,

```lean
(.lam (.ap (.var (v♯1)) (.var (v♯0))) : Term sg [_] _ (σ ⇒ τ) .lam)
```

and it elaborates to the split constructors.  `#leanscript_to_term` builds its terms with
these functions and then unfolds them, so what it emits is the split constructors
themselves.

The heads the categories can have (`Comp.isAtom_head`, `Comp.isBindable_head`) are what
makes the reading total: a computation is an atom exactly when it is a closed value, and it
is always something a `let` may bind.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-! ## The heads of the categories -/

namespace Head

/-- The heads a computation or a constructor can have: it is an atom exactly when it is a
    closed value, and it is something a `let` may bind. -/
def IsCompHead (k : Head) : Prop := k.isAtom = k.isClosedValue ∧ k.isBindable = true

theorem isCompHead_join (a b : Head) : IsCompHead (join a b) := by
  unfold join IsCompHead
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem isCompHead_settle_group (l : Option Head) (e : Option Nat) (a b : Head) :
    IsCompHead (settle (group l e a b)) := by
  unfold group
  split
  · exact isCompHead_join _ _
  · exact ⟨rfl, rfl⟩
  · show IsCompHead (settle (join a b))
    unfold join
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem isCompHead_settle_summarize (l : Option Head) (e : Option Nat) (a b : Head) :
    IsCompHead (settle (summarize l e a b)) :=
  isCompHead_settle_group _ _ _ _

theorem isCompHead_settle_branchAt (n d : Nat) (a b : Head) :
    IsCompHead (settle (branchAt n d a b)) :=
  isCompHead_settle_summarize _ _ _ _

theorem isCompHead_settle_branchTag (n t : Nat) (a b : Head) :
    IsCompHead (settle (branchTag n t a b)) :=
  isCompHead_settle_summarize _ _ _ _

theorem isCompHead_settle_withDefault (kd kc : Head) :
    IsCompHead (settle (withDefault kd kc)) :=
  isCompHead_settle_summarize _ _ _ _

theorem isCompHead_ctorOf (ks : List Head) : IsCompHead (ctorOf ks) := by
  unfold ctorOf
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem isCompHead_ctorAtOf (t : Nat) (ks : List Head) : IsCompHead (ctorAtOf t ks) := by
  unfold ctorAtOf
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · rename_i hne _ _
        cases ks with
        | nil => simp at hne
        | cons _ _ => exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

theorem IsCompHead.isName_eq_false {k : Head} (h : IsCompHead k) : k.isName = false := by
  cases k <;> simp_all [IsCompHead, isName, isAtom, isClosedValue]

theorem IsCompHead.isAtom_eq_true {k : Head} (h : IsCompHead k) (ha : k.isAtom = true) :
    k.isClosedValue = true := h.1 ▸ ha

theorem isName_eq_false_of_isClosedValue {k : Head} (h : k.isClosedValue = true) :
    k.isName = false := by
  cases k <;> simp_all [isName, isClosedValue]

theorem isAtom_of_isClosedValue {k : Head} (h : k.isClosedValue = true) : k.isAtom = true := by
  cases k <;> simp_all [isAtom, isClosedValue]
  split at h <;> simp_all

end Head

theorem EnumCases.isCompHead_settle {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {s : LeanEnumSchema}
    {k : Head} (c : EnumCases Sg Γ u τ s k) : Head.IsCompHead (Head.settle k) := by
  cases c <;> exact Head.isCompHead_settle_branchAt _ _ _ _

theorem TaggedUnionCases.isCompHead_settle {Γ : Ctx} {u : Usage Γ}
    {l : LeanTaggedUnionSchema TyWf} {τ : TyWf} {k : Head}
    (c : TaggedUnionCases Sg Γ u l τ k) : Head.IsCompHead (Head.settle k) := by
  cases c <;> exact Head.isCompHead_settle_branchAt _ _ _ _

theorem FamilyMemberCases.isCompHead {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {m : LeanFamMemberSchema TyWf} {k : Head} (c : FamilyMemberCases Sg Γ u τ m k) :
    Head.IsCompHead k := by
  cases c with
  | ctors cs => exact cs.isCompHead_settle
  | record => exact Head.isCompHead_join _ _
  | «alias» => exact Head.isCompHead_join _ _

/-- The head of a computation or a constructor is a head of a computation
    (`Head.IsCompHead`): an atom exactly when it is a closed value, and bindable. -/
theorem Comp.isCompHead {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (c : Comp Sg Γ u τ k) : Head.IsCompHead k := by
  cases c <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact Head.isCompHead_join _ _
    | exact Head.isCompHead_ctorOf _
    | exact Head.isCompHead_ctorAtOf _ _
    | exact Head.isCompHead_settle_withDefault _ _
    | exact EnumCases.isCompHead_settle ‹_›
    | exact TaggedUnionCases.isCompHead_settle ‹_›
    | exact FamilyMemberCases.isCompHead ‹_›

/-- A computation is an atom exactly when it is a closed value (`Atom.val`). -/
theorem Comp.isAtom_head {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (c : Comp Sg Γ u τ k) : k.isAtom = k.isClosedValue := c.isCompHead.1

/-- A computation is always something a `let` may bind (`Head.isBindable`): so `Term.letE`
    needs no proof of it. -/
theorem Comp.isBindable_head {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (c : Comp Sg Γ u τ k) : k.isBindable = true := c.isCompHead.2

/-- The head of an atom is an atom's (`Head.isAtom`). -/
theorem Atom.isAtom_head {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (a : Atom Sg Γ u τ k) : k.isAtom = true := by
  cases a with
  | ref n => cases n <;> rfl
  | val _ h => exact Head.isAtom_of_isClosedValue h
  | _ => rfl

/-! ## Reading a term in a category -/

/-- A computation as a term: an atom when it is a closed value (`Atom.val`), a term of its
    own (`Term.comp`) otherwise. -/
def Term.ofComp {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} (c : Comp Sg Γ u τ k) :
    Term Sg Γ u τ k :=
  if h : k.isClosedValue = true then .atom (.val c h) else .comp c (by simpa using h)

/-- An atom, read as a name: it is one when its head is (`Head.isName`). -/
def Atom.toRef {Γ : Ctx} {u : Usage Γ} {τ : TyWf} :
    {k : Head} → Atom Sg Γ u τ k → k.isName = true → Ref Sg Γ u τ k
  | _, .ref n, _ => n
  | _, .val _ hc, h => absurd h (by simp [Head.isName_eq_false_of_isClosedValue hc])
  | _, .lam .., h => absurd h (by simp [Head.isName])
  | _, .bool_mk .., h => absurd h (by simp [Head.isName])
  | _, .nat_mk .., h => absurd h (by simp [Head.isName])
  | _, .int_mk .., h => absurd h (by simp [Head.isName])
  | _, .bitvec_mk .., h => absurd h (by simp [Head.isName])
  | _, .uint8_mk .., h => absurd h (by simp [Head.isName])
  | _, .uint16_mk .., h => absurd h (by simp [Head.isName])
  | _, .uint32_mk .., h => absurd h (by simp [Head.isName])
  | _, .uint64_mk .., h => absurd h (by simp [Head.isName])
  | _, .int8_mk .., h => absurd h (by simp [Head.isName])
  | _, .int16_mk .., h => absurd h (by simp [Head.isName])
  | _, .int32_mk .., h => absurd h (by simp [Head.isName])
  | _, .int64_mk .., h => absurd h (by simp [Head.isName])
  | _, .char_mk .., h => absurd h (by simp [Head.isName])
  | _, .string_mk .., h => absurd h (by simp [Head.isName])
  | _, .stringPos_mk .., h => absurd h (by simp [Head.isName])
  | _, .stringPosRaw_mk .., h => absurd h (by simp [Head.isName])
  | _, .substringRaw_mk .., h => absurd h (by simp [Head.isName])
  | _, .stringSlice_mk .., h => absurd h (by simp [Head.isName])
  | _, .float_mk .., h => absurd h (by simp [Head.isName])
  | _, .float32_mk .., h => absurd h (by simp [Head.isName])
  | _, .floatModel_mk .., h => absurd h (by simp [Head.isName])
  | _, .float32Model_mk .., h => absurd h (by simp [Head.isName])
  | _, .enum_mk .., h => absurd h (by simp [Head.isName])

/-- A term, read as an atom: it is one when its head is (`Head.isAtom`). -/
def Term.toAtom {Γ : Ctx} {u : Usage Γ} {τ : TyWf} :
    {k : Head} → Term Sg Γ u τ k → k.isAtom = true → Atom Sg Γ u τ k
  | _, .atom a, _ => a
  | _, .comp c hc, h => absurd (c.isCompHead.isAtom_eq_true h) (by simp [hc])
  | _, .letE .., h => absurd h (by simp [Head.isAtom])

/-- A term, read as a name: it is one when its head is (`Head.isName`). -/
def Term.toRef {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} (t : Term Sg Γ u τ k)
    (h : k.isName = true) : Ref Sg Γ u τ k :=
  (t.toAtom (by revert h; cases k <;> simp [Head.isName, Head.isAtom])).toRef h

/-- A term, read as what an application may call: a name, or an application
    (`Head.isCallee`). -/
def Term.toCallee {Γ : Ctx} {u : Usage Γ} {τ : TyWf} :
    {k : Head} → Term Sg Γ u τ k → k.isCallee = true → Callee Sg Γ u τ k
  | .var _, t, _ => .ref (t.toRef rfl)
  | .global, t, _ => .ref (t.toRef rfl)
  | .app _, .comp c _, _ => .app c
  | .app _, .atom a, _ => absurd a.isAtom_head (by simp [Head.isAtom])
  | .lam, _, h | .lit, _, h | .bool _, _, h | .enumLit _, _, h | .ctor, _, h | .rebuild _, _, h
  | .ctorAt _ _, _, h | .comp, _, h | .force _ _, _, h | .val, _, h | .caseIntro, _, h
  | .caseCtor, _, h | .empty, _, h | .letIn _, _, h | .caseLeaf _ _, _, h
  | .caseEta _, _, h => absurd h (by simp [Head.isCallee])

/-- A term, read as a computation: it is one when a `let` may bind it
    (`Head.isBindable`) — a computation, or a closed value built by a constructor. -/
def Term.toComp {Γ : Ctx} {u : Usage Γ} {τ : TyWf} :
    {k : Head} → Term Sg Γ u τ k → k.isBindable = true → Comp Sg Γ u τ k
  | _, .comp c _, _ => c
  | _, .atom (.val c _), _ => c
  | _, .atom (.ref n), h => absurd h (by cases n <;> simp [Head.isBindable, Head.isComp, Head.isCtor])
  | _, .atom (.lam ..), h => absurd h (by simp [Head.isBindable, Head.isComp, Head.isCtor])
  | _, .atom (.bool_mk ..), h => absurd h (by simp [Head.isBindable, Head.isComp, Head.isCtor])
  | _, .atom (.enum_mk ..), h => absurd h (by simp [Head.isBindable, Head.isComp, Head.isCtor])
  | _, .atom (.nat_mk ..), h | _, .atom (.int_mk ..), h | _, .atom (.bitvec_mk ..), h
  | _, .atom (.uint8_mk ..), h | _, .atom (.uint16_mk ..), h | _, .atom (.uint32_mk ..), h
  | _, .atom (.uint64_mk ..), h | _, .atom (.int8_mk ..), h | _, .atom (.int16_mk ..), h
  | _, .atom (.int32_mk ..), h | _, .atom (.int64_mk ..), h | _, .atom (.char_mk ..), h
  | _, .atom (.string_mk ..), h | _, .atom (.stringPos_mk ..), h
  | _, .atom (.stringPosRaw_mk ..), h | _, .atom (.substringRaw_mk ..), h
  | _, .atom (.stringSlice_mk ..), h | _, .atom (.float_mk ..), h | _, .atom (.float32_mk ..), h
  | _, .atom (.floatModel_mk ..), h | _, .atom (.float32Model_mk ..), h =>
      absurd h (by simp [Head.isBindable, Head.isComp, Head.isCtor])
  | _, .letE .., h => absurd h (by simp [Head.isBindable, Head.isComp, Head.isCtor])

/-- `Ref.var` as a term. -/
def Term.var : ∀ {Γ τ} (x : Γ ∋ τ), Term Sg Γ (Usage.single x) τ (.var x.index) :=
  fun x => Term.atom (Atom.ref (Ref.var x))

/-- `Atom.lam` as a term. -/
def Term.lam {Γ : Ctx} {σ τ : TyWf} {u : Usage (σ :: Γ)} {kb : Head}
      (b : Term Sg (σ :: Γ) u τ kb)
      (hEta : Head.isEtaRedex kb (Usage.head u) = false := by head_ok) :
    Term Sg Γ (Usage.many (Usage.tail u)) (σ ⇒ τ) .lam :=
  Term.atom (Atom.lam (b := b) (hEta := hEta))

/-- `Comp.ap` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.ap {Γ : Ctx} {σ τ : TyWf} {u v : Usage Γ} {kf ka : Head}
      (f : Term Sg Γ u (σ ⇒ τ) kf) (a : Term Sg Γ v σ ka)
      (hAnf : (Head.isCallee kf && Head.isAtom ka) = true := by head_ok)
      (hClosed : Head.closedComp (Usage.scrutinize kf (Usage.arg ka (u + v))) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.scrutinize kf (Usage.arg ka (u + v))) τ (.app ka.isVar0) :=
  Term.ofComp (Comp.ap (f := (f.toCallee (Bool.and_eq_true_iff.mp hAnf).1)) (a := (a.toAtom (Bool.and_eq_true_iff.mp hAnf).2)) (hClosed := hClosed))

/-- `Ref.global` as a term. -/
def Term.global : ∀ {Γ τ}, GlobalRef Sg.decls τ → Term Sg Γ Usage.global τ .global :=
  fun a0 => Term.atom (Atom.ref (Ref.global a0))

/-- `Atom.bool_mk` as a term. -/
def Term.bool_mk : ∀ {Γ} (b : Bool), Term Sg Γ 0 (.prim .bool) (.bool b) :=
  fun b => Term.atom (Atom.bool_mk b)

/-- `Atom.nat_mk` as a term. -/
def Term.nat_mk : ∀ {Γ}, Nat → Term Sg Γ 0 (.prim .nat) .lit :=
  fun a0 => Term.atom (Atom.nat_mk a0)

/-- `Atom.int_mk` as a term. -/
def Term.int_mk : ∀ {Γ}, Int → Term Sg Γ 0 (.prim .int) .lit :=
  fun a0 => Term.atom (Atom.int_mk a0)

/-- `Atom.bitvec_mk` as a term. -/
def Term.bitvec_mk {Γ : Ctx} {n : Nat} (h_positive : 0 < n := by head_ok) (v : BitVec n) :
    Term Sg Γ 0 (.prim (.bitvec n h_positive)) .lit :=
  Term.atom (Atom.bitvec_mk (h_positive := h_positive) (v := v))

/-- `Atom.uint8_mk` as a term. -/
def Term.uint8_mk : ∀ {Γ}, UInt8 → Term Sg Γ 0 (.prim .uint8) .lit :=
  fun a0 => Term.atom (Atom.uint8_mk a0)

/-- `Atom.uint16_mk` as a term. -/
def Term.uint16_mk : ∀ {Γ}, UInt16 → Term Sg Γ 0 (.prim .uint16) .lit :=
  fun a0 => Term.atom (Atom.uint16_mk a0)

/-- `Atom.uint32_mk` as a term. -/
def Term.uint32_mk : ∀ {Γ}, UInt32 → Term Sg Γ 0 (.prim .uint32) .lit :=
  fun a0 => Term.atom (Atom.uint32_mk a0)

/-- `Atom.uint64_mk` as a term. -/
def Term.uint64_mk : ∀ {Γ}, UInt64 → Term Sg Γ 0 (.prim .uint64) .lit :=
  fun a0 => Term.atom (Atom.uint64_mk a0)

/-- `Atom.int8_mk` as a term. -/
def Term.int8_mk : ∀ {Γ}, Int8 → Term Sg Γ 0 (.prim .int8) .lit :=
  fun a0 => Term.atom (Atom.int8_mk a0)

/-- `Atom.int16_mk` as a term. -/
def Term.int16_mk : ∀ {Γ}, Int16 → Term Sg Γ 0 (.prim .int16) .lit :=
  fun a0 => Term.atom (Atom.int16_mk a0)

/-- `Atom.int32_mk` as a term. -/
def Term.int32_mk : ∀ {Γ}, Int32 → Term Sg Γ 0 (.prim .int32) .lit :=
  fun a0 => Term.atom (Atom.int32_mk a0)

/-- `Atom.int64_mk` as a term. -/
def Term.int64_mk : ∀ {Γ}, Int64 → Term Sg Γ 0 (.prim .int64) .lit :=
  fun a0 => Term.atom (Atom.int64_mk a0)

/-- `Atom.char_mk` as a term. -/
def Term.char_mk : ∀ {Γ}, Char → Term Sg Γ 0 (.prim .char) .lit :=
  fun a0 => Term.atom (Atom.char_mk a0)

/-- `Atom.string_mk` as a term. -/
def Term.string_mk : ∀ {Γ}, String → Term Sg Γ 0 (.prim .string) .lit :=
  fun a0 => Term.atom (Atom.string_mk a0)

/-- `Atom.stringPos_mk` as a term. -/
def Term.stringPos_mk : ∀ {Γ} (s : String), String.Pos s → Term Sg Γ 0 (.prim (.stringPos s)) .lit :=
  fun s a0 => Term.atom (Atom.stringPos_mk s a0)

/-- `Atom.stringPosRaw_mk` as a term. -/
def Term.stringPosRaw_mk : ∀ {Γ}, String.Pos.Raw → Term Sg Γ 0 (.prim .stringPosRaw) .lit :=
  fun a0 => Term.atom (Atom.stringPosRaw_mk a0)

/-- `Atom.substringRaw_mk` as a term. -/
def Term.substringRaw_mk : ∀ {Γ}, Substring.Raw → Term Sg Γ 0 (.prim .substringRaw) .lit :=
  fun a0 => Term.atom (Atom.substringRaw_mk a0)

/-- `Atom.stringSlice_mk` as a term. -/
def Term.stringSlice_mk : ∀ {Γ}, String.Slice → Term Sg Γ 0 (.prim .stringSlice) .lit :=
  fun a0 => Term.atom (Atom.stringSlice_mk a0)

/-- `Atom.float_mk` as a term. -/
def Term.float_mk : ∀ {Γ}, Float → Term Sg Γ 0 (.prim .float) .lit :=
  fun a0 => Term.atom (Atom.float_mk a0)

/-- `Atom.float32_mk` as a term. -/
def Term.float32_mk : ∀ {Γ}, Float32 → Term Sg Γ 0 (.prim .float32) .lit :=
  fun a0 => Term.atom (Atom.float32_mk a0)

/-- `Atom.floatModel_mk` as a term. -/
def Term.floatModel_mk : ∀ {Γ}, Float.Model → Term Sg Γ 0 (.prim .floatModel) .lit :=
  fun a0 => Term.atom (Atom.floatModel_mk a0)

/-- `Atom.float32Model_mk` as a term. -/
def Term.float32Model_mk : ∀ {Γ}, Float32.Model → Term Sg Γ 0 (.prim .float32Model) .lit :=
  fun a0 => Term.atom (Atom.float32Model_mk a0)

/-- `Comp.extern` as a term. -/
def Term.extern {Γ : Ctx} {τ : TyWf} (e : Extern τ) (h : TyWf.quotable τ = false := by head_ok) :
    Term Sg Γ 0 τ .comp :=
  Term.ofComp (Comp.extern (e := e) (h := h))

/-- `Comp.externCall` as a term. -/
def Term.externCall {Γ : Ctx} {σs : List TyWf} {τ : TyWf} {u : Usage Γ} {ks : List Head}
      (args : Spine Sg Γ u σs ks) (call : TyWf.DenList σs → Extern τ)
      (h : Head.allValue ks = false := by head_ok)
      (hClosed : Head.closedComp (u) τ .comp = false := by not_closed) :
    Term Sg Γ u τ .comp :=
  Term.ofComp (Comp.externCall (args := args) (call := call) (h := h) (hClosed := hClosed))

/-- `Comp.externCallChecked` as a term. -/
def Term.externCallChecked {Γ : Ctx} {σs : List TyWf} {τ : TyWf} {u v : Usage Γ}
      {ks : List Head} {kf : Head} (args : Spine Sg Γ u σs ks)
      (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ v τ kf)
      (h : Head.allValue ks = false := by head_ok)
      (hClosed : Head.closedComp (u + v) τ .comp = false := by not_closed) :
    Term Sg Γ (u + v) τ .comp :=
  Term.ofComp (Comp.externCallChecked (args := args) (call := call) (fallback := fallback) (h := h) (hClosed := hClosed))

/-- `Comp.bool_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.bool_casesOn {Γ : Ctx} {τ : TyWf} {u v w : Usage Γ} {kc kt ke : Head}
      (c : Term Sg Γ u (.prim .bool) kc) (t : Term Sg Γ v τ kt) (e : Term Sg Γ w τ ke)
      (hAnf : Head.isName kc = true := by head_ok)
      (hId : (kt, ke) ≠ (.bool true, .bool false) := by head_ok)
      (hSame : Head.sameLeaf kt ke = false := by head_ok)
      (hKnown : Head.rescrutinizes kc (v + w) = false := by head_ok)
      (hLit : Head.readsScrutinee kc (v + w) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kc (u + Usage.cond v + Usage.cond w)) τ (Head.join kt ke) :=
  Term.ofComp (Comp.bool_casesOn (c := (c.toRef hAnf)) (t := t) (e := e) (hId := hId) (hSame := hSame) (hKnown := hKnown) (hLit := hLit))

/-- `Comp.nat_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.nat_casesOn {Γ : Ctx} {τ : TyWf} {u v : Usage Γ} {w : Usage (TyWf.prim .nat :: Γ)}
      {kn kz ks : Head} (n : Term Sg Γ u (.prim .nat) kn) (z : Term Sg Γ v τ kz)
      (s : Term Sg (TyWf.prim .nat :: Γ) w τ ks) (hAnf : Head.isName kn = true := by head_ok)
      (hKnown : Head.rescrutinizes kn (v + Usage.tail w) = false := by head_ok)
      (hLit : Head.readsScrutinee kn v = false := by head_ok)
      (hSame : Head.sameLeafOver kz ks = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kn (u + Usage.cond v + Usage.cond (Usage.tail w))) τ (Head.join kz ks) :=
  Term.ofComp (Comp.nat_casesOn (n := (n.toRef hAnf)) (z := z) (s := s) (hKnown := hKnown) (hLit := hLit) (hSame := hSame))

/-- `Comp.nat_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.nat_rec {Γ : Ctx} {τ : TyWf} (k : Nat := 0) {u ub : Usage Γ}
      {w : Usage (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ)} {kn kb : Head} {ks : List Head}
      (n : Term Sg Γ u (.prim .nat) kn) (base : Spine Sg Γ ub (natRecCtx τ (k + 1) []) ks)
      (branch : Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) w τ kb)
      (hRec : 0 < Usage.sumN τ (k + 1) (Usage.tail w) := by usage_pos)
      (hStep : k = 0 → Head.isVar kb = false := by head_ok)
      (hAnf : (Head.isAtom kn && Head.allAtom ks) = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kn u + ub + Usage.many (Usage.dropN τ (k + 1) (Usage.tail w))) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg kn u + ub + Usage.many (Usage.dropN τ (k + 1) (Usage.tail w))) τ .comp :=
  Term.ofComp (Comp.nat_rec (k := k) (n := (n.toAtom (Bool.and_eq_true_iff.mp hAnf).1)) (base := base) (branch := branch) (hRec := hRec) (hStep := hStep) (hClosed := hClosed))

/-- `Comp.int_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.int_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v w : Usage (TyWf.prim .nat :: Γ)}
      {ki ka kb : Head} (i : Term Sg Γ u (.prim .int) ki)
      (ofNat : Term Sg (TyWf.prim .nat :: Γ) v τ ka)
      (negSucc : Term Sg (TyWf.prim .nat :: Γ) w τ kb) (hAnf : Head.isName ki = true := by head_ok)
      (hKnown : Head.rescrutinizes ki (Usage.tail v + Usage.tail w) = false := by head_ok)
      (hSame : Head.sameLeafPast ka kb = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize ki (u + Usage.cond (Usage.tail v) + Usage.cond (Usage.tail w))) τ (Head.join ka kb) :=
  Term.ofComp (Comp.int_casesOn (i := (i.toRef hAnf)) (ofNat := ofNat) (negSucc := negSucc) (hKnown := hKnown) (hSame := hSame))

/-- `Comp.uint8_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.uint8_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim (.bitvec 8) :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .uint8) kx) (b : Term Sg (TyWf.prim (.bitvec 8) :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.uint8_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.uint16_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.uint16_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim (.bitvec 16) :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .uint16) kx) (b : Term Sg (TyWf.prim (.bitvec 16) :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.uint16_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.uint32_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.uint32_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim (.bitvec 32) :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .uint32) kx) (b : Term Sg (TyWf.prim (.bitvec 32) :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.uint32_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.uint64_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.uint64_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim (.bitvec 64) :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .uint64) kx) (b : Term Sg (TyWf.prim (.bitvec 64) :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.uint64_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.int8_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.int8_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint8 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .int8) kx) (b : Term Sg (TyWf.prim .uint8 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.int8_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.int16_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.int16_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint16 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .int16) kx) (b : Term Sg (TyWf.prim .uint16 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.int16_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.int32_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.int32_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint32 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .int32) kx) (b : Term Sg (TyWf.prim .uint32 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.int32_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.int64_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.int64_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint64 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .int64) kx) (b : Term Sg (TyWf.prim .uint64 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.int64_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.char_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.char_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint32 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .char) kx) (b : Term Sg (TyWf.prim .uint32 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.char_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.stringPosRaw_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.stringPosRaw_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .nat :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .stringPosRaw) kx) (b : Term Sg (TyWf.prim .nat :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.stringPosRaw_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.stringPos_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.stringPos_casesOn {Γ : Ctx} {τ : TyWf} {s : String} {u : Usage Γ}
      {v : Usage (TyWf.prim .stringPosRaw :: Γ)} {kx kb : Head}
      (x : Term Sg Γ u (.prim (.stringPos s)) kx) (b : Term Sg (TyWf.prim .stringPosRaw :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.stringPos_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.substringRaw_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.substringRaw_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ}
      {v : Usage (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .substringRaw) kx)
      (b : Term Sg (TyWf.prim .string :: TyWf.prim .stringPosRaw :: TyWf.prim .stringPosRaw :: Γ)
        v τ kb)
      (hAnf : Head.isName kx = true := by head_ok)
      (hUsed : 0 < Usage.front
        [TyWf.prim .string, TyWf.prim .stringPosRaw, TyWf.prim .stringPosRaw] v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail (Usage.tail (Usage.tail v))) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail (Usage.tail (Usage.tail v)))) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.substringRaw_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.float_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.float_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .floatModel :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .float) kx) (b : Term Sg (TyWf.prim .floatModel :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.float_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.float32_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.float32_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .float32Model :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .float32) kx) (b : Term Sg (TyWf.prim .float32Model :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.float32_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.floatModel_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.floatModel_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint64 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .floatModel) kx) (b : Term Sg (TyWf.prim .uint64 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.floatModel_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.float32Model_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.float32Model_casesOn {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {v : Usage (TyWf.prim .uint32 :: Γ)}
      {kx kb : Head} (x : Term Sg Γ u (.prim .float32Model) kx) (b : Term Sg (TyWf.prim .uint32 :: Γ) v τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head v := by usage_pos)
      (hKnown : Head.rescrutinizes kx (Usage.tail v) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.float32Model_casesOn (x := (x.toRef hAnf)) (b := b) (hUsed := hUsed) (hKnown := hKnown))

/-- `Comp.lazy_mk` as a term. -/
def Term.lazy_mk {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {ke : Head} (e : Term Sg Γ u τ ke)
      (hEta : Head.isForcedName false ke = false := by head_ok) :
    Term Sg Γ (Usage.many u) (.lazy τ) (Head.ctorOf [ke]) :=
  Term.ofComp (Comp.lazy_mk (e := e) (hEta := hEta))

/-- `Comp.lazy_force` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.lazy_force {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {ke : Head} (e : Term Sg Γ u (.lazy τ) ke)
      (hAnf : Head.isName ke = true := by head_ok)
      (hClosed : Head.closedComp (Usage.scrutinize ke u) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.scrutinize ke u) τ (.force false ke.isName) :=
  Term.ofComp (Comp.lazy_force (e := (e.toRef hAnf)) (hClosed := hClosed))

/-- `Comp.thunk_mk` as a term. -/
def Term.thunk_mk {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {ke : Head} (e : Term Sg Γ u τ ke)
      (hEta : Head.isForcedName true ke = false := by head_ok) :
    Term Sg Γ (Usage.cond u) (.thunk τ) (Head.ctorOf [ke]) :=
  Term.ofComp (Comp.thunk_mk (e := e) (hEta := hEta))

/-- `Comp.thunk_force` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.thunk_force {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {ke : Head} (e : Term Sg Γ u (.thunk τ) ke)
      (hAnf : Head.isName ke = true := by head_ok)
      (hClosed : Head.closedComp (Usage.scrutinize ke u) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.scrutinize ke u) τ (.force true ke.isName) :=
  Term.ofComp (Comp.thunk_force (e := (e.toRef hAnf)) (hClosed := hClosed))

/-- `Comp.array_mk` as a term. -/
def Term.array_mk {Γ : Ctx} {τ : TyWf} {u : Usage Γ} {ks : List Head} (elems : Terms Sg Γ u τ ks) :
    Term Sg Γ u (.array τ) (Head.ctorOf ks) :=
  Term.ofComp (Comp.array_mk (elems := elems))

/-- `Comp.array_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.array_casesOn {Γ : Ctx} {σ τ : TyWf} {u v : Usage Γ} {w : Usage (σ :: TyWf.array σ :: Γ)}
      {ka kz ks : Head} (a : Term Sg Γ u (.array σ) ka) (z : Term Sg Γ v τ kz)
      (s : Term Sg (σ :: TyWf.array σ :: Γ) w τ ks) (hAnf : Head.isName ka = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg ka (u + Usage.cond v + Usage.cond (Usage.tail (Usage.tail w)))) τ (Head.join kz ks) = false := by not_closed) :
    Term Sg Γ (Usage.arg ka (u + Usage.cond v + Usage.cond (Usage.tail (Usage.tail w)))) τ (Head.join kz ks) :=
  Term.ofComp (Comp.array_casesOn (a := (a.toRef hAnf)) (z := z) (s := s) (hClosed := hClosed))

/-- `Comp.array_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.array_rec {Γ : Ctx} {σ τ : TyWf} (k : Nat := 0) {u ub : Usage Γ}
      {w : Usage (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ)} {ka kb : Head}
      (a : Term Sg Γ u (.array σ) ka) (bases : ArrayRecBases Sg Γ ub σ τ k)
      (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) w τ kb)
      (hRec : 0 < Usage.sumN τ (k + 1) (Usage.tail (Usage.tail w)) := by usage_pos)
      (hStep : k = 0 → Head.isVar kb = false := by head_ok)
      (hAnf : Head.isAtom ka = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg ka u + ub + Usage.many (Usage.dropN τ (k + 1) (Usage.tail (Usage.tail w)))) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg ka u + ub + Usage.many (Usage.dropN τ (k + 1) (Usage.tail (Usage.tail w)))) τ .comp :=
  Term.ofComp (Comp.array_rec (k := k) (a := (a.toAtom hAnf)) (bases := bases) (branch := branch) (hRec := hRec) (hStep := hStep) (hClosed := hClosed))

/-- `Atom.enum_mk` as a term. -/
def Term.enum_mk : ∀ {Γ} (s : LeanEnumSchema) (i : Fin s.nOfConstructors), Term Sg Γ 0 (.enum s) (.enumLit i.val) :=
  fun s i => Term.atom (Atom.enum_mk s i)

/-- `Comp.enum_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.enum_casesOn {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {u v : Usage Γ} {ke kc : Head}
      (e : Term Sg Γ u (.enum s) ke) (cases : EnumCases Sg Γ v τ s kc)
      (hAnf : Head.isName ke = true := by head_ok)
      (hKnown : Head.rescrutinizes ke v = false := by head_ok)
      (hLit : Head.readsScrutinee ke v = false := by head_ok)
      (hSame : Head.isCaseLeaf kc = false := by head_ok)
      (hEta : Head.isUnionEta kc s.nOfConstructors (TyWf.isEnumOf τ s) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize ke (u + v)) τ (Head.settle kc) :=
  Term.ofComp (Comp.enum_casesOn (e := (e.toRef hAnf)) (cases := cases) (hKnown := hKnown) (hLit := hLit) (hSame := hSame) (hEta := hEta))

/-- `Comp.enum_casesOnWithDefault` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.enum_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {k : Nat}
      {u v w : Usage Γ} {ke kc kd : Head}
      (e : Term Sg Γ u (.enum s) ke) (cases : EnumSomeCases Sg Γ v τ s kc k)
      (dflt : Term Sg Γ w τ kd)
      (hk : k < s.nOfConstructors := by ctor_lt) (hAnf : Head.isName ke = true := by head_ok)
      (hKnown : Head.rescrutinizes ke v = false := by head_ok)
      (hLit : Head.readsScrutinee ke v = false := by head_ok)
      (hSame : Head.isCaseLeaf (Head.withDefault kd kc) = false := by head_ok)
      (hEta : Head.isUnionEtaDflt kc kd ke (TyWf.isEnumOf τ s) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize ke (u + v + Usage.cond w)) τ (Head.settle (Head.withDefault kd kc)) :=
  Term.ofComp (Comp.enum_casesOnWithDefault (e := (e.toRef hAnf)) (cases := cases) (dflt := dflt) (hk := hk) (hKnown := hKnown) (hLit := hLit) (hSame := hSame) (hEta := hEta))

/-- `Comp.record_mk` as a term. -/
def Term.record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf) {u : Usage Γ} {ks : List Head}
      (fields : Spine Sg Γ u fs.toList ks) :
    Term Sg Γ u (.record fs) (Head.ctorOf ks) :=
  Term.ofComp (Comp.record_mk (fs := fs) (fields := fields))

/-- `Comp.record_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.record_casesOn {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf} {u : Usage Γ}
      {v : Usage (fs.toList ++ Γ)} {kr kb : Head}
      (r : Term Sg Γ u (.record fs) kr) (body : Term Sg (fs.toList ++ Γ) v τ kb)
      (hAnf : Head.isName kr = true := by head_ok)
      (hUsed : 0 < Usage.front fs.toList v := by usage_pos)
      (hClosed : Head.closedComp (u + Usage.drop fs.toList v) τ (Head.join kb .empty) = false := by not_closed)
      (hKnown : Head.rescrutinizes kr (Usage.drop fs.toList v) = false := by head_ok)
      (hEta : Head.isRecordEta kb fs.toList.length τ = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kr (u + Usage.drop fs.toList v)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.record_casesOn (r := (r.toRef hAnf)) (body := body) (hUsed := hUsed) (hClosed := hClosed) (hKnown := hKnown) (hEta := hEta))

/-- `Comp.taggedUnion_mk` as a term. -/
def Term.taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
      (ht : t < l.length := by ctor_tag) {u : Usage Γ} {ks : List Head}
      (fields : Spine Sg Γ u (l.get t ht) ks) :
    Term Sg Γ u (.taggedUnion l) (Head.ctorAtOf t ks) :=
  Term.ofComp (Comp.taggedUnion_mk (l := l) (t := t) (ht := ht) (fields := fields))

/-- `Comp.taggedUnion_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.taggedUnion_casesOn {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf} {u w : Usage Γ}
      {kx kc : Head} (x : Term Sg Γ u (.taggedUnion l) kx) (cases : TaggedUnionCases Sg Γ w l τ kc)
      (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (u + w) τ (Head.settle kc) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx w = false := by head_ok)
      (hSame : Head.isCaseLeaf kc = false := by head_ok)
      (hLit : Head.readsInFieldless kx w = false := by head_ok)
      (hEta : Head.isUnionEta kc l.length (TyWf.isTaggedUnionOf τ l.length) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + w)) τ (Head.settle kc) :=
  Term.ofComp (Comp.taggedUnion_casesOn (x := (x.toRef hAnf)) (cases := cases) (hClosed := hClosed) (hKnown := hKnown) (hSame := hSame) (hLit := hLit) (hEta := hEta))

/-- `Comp.taggedUnion_casesOnWithDefault` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.taggedUnion_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
      {k : Nat} {u w d : Usage Γ} {kx kc kd : Head} (v : Term Sg Γ u (.taggedUnion l) kx)
      (cases : TaggedUnionSomeCases Sg Γ w l τ kc k) (dflt : Term Sg Γ d τ kd)
      (hk : k < l.length := by ctor_lt) (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (u + w + d) τ (Head.settle (Head.withDefault kd kc)) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx w = false := by head_ok)
      (hSame : Head.isCaseLeaf (Head.withDefault kd kc) = false := by head_ok)
      (hLit : Head.readsInFieldless kx w = false := by head_ok)
      (hEta : Head.isUnionEtaDflt kc kd kx (TyWf.isTaggedUnionOf τ l.length) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + w + Usage.cond d)) τ (Head.settle (Head.withDefault kd kc)) :=
  Term.ofComp (Comp.taggedUnion_casesOnWithDefault (v := (v.toRef hAnf)) (cases := cases) (dflt := dflt) (hk := hk) (hClosed := hClosed) (hKnown := hKnown) (hSame := hSame) (hLit := hLit) (hEta := hEta))

/-- `Comp.recTaggedUnion_mk` as a term. -/
def Term.recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
      (hwf : Ty.Wf (TyWf.recTaggedUnionTy l) := by ty_wf) (t : Nat)
      (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_tag) {u : Usage Γ}
      {ks : List Head} (fields : Spine Sg Γ u ((TyWf.recTaggedUnionUnfold l hwf).get t ht) ks) :
    Term Sg Γ u (.recTaggedUnion l hwf) (Head.ctorAtOf t ks) :=
  Term.ofComp (Comp.recTaggedUnion_mk (l := l) (hwf := hwf) (t := t) (ht := ht) (fields := fields))

/-- `Comp.recTaggedUnion_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recTaggedUnion_casesOn {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {u w : Usage Γ} {kx kc : Head}
      (x : Term Sg Γ u (.recTaggedUnion l hwf) kx)
      (cases : TaggedUnionCases Sg Γ w (TyWf.recTaggedUnionUnfold l hwf) τ kc)
      (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (u + w) τ (Head.settle kc) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx w = false := by head_ok)
      (hSame : Head.isCaseLeaf kc = false := by head_ok)
      (hLit : Head.readsInFieldless kx w = false := by head_ok)
      (hEta : Head.isUnionEta kc l.length (TyWf.isRecTaggedUnionOf τ l.length) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + w)) τ (Head.settle kc) :=
  Term.ofComp (Comp.recTaggedUnion_casesOn (x := (x.toRef hAnf)) (cases := cases) (hClosed := hClosed) (hKnown := hKnown) (hSame := hSame) (hLit := hLit) (hEta := hEta))

/-- `Comp.recTaggedUnion_casesOnWithDefault` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recTaggedUnion_casesOnWithDefault {Γ : Ctx} {τ : TyWf}
      {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
      {k : Nat} {u w d : Usage Γ} {kx kc kd : Head} (v : Term Sg Γ u (.recTaggedUnion l hwf) kx)
      (cases : TaggedUnionSomeCases Sg Γ w (TyWf.recTaggedUnionUnfold l hwf) τ kc k)
      (dflt : Term Sg Γ d τ kd)
      (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_lt)
      (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (u + w + d) τ (Head.settle (Head.withDefault kd kc)) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx w = false := by head_ok)
      (hSame : Head.isCaseLeaf (Head.withDefault kd kc) = false := by head_ok)
      (hLit : Head.readsInFieldless kx w = false := by head_ok)
      (hEta : Head.isUnionEtaDflt kc kd kx (TyWf.isRecTaggedUnionOf τ l.length) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + w + Usage.cond d)) τ (Head.settle (Head.withDefault kd kc)) :=
  Term.ofComp (Comp.recTaggedUnion_casesOnWithDefault (v := (v.toRef hAnf)) (cases := cases) (dflt := dflt) (hk := hk) (hClosed := hClosed) (hKnown := hKnown) (hSame := hSame) (hLit := hLit) (hEta := hEta))

/-- `Comp.recTaggedUnion_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recTaggedUnion_rec {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat := 0) {u w : Usage Γ} {kx : Head}
      (x : Term Sg Γ u (.recTaggedUnion l hwf) kx)
      (cases : TaggedUnionFoldKCases Sg l
        (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ w l τ k)
      (hAnf : Head.isAtom kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx u + Usage.many w) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg kx u + Usage.many w) τ .comp :=
  Term.ofComp (Comp.recTaggedUnion_rec (k := k) (x := (x.toAtom hAnf)) (cases := cases) (hClosed := hClosed))

/-- `Comp.recObject_mk` as a term. -/
def Term.recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
      (hwf : Ty.Wf (TyWf.recObjectTy fs) := by ty_wf) {u : Usage Γ} {ks : List Head}
      (fields : Spine Sg Γ u (TyWf.recObjectUnfold fs hwf).toList ks) :
    Term Sg Γ u (.recObject fs hwf) .ctor :=
  Term.ofComp (Comp.recObject_mk (fs := fs) (hwf := hwf) (fields := fields))

/-- `Comp.recObject_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recObject_casesOn {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recObjectTy fs)} {u : Usage Γ}
      {w : Usage ((TyWf.recObjectUnfold fs hwf).toList ++ Γ)} {kx kb : Head}
      (x : Term Sg Γ u (.recObject fs hwf) kx)
      (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) w τ kb)
      (hAnf : Head.isName kx = true := by head_ok)
      (hUsed : 0 < Usage.front (TyWf.recObjectUnfold fs hwf).toList w := by usage_pos)
      (hClosed : Head.closedComp (u + Usage.drop (TyWf.recObjectUnfold fs hwf).toList w) τ (Head.join kb .empty) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx (Usage.drop (TyWf.recObjectUnfold fs hwf).toList w) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.drop (TyWf.recObjectUnfold fs hwf).toList w)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.recObject_casesOn (x := (x.toRef hAnf)) (body := body) (hUsed := hUsed) (hClosed := hClosed) (hKnown := hKnown))

/-- `Comp.recObject_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recObject_rec {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
      {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat := 0) {u : Usage Γ}
      {w : Usage (TyWf.recObjectRecBinders fs hwf τ k ++ Γ)} {kx kb : Head}
      (x : Term Sg Γ u (.recObject fs hwf) kx)
      (branch : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) w τ kb)
      (hAnf : Head.isAtom kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx u + Usage.many (Usage.drop (TyWf.recObjectRecBinders fs hwf τ k) w)) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg kx u + Usage.many (Usage.drop (TyWf.recObjectRecBinders fs hwf τ k) w)) τ .comp :=
  Term.ofComp (Comp.recObject_rec (k := k) (x := (x.toAtom hAnf)) (branch := branch) (hClosed := hClosed))

/-- `Comp.recAlias_mk` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b) := by ty_wf)
      {u : Usage Γ} {kv : Head} (value : Term Sg Γ u (TyWf.recAliasUnfold b hwf) kv)
      (hAnf : Head.isAtom kv = true := by head_ok) :
    Term Sg Γ (Usage.arg kv u) (.recAlias b hwf) .ctor :=
  Term.ofComp (Comp.recAlias_mk (b := b) (hwf := hwf) (value := (value.toAtom hAnf)))

/-- `Comp.recAlias_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recAlias_casesOn {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
      {u : Usage Γ} {w : Usage (TyWf.recAliasUnfold b hwf :: Γ)} {kx kb : Head}
      (x : Term Sg Γ u (.recAlias b hwf) kx)
      (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) w τ kb)
      (hAnf : Head.isName kx = true := by head_ok) (hUsed : 0 < Usage.head w := by usage_pos)
      (hClosed : Head.closedComp (u + Usage.tail w) τ (Head.join kb .empty) = false := by not_closed)
      (hKnown : Head.rescrutinizes kx (Usage.tail w) = false := by head_ok) :
    Term Sg Γ (Usage.scrutinize kx (u + Usage.tail w)) τ (Head.join kb .empty) :=
  Term.ofComp (Comp.recAlias_casesOn (x := (x.toRef hAnf)) (body := body) (hUsed := hUsed) (hClosed := hClosed) (hKnown := hKnown))

/-- `Comp.recAlias_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.recAlias_rec {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
      (k : Nat := 0) {u : Usage Γ} {w : Usage (TyWf.recAliasRecBinders b hwf τ k ++ Γ)}
      {kx kb : Head}
      (x : Term Sg Γ u (.recAlias b hwf) kx)
      (branch : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) w τ kb)
      (hAnf : Head.isAtom kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx u + Usage.many (Usage.drop (TyWf.recAliasRecBinders b hwf τ k) w)) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg kx u + Usage.many (Usage.drop (TyWf.recAliasRecBinders b hwf τ k) w)) τ .comp :=
  Term.ofComp (Comp.recAlias_rec (k := k) (x := (x.toAtom hAnf)) (branch := branch) (hClosed := hClosed))

/-- `Comp.mutualRecursiveFamily_mk` as a term. -/
def Term.mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
      (f : LeanMutualRecFamily (TyWfIn (n + 2)))
      (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f) := by ty_wf) {u : Usage Γ}
      (value : FamilyMemberValue Sg Γ u (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ u (.mutualRecursiveFamily f hwf) .ctor :=
  Term.ofComp (Comp.mutualRecursiveFamily_mk (f := f) (hwf := hwf) (value := value))

/-- `Comp.mutualRecursiveFamily_casesOn` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.mutualRecursiveFamily_casesOn {Γ : Ctx} {τ : TyWf} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} {u w : Usage Γ} {kx kc : Head}
      (x : Term Sg Γ u (.mutualRecursiveFamily f hwf) kx)
      (cases : FamilyMemberCases Sg Γ w τ (f.current.map (TyWfIn.unfoldFam f hwf)) kc)
      (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx (u + w)) τ kc = false := by not_closed) :
    Term Sg Γ (Usage.arg kx (u + w)) τ kc :=
  Term.ofComp (Comp.mutualRecursiveFamily_casesOn (x := (x.toRef hAnf)) (cases := cases) (hClosed := hClosed))

/-- `Comp.mutualRecursiveFamily_casesOnWithDefault` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.mutualRecursiveFamily_casesOnWithDefault {Γ : Ctx} {τ : TyWf} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} {u w d : Usage Γ} {kx kc kd : Head}
      (x : Term Sg Γ u (.mutualRecursiveFamily f hwf) kx)
      (cases : FamilyMemberSomeCases Sg Γ w τ (f.current.map (TyWfIn.unfoldFam f hwf)) kc)
      (dflt : Term Sg Γ d τ kd) (hAnf : Head.isName kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx (u + w + Usage.cond d)) τ (Head.join kc kd) = false := by not_closed) :
    Term Sg Γ (Usage.arg kx (u + w + Usage.cond d)) τ (Head.join kc kd) :=
  Term.ofComp (Comp.mutualRecursiveFamily_casesOnWithDefault (x := (x.toRef hAnf)) (cases := cases) (dflt := dflt) (hClosed := hClosed))

/-- `Comp.mutualRecursiveFamily_rec` as a term, its operands given as terms, with the A-normal form they must be in as a
    proof (`hAnf`). -/
def Term.mutualRecursiveFamily_rec {Γ : Ctx} {τ : TyWf} {n : Nat}
      {f : LeanMutualRecFamily (TyWfIn (n + 2))}
      {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} (k : Nat := 0) {u w : Usage Γ}
      {kx : Head}
      (x : Term Sg Γ u (.mutualRecursiveFamily f hwf) kx)
      (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ w τ f.members k)
      (hAnf : Head.isAtom kx = true := by head_ok)
      (hClosed : Head.closedComp (Usage.arg kx u + Usage.many w) τ .comp = false := by not_closed) :
    Term Sg Γ (Usage.arg kx u + Usage.many w) τ .comp :=
  Term.ofComp (Comp.mutualRecursiveFamily_rec (k := k) (x := (x.toAtom hAnf)) (cases := cases) (hClosed := hClosed))

/-- `Term.letE` with the bound computation given as a term, with the proof that a `let` may
    bind it (`hValue`, `Head.isBindable`). -/
def Term.letT {Γ : Ctx} {σ τ : TyWf} {u : Usage Γ} {v : Usage (σ :: Γ)} {ke kb : Head}
      (e : Term Sg Γ u σ ke) (b : Term Sg (σ :: Γ) v τ kb)
      (hValue : Head.isBindable ke = true := by head_ok)
      (hUsed : Head.letUsed ke (Usage.head v) (v.opnd 0) = true := by head_ok)
      (hClosed : Head.closedComp (Usage.letU u v) τ kb = false := by not_closed)
      (hKnownLet : Head.letKnown ke σ v = false := by head_ok)
      (hPlace : Usage.confined v 0 = false := by head_ok) :
    Term Sg Γ (Usage.letU u v) τ (.letIn kb) :=
  Term.letE (e.toComp hValue) b hUsed hClosed hKnownLet hPlace

/-- `Spine.cons` with the argument given as a term, with the proof that it is an atom. -/
def Spine.consT {Γ : Ctx} {σ : TyWf} {σs : List TyWf} {u v : Usage Γ} {k : Head}
    {ks : List Head} (t : Term Sg Γ u σ k) (rest : Spine Sg Γ v σs ks)
    (hAnf : Head.isAtom k = true := by head_ok) :
    Spine Sg Γ (Usage.arg k u + v) (σ :: σs) (k :: ks) :=
  .cons (t.toAtom hAnf) rest

/-- `Terms.cons` with the element given as a term, with the proof that it is an atom. -/
def Terms.consT {Γ : Ctx} {τ : TyWf} {u v : Usage Γ} {k : Head} {ks : List Head}
    (t : Term Sg Γ u τ k) (rest : Terms Sg Γ v τ ks)
    (hAnf : Head.isAtom k = true := by head_ok) :
    Terms Sg Γ (Usage.arg k u + v) τ (k :: ks) :=
  .cons (t.toAtom hAnf) rest

/-- `FamilyMemberValue.alias` with the value given as a term, with the proof that it is an
    atom. -/
def FamilyMemberValue.aliasT {Γ : Ctx} (b : TyWf) {u : Usage Γ} {kv : Head}
    (value : Term Sg Γ u b kv) (hAnf : Head.isAtom kv = true := by head_ok) :
    FamilyMemberValue Sg Γ (Usage.arg kv u) (.alias b) :=
  .alias b (value.toAtom hAnf)

/-! ## Writing a name where an atom or a callee is asked -/

/-- A variable, as an atom. -/
abbrev Atom.var {Γ : Ctx} {τ : TyWf} (x : Γ ∋ τ) : Atom Sg Γ (Usage.single x) τ (.var x.index) :=
  .ref (.var x)

/-- A reference to a declaration, as an atom. -/
abbrev Atom.global {Γ : Ctx} {τ : TyWf} (r : GlobalRef Sg.decls τ) :
    Atom Sg Γ Usage.global τ .global :=
  .ref (.global r)

/-- A variable, as what an application calls. -/
abbrev Callee.var {Γ : Ctx} {τ : TyWf} (x : Γ ∋ τ) :
    Callee Sg Γ (Usage.single x) τ (.var x.index) :=
  .ref (.var x)

/-- A reference to a declaration, as what an application calls. -/
abbrev Callee.global {Γ : Ctx} {τ : TyWf} (r : GlobalRef Sg.decls τ) :
    Callee Sg Γ Usage.global τ .global :=
  .ref (.global r)

/-- An application, as what a further application calls: `f a b` is `(f a) b`. -/
abbrev Callee.ap {Γ : Ctx} {σ τ : TyWf} {u v : Usage Γ} {kf ka : Head}
    (f : Callee Sg Γ u (σ ⇒ τ) kf) (a : Atom Sg Γ v σ ka)
    (hClosed : Head.closedComp (Usage.scrutinize kf (Usage.arg ka (u + v))) τ .comp = false := by
      not_closed) :
    Callee Sg Γ (Usage.scrutinize kf (Usage.arg ka (u + v))) τ (.app ka.isVar0) :=
  .app (.ap f a hClosed)

end LeanScript

end
