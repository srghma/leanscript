module

public import LeanScript.Expr.Term
public import LeanScript.Eval
public import LeanScript.RecObjectRecFacts
public import TyTests.FibWindowTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a recursive record: `recObject_rec` at every depth

`TyTests/NatRecDepthTest.lean` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`; `TyTests/ArrayRecDepthTest.lean` does the same
for a fold over an array and `TyTests/RecUnionRecDepthTest.lean` for a fold over a
recursive tagged union.  This file is that exercise for a fold over a **recursive
record**, which is `LeanScript.Term.recObject_rec`.

## Why a record needed a different window

A recursive record is the one binder that can never have a field that is *literally* an
occurrence of itself: a record has values only when **all** of its fields do, so a field
written `Ty.self` would leave it with none and the tree would not be a type
(`LeanScript.Ty.not_wf_recObject_self`).  So `LeanScript.TyWf.recBinders`, which puts the
value of the fold after a field that *is* an occurrence, put nothing anywhere: the fold of
a record handed its branch no answer at all
(`LeanScript.TyWf.recBinders_recObject`, and the `rfl` example in §1).

What the fold hands the branch now is one **window** binder: the record's own fields with
every occurrence of the record replaced by the answer there
(`LeanScript.TyWf.recObjectMap`), and at depth `k` by the **answer tree** of depth `k` at
that subvalue — the answer at it beside, in the shape of *its* fields, the depth-`k - 1`
trees of its own subvalues (`LeanScript.TyWf.recObjectAnswerTree`).  So a depth-`k` branch
reads the answers at everything `k + 1` levels down, along the path it descends, exactly
as a depth-`k` branch of `Term.recTaggedUnion_rec` does.

## The record

```lean
inductive Cell where
  | mk (label : Nat) (next : Option Cell)
```

a chain of labelled cells — the shortest recursive record there is, since the occurrence
has to sit inside something that has a value without it, here an `Option`.  Its `fib` is
the program the depth is for:

```lean
def Cell.fib : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 1
  | .mk _ (some (.mk l (some g))) => fib (.mk l (some g)) + fib g
```

| the program | the node it is | here |
| :-- | :-- | :-- |
| `Cell.fib` (reads two cells down) | `recObject_rec 1` | `fibTerm` |
| `Cell.trib`, `Cell.tetra`, `Cell.penta`, `Cell.hexa` | `recObject_rec 2 … 5` | `tribTerm`, … |
| `Cell.fibLoopTR` (tail-recursive, two accumulators) | `recObject_rec 0` **at a function type** | `fibTRTerm` |
| `Cell.fibPair` (pair recursion) | `recObject_rec 0` at a record type | `fibPairTerm` |
| `Cell.cont` (the continuant, which reads the **label** too) | `recObject_rec 1` | `contTerm` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

**What is checked.**  `LeanScript.Ty.Den` gives a recursive shape no values — there is no
least fixpoint in the model yet — so, exactly as in `TyTests/RecTermTest.lean` and
`TyTests/RecUnionRecDepthTest.lean`, a term over a recursive record is checked **by its
type** rather than by running it: each definition below states the type of the term it
builds, so the file fails to build if the branch a program needs cannot be written at that
depth, or is written in a context other than the documented one.  What the contexts are is
pinned separately, by the `rfl` examples of §1.

The Lean programs the terms transcribe are checked too, in §0: their values at `10` by
`#guard`, that `Cell.fib` is the ordinary `fib` of the chain's length, and the request's
own theorems — that the pair recursion carries `(fib n, fib (n + 1))`, that its first
component is `fib`, and that the tail-recursive loop computes `fib`.
-/

namespace TyTests.RecObjectRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of. -/

/-- A chain of labelled cells: the recursive record this file folds over. -/
inductive Cell where
  /-- A label, and perhaps one more cell. -/
  | mk (label : Nat) (next : Option Cell)

namespace Cell

/-- How many cells there are **below** this one. -/
def len : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some c) => len c + 1

/-- A chain of `n + 1` cells, all labelled `0`. -/
def ofNat : Nat → Cell
  | 0 => .mk 0 none
  | n + 1 => .mk 0 (some (ofNat n))

@[simp] theorem len_ofNat : (n : Nat) → len (ofNat n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (len_ofNat n)

/-- `fib`, on a chain: it reads the answer two cells down. -/
def fib : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 1
  | .mk _ (some (.mk l (some g))) => fib (.mk l (some g)) + fib g
decreasing_by all_goals (simp_wf; omega)

/-- The tribonacci numbers: three cells down. -/
def trib : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some g))))) =>
      trib (.mk l₂ (some (.mk l₃ (some g)))) + trib (.mk l₃ (some g)) + trib g
decreasing_by all_goals (simp_wf; omega)

/-- The tetranacci numbers: four cells down. -/
def tetra : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some g))))))) =>
      tetra (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some g)))))) +
      tetra (.mk l₃ (some (.mk l₄ (some g)))) + tetra (.mk l₄ (some g)) + tetra g
decreasing_by all_goals (simp_wf; omega)

/-- The pentanacci numbers: five cells down. -/
def penta : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))))) => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g))))))))) =>
      penta (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g)))))))) +
      penta (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some g)))))) +
      penta (.mk l₄ (some (.mk l₅ (some g)))) + penta (.mk l₅ (some g)) + penta g
decreasing_by all_goals (simp_wf; omega)

/-- The hexanacci numbers: six cells down. -/
def hexa : Cell → Nat
  | .mk _ none => 0
  | .mk _ (some (.mk _ none)) => 0
  | .mk _ (some (.mk _ (some (.mk _ none)))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none)))))))) => 0
  | .mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ (some (.mk _ none))))))))))
      => 1
  | .mk _ (some (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅
      (some (.mk l₆ (some g))))))))))) =>
      hexa (.mk l₂ (some (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))))))
        + hexa (.mk l₃ (some (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))))
        + hexa (.mk l₄ (some (.mk l₅ (some (.mk l₆ (some g))))))
        + hexa (.mk l₅ (some (.mk l₆ (some g)))) + hexa (.mk l₆ (some g)) + hexa g
decreasing_by all_goals (simp_wf; omega)

/-- The tail-recursive loop, with two accumulators. -/
def fibLoopTR : Cell → Nat → Nat → Nat
  | .mk _ none, a, _ => a
  | .mk _ (some c), a, b => fibLoopTR c b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (t : Cell) : Nat := fibLoopTR t 0 1

/-- The pair recursion: the answer at the chain and the answer at one cell more. -/
def fibPair : Cell → Nat × Nat
  | .mk _ none => (0, 1)
  | .mk _ (some c) => let (a, b) := fibPair c; (b, a + b)

/-- The **continuant** of the labels of a chain, the one program here that reads the
    record's own field as well as the answers: `K ⟨a⟩ = a` and
    `K ⟨a, b, …⟩ = a * K ⟨b, …⟩ + K ⟨…⟩`, where the empty chain answers `1`. -/
def cont : Cell → Nat
  | .mk a none => a
  | .mk a (some (.mk b none)) => a * cont (.mk b none) + 1
  | .mk a (some (.mk b (some g))) => a * cont (.mk b (some g)) + cont g
decreasing_by all_goals (simp_wf; omega)

-- The reference programs are the familiar sequences.
#guard fib (ofNat 10) = 55
#guard fibTR (ofNat 10) = 55
#guard fibPair (ofNat 10) = (55, 89)
#guard trib (ofNat 10) = 81
#guard tetra (ofNat 10) = 56
#guard penta (ofNat 10) = 31
#guard hexa (ofNat 10) = 16
#guard cont (.mk 3 (some (.mk 2 (some (.mk 1 none))))) = 10

/-- **The chain's `fib` is the ordinary `fib`** of the number of cells below it. -/
theorem fib_eq_fib_len : (t : Cell) → fib t = TyTests.FibWindow.fib (len t)
  | .mk _ none => by simp [fib, len, TyTests.FibWindow.fib]
  | .mk _ (some (.mk _ none)) => by simp [fib, len, TyTests.FibWindow.fib]
  | .mk a (some (.mk l (some g))) => by
      have e : fib (.mk a (some (.mk l (some g)))) = fib (.mk l (some g)) + fib g := by
        simp [fib]
      have hl : len (.mk a (some (.mk l (some g)))) = len g + 2 := by simp [len]
      rw [e, hl, fib_eq_fib_len (.mk l (some g)), fib_eq_fib_len g]
      show TyTests.FibWindow.fib (len g + 1) + TyTests.FibWindow.fib (len g) = _
      show _ = TyTests.FibWindow.fib (len g) + TyTests.FibWindow.fib (len g + 1)
      omega
decreasing_by all_goals (simp_wf; omega)

/-- So on the chain of `n + 1` cells it is `fib n`. -/
theorem fib_ofNat (n : Nat) : fib (ofNat n) = TyTests.FibWindow.fib n := by
  rw [fib_eq_fib_len, len_ofNat]

/-- The pair recursion carries the answer at the chain and the answer at one cell
    more. -/
theorem fibPair_eq : (t : Cell) → fibPair t = (fib t, fib (.mk 0 (some t)))
  | .mk _ none => by simp [fibPair, fib]
  | .mk l (some c) => by
      have ih := fibPair_eq c
      have hfib : fib (.mk l (some c)) = fib (.mk 0 (some c)) := by
        cases c with
        | mk m o => cases o <;> simp [fib]
      show (let (a, b) := fibPair c; ((b, a + b) : Nat × Nat)) = _
      rw [ih]
      have hup : fib (.mk 0 (some (.mk l (some c)))) =
          fib (.mk l (some c)) + fib c := by simp [fib]
      simp only [hup, hfib]
      exact Prod.ext rfl (Nat.add_comm _ _)

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (t : Cell) : (fibPair t).1 = fib t := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `k` and `k + 1`, answers at `k` plus the length
    of the chain. -/
theorem fibLoopTR_eq : (t : Cell) → (k : Nat) →
    fibLoopTR t (TyTests.FibWindow.fib k) (TyTests.FibWindow.fib (k + 1)) =
      TyTests.FibWindow.fib (k + len t)
  | .mk _ none, k => rfl
  | .mk _ (some c), k => by
      show fibLoopTR c (TyTests.FibWindow.fib (k + 1))
        (TyTests.FibWindow.fib k + TyTests.FibWindow.fib (k + 1)) = _
      rw [show TyTests.FibWindow.fib k + TyTests.FibWindow.fib (k + 1) =
        TyTests.FibWindow.fib (k + 2) from rfl, fibLoopTR_eq c (k + 1)]
      show TyTests.FibWindow.fib (k + 1 + len c) = TyTests.FibWindow.fib (k + (len c + 1))
      congr 1
      omega

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (t : Cell) : fibTR t = fib t := by
  show fibLoopTR t (TyTests.FibWindow.fib 0) (TyTests.FibWindow.fib 1) = _
  rw [fibLoopTR_eq t 0, fib_eq_fib_len, Nat.zero_add]

end Cell

/-! ## 1. The record, and what its branch binds -/

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

/-- A signature with two declarations, `add` and `mul`, both `nat ⇒ nat ⇒ nat`:
    arithmetic is external to the language. -/
def sigAdd : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"mul", natT ⇒ natT ⇒ natT⟩], by decide⟩

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ natT) : Term sigAdd Γ natT :=
  .ap (.ap (.global .here) a) b

/-- `mul a b`, for two terms in hand. -/
def mulT {Γ : Ctx} (a b : Term sigAdd Γ natT) : Term sigAdd Γ natT :=
  .ap (.ap (.global (.there .here)) a) b

/-- `Option τ`, as a union of the language: `none` first, then `some`. -/
abbrev optTy (τ : TyWf) : TyWf := .taggedUnion (.skip (.here ⟨τ, []⟩ []))

/-- `Option Ty.self`, written inside the binder. -/
def optSelf : Ty := .taggedUnion (.skip (.here ⟨Ty.self, []⟩ []))

/-- The schema of a cell: a label, and perhaps one more cell.  The occurrence of the
    record sits **inside** the union, which is the only way a recursive record can
    mention itself and still have values. -/
def cellSchema : LeanRecordSchema (TyWfIn 1) :=
  ⟨(Ty.prim .nat).toTyWfIn, optSelf.toTyWfIn, []⟩

/-- The type of a cell. -/
def cellTy : TyWf := .recObject cellSchema

-- A value of it holds a `nat` and an `Option` of the record itself.
example : (TyWf.recObjectUnfold cellSchema).toList = [natT, optTy cellTy] := rfl

-- **The old fold bound no answer**: no field of the record is an occurrence of it, so
-- `TyWf.recBinders` — which is what the branch of every other fold uses — hands the
-- branch the fields and nothing else (`LeanScript.TyWf.recBinders_recObject`, at every
-- record).
example (τ : TyWf) :
    TyWf.recBinders cellTy τ cellSchema.toList = [natT, optTy cellTy] := rfl

example (τ : TyWf) :
    TyWf.recBinders cellTy τ cellSchema.toList = (TyWf.recObjectUnfold cellSchema).toList :=
  TyWf.recBinders_recObject cellSchema (by ty_wf) τ

/-- **The answer tree of depth `j` at a cell**, written out: at `0` the answer there, and
    at `j + 1` that answer beside the cell's own fields — a label, and an `Option` of the
    tree of depth `j` at the cell below. -/
abbrev treeTy (τ : TyWf) : Nat → TyWf
  | 0 => τ
  | j + 1 => .record ⟨τ, .record ⟨natT, optTy (treeTy τ j), []⟩, []⟩

/-- **The window a depth-`k` fold binds**, written out: the cell's fields with the cell
    below replaced by the answer tree of depth `k` at it. -/
abbrev winTy (τ : TyWf) (k : Nat) : TyWf := .record ⟨natT, optTy (treeTy τ k), []⟩

-- At depth `0` the branch binds the label, the `Option` of cells, and the `Option` of
-- the answers: the plain fold of the record.
example (τ : TyWf) (Γ : Ctx) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 0 ++ Γ =
      natT :: optTy cellTy :: .record ⟨natT, optTy τ, []⟩ :: Γ := rfl

-- At depth `1` the `Option` of the window holds, for the cell below, the answer at it
-- *and* the answers at the cells below that one.
example (τ : TyWf) (Γ : Ctx) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 1 ++ Γ =
      natT :: optTy cellTy ::
        .record ⟨natT, optTy (.record ⟨τ, .record ⟨natT, optTy τ, []⟩, []⟩), []⟩ :: Γ :=
  rfl

/-- The context every fold below is written in: the cell it folds over, bound by the
    `fun` in front of it. -/
abbrev CCtx : Ctx := [cellTy]

/-- **The context a branch of a depth-`k` fold is written in**: the label, the `Option` of
    cells below, the window, and then the context the fold stands in. -/
abbrev branchCtx (τ : TyWf) (k : Nat) : Ctx :=
  natT :: optTy cellTy :: winTy τ k :: CCtx

-- That really is the context the grammar asks for, at each of the depths used below.
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 0 ++ CCtx = branchCtx τ 0 := rfl
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 1 ++ CCtx = branchCtx τ 1 := rfl
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 2 ++ CCtx = branchCtx τ 2 := rfl
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 3 ++ CCtx = branchCtx τ 3 := rfl
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 4 ++ CCtx = branchCtx τ 4 := rfl
example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 5 ++ CCtx = branchCtx τ 5 := rfl

/-- A cell with no cell below it, as a term. -/
def leafTerm : Term sigAdd [] cellTy :=
  .recObject_mk cellSchema
    (fields := .cons (.nat_mk 1)
      (.cons (.taggedUnion_mk (.skip (.here ⟨cellTy, []⟩ [])) 0 (fields := .nil)) .nil))

/-- One more cell on top of the one in scope. -/
def consTerm : Term sigAdd [] (cellTy ⇒ cellTy) :=
  .lam (.recObject_mk cellSchema
    (fields := .cons (.nat_mk 1)
      (.cons (.taggedUnion_mk (.skip (.here ⟨cellTy, []⟩ [])) 1
        (fields := .cons (.var (v♯0)) .nil)) .nil)))

/-! ## 2. `fib`, written out at depth one

The branch binds the label (index `0`), the `Option` of cells below (index `1`) and the
window (index `2`).  Taking the window apart is the descent: its second field is an
`Option` of the answer tree at the cell below, and

* `none` — no cell below — answers `0`;
* `some d` binds that tree, whose first field is the answer at the cell below and whose
  second field is *its* fields' shape: a label and an `Option` of the answer at the cell
  below **that**.  `none` there answers `1`, and `some y` answers
  `fib (cell below) + fib (cell below that)`, which is the `fib n + fib (n + 1)` of the
  program. -/

/-- The branch of `fib`. -/
def fibBranch : Term sigAdd (branchCtx natT 1) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (.nat_mk 1)
                  (.here (addT (.var (v♯3)) (.var (v♯0))) .nil)))))
          .nil)))

/-- **`fib` over a recursive record**: the depth-one fold. -/
def fibTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 1 (.var (v♯0)) fibBranch)

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

Each further level is the same three steps — take the answer tree apart (the answer at
that cell, and its fields' shape), take that shape apart (the label, and the `Option`
below it), and dispatch — so a level pushes five binders in front of the context and the
answers read so far sit at the indices `3, 8, 13, …`, nearest first. -/

/-- The tribonacci numbers: a depth-two fold. -/
def tribBranch : Term sigAdd (branchCtx natT 2) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (.nat_mk 0)
                  (.here
                    (.record_casesOn (.var (v♯0))
                      (.record_casesOn (.var (v♯1))
                        (.taggedUnion_casesOn (.var (v♯1))
                          (.skip (.nat_mk 1)
                            (.here
                              (addT (addT (.var (v♯8)) (.var (v♯3))) (.var (v♯0)))
                              .nil)))))
                    .nil)))))
          .nil)))

/-- `trib`, as a term. -/
def tribTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 2 (.var (v♯0)) tribBranch)

/-- The tetranacci numbers: a depth-three fold. -/
def tetraBranch : Term sigAdd (branchCtx natT 3) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (.nat_mk 0)
                  (.here
                    (.record_casesOn (.var (v♯0))
                      (.record_casesOn (.var (v♯1))
                        (.taggedUnion_casesOn (.var (v♯1))
                          (.skip (.nat_mk 0)
                            (.here
                              (.record_casesOn (.var (v♯0))
                                (.record_casesOn (.var (v♯1))
                                  (.taggedUnion_casesOn (.var (v♯1))
                                    (.skip (.nat_mk 1)
                                      (.here
                                        (addT (addT (addT (.var (v♯13)) (.var (v♯8)))
                                          (.var (v♯3))) (.var (v♯0)))
                                        .nil)))))
                              .nil)))))
                    .nil)))))
          .nil)))

/-- `tetra`, as a term. -/
def tetraTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 3 (.var (v♯0)) tetraBranch)

/-- The pentanacci numbers: a depth-four fold. -/
def pentaBranch : Term sigAdd (branchCtx natT 4) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (.nat_mk 0)
                  (.here
                    (.record_casesOn (.var (v♯0))
                      (.record_casesOn (.var (v♯1))
                        (.taggedUnion_casesOn (.var (v♯1))
                          (.skip (.nat_mk 0)
                            (.here
                              (.record_casesOn (.var (v♯0))
                                (.record_casesOn (.var (v♯1))
                                  (.taggedUnion_casesOn (.var (v♯1))
                                    (.skip (.nat_mk 0)
                                      (.here
                                        (.record_casesOn (.var (v♯0))
                                          (.record_casesOn (.var (v♯1))
                                            (.taggedUnion_casesOn (.var (v♯1))
                                              (.skip (.nat_mk 1)
                                                (.here
                                                  (addT (addT (addT (addT
                                                    (.var (v♯18)) (.var (v♯13)))
                                                    (.var (v♯8))) (.var (v♯3)))
                                                    (.var (v♯0)))
                                                  .nil)))))
                                        .nil)))))
                              .nil)))))
                    .nil)))))
          .nil)))

/-- `penta`, as a term. -/
def pentaTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 4 (.var (v♯0)) pentaBranch)

/-- The hexanacci numbers: a depth-five fold. -/
def hexaBranch : Term sigAdd (branchCtx natT 5) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (.nat_mk 0)
                  (.here
                    (.record_casesOn (.var (v♯0))
                      (.record_casesOn (.var (v♯1))
                        (.taggedUnion_casesOn (.var (v♯1))
                          (.skip (.nat_mk 0)
                            (.here
                              (.record_casesOn (.var (v♯0))
                                (.record_casesOn (.var (v♯1))
                                  (.taggedUnion_casesOn (.var (v♯1))
                                    (.skip (.nat_mk 0)
                                      (.here
                                        (.record_casesOn (.var (v♯0))
                                          (.record_casesOn (.var (v♯1))
                                            (.taggedUnion_casesOn (.var (v♯1))
                                              (.skip (.nat_mk 0)
                                                (.here
                                                  (.record_casesOn (.var (v♯0))
                                                    (.record_casesOn (.var (v♯1))
                                                      (.taggedUnion_casesOn (.var (v♯1))
                                                        (.skip (.nat_mk 1)
                                                          (.here
                                                            (addT (addT (addT (addT (addT
                                                              (.var (v♯23)) (.var (v♯18)))
                                                              (.var (v♯13))) (.var (v♯8)))
                                                              (.var (v♯3))) (.var (v♯0)))
                                                            .nil)))))
                                                  .nil)))))
                                        .nil)))))
                              .nil)))))
                    .nil)))))
          .nil)))

/-- `hexa`, as a term. -/
def hexaTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 5 (.var (v♯0)) hexaBranch)

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the cell immediately below, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- The branch of the loop: with no cell below, `fun a b => a`; with the loop `ih` at the
    cell below, `fun a b => ih b (a + b)`. -/
def fibTRBranch : Term sigAdd (branchCtx loopTy 0) loopTy :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.lam (.lam (.var (v♯1))))
        (.here
          (.lam (.lam (.ap (.ap (.var (v♯2)) (.var (v♯0)))
            (addT (.var (v♯1)) (.var (v♯0))))))
          .nil)))

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.ap (.ap (.recObject_rec 0 (.var (v♯0)) fibTRBranch) (.nat_mk 0)) (.nat_mk 1))

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at one cell more alongside
the answer at this one.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib t, fib (cell above t))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- The branch of the pair recursion: with no cell below, `(0, 1)`; with the pair at the
    cell below taken apart as `a` and `b`, `(b, a + b)`. -/
def fibPairBranch : Term sigAdd (branchCtx pairTy 0) pairTy :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.record_mk pairSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil)))
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_mk pairSchema
              (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil))))
          .nil)))

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.record_casesOn (.recObject_rec 0 (.var (v♯0)) fibPairBranch) (.var (v♯0)))

/-! ## 6. The continuant: a fold that reads the record's **own field** as well

Every branch above ignores the label the record carries.  The continuant does not: it is
the `fib`-shaped recursion

```lean
def cont : Cell → Nat
  | .mk a none => a
  | .mk a (some (.mk b none)) => a * cont (.mk b none) + 1
  | .mk a (some (.mk b (some g))) => a * cont (.mk b (some g)) + cont g
```

so its branch multiplies the label — index `0` of the branch, pushed further out by each
descent — by the answer one cell down and adds the answer two cells down. -/

/-- The branch of the continuant. -/
def contBranch : Term sigAdd (branchCtx natT 1) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.var (v♯2))
        (.here
          (.record_casesOn (.var (v♯0))
            (.record_casesOn (.var (v♯1))
              (.taggedUnion_casesOn (.var (v♯1))
                (.skip (addT (mulT (.var (v♯7)) (.var (v♯2))) (.nat_mk 1))
                  (.here (addT (mulT (.var (v♯8)) (.var (v♯3))) (.var (v♯0))) .nil)))))
          .nil)))

/-- The continuant, as a term: the depth-one fold that also reads the label. -/
def contTerm : Term sigAdd [] (cellTy ⇒ natT) :=
  .lam (.recObject_rec 1 (.var (v♯0)) contBranch)

/-! ## 7. What the evaluator says about these terms

A recursive shape has no values in the model (`LeanScript.Ty.Den`), so a fold over one is
a term the evaluator does not run, and `LeanScript.Term.NoRecMk` says so: taking a value
apart is fine — there is nothing to take apart — while *building* one is not. -/

example : Term.NoRecMk fibTerm := by no_rec_mk
example : Term.NoRecMk hexaTerm := by no_rec_mk
example : Term.NoRecMk fibTRTerm := by no_rec_mk
example : Term.NoRecMk fibPairTerm := by no_rec_mk
example : Term.NoRecMk contTerm := by no_rec_mk

/-! ## 8. The depth-zero fold, and what no depth reaches

At depth `0` the window holds the answer at the cell below and nothing more, so there is
nothing to take apart there and the `fib` branch of §2 cannot be written: the answers two
cells down are not in scope at all.  `LeanScript.TyWf.recObjectRecBinders_zero` is the
statement that the default depth is the old branch context — the record's fields — with
exactly that one answer appended. -/

example (τ : TyWf) :
    TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 0 =
      TyWf.recBinders cellTy τ cellSchema.toList ++ [TyWf.recObjectMap cellSchema τ] :=
  TyWf.recObjectRecBinders_zero cellSchema (by ty_wf) τ

example (τ : TyWf) :
    (TyWf.recObjectRecBinders cellSchema (by ty_wf) τ 5).length = cellSchema.length + 1 :=
  TyWf.length_recObjectRecBinders cellSchema (by ty_wf) τ 5

-- And at depth `0` there is nothing below the answer to take apart: the `some` of the
-- window binds the answer at the cell below, a `nat`, so the second descent of §2 —
-- which is what `fib` needs — cannot be written.
/--
error: PLACEHOLDER
-/
#guard_msgs (error) in
def fibBranchTooShallow : Term sigAdd (branchCtx natT 0) natT :=
  .record_casesOn (.var (v♯2))
    (.taggedUnion_casesOn (.var (v♯1))
      (.skip (.nat_mk 0)
        (.here (.record_casesOn (.var (v♯0)) (.nat_mk 1)) .nil)))

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: the cell half way down a chain is not the cell a fixed number
of links below it, so there is no depth at which the branch is *given* the answer at it.
A fold is given the answers on the path it descended, and a recursion that jumps needs a
measure and a proof, which a `Term` does not carry.  This is the same boundary
`TyTests/NatRecDepthTest.lean` records for `Nat`.
-/

end TyTests.RecObjectRecDepth

end
