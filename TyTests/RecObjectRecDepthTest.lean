module

public import TyTests.RecObjectRecDepthTest.Programs

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive record: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TyTests.RecObjectRecDepthTest.Programs`; this file writes the programs as terms of the
language and checks them against the references.
-/

namespace TyTests.RecObjectRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

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
example : Term.NoRecMk tribTerm := by no_rec_mk
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
error: Application type mismatch: The argument
  DeBruijn.head
has type
  DeBruijn (?m.56 :: ?m.57) ?m.56
but is expected to have type
  { head := treeTy natT 0, tail := [] }.toList ++
      ({ fst := natT, snd := optTy (treeTy natT 0), rest := [] }.toList ++ branchCtx natT 0) ∋
    TyWf.record ?m.51
in the application
  Term.var DeBruijn.head
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
