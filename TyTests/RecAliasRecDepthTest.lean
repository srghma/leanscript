module

public import TyTests.RecAliasRecDepthTest.Programs

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive newtype: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TyTests.RecAliasRecDepthTest.Programs`; this file writes the programs as terms of the
language and checks them against the references.
-/

namespace TyTests.RecAliasRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`, written out at depth one

The branch binds the body (index `0`) and the window (index `1`).  Taking the window apart
is the descent: it is an `Option` of a label and the answer tree at the chain below, and

* `none` — the chain ends here — answers `0`;
* `some` binds that link, whose second field is the answer tree at the chain below, and
  whose tree in turn holds the answer at that chain and *its* window: a label and an
  `Option` of the answer at the chain below **that**.  `none` there answers `1`, and
  `some` answers `fib (chain below) + fib (chain below that)`, which is the
  `fib n + fib (n + 1)` of the program. -/

/-- The branch of `fib`. -/
def fibBranch : Term sigAdd (branchCtx natT 1) natT :=
  .taggedUnion_casesOn (.var (v♯1))
    (.skip (.nat_mk 0)
      (.here
        (.record_casesOn (.var (v♯0))
          (.record_casesOn (.var (v♯1))
            (.taggedUnion_casesOn (.var (v♯1))
              (.skip (.nat_mk 1)
                (.here
                  (.record_casesOn (.var (v♯0))
                    (addT (.var (v♯3)) (.var (v♯1))))
                  .nil)))))
        .nil))

/-- **`fib` over a recursive newtype**: the depth-one fold. -/
def fibTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 1 (.var (v♯0)) fibBranch)

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

Each further level is the same three steps — take the link apart (a label, and the answer
tree at the chain below), take that tree apart (the answer there, and its own window), and
dispatch — so a level pushes five binders in front of the context and the answers read so
far sit at the indices `1, 3, 8, 13, …`, nearest first. -/

/-- The tribonacci numbers: a depth-two fold. -/
def tribBranch : Term sigAdd (branchCtx natT 2) natT :=
  .taggedUnion_casesOn (.var (v♯1))
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
                            (.record_casesOn (.var (v♯0))
                              (addT (addT (.var (v♯8)) (.var (v♯3))) (.var (v♯1))))
                            .nil)))))
                  .nil)))))
        .nil))

/-- `trib`, as a term. -/
def tribTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 2 (.var (v♯0)) tribBranch)

/-- The tetranacci numbers: a depth-three fold. -/
def tetraBranch : Term sigAdd (branchCtx natT 3) natT :=
  .taggedUnion_casesOn (.var (v♯1))
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
                                      (.record_casesOn (.var (v♯0))
                                        (addT (addT (addT (.var (v♯13)) (.var (v♯8)))
                                          (.var (v♯3))) (.var (v♯1))))
                                      .nil)))))
                            .nil)))))
                  .nil)))))
        .nil))

/-- `tetra`, as a term. -/
def tetraTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 3 (.var (v♯0)) tetraBranch)

/-- The pentanacci numbers: a depth-four fold. -/
def pentaBranch : Term sigAdd (branchCtx natT 4) natT :=
  .taggedUnion_casesOn (.var (v♯1))
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
                                                (.record_casesOn (.var (v♯0))
                                                  (addT (addT (addT (addT
                                                    (.var (v♯18)) (.var (v♯13)))
                                                    (.var (v♯8))) (.var (v♯3)))
                                                    (.var (v♯1))))
                                                .nil)))))
                                      .nil)))))
                            .nil)))))
                  .nil)))))
        .nil))

/-- `penta`, as a term. -/
def pentaTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 4 (.var (v♯0)) pentaBranch)

/-- The hexanacci numbers: a depth-five fold. -/
def hexaBranch : Term sigAdd (branchCtx natT 5) natT :=
  .taggedUnion_casesOn (.var (v♯1))
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
                                                          (.record_casesOn (.var (v♯0))
                                                            (addT (addT (addT (addT (addT
                                                              (.var (v♯23)) (.var (v♯18)))
                                                              (.var (v♯13))) (.var (v♯8)))
                                                              (.var (v♯3))) (.var (v♯1))))
                                                          .nil)))))
                                                .nil)))))
                                      .nil)))))
                            .nil)))))
                  .nil)))))
        .nil))

/-- `hexa`, as a term. -/
def hexaTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 5 (.var (v♯0)) hexaBranch)

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the chain immediately below, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- The branch of the loop: at the end of the chain, `fun a b => a`; with the loop `ih` at
    the chain below, `fun a b => ih b (a + b)`. -/
def fibTRBranch : Term sigAdd (branchCtx loopTy 0) loopTy :=
  .taggedUnion_casesOn (.var (v♯1))
    (.skip (.lam (.lam (.var (v♯1))))
      (.here
        (.record_casesOn (.var (v♯0))
          (.lam (.lam (.ap (.ap (.var (v♯3)) (.var (v♯0)))
            (addT (.var (v♯1)) (.var (v♯0)))))))
        .nil))

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.ap (.ap (.recAlias_rec 0 (.var (v♯0)) fibTRBranch) (.nat_mk 0)) (.nat_mk 1))

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at one link more alongside
the answer at this one.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib t, fib (link above t))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- The branch of the pair recursion: at the end of the chain, `(0, 1)`; with the pair at
    the chain below taken apart as `a` and `b`, `(b, a + b)`. -/
def fibPairBranch : Term sigAdd (branchCtx pairTy 0) pairTy :=
  .taggedUnion_casesOn (.var (v♯1))
    (.skip (.record_mk pairSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil)))
      (.here
        (.record_casesOn (.var (v♯0))
          (.record_casesOn (.var (v♯1))
            (.record_mk pairSchema
              (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil)))))
        .nil))

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.record_casesOn (.recAlias_rec 0 (.var (v♯0)) fibPairBranch) (.var (v♯0)))

/-! ## 6. The continuant: a fold that reads the newtype's **own label** as well

Every branch above ignores the labels the chain carries.  The continuant does not: it is
the `fib`-shaped recursion

```lean
def cont : Chain → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a t@(.cons _ r) => a * cont t + cont r
```

so its branch multiplies the label — which the window carries beside the answer, and which
each descent pushes further out — by the answer one link down and adds the answer two
links down. -/

/-- The branch of the continuant. -/
def contBranch : Term sigAdd (branchCtx natT 1) natT :=
  .taggedUnion_casesOn (.var (v♯1))
    (.skip (.nat_mk 1)
      (.here
        (.record_casesOn (.var (v♯0))
          (.record_casesOn (.var (v♯1))
            (.taggedUnion_casesOn (.var (v♯1))
              (.skip (.var (v♯2))
                (.here
                  (.record_casesOn (.var (v♯0))
                    (addT (mulT (.var (v♯5)) (.var (v♯3))) (.var (v♯1))))
                  .nil)))))
        .nil))

/-- The continuant, as a term: the depth-one fold that also reads the label. -/
def contTerm : Term sigAdd [] (chainTy ⇒ natT) :=
  .lam (.recAlias_rec 1 (.var (v♯0)) contBranch)

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

At depth `0` the window holds the answer at the chain below and nothing more, so there is
nothing to take apart there and the `fib` branch of §2 cannot be written: the answers two
links down are not in scope at all.  `LeanScript.TyWf.recAliasRecBinders_zero` is the
statement that the default depth is the old branch context — the newtype's body — with
exactly that one answer appended. -/

example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 =
      TyWf.recBinders chainTy τ [chainBodyW] ++ [TyWf.recAliasMap chainBodyW τ] :=
  TyWf.recAliasRecBinders_zero chainBodyW (by ty_wf) τ

example (τ : TyWf) :
    (TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 5).length = 2 :=
  TyWf.length_recAliasRecBinders chainBodyW (by ty_wf) τ 5

-- And at depth `0` there is nothing below the answer to take apart: the `some` of the
-- window binds a label and the answer at the chain below, a `nat`, so the second descent
-- of §2 — which is what `fib` needs — cannot be written.
/--
error: Application type mismatch: The argument
  DeBruijn.head
has type
  DeBruijn (?m.52 :: ?m.53) ?m.52
but is expected to have type
  DeBruijn
    (((linkSchema (treeTy natT 0)).snd :: (linkSchema (treeTy natT 0)).rest).append
      ({ head := linkTy (treeTy natT 0), tail := [] }.toList ++ branchCtx natT 0))
    (TyWf.record ?m.43)
in the application
  DeBruijn.head.tail
-/
#guard_msgs (error) in
def fibBranchTooShallow : Term sigAdd (branchCtx natT 0) natT :=
  .taggedUnion_casesOn (.var (v♯1))
    (.skip (.nat_mk 0)
      (.here
        (.record_casesOn (.var (v♯0))
          (.record_casesOn (.var (v♯1)) (.nat_mk 1)))
        .nil))

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: the link half way down a chain is not the link a fixed number
of steps below it, so there is no depth at which the branch is *given* the answer at it.
A fold is given the answers on the path it descended, and a recursion that jumps needs a
measure and a proof, which a `Term` does not carry.  This is the same boundary
`TyTests/NatRecDepthTest.lean` records for `Nat`.
-/

end TyTests.RecAliasRecDepth

end
