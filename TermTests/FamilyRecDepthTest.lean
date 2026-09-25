module

public import TermTests.FamilyRecDepthTest.Programs

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a mutual recursive family: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TermTests.FamilyRecDepthTest.Programs`; this file writes the programs as terms of the
language and checks them against the references.
-/

namespace TermTests.FamilyRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`, written out at depth one

The `zero` branch answers `0`.  The `succ` branch does not answer: it descends into its
field — the only occurrence of a member among its fields, which is
`FamilyMemberField.here rfl`, an occurrence of member `0` — and dispatches on member `0`
again.  In that dispatch the value is `succ n` with `n` in hand, so:

* if `n` is `zero` the value is `succ zero`, and the answer is `1`;
* if `n` is `succ m`, the context binds `m` (index `0`), the answer at `m` (index `1`),
  `n` (index `2`) and the answer at `n` (index `3`), and the answer is `fib m + fib n` —
  which is the `fib n + fib (n + 1)` of the program. -/

/-- The branches of `fib`: those of member `0`, which descend, and those of member `1`,
    which answer. -/
def fibCases :=
  (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.ctors
                (.skip (.here (.nat_mk 1))
                  (.here (.here (addT (.var (v♯1)) (.var (v♯3)))) .nil))))
            .nil)))
      (.cons (lsCases (.nat_mk 0)) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx _ natT famPe.members 1)

/-- **`fib` over a mutual family**: the depth-one fold. -/
def fibTerm :=
  (.lam (.mutualRecursiveFamily_rec 1 (.var (v♯0)) fibCases) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

The `n + k` recursions of the request, transcribed: at depth `k` the branch descends `k`
times, and the answers at the values it descended past are the odd indices `1, 3, …,
2k + 1` — nearest last, since each descent pushes the subvalue and its answer in front of
the context.  Every descent here is into member `0` again (`FamilyMemberAt.here`), since
that is the member whose constructor the fold is walking down; `TermTests/FamilyRecDepthMembersTest.lean` descends into the
*other* member. -/

/-- The tribonacci numbers: a depth-two fold. -/
def tribCases :=
  (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.ctors
                (.skip (.here (.nat_mk 0))
                  (.here
                    (.deep (.here rfl) .here
                      (.ctors
                        (.skip (.here (.nat_mk 1))
                          (.here
                            (.here (.letT (addT (.var (v♯1)) (.var (v♯3)))
                                     (addT (.var (v♯0)) (.var (v♯6)))))
                            .nil))))
                    .nil))))
            .nil)))
      (.cons (lsCases (.nat_mk 0)) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx _ natT famPe.members 2)

/-- `trib`, as a term. -/
def tribTerm :=
  (.lam (.mutualRecursiveFamily_rec 2 (.var (v♯0)) tribCases) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-- The tetranacci numbers: a depth-three fold. -/
def tetraCases :=
  (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.ctors
                (.skip (.here (.nat_mk 0))
                  (.here
                    (.deep (.here rfl) .here
                      (.ctors
                        (.skip (.here (.nat_mk 0))
                          (.here
                            (.deep (.here rfl) .here
                              (.ctors
                                (.skip (.here (.nat_mk 1))
                                  (.here
                                    (.here (.letT (addT (.var (v♯1)) (.var (v♯3)))
                                             (.letT (addT (.var (v♯0)) (.var (v♯6)))
                                               (addT (.var (v♯0)) (.var (v♯9))))))
                                    .nil))))
                            .nil))))
                    .nil))))
            .nil)))
      (.cons (lsCases (.nat_mk 0)) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx _ natT famPe.members 3)

/-- `tetra`, as a term. -/
def tetraTerm :=
  (.lam (.mutualRecursiveFamily_rec 3 (.var (v♯0)) tetraCases) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-- The pentanacci numbers: a depth-four fold. -/
def pentaCases :=
  (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.ctors
                (.skip (.here (.nat_mk 0))
                  (.here
                    (.deep (.here rfl) .here
                      (.ctors
                        (.skip (.here (.nat_mk 0))
                          (.here
                            (.deep (.here rfl) .here
                              (.ctors
                                (.skip (.here (.nat_mk 0))
                                  (.here
                                    (.deep (.here rfl) .here
                                      (.ctors
                                        (.skip (.here (.nat_mk 1))
                                          (.here
                                            (.here (.letT (addT (.var (v♯1)) (.var (v♯3)))
                                                     (.letT (addT (.var (v♯0)) (.var (v♯6)))
                                                       (.letT (addT (.var (v♯0)) (.var (v♯9)))
                                                         (addT (.var (v♯0)) (.var (v♯12)))))))
                                            .nil))))
                                    .nil))))
                            .nil))))
                    .nil))))
            .nil)))
      (.cons (lsCases (.nat_mk 0)) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx _ natT famPe.members 4)

/-- `penta`, as a term. -/
def pentaTerm :=
  (.lam (.mutualRecursiveFamily_rec 4 (.var (v♯0)) pentaCases) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-- The hexanacci numbers: a depth-five fold. -/
def hexaCases :=
  (.cons
      (.ctors
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl) .here
              (.ctors
                (.skip (.here (.nat_mk 0))
                  (.here
                    (.deep (.here rfl) .here
                      (.ctors
                        (.skip (.here (.nat_mk 0))
                          (.here
                            (.deep (.here rfl) .here
                              (.ctors
                                (.skip (.here (.nat_mk 0))
                                  (.here
                                    (.deep (.here rfl) .here
                                      (.ctors
                                        (.skip (.here (.nat_mk 0))
                                          (.here
                                            (.deep (.here rfl) .here
                                              (.ctors
                                                (.skip (.here (.nat_mk 1))
                                                  (.here
                                                    (.here (.letT (addT (.var (v♯1)) (.var (v♯3)))
                                                             (.letT (addT (.var (v♯0)) (.var (v♯6)))
                                                               (.letT (addT (.var (v♯0)) (.var (v♯9)))
                                                                 (.letT (addT (.var (v♯0)) (.var (v♯12)))
                                                                   (addT (.var (v♯0)) (.var (v♯15))))))))
                                                    .nil))))
                                            .nil))))
                                    .nil))))
                            .nil))))
                    .nil))))
            .nil)))
      (.cons (lsCases (.nat_mk 0)) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx _ natT famPe.members 5)

/-- `hexa`, as a term. -/
def hexaTerm :=
  (.lam (.mutualRecursiveFamily_rec 5 (.var (v♯0)) hexaCases) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the immediate predecessor, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- The branches of the loop: `zero` answers `fun a b => a`, and `succ` answers
    `fun a b => ih b (a + b)`, where `ih` is the loop at the predecessor. -/
def fibTRCases :=
  (.cons
      (.ctors
        (.skip (.here (.lam (.lam (.var (v♯1)))))
          (.here
            (.here (.lam (.lam (.letT (addT (.var (v♯1)) (.var (v♯0)))
              (.ap (.ap (.var (v♯4)) (.var (v♯1))) (.var (v♯0)))))))
            .nil)))
      (.cons (lsCases (.lam (.lam (.nat_mk 0)))) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind loopTy) PCtx _ loopTy famPe.members 0)

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm :=
  (.lam (.letT (.mutualRecursiveFamily_rec 0 (.var (v♯0)) fibTRCases)
     (.ap (.ap (.var (v♯0)) (.nat_mk 0)) (.nat_mk 1))) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at `n + 1` alongside the
answer at `n`.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib n, fib (n + 1))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- The branches of the pair recursion: `zero` answers `(0, 1)`, and `succ` takes the pair
    at the predecessor apart — binding `a` at index `0` and `b` at index `1` — and answers
    `(b, a + b)`. -/
def fibPairCases :=
  (.cons
      (.ctors
        (.skip (.here (.record_mk pairSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil))))
          (.here
            (.here (.record_casesOn (.var (v♯1))
              (.letT (addT (.var (v♯0)) (.var (v♯1)))
                (.record_mk pairSchema (.cons (.var (v♯2)) (.cons (.var (v♯0)) .nil))))))
            .nil)))
      (.cons (lsCases (.record_mk pairSchema
        (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil)))) .nil) :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind pairTy) PCtx _ pairTy famPe.members 0)

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm :=
  (.lam (.letT (.mutualRecursiveFamily_rec 0 (.var (v♯0)) fibPairCases)
     (.record_casesOn (.var (v♯0)) (.var (v♯0)))) :
    Term sigAdd [] _ (peTy ⇒ natT) .lam)

/-! ## 6. The other member: the continuant, and a constructor with two fields

Every constructor above has at most one field, so a deeper look had only one field it
could descend into.  Member `1` of the family is a list, whose recursive constructor
carries a payload first, and the **continuant** is the `fib`-shaped recursion over it:

```lean
def Ls.cont : Ls → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a (.cons b as) => a * cont (.cons b as) + cont as
```

Its `cons` branch reads the answer at the tail *of the tail*, so it descends once, and the
field it descends into is the **second** — which is what `FamilyMemberField.there` says.
This is a fold over the *same family*, selecting the other member, so the branches are
those of the same two members and the descent is into member `1`
(`FamilyMemberAt.there .here`). -/

/-- How the value of a fold over member `1` at motive `τ` reaches a branch. -/
abbrev lbind (τ : TyWf) : List (TyWfIn 2) → List TyWf := TyWf.famRecBinders famLs lsWf τ

/-- The context the fold below is written in. -/
abbrev LCtx : Ctx := [lsTy]

-- The `cons` branch binds the head, the tail, and the value of the fold at the tail — the
-- head is not an occurrence of a member, so no value of the fold follows it.
example (τ : TyWf) : lbind τ consFields = [natT, lsTy, τ] := rfl
example (τ : TyWf) : lbind τ succFields = [peTy, τ] := rfl

/-- **The branches of the member this fold does not descend into**: member `0`, the Peano
    naturals.  `zero` answers with the term given here, and `succ` answers with the value
    of the fold at its predecessor, which its branch binds at index `1`. -/
def peCases {τ : TyWf} {Γ : Ctx} {k : Nat} {u : Usage Γ} {h : Head}
    (zeroAnswer : Term sigAdd Γ u τ h) :=
  (.ctors (.skip (.here zeroAnswer) (.here (.here (.var (v♯1))) .nil)) :
    FamilyMemberFoldKCases sigAdd 0 famLs.members (lbind τ) Γ _ τ memPe k)

/-- The branches of the continuant: `nil` answers `1`; `cons` descends into its **second**
    field, and then answers `a` for a one-element list and `a * K (b :: bs) + K bs` for a
    longer one.  In that last branch the context binds `b`, `bs`, `K bs`, `a`,
    `as = b :: bs` and `K as`, in that order. -/
def contCases :=
  (.cons (peCases (.nat_mk 0))
      (.cons
        (.ctors
          (.skip (.here (.nat_mk 1))
            (.here
              (.deep (.there (.here rfl)) (.there .here)
                (.ctors
                  (.skip (.here (.var (v♯0)))
                    (.here (.here (.letT (mulT (.var (v♯3)) (.var (v♯5)))
                                    (addT (.var (v♯0)) (.var (v♯3)))))
                      .nil))))
              .nil)))
        .nil) :
    FamilyFoldKCases sigAdd 0 famLs.members (lbind natT) LCtx _ natT famLs.members 1)

/-- The continuant, as a term: the depth-one fold over member `1` of the family. -/
def contTerm :=
  (.lam (.mutualRecursiveFamily_rec 1 (.var (v♯0)) contCases) :
    Term sigAdd [] _ (lsTy ⇒ natT) .lam)

/-! ## 7. What the evaluator says about these terms

A recursive shape has no values in the model (`LeanScript.Ty.Den`), so a fold over one is a
term the evaluator does not run, and `LeanScript.Term.NoRecMk` says so: taking a value
apart is fine — there is nothing to take apart — while *building* one is not. -/

example : Term.NoRecMk fibTerm := by no_rec_mk
example : Term.NoRecMk hexaTerm := by no_rec_mk
example : Term.NoRecMk fibTRTerm := by no_rec_mk
example : Term.NoRecMk fibPairTerm := by no_rec_mk
example : Term.NoRecMk contTerm := by no_rec_mk

/-! ## 8. A depth is needed: what cannot be written without one

At depth `0` a branch is an answer and nothing else — `LeanScript.FamilyFoldKBranch.deep`
is a branch of a depth `k + 1` fold — so the `succ` branch of `fib`, which has to look one
constructor further down before it can answer, is not a branch of the plain fold. -/

/--
error: Type mismatch
  FamilyFoldKBranch.deep (FamilyMemberField.here ?m.25) FamilyMemberAt.here
    (FamilyMemberFoldKCases.ctors
      (FamilyTaggedUnionFoldKCases.skip (FamilyFoldKBranch.here (Term.nat_mk 1))
        (FamilyCtorsWithPayloadFoldKCases.here (FamilyFoldKBranch.here (Term.nat_mk 2))
          FamilyTaggedUnionFoldKCasesRest.nil)))
has type
  FamilyFoldKBranch ?m.87 ?m.88
    (LeanFamMemberSchema.ctors (LeanTaggedUnionSchema.skip (CtorsWithPayload.here ?m.69 [])) :: ?m.28) ?m.90 ?m.12
    (Usage.drop (?m.90 (?m.21 :: ?m.22))
      (Usage.drop (?m.90 []) 0 + (Usage.drop (?m.90 (NonEmptyList.toList ?m.69)) 0 + 0)))
    (?m.21 :: ?m.22) (TyWf.prim LeanPrimTy.nat) (?m.93 + 1)
but is expected to have type
  FamilyFoldKBranch sigAdd 0 famPe.members (pbind natT) PCtx ?m.95 succFields natT 0
-/
#guard_msgs (error) in
def succBranchTooShallow :=
  (.deep (.here rfl) .here
      (.ctors (.skip (.here (.nat_mk 1)) (.here (.here (.nat_mk 2)) .nil))) :
    FamilyFoldKBranch sigAdd 0 famPe.members (pbind natT) PCtx _ succFields natT 0)

-- And a depth-zero fold *is* the fold that was there before the depth was added: the
-- branches of the loop of §4 and of the pair recursion of §5, read as branches of the
-- plain fold and back, are the same branches (`LeanScript.FamilyRecFacts`, at every family
-- and every motive).
example : FamilyFoldCases.toFoldK (FamilyFoldKCases.ofFoldK fibTRCases) = fibTRCases :=
  FamilyFoldKCases.toFoldK_ofFoldK fibTRCases

example : FamilyFoldCases.toFoldK (FamilyFoldKCases.ofFoldK fibPairCases) = fibPairCases :=
  FamilyFoldKCases.toFoldK_ofFoldK fibPairCases

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: `n / 2` is not `n` with a fixed number of constructors taken off
it, so there is no depth at which the branch is *given* the answer at it.  A fold over a
family is given the answers on the path it descended — through whichever members that path
crosses — and a recursion that jumps needs a measure and a proof, which a `Term` does not
carry.  This is the same boundary `TermTests/NatRecDepthTest.lean` records for `Nat`.
-/

end TermTests.FamilyRecDepth
