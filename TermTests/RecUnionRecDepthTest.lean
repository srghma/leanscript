module

public import TermTests.RecUnionRecDepthTest.Programs
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: the terms

The Lean reference programs, the type the fold runs over and what its branches bind
are in `TermTests.RecUnionRecDepthTest.Programs`; this file writes the programs as terms of the
language and checks them against the references.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 2. `fib`, written out at depth one

The `zero` branch answers `0`.  The `succ` branch does not answer: it descends into its
field — the only occurrence of the union among its fields, which is
`SelfField.here rfl` — and dispatches on it.  In that dispatch the value is `succ n`
with `n` in hand, so:

* if `n` is `zero` the value is `succ zero`, and the answer is `1`;
* if `n` is `succ m`, the context binds `m` (index `0`), the answer at `m` (index `1`),
  `n` (index `2`) and the answer at `n` (index `3`), and the answer is `fib m + fib n` —
  which is the `fib n + fib (n + 1)` of the program. -/

/-- The branches of `fib`. -/
def fibCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind natT) PCtx peanoSchema natT 1 :=
  .skip (.here (.nat_mk 0))
    (.here
      (.deep (.here rfl)
        (.skip (.here (.nat_mk 1))
          (.here (.here (addT (.var (v♯1)) (.var (v♯3)))) .nil)))
      .nil)

/-- **`fib` over a recursive tagged union**: the depth-one fold. -/
def fibTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 1 (.var (v♯0)) fibCases)

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

The `n + k` recursions of the request, transcribed: at depth `k` the branch descends `k`
times, and the answers at the values it descended past are the odd indices `1, 3, …,
2k + 1` — nearest last, since each descent pushes the subvalue and its answer in front of
the context. -/

/-- The tribonacci numbers: a depth-two fold. -/
def tribCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind natT) PCtx peanoSchema natT 2 :=
  .skip (.here (.nat_mk 0))
    (.here
      (.deep (.here rfl)
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl)
              (.skip (.here (.nat_mk 1))
                (.here
                  (.here (addT (addT (.var (v♯1)) (.var (v♯3))) (.var (v♯5))))
                  .nil)))
            .nil)))
      .nil)

/-- `trib`, as a term. -/
def tribTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 2 (.var (v♯0)) tribCases)

/-- The tetranacci numbers: a depth-three fold. -/
def tetraCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind natT) PCtx peanoSchema natT 3 :=
  .skip (.here (.nat_mk 0))
    (.here
      (.deep (.here rfl)
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl)
              (.skip (.here (.nat_mk 0))
                (.here
                  (.deep (.here rfl)
                    (.skip (.here (.nat_mk 1))
                      (.here
                        (.here (addT (addT (addT (.var (v♯1)) (.var (v♯3)))
                          (.var (v♯5))) (.var (v♯7))))
                        .nil)))
                  .nil)))
            .nil)))
      .nil)

/-- `tetra`, as a term. -/
def tetraTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 3 (.var (v♯0)) tetraCases)

/-- The pentanacci numbers: a depth-four fold. -/
def pentaCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind natT) PCtx peanoSchema natT 4 :=
  .skip (.here (.nat_mk 0))
    (.here
      (.deep (.here rfl)
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl)
              (.skip (.here (.nat_mk 0))
                (.here
                  (.deep (.here rfl)
                    (.skip (.here (.nat_mk 0))
                      (.here
                        (.deep (.here rfl)
                          (.skip (.here (.nat_mk 1))
                            (.here
                              (.here (addT (addT (addT (addT (.var (v♯1)) (.var (v♯3)))
                                (.var (v♯5))) (.var (v♯7))) (.var (v♯9))))
                              .nil)))
                        .nil)))
                  .nil)))
            .nil)))
      .nil)

/-- `penta`, as a term. -/
def pentaTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 4 (.var (v♯0)) pentaCases)

/-- The hexanacci numbers: a depth-five fold. -/
def hexaCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind natT) PCtx peanoSchema natT 5 :=
  .skip (.here (.nat_mk 0))
    (.here
      (.deep (.here rfl)
        (.skip (.here (.nat_mk 0))
          (.here
            (.deep (.here rfl)
              (.skip (.here (.nat_mk 0))
                (.here
                  (.deep (.here rfl)
                    (.skip (.here (.nat_mk 0))
                      (.here
                        (.deep (.here rfl)
                          (.skip (.here (.nat_mk 0))
                            (.here
                              (.deep (.here rfl)
                                (.skip (.here (.nat_mk 1))
                                  (.here
                                    (.here (addT (addT (addT (addT (addT
                                      (.var (v♯1)) (.var (v♯3))) (.var (v♯5)))
                                      (.var (v♯7))) (.var (v♯9))) (.var (v♯11))))
                                    .nil)))
                              .nil)))
                        .nil)))
                  .nil)))
            .nil)))
      .nil)

/-- `hexa`, as a term. -/
def hexaTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 5 (.var (v♯0)) hexaCases)

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the immediate predecessor, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- The branches of the loop: `zero` answers `fun a b => a`, and `succ` answers
    `fun a b => ih b (a + b)`, where `ih` is the loop at the predecessor. -/
def fibTRCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind loopTy) PCtx peanoSchema loopTy 0 :=
  .skip (.here (.lam (.lam (.var (v♯1)))))
    (.here
      (.here (.lam (.lam (.ap (.ap (.var (v♯3)) (.var (v♯0)))
        (addT (.var (v♯1)) (.var (v♯0)))))))
      .nil)

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.ap (.ap (.recTaggedUnion_rec 0 (.var (v♯0)) fibTRCases) (.nat_mk 0)) (.nat_mk 1))

/-! ## 5. The pair recursion: a depth-zero fold at a record type

The other way to write `fib` without a depth: carry the answer at `n + 1` alongside the
answer at `n`.  The motive is a record of two naturals. -/

/-- A record of two naturals: the pair `(fib n, fib (n + 1))`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- The type of that pair. -/
abbrev pairTy : TyWf := .record pairSchema

/-- The branches of the pair recursion: `zero` answers `(0, 1)`, and `succ` takes the
    pair at the predecessor apart — binding `a` at index `0` and `b` at index `1` — and
    answers `(b, a + b)`. -/
def fibPairCases :
    TaggedUnionFoldKCases sigAdd peanoSchema (pbind pairTy) PCtx peanoSchema pairTy 0 :=
  .skip (.here (.record_mk pairSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil))))
    (.here
      (.here (.record_casesOn (.var (v♯1))
        (.record_mk pairSchema
          (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil)))))
      .nil)

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (peanoTy ⇒ natT) :=
  .lam (.record_casesOn (.recTaggedUnion_rec 0 (.var (v♯0)) fibPairCases) (.var (v♯0)))

/-! ## 6. A constructor with more than one field: the continuant over a list

Every constructor above has at most one field, so a deeper look had only one field it
could descend into.  The **continuant** is the same `fib`-shaped recursion over a union
whose recursive constructor carries a payload first:

```lean
def cont : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * cont (b :: as) + cont as
```

Its `cons` branch reads the answer at the tail *of the tail*, so it descends once, and
the field it descends into is the **second** — which is what `SelfField.there` says. -/

/-- The schema of a list of naturals: `nil` carries nothing, `cons` carries a natural and
    the list itself. -/
def natListSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.prim .nat).toTyWfIn, [Ty.self.toTyWfIn]⟩ [])

/-- The type of a list of naturals. -/
def natListTy : TyWf := .recTaggedUnion natListSchema

/-- The fields of `cons`. -/
abbrev consFields : List (TyWfIn 1) := [(Ty.prim .nat).toTyWfIn, Ty.self.toTyWfIn]

/-- How the value of a fold over the list reaches a branch. -/
abbrev lbind (τ : TyWf) : List (TyWfIn 1) → List TyWf := TyWf.recBinders natListTy τ

/-- The context the fold below is written in. -/
abbrev LCtx : Ctx := [natListTy]

-- The `cons` branch binds the head, the tail, and the value of the fold at the tail —
-- the head is not an occurrence of the union, so no value of the fold follows it.
example (τ : TyWf) : lbind τ consFields = [natT, natListTy, τ] := by kernel_rfl

/-- The branches of the continuant: `nil` answers `1`; `cons` descends into its
    **second** field, and then answers `a` for a one-element list and
    `a * K (b :: bs) + K bs` for a longer one.  In that last branch the context binds
    `b`, `bs`, `K bs`, `a`, `as = b :: bs` and `K as`, in that order. -/
def contCases :
    TaggedUnionFoldKCases sigAdd natListSchema (lbind natT) LCtx natListSchema natT 1 :=
  .skip (.here (.nat_mk 1))
    (.here
      (.deep (.there (.here rfl))
        (.skip (.here (.var (v♯0)))
          (.here (.here (addT (mulT (.var (v♯3)) (.var (v♯5))) (.var (v♯2)))) .nil)))
      .nil)

/-- The continuant, as a term: the depth-one fold of a list union. -/
def contTerm : Term sigAdd [] (natListTy ⇒ natT) :=
  .lam (.recTaggedUnion_rec 1 (.var (v♯0)) contCases)

/-! ## 7. Running the terms

A recursive tagged union has values in the model (`LeanScript.Ty.Den` gives it the W-tree
of its constructors), so these terms run, and the kernel checks them against their Lean
references.  The depth-`k` folds are evaluated with every answer remembered
(`LeanScript.WType.memo`), so a deeper look reads answers that are already there. -/


/-- The values of `add` and `mul`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigAdd` (scoped: the checks in
    `TermTests/RecUnionRecDepthTest/Run*.lean` use it too). -/
scoped macro:max "runP" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- The Peano natural `n`, built by the terms `zeroTerm` and `succTerm`. -/
def peanoVal : Nat → TyWf.Den peanoTy
  | 0 => runP zeroTerm
  | n + 1 => runP succTerm (peanoVal n)

/-- The list of naturals `l`, built by the introduction form. -/
def natListVal : List Nat → TyWf.Den natListTy
  | [] => runP (.recTaggedUnion_mk natListSchema (t := 0) (fields := .nil) :
      Term sigAdd [] natListTy)
  | a :: as => runP (.lam (.recTaggedUnion_mk natListSchema (t := 1)
      (fields := .cons (.nat_mk a) (.cons (.var (v♯0)) .nil))) :
      Term sigAdd [] (natListTy ⇒ natListTy)) (natListVal as)

/-- The continuant, in Lean: the reference `contTerm` is checked against. -/
def contRef : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * contRef (b :: as) + contRef as

example : runP fibTerm (peanoVal 10) = 55 := by decide +kernel
-- The checks of each term against its reference at the first ten arguments are in
-- `TermTests/RecUnionRecDepthTest/RunFibToPenta.lean` and
-- `TermTests/RecUnionRecDepthTest/RunHexaLoopPair.lean`: each takes a few seconds of
-- kernel time, and in two files of their own they are checked in parallel.
example : runP contTerm (natListVal [3, 1, 4, 1, 5]) = contRef [3, 1, 4, 1, 5] := by decide +kernel
example : runP contTerm (natListVal []) = contRef [] := by decide +kernel
example : runP contTerm (natListVal [7]) = contRef [7] := by decide +kernel

/-! ## 8. A depth is needed: what cannot be written without one

At depth `0` a branch is an answer and nothing else — `LeanScript.FoldKBranch.deep` is a
branch of a depth `k + 1` fold — so the `succ` branch of `fib`, which has to look one
constructor further down before it can answer, is not a branch of the plain fold. -/

/--
error: Type mismatch
  FoldKBranch.deep (SelfField.here ?m.14)
    (TaggedUnionFoldKCases.skip (FoldKBranch.here (Term.nat_mk 1))
      (CtorsWithPayloadFoldKCases.here (FoldKBranch.here (Term.nat_mk 2)) TaggedUnionFoldKCasesRest.nil))
has type
  FoldKBranch ?m.52 (LeanTaggedUnionSchema.skip (CtorsWithPayload.here ?m.39 [])) ?m.54 ?m.6 (?m.10 :: ?m.11)
    (TyWf.prim LeanPrimTy.nat) (?m.57 + 1)
but is expected to have type
  FoldKBranch sigAdd peanoSchema (pbind natT) PCtx succFields natT 0
-/
#guard_msgs (error) in
def succBranchTooShallow :
    FoldKBranch sigAdd peanoSchema (pbind natT) PCtx succFields natT 0 :=
  .deep (.here rfl)
    (.skip (.here (.nat_mk 1)) (.here (.here (.nat_mk 2)) .nil))

-- And a depth-zero fold *is* the fold that was there before the depth was added: the
-- branches of the loop of §4, read as branches of the plain fold and back, are the same
-- branches (`LeanScript.RecUnionRecFacts`, at every union and every motive).
example :
    TaggedUnionFoldCases.toFoldK (TaggedUnionFoldKCases.ofFoldK fibTRCases) = fibTRCases :=
  TaggedUnionFoldKCases.toFoldK_ofFoldK fibTRCases

example :
    TaggedUnionFoldCases.toFoldK (TaggedUnionFoldKCases.ofFoldK fibPairCases) =
      fibPairCases :=
  TaggedUnionFoldKCases.toFoldK_ofFoldK fibPairCases

/-! ### The recursion that no depth reaches

```lean
def fibFast (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else
    let (a, b) := fibFast (n / 2)
    …
```

Halving is not descending: `n / 2` is not `n` with a fixed number of constructors taken
off it, so there is no depth at which the branch is *given* the answer at it.  The same
is true of the union — a fold is given the answers on the path it descended, and a
recursion that jumps needs a measure and a proof, which a `Term` does not carry.  This is
the same boundary `TermTests/NatRecDepthTest/` records for `Nat`.
-/

end TermTests.RecUnionRecDepth
