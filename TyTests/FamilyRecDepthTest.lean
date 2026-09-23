module

public import LeanScript.Expr.Term
public import LeanScript.Eval
public import LeanScript.FamilyRecFacts
public import TyTests.FibWindowTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a mutual recursive family: `mutualRecursiveFamily_rec` at every depth

`TyTests/NatRecDepthTest.lean` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`; `TyTests/ArrayRecDepthTest.lean`,
`TyTests/RecUnionRecDepthTest.lean`, `TyTests/RecObjectRecDepthTest.lean` and
`TyTests/RecAliasRecDepthTest.lean` do the same for a fold over an array, over a recursive
tagged union, over a recursive record and over a recursive newtype.  This file is that
exercise for a fold over a **mutual recursive family**, which is
`LeanScript.Term.mutualRecursiveFamily_rec`.

The family is a `mutual` block of two declarations — the Peano naturals and a list of
naturals:

```lean
mutual
inductive Pe where
  | zero
  | succ (n : Pe)
inductive Ls where
  | nil
  | cons (a : Nat) (as : Ls)
end
```

so `fib` is the program the depth is for:

```lean
def Pe.fib : Pe → Nat
  | .zero            => 0
  | .succ .zero      => 1
  | .succ (.succ n)  => fib n + fib (.succ n)
```

Its `succ` branch does not answer: it **looks one constructor further down**, and only
then answers, using the value of the recursion at the value it descended past *and* at the
one it arrived at.  That is exactly the shape of a depth-one branch of the fold —
`LeanScript.FamilyFoldKBranch.deep`, which names the field descended into, says which
member of the family that field is an occurrence of, and dispatches on **that member**
again — and the nesting of the Lean `match` above is the nesting of the case tree below,
one for one.

| the program | the node it is | here |
| :-- | :-- | :-- |
| `Pe.fib` (reads two constructors down) | `mutualRecursiveFamily_rec 1` | `fibTerm` |
| `Pe.trib`, `Pe.tetra`, `Pe.penta`, `Pe.hexa` | `mutualRecursiveFamily_rec 2 … 5` | `tribTerm`, `tetraTerm`, `pentaTerm`, `hexaTerm` |
| `Pe.fibLoopTR` (tail-recursive, two accumulators) | `mutualRecursiveFamily_rec 0` **at a function type** | `fibTRTerm` |
| `Pe.fibPair` (pair recursion) | `mutualRecursiveFamily_rec 0` at a record type | `fibPairTerm` |
| `Ls.cont` (the continuant, over the **other member**) | `mutualRecursiveFamily_rec 1`, descending into the *second* field | `contTerm` |
| `Ev.fib` (over a family whose members mention **each other**) | `mutualRecursiveFamily_rec 1`, descending into the *other member* | `TyTests/FamilyRecDepthMembersTest.lean` |
| `Node.fib` (over a family of a record, a union and a newtype) | `mutualRecursiveFamily_rec 1`, both recursive members descending | `TyTests/FamilyRecDepthMembersTest.lean` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

A fold over a family always gives the branches of **every** member, whichever member the
value belongs to and wherever a deeper look lands, so each term below carries the branches
of both members of its family; §1 says what those branches bind.

**What is checked.**  `LeanScript.Ty.Den` gives a recursive shape no values — there is no
least fixpoint in the model yet — so, exactly as in `TyTests/RecTermTest.lean`, a term over
a family is checked **by its type** rather than by running it: each definition below states
the type of the term it builds, so the file fails to build if the branch a program needs
cannot be written at that depth, or is written in a context other than the documented one.
What the contexts are is pinned separately, by the `rfl` examples of §1, and the Lean
programs at the top of each section say what each term means.

Those Lean programs are themselves checked, in §0: their values at `10` by `#guard`, that
`Pe.fib` is the ordinary `fib` at *every* argument (`Pe.fib_ofNat`), and the three theorems
of the request — `Pe.fibPair_eq`, `Pe.fibPair_fst_eq_fib` and `Pe.fibTR_eq_fib`, that the
pair recursion and the tail-recursive loop both compute `fib`.

The depth-zero fold is the fold that was there before the depth was added: §8 checks that,
at `k = 0`, no branch can look down at all, and `LeanScript.FamilyRecFacts` proves that the
branches of a depth-zero fold are exactly the branches of the plain fold.

What a deeper look into **another member** looks like, and what the branches of a record
member and of a newtype member are, is the companion file
`TyTests/FamilyRecDepthMembersTest.lean`.

The terms are **written out**: `#leanscript_to_term` compiles a recursion on a `Nat` at any
depth, and a recursion on a list one constructor at a time, so a depth-`k` recursion over a
mutual family is not something it reads yet.
-/

namespace TyTests.FamilyRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of.
`Pe` and `Ls` are declared as one `mutual` block, which is the block the family of §1
describes. -/

mutual

/-- Member `0` of the family: the Peano naturals. -/
inductive Pe where
  /-- Zero. -/
  | zero
  /-- The successor of a Peano natural. -/
  | succ (n : Pe)

/-- Member `1` of the family: a list of naturals. -/
inductive Ls where
  /-- The empty list. -/
  | nil
  /-- One more element, at the front. -/
  | cons (a : Nat) (as : Ls)

end

namespace Pe

/-- `fib`, on Peano naturals: it reads the answer two constructors down. -/
def fib : Pe → Nat
  | .zero => 0
  | .succ .zero => 1
  | .succ (.succ n) => fib n + fib (.succ n)

/-- The tribonacci numbers: three constructors down. -/
def trib : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 1
  | .succ (.succ (.succ n)) => trib n + trib (.succ n) + trib (.succ (.succ n))

/-- The tetranacci numbers: four constructors down. -/
def tetra : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 1
  | .succ (.succ (.succ (.succ n))) =>
      tetra n + tetra (.succ n) + tetra (.succ (.succ n)) + tetra (.succ (.succ (.succ n)))

/-- The pentanacci numbers: five constructors down. -/
def penta : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 0
  | .succ (.succ (.succ (.succ .zero))) => 1
  | .succ (.succ (.succ (.succ (.succ n)))) =>
      penta n + penta (.succ n) + penta (.succ (.succ n)) + penta (.succ (.succ (.succ n)))
        + penta (.succ (.succ (.succ (.succ n))))

/-- The hexanacci numbers: six constructors down. -/
def hexa : Pe → Nat
  | .zero => 0
  | .succ .zero => 0
  | .succ (.succ .zero) => 0
  | .succ (.succ (.succ .zero)) => 0
  | .succ (.succ (.succ (.succ .zero))) => 0
  | .succ (.succ (.succ (.succ (.succ .zero)))) => 1
  | .succ (.succ (.succ (.succ (.succ (.succ n))))) =>
      hexa n + hexa (.succ n) + hexa (.succ (.succ n)) + hexa (.succ (.succ (.succ n)))
        + hexa (.succ (.succ (.succ (.succ n))))
        + hexa (.succ (.succ (.succ (.succ (.succ n)))))

/-- The tail-recursive loop, with two accumulators. -/
def fibLoopTR : Pe → Nat → Nat → Nat
  | .zero, a, _ => a
  | .succ n, a, b => fibLoopTR n b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (n : Pe) : Nat := fibLoopTR n 0 1

/-- The pair recursion: the answer at `n` together with the answer at `n + 1`. -/
def fibPair : Pe → Nat × Nat
  | .zero => (0, 1)
  | .succ n => let (a, b) := fibPair n; (b, a + b)

/-- A Peano natural from a `Nat`, for the checks below. -/
def ofNat : Nat → Pe
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

-- The reference programs are the familiar sequences.
#guard fib (ofNat 10) = 55
#guard fibTR (ofNat 10) = 55
#guard fibPair (ofNat 10) = (55, 89)
#guard trib (ofNat 10) = 81
#guard tetra (ofNat 10) = 56
#guard penta (ofNat 10) = 31
#guard hexa (ofNat 10) = 16

/-- The Peano `fib` is the `fib` of `TyTests.FibWindow`, at **every** argument. -/
theorem fib_ofNat : (n : Nat) → fib (ofNat n) = TyTests.FibWindow.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show fib (ofNat n) + fib (ofNat (n + 1)) =
        TyTests.FibWindow.fib n + TyTests.FibWindow.fib (n + 1)
      rw [fib_ofNat n, fib_ofNat (n + 1)]

/-- Addition of Peano naturals, by recursion on the left argument. -/
def add : Pe → Pe → Pe
  | .zero, m => m
  | .succ n, m => .succ (add n m)

@[simp] theorem add_succ : (n m : Pe) → add n (.succ m) = .succ (add n m)
  | .zero, _ => rfl
  | .succ n, m => congrArg Pe.succ (add_succ n m)

@[simp] theorem add_zero : (n : Pe) → add n .zero = n
  | .zero => rfl
  | .succ n => congrArg Pe.succ (add_zero n)

/-- The pair recursion carries the answer at `n` and the answer at `n + 1`. -/
theorem fibPair_eq : (n : Pe) → fibPair n = (fib n, fib (.succ n))
  | .zero => rfl
  | .succ n => by
      show (let (a, b) := fibPair n; ((b, a + b) : Nat × Nat)) = _
      rw [fibPair_eq n]
      rfl

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (n : Pe) : (fibPair n).1 = fib n := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `m` and `m + 1`, answers at `n + m`. -/
theorem fibLoopTR_eq : (n m : Pe) → fibLoopTR n (fib m) (fib (.succ m)) = fib (add n m)
  | .zero, _ => rfl
  | .succ n, m => by
      show fibLoopTR n (fib (.succ m)) (fib m + fib (.succ m)) = fib (.succ (add n m))
      rw [show fib m + fib (.succ m) = fib (.succ (.succ m)) from rfl,
        fibLoopTR_eq n (.succ m), add_succ]

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (n : Pe) : fibTR n = fib n := by
  show fibLoopTR n (fib .zero) (fib (.succ .zero)) = fib n
  rw [fibLoopTR_eq n .zero]
  show fib (add n .zero) = fib n
  rw [add_zero]

end Pe

namespace Ls

/-- The **continuant** over the other member of the family:
    `K [] = 1`, `K [a] = a`, `K (a :: b :: as) = a * K (b :: as) + K as`. -/
def cont : Ls → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a (.cons b as) => a * cont (.cons b as) + cont as

/-- A list of `n` ones. -/
def ones : Nat → Ls
  | 0 => .nil
  | n + 1 => .cons 1 (ones n)

#guard cont (.cons 3 (.cons 1 (.cons 4 .nil))) = 3 * (1 * 4 + 1) + 4

/-- The continuant of a list of `n` ones is `fib (n + 1)`: the continuant *is* the
    `fib`-shaped recursion, read over the second member of the family. -/
theorem cont_ones : (n : Nat) → cont (ones n) = TyTests.FibWindow.fib (n + 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show 1 * cont (ones (n + 1)) + cont (ones n) =
        TyTests.FibWindow.fib (n + 1) + TyTests.FibWindow.fib (n + 2)
      rw [cont_ones n, cont_ones (n + 1)]
      show 1 * TyTests.FibWindow.fib (n + 2) + TyTests.FibWindow.fib (n + 1) = _
      omega

end Ls

/-! ## 1. The family, and what its branches bind

The family has the two members of the `mutual` block above: member `0` has the
constructors `zero`, which carries nothing, and `succ`, whose one field is an occurrence of
member `0`; member `1` has `nil`, which carries nothing, and `cons`, which carries a
natural and an occurrence of member `1`.  A family is written in the scope of all of its
members, so a field is `Ty.familyMember i` rather than `Ty.self`. -/

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

/-- Member `0` of the family: the Peano naturals, `zero | succ (n : member 0)`. -/
def memPe : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 0).toTyWfIn, []⟩ []))

/-- Member `1` of the family: a list of naturals,
    `nil | cons (a : nat) (as : member 1)`. -/
def memLs : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.prim .nat).toTyWfIn, [(Ty.familyMember 1).toTyWfIn]⟩ []))

/-- The family, selecting member `0`. -/
def famPe : LeanMutualRecFamily (TyWfIn 2) := .selectedThenMore [] memPe memLs []

/-- The family, selecting member `1`. -/
def famLs : LeanMutualRecFamily (TyWfIn 2) := .selectedLast memPe [] memLs

-- Both are the same block of declarations: they differ only in which member is selected.
example : famPe.members = [memPe, memLs] := rfl
example : famLs.members = [memPe, memLs] := rfl
example : famPe.memberIdx = 0 := rfl
example : famLs.memberIdx = 1 := rfl

/-- That the family describes types: every member is mentioned, no occurrence is in the
    domain of a function, and every member has values. -/
theorem peWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famPe) := by ty_wf

/-- The same, for the family that selects member `1`. -/
theorem lsWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famLs) := by ty_wf

/-- The type of member `0`: a Peano natural. -/
def peTy : TyWf := .mutualRecursiveFamily famPe peWf

/-- The type of member `1`: a list of naturals. -/
def lsTy : TyWf := .mutualRecursiveFamily famLs lsWf

/-- The fields of `succ`, as the branch families see them. -/
abbrev succFields : List (TyWfIn 2) := [(Ty.familyMember 0).toTyWfIn]

/-- The fields of `cons`. -/
abbrev consFields : List (TyWfIn 2) :=
  [(Ty.prim .nat).toTyWfIn, (Ty.familyMember 1).toTyWfIn]

/-- How the value of a fold over member `0` at motive `τ` reaches a branch. -/
abbrev pbind (τ : TyWf) : List (TyWfIn 2) → List TyWf := TyWf.famRecBinders famPe peWf τ

-- What a branch binds: a field-less constructor binds nothing; `succ` binds its field — a
-- Peano natural — and then the value of the fold at that field; `cons` binds its natural,
-- its tail and the value of the fold at the tail, since the natural is not an occurrence
-- of a member.
example (τ : TyWf) : pbind τ [] = [] := rfl
example (τ : TyWf) : pbind τ succFields = [peTy, τ] := rfl
example (τ : TyWf) : pbind τ consFields = [natT, lsTy, τ] := rfl

-- So the branch of `succ` of a depth-zero fold over `Γ` is written in `peTy :: τ :: Γ`,
-- and a branch reached by descending once more is written in that context again with the
-- subvalue and the value of the fold at it in front of it.
example (τ : TyWf) (Γ : Ctx) : pbind τ succFields ++ Γ = peTy :: τ :: Γ := rfl
example (τ : TyWf) (Γ : Ctx) :
    pbind τ succFields ++ (pbind τ succFields ++ Γ) = peTy :: τ :: peTy :: τ :: Γ := rfl

/-- The context every fold over member `0` below is written in: the Peano natural it folds
    over, bound by the `fun` in front of it. -/
abbrev PCtx : Ctx := [peTy]

/-- Zero, as a term. -/
def zeroTerm : Term sigAdd [] peTy :=
  .mutualRecursiveFamily_mk famPe peWf (value := .ctors _ 0 (fields := .nil))

/-- The successor of the variable in scope. -/
def succTerm : Term sigAdd [] (peTy ⇒ peTy) :=
  .lam (.mutualRecursiveFamily_mk famPe peWf
    (value := .ctors _ 1 (fields := .cons (.var (v♯0)) .nil)))

/-- **The branches of the member the fold does not descend into.**  Every fold over this
    family has to answer for member `1` as well, whatever it is folding: `nil` answers with
    the term given here, and `cons` answers with the value of the fold at its tail, which
    its branch binds at index `2`.  It is written once, for every motive and every depth,
    and used by every fold below. -/
def lsCases {τ : TyWf} {Γ : Ctx} {k : Nat} (nilAnswer : Term sigAdd Γ τ) :
    FamilyMemberFoldKCases sigAdd 0 famPe.members (pbind τ) Γ τ memLs k :=
  .ctors (.skip (.here nilAnswer) (.here (.here (.var (v♯2))) .nil))

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
def fibCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx natT famPe.members 1 :=
  .cons
    (.ctors
      (.skip (.here (.nat_mk 0))
        (.here
          (.deep (.here rfl) .here
            (.ctors
              (.skip (.here (.nat_mk 1))
                (.here (.here (addT (.var (v♯1)) (.var (v♯3)))) .nil))))
          .nil)))
    (.cons (lsCases (.nat_mk 0)) .nil)

/-- **`fib` over a mutual family**: the depth-one fold. -/
def fibTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 1 (.var (v♯0)) fibCases)

/-! ## 3. Tribonacci … hexanacci: one more level of descent each

The `n + k` recursions of the request, transcribed: at depth `k` the branch descends `k`
times, and the answers at the values it descended past are the odd indices `1, 3, …,
2k + 1` — nearest last, since each descent pushes the subvalue and its answer in front of
the context.  Every descent here is into member `0` again (`FamilyMemberAt.here`), since
that is the member whose constructor the fold is walking down; `TyTests/FamilyRecDepthMembersTest.lean` descends into the
*other* member. -/

/-- The tribonacci numbers: a depth-two fold. -/
def tribCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx natT famPe.members 2 :=
  .cons
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
                          (.here (addT (addT (.var (v♯1)) (.var (v♯3))) (.var (v♯5))))
                          .nil))))
                  .nil))))
          .nil)))
    (.cons (lsCases (.nat_mk 0)) .nil)

/-- `trib`, as a term. -/
def tribTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 2 (.var (v♯0)) tribCases)

/-- The tetranacci numbers: a depth-three fold. -/
def tetraCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx natT famPe.members 3 :=
  .cons
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
                                  (.here (addT (addT (addT (.var (v♯1)) (.var (v♯3)))
                                    (.var (v♯5))) (.var (v♯7))))
                                  .nil))))
                          .nil))))
                  .nil))))
          .nil)))
    (.cons (lsCases (.nat_mk 0)) .nil)

/-- `tetra`, as a term. -/
def tetraTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 3 (.var (v♯0)) tetraCases)

/-- The pentanacci numbers: a depth-four fold. -/
def pentaCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx natT famPe.members 4 :=
  .cons
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
                                          (.here (addT (addT (addT (addT (.var (v♯1))
                                            (.var (v♯3))) (.var (v♯5))) (.var (v♯7)))
                                            (.var (v♯9))))
                                          .nil))))
                                  .nil))))
                          .nil))))
                  .nil))))
          .nil)))
    (.cons (lsCases (.nat_mk 0)) .nil)

/-- `penta`, as a term. -/
def pentaTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 4 (.var (v♯0)) pentaCases)

/-- The hexanacci numbers: a depth-five fold. -/
def hexaCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind natT) PCtx natT famPe.members 5 :=
  .cons
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
                                                  (.here (addT (addT (addT (addT (addT
                                                    (.var (v♯1)) (.var (v♯3)))
                                                    (.var (v♯5))) (.var (v♯7)))
                                                    (.var (v♯9))) (.var (v♯11))))
                                                  .nil))))
                                          .nil))))
                                  .nil))))
                          .nil))))
                  .nil))))
          .nil)))
    (.cons (lsCases (.nat_mk 0)) .nil)

/-- `hexa`, as a term. -/
def hexaTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 5 (.var (v♯0)) hexaCases)

/-! ## 4. The tail-recursive loop: a depth-**zero** fold at a function type

`fibLoopTR` never reads the answer at anything but the immediate predecessor, so no depth
is needed: what makes it a fold is that its motive is a function, `nat ⇒ nat ⇒ nat`, and
the branch returns the loop with its accumulators swapped and added. -/

/-- The motive of the loop: two accumulators still to come. -/
abbrev loopTy : TyWf := natT ⇒ natT ⇒ natT

/-- The branches of the loop: `zero` answers `fun a b => a`, and `succ` answers
    `fun a b => ih b (a + b)`, where `ih` is the loop at the predecessor. -/
def fibTRCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind loopTy) PCtx loopTy famPe.members 0 :=
  .cons
    (.ctors
      (.skip (.here (.lam (.lam (.var (v♯1)))))
        (.here
          (.here (.lam (.lam (.ap (.ap (.var (v♯3)) (.var (v♯0)))
            (addT (.var (v♯1)) (.var (v♯0)))))))
          .nil)))
    (.cons (lsCases (.lam (.lam (.nat_mk 0)))) .nil)

/-- `fibTR`: the loop, started at `0` and `1`. -/
def fibTRTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.ap (.ap (.mutualRecursiveFamily_rec 0 (.var (v♯0)) fibTRCases) (.nat_mk 0))
    (.nat_mk 1))

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
def fibPairCases :
    FamilyFoldKCases sigAdd 0 famPe.members (pbind pairTy) PCtx pairTy famPe.members 0 :=
  .cons
    (.ctors
      (.skip (.here (.record_mk pairSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil))))
        (.here
          (.here (.record_casesOn (.var (v♯1))
            (.record_mk pairSchema
              (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil)))))
          .nil)))
    (.cons (lsCases (.record_mk pairSchema
      (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil)))) .nil)

/-- `fib`, as the first component of the pair recursion. -/
def fibPairTerm : Term sigAdd [] (peTy ⇒ natT) :=
  .lam (.record_casesOn (.mutualRecursiveFamily_rec 0 (.var (v♯0)) fibPairCases)
    (.var (v♯0)))

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
def peCases {τ : TyWf} {Γ : Ctx} {k : Nat} (zeroAnswer : Term sigAdd Γ τ) :
    FamilyMemberFoldKCases sigAdd 0 famLs.members (lbind τ) Γ τ memPe k :=
  .ctors (.skip (.here zeroAnswer) (.here (.here (.var (v♯1))) .nil))

/-- The branches of the continuant: `nil` answers `1`; `cons` descends into its **second**
    field, and then answers `a` for a one-element list and `a * K (b :: bs) + K bs` for a
    longer one.  In that last branch the context binds `b`, `bs`, `K bs`, `a`,
    `as = b :: bs` and `K as`, in that order. -/
def contCases :
    FamilyFoldKCases sigAdd 0 famLs.members (lbind natT) LCtx natT famLs.members 1 :=
  .cons (peCases (.nat_mk 0))
    (.cons
      (.ctors
        (.skip (.here (.nat_mk 1))
          (.here
            (.deep (.there (.here rfl)) (.there .here)
              (.ctors
                (.skip (.here (.var (v♯0)))
                  (.here (.here (addT (mulT (.var (v♯3)) (.var (v♯5))) (.var (v♯2))))
                    .nil))))
            .nil)))
      .nil)

/-- The continuant, as a term: the depth-one fold over member `1` of the family. -/
def contTerm : Term sigAdd [] (lsTy ⇒ natT) :=
  .lam (.mutualRecursiveFamily_rec 1 (.var (v♯0)) contCases)

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
  FamilyFoldKBranch.deep (FamilyMemberField.here ?m.22) FamilyMemberAt.here
    (FamilyMemberFoldKCases.ctors
      (FamilyTaggedUnionFoldKCases.skip (FamilyFoldKBranch.here (Term.nat_mk 1))
        (FamilyCtorsWithPayloadFoldKCases.here (FamilyFoldKBranch.here (Term.nat_mk 2))
          FamilyTaggedUnionFoldKCasesRest.nil)))
has type
  FamilyFoldKBranch ?m.75 ?m.76
    (LeanFamMemberSchema.ctors (LeanTaggedUnionSchema.skip (CtorsWithPayload.here ?m.61 [])) :: ?m.25) ?m.78 ?m.10
    (?m.18 :: ?m.19) (TyWf.prim LeanPrimTy.nat) (?m.81 + 1)
but is expected to have type
  FamilyFoldKBranch sigAdd 0 famPe.members (pbind natT) PCtx succFields natT 0
-/
#guard_msgs (error) in
def succBranchTooShallow :
    FamilyFoldKBranch sigAdd 0 famPe.members (pbind natT) PCtx succFields natT 0 :=
  .deep (.here rfl) .here
    (.ctors (.skip (.here (.nat_mk 1)) (.here (.here (.nat_mk 2)) .nil)))

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
carry.  This is the same boundary `TyTests/NatRecDepthTest.lean` records for `Nat`.
-/

end TyTests.FamilyRecDepth
