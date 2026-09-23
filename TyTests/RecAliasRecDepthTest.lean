module

public import LeanScript.Expr.Term
public import LeanScript.Eval
public import LeanScript.RecAliasRecFacts
public import TyTests.FibWindowTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over a recursive newtype: `recAlias_rec` at every depth

`TyTests/NatRecDepthTest.lean` writes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, and the tribonacci … hexanacci
numbers — as terms that fold over a `Nat`; `TyTests/ArrayRecDepthTest.lean` does the same
for a fold over an array, `TyTests/RecUnionRecDepthTest.lean` for a fold over a recursive
tagged union and `TyTests/RecObjectRecDepthTest.lean` for a fold over a recursive record.
This file is that exercise for a fold over a **recursive newtype**, which is
`LeanScript.Term.recAlias_rec`.

## Why a newtype needed a window too

The body of a recursive newtype can never be *literally* an occurrence of it: `μX. X` is
the equation `T = T`, which no value satisfies (`LeanScript.Ty.not_wf_recAlias_self`).  So
`LeanScript.TyWf.recBinders`, which puts the value of the fold after a field that *is* an
occurrence, put nothing anywhere: the fold of a newtype handed its branch no answer at all
(`LeanScript.TyWf.recBinders_recAlias`, and the `rfl` example in §1).

What the fold hands the branch now is one **window** binder: the newtype's body with every
occurrence of the newtype replaced by the answer there (`LeanScript.TyWf.recAliasMap`),
and at depth `k` by the **answer tree** of depth `k` at that subvalue — the answer at it
beside, in the shape of the body, the depth-`k - 1` trees of its own subvalues
(`LeanScript.TyWf.recAliasAnswerTree`).  So a depth-`k` branch reads the answers at
everything `k + 1` levels down, along the path it descends, exactly as a depth-`k` branch
of `Term.recObject_rec` does.

## The newtype

```lean
inductive Chain where
  | nil
  | cons (label : Nat) (rest : Chain)
```

a list of labels, written as the newtype `Chain = Option (Nat × Chain)`: one binder whose
body is a *union*, which is the shape a newtype has when it stands for a list.  Its `fib`
is the program the depth is for:

```lean
def Chain.fib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 1
  | .cons _ t@(.cons _ r) => fib t + fib r
```

| the program | the node | the term |
| --- | --- | --- |
| `Chain.fib` (reads two links down) | `recAlias_rec 1` | `fibTerm` |
| `Chain.trib`, `Chain.tetra`, `Chain.penta`, `Chain.hexa` | `recAlias_rec 2 … 5` | `tribTerm`, … |
| `Chain.fibLoopTR` (tail-recursive, two accumulators) | `recAlias_rec 0` **at a function type** | `fibTRTerm` |
| `Chain.fibPair` (pair recursion) | `recAlias_rec 0` at a record type | `fibPairTerm` |
| `Chain.cont` (the continuant, which reads the **label** too) | `recAlias_rec 1` | `contTerm` |
| `fibFast` (halves its argument) | no depth reaches it | the prose at the end |

**What is checked.**  `LeanScript.Ty.Den` gives a recursive shape no values — there is no
least fixpoint in the model yet — so, exactly as in `TyTests/RecTermTest.lean` and
`TyTests/RecObjectRecDepthTest.lean`, a term over a recursive newtype is checked **by its
type** rather than by running it: each definition below states the type of the term it
builds, so the file fails to build if the branch a program needs cannot be written at that
depth, or is written in a context other than the documented one.  What the contexts are is
pinned separately, by the `rfl` examples of §1.

The Lean programs the terms transcribe are checked too, in §0: their values at a chain of
ten links by `#guard`, that `Chain.fib` is the ordinary `fib` of the chain's length, and
the request's own theorems — that the pair recursion carries `(fib n, fib (n + 1))`, that
its first component is `fib`, and that the tail-recursive loop computes `fib`.
-/

namespace TyTests.RecAliasRecDepth

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## 0. The programs, in Lean

The reference definitions: what each term of the language below is a transcription of. -/

/-- A chain of labels: the recursive newtype this file folds over. -/
inductive Chain where
  /-- The chain ends. -/
  | nil
  /-- A label, and the rest of the chain. -/
  | cons (label : Nat) (rest : Chain)

namespace Chain

/-- How many links the chain has. -/
def len : Chain → Nat
  | .nil => 0
  | .cons _ r => len r + 1

/-- A chain of `n` links, all labelled `0`. -/
def ofNat : Nat → Chain
  | 0 => .nil
  | n + 1 => .cons 0 (ofNat n)

@[simp] theorem len_ofNat : (n : Nat) → len (ofNat n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (len_ofNat n)

/-- `fib`, on a chain: it reads the answer two links down. -/
def fib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 1
  | .cons _ t@(.cons _ r) => fib t + fib r

/-- The tribonacci numbers: three links down. -/
def trib : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 1
  | .cons _ t@(.cons _ u@(.cons _ r)) => trib t + trib u + trib r

/-- The tetranacci numbers: four links down. -/
def tetra : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 1
  | .cons _ t@(.cons _ u@(.cons _ v@(.cons _ r))) => tetra t + tetra u + tetra v + tetra r

/-- The pentanacci numbers: five links down. -/
def penta : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => 1
  | .cons _ t@(.cons _ u@(.cons _ v@(.cons _ w@(.cons _ r)))) =>
      penta t + penta u + penta v + penta w + penta r

/-- The hexanacci numbers: six links down. -/
def hexa : Chain → Nat
  | .nil => 0
  | .cons _ .nil => 0
  | .cons _ (.cons _ .nil) => 0
  | .cons _ (.cons _ (.cons _ .nil)) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => 0
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil)))) => 1
  | .cons _ t@(.cons _ u@(.cons _ v@(.cons _ w@(.cons _ x@(.cons _ r))))) =>
      hexa t + hexa u + hexa v + hexa w + hexa x + hexa r

/-- The tail-recursive loop, with two accumulators. -/
def fibLoopTR : Chain → Nat → Nat → Nat
  | .nil, a, _ => a
  | .cons _ r, a, b => fibLoopTR r b (a + b)

/-- `fib`, as the loop above started at `0, 1`. -/
def fibTR (t : Chain) : Nat := fibLoopTR t 0 1

/-- The pair recursion: the answer at the chain and the answer at one link more. -/
def fibPair : Chain → Nat × Nat
  | .nil => (0, 1)
  | .cons _ r => let (a, b) := fibPair r; (b, a + b)

/-- The **continuant** of the labels of a chain, the one program here that reads the
    newtype's own label as well as the answers: `K ⟨⟩ = 1`, `K ⟨a⟩ = a` and
    `K ⟨a, b, …⟩ = a * K ⟨b, …⟩ + K ⟨…⟩`. -/
def cont : Chain → Nat
  | .nil => 1
  | .cons a .nil => a
  | .cons a t@(.cons _ r) => a * cont t + cont r

-- The reference programs are the familiar sequences.
#guard fib (ofNat 10) = 55
#guard fibTR (ofNat 10) = 55
#guard fibPair (ofNat 10) = (55, 89)
#guard trib (ofNat 10) = 81
#guard tetra (ofNat 10) = 56
#guard penta (ofNat 10) = 31
#guard hexa (ofNat 10) = 16
#guard cont (.cons 3 (.cons 2 (.cons 1 .nil))) = 10

/-- **The chain's `fib` is the ordinary `fib`** of the number of links it has. -/
theorem fib_eq_fib_len : (t : Chain) → fib t = TyTests.FibWindow.fib (len t)
  | .nil => by simp [fib, len, TyTests.FibWindow.fib]
  | .cons _ .nil => by simp [fib, len, TyTests.FibWindow.fib]
  | .cons a (.cons b r) => by
      have he : fib (.cons a (.cons b r)) = fib (.cons b r) + fib r := by simp [fib]
      have hlen : len (.cons a (.cons b r)) = len r + 2 := by simp [len]
      have hl1 : len (.cons b r) = len r + 1 := by simp [len]
      have hw : TyTests.FibWindow.fib (len r + 2) =
          TyTests.FibWindow.fib (len r) + TyTests.FibWindow.fib (len r + 1) := by
        simp [TyTests.FibWindow.fib]
      rw [he, fib_eq_fib_len (.cons b r), fib_eq_fib_len r, hlen, hl1, hw]
      omega

/-- So on the chain of `n` links it is `fib n`. -/
theorem fib_ofNat (n : Nat) : fib (ofNat n) = TyTests.FibWindow.fib n := by
  rw [fib_eq_fib_len, len_ofNat]

/-- The pair recursion carries the answer at the chain and the answer at one link
    more. -/
theorem fibPair_eq : (t : Chain) → fibPair t = (fib t, fib (.cons 0 t))
  | .nil => by simp [fibPair, fib]
  | .cons l c => by
      have ih := fibPair_eq c
      have hfib : fib (.cons l c) = fib (.cons 0 c) := by cases c <;> simp [fib]
      show (let (a, b) := fibPair c; ((b, a + b) : Nat × Nat)) = _
      rw [ih]
      have hup : fib (.cons 0 (.cons l c)) = fib (.cons l c) + fib c := by simp [fib]
      simp only [hup, hfib]
      exact Prod.ext rfl (Nat.add_comm _ _)

/-- The first component of the pair recursion is `fib`. -/
theorem fibPair_fst_eq_fib (t : Chain) : (fibPair t).1 = fib t := by
  rw [fibPair_eq]

/-- The loop, started at the answers at `k` and `k + 1`, answers at `k` plus the length
    of the chain. -/
theorem fibLoopTR_eq : (t : Chain) → (k : Nat) →
    fibLoopTR t (TyTests.FibWindow.fib k) (TyTests.FibWindow.fib (k + 1)) =
      TyTests.FibWindow.fib (k + len t)
  | .nil, _ => rfl
  | .cons _ c, k => by
      show fibLoopTR c (TyTests.FibWindow.fib (k + 1))
        (TyTests.FibWindow.fib k + TyTests.FibWindow.fib (k + 1)) = _
      rw [show TyTests.FibWindow.fib k + TyTests.FibWindow.fib (k + 1) =
        TyTests.FibWindow.fib (k + 2) from rfl, fibLoopTR_eq c (k + 1)]
      show TyTests.FibWindow.fib (k + 1 + len c) = TyTests.FibWindow.fib (k + (len c + 1))
      congr 1
      omega

/-- The tail-recursive program is `fib`. -/
theorem fibTR_eq_fib (t : Chain) : fibTR t = fib t := by
  show fibLoopTR t (TyTests.FibWindow.fib 0) (TyTests.FibWindow.fib 1) = _
  rw [fibLoopTR_eq t 0, fib_eq_fib_len, Nat.zero_add]

end Chain

/-! ## 1. The newtype, and what its branch binds -/

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

/-- The schema of a **link**: a label, and whatever follows it. -/
abbrev linkSchema (τ : TyWf) : LeanRecordSchema TyWf := ⟨natT, τ, []⟩

/-- A link: `Nat × τ`. -/
abbrev linkTy (τ : TyWf) : TyWf := .record (linkSchema τ)

/-- `Nat × Ty.self`, written inside the binder. -/
def linkSelf : Ty := .record ⟨.prim .nat, Ty.self, []⟩

/-- The body of the newtype: `Option (Nat × Ty.self)`, written inside the binder.  The
    occurrence sits inside the `some` constructor, which is the only way a newtype can
    mention itself and still have values — the `none` constructor is the one that does
    not. -/
def chainBody : Ty := .taggedUnion (.skip (.here ⟨linkSelf, []⟩ []))

/-- That body, with the proof that it is well formed in the scope the binder opens. -/
def chainBodyW : TyWfIn 1 := chainBody.toTyWfIn

/-- The type of a chain. -/
def chainTy : TyWf := .recAlias chainBodyW

-- A value of it is an `Option` of a label and one more chain.
example : TyWf.recAliasUnfold chainBodyW = optTy (linkTy chainTy) := rfl

-- **The old fold bound no answer**: the body of the newtype is not an occurrence of it,
-- so `TyWf.recBinders` — which is what the branch of every other fold uses — hands the
-- branch the body and nothing else (`LeanScript.TyWf.recBinders_recAlias`, at every
-- newtype).
example (τ : TyWf) :
    TyWf.recBinders chainTy τ [chainBodyW] = [optTy (linkTy chainTy)] := rfl

example (τ : TyWf) :
    TyWf.recBinders chainTy τ [chainBodyW] = [TyWf.recAliasUnfold chainBodyW] :=
  TyWf.recBinders_recAlias chainBodyW (by ty_wf) τ

/-- **The answer tree of depth `j` at a chain**, written out: at `0` the answer there, and
    at `j + 1` that answer beside the body's own shape — an `Option` of a label and the
    tree of depth `j` at the chain below. -/
abbrev treeTy (τ : TyWf) : Nat → TyWf
  | 0 => τ
  | j + 1 => .record ⟨τ, optTy (linkTy (treeTy τ j)), []⟩

/-- **The window a depth-`k` fold binds**, written out: the newtype's body with the chain
    below replaced by the answer tree of depth `k` at it. -/
abbrev winTy (τ : TyWf) (k : Nat) : TyWf := optTy (linkTy (treeTy τ k))

-- These two equations are the whole of the descent, and they are what the branches below
-- are written against: **taking a window apart** binds a link whose second field is the
-- answer tree at the chain below, and **taking an answer tree apart** binds the answer at
-- that chain and the window of one depth less at it.  So each level of descent pushes
-- `1 + 2 + 2` binders in front of the context, and the answers read so far sit at the
-- indices `1, 3, 8, 13, …`.
example (τ : TyWf) (k : Nat) : winTy τ k = optTy (linkTy (treeTy τ k)) := rfl
example (τ : TyWf) (j : Nat) : treeTy τ (j + 1) = .record ⟨τ, winTy τ j, []⟩ := rfl

-- At depth `0` the branch binds the body — an `Option` of a label and a chain — and the
-- window, an `Option` of a label and the answer at the chain below: the plain fold of a
-- newtype.
example (τ : TyWf) (Γ : Ctx) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 ++ Γ =
      optTy (linkTy chainTy) :: optTy (linkTy τ) :: Γ := rfl

-- At depth `1` the window holds, for the chain below, the answer at it *and* the answers
-- at the chains below that one.
example (τ : TyWf) (Γ : Ctx) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 1 ++ Γ =
      optTy (linkTy chainTy) ::
        optTy (linkTy (.record ⟨τ, optTy (linkTy τ), []⟩)) :: Γ := rfl

/-- The context every fold below is written in: the chain it folds over, bound by the
    `fun` in front of it. -/
abbrev CCtx : Ctx := [chainTy]

/-- **The context a branch of a depth-`k` fold is written in**: the body, the window, and
    then the context the fold stands in. -/
abbrev branchCtx (τ : TyWf) (k : Nat) : Ctx :=
  optTy (linkTy chainTy) :: winTy τ k :: CCtx

-- That really is the context the grammar asks for, at each of the depths used below.
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 0 ++ CCtx = branchCtx τ 0 := rfl
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 1 ++ CCtx = branchCtx τ 1 := rfl
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 2 ++ CCtx = branchCtx τ 2 := rfl
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 3 ++ CCtx = branchCtx τ 3 := rfl
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 4 ++ CCtx = branchCtx τ 4 := rfl
example (τ : TyWf) :
    TyWf.recAliasRecBinders chainBodyW (by ty_wf) τ 5 ++ CCtx = branchCtx τ 5 := rfl

/-- The union the body of the newtype is, once unfolded: what `Term.recAlias_mk` takes
    a value of. -/
abbrev chainUnion : LeanTaggedUnionSchema TyWf := .skip (.here ⟨linkTy chainTy, []⟩ [])

/-- The empty chain, as a term. -/
def nilTerm : Term sigAdd [] chainTy :=
  .recAlias_mk chainBodyW (value := .taggedUnion_mk chainUnion 0 (fields := .nil))

/-- One more link on top of the chain in scope. -/
def consTerm : Term sigAdd [] (natT ⇒ chainTy ⇒ chainTy) :=
  .lam (.lam (.recAlias_mk chainBodyW
    (value := .taggedUnion_mk chainUnion 1
      (fields := .cons
        (.record_mk (linkSchema chainTy)
          (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))) .nil))))

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
