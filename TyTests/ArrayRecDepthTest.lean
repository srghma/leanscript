module

public import TyTests.ArrayRecKTest
public import TyTests.FibWindowTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite, over arrays: `array_rec` written out at every depth

`TyTests/NatRecDepthTest.lean` takes the family of Fibonacci programs — the `n + 2`
recursion, the tail-recursive loop, the pair recursion, the `for` loop, and the
tribonacci … hexanacci numbers — and writes each of them as a term of the grammar.  This
file is the same exercise for a recursion over an **array**, which is what
`LeanScript.Term.array_rec k` is for.

The array-valued `fib` is the **continuant**:

```lean
def cont : List Nat → Nat
  | [] => 1
  | [a] => a
  | a :: b :: as => a * cont (b :: as) + cont as
```

It is `fib` with a coefficient at each step — on a list of `n` ones it **is** `fib (n + 1)`
(`cont_replicate_one`) — and, exactly like `fib`'s `n + 2` pattern, it reads the answer at
a suffix that is not the immediate tail.  That is the recursion the depth is for: at
`k = 1` the branch of `array_rec` is given the answers at `as` and at `as.drop 1`.

What is written out here, in the grammar and with the value of every term proved at
**every** list rather than at a few:

| the program | the node it is | here |
| :-- | :-- | :-- |
| `cont` (reads the tail of the tail) | `array_rec 1` | `contTerm_eval` |
| `cont3`, `cont4` (three and four suffixes) | `array_rec 2`, `array_rec 3` | `cont3Term_eval`, `cont4Term_eval` |
| `contTR` (tail-recursive, two accumulators) | `array_rec 0` **at a function type** | `contTRTerm_eval` |
| `contPair` (pair recursion) | `array_rec 0` at a record type | `contPairTerm_eval` |
| `contLoop` (`for x in l do …`) | the same fold, written as a loop | `contLoop_eq` |
| a recursion that **halves** the list | no depth reaches it | prose at the end |

Every program runs in one signature, `sigArith`, whose two declarations are `add` and
`mul`: arithmetic is external to the language.

The terms here are **written out**, as the first half of `TyTests/NatRecDepthTest.lean`
is: `#leanscript_to_term` compiles a recursion on a `Nat` and on a recursive tagged
union, and a recursion over a list is not one of the shapes it reads yet, so there is no
translated half to check.  What is checked instead is the same thing that half checks —
the value of each term, at **every** argument.
-/

namespace TyTests.ArrayRecDepth

open LeanScript
open TyTests.ArrayRecK (natT cont cont3 cont4 listFoldK_eq_cont listFoldK_eq_cont3
  listFoldK_eq_cont4)
open TyTests.FibWindow (fib)

/-- A signature with two declarations, `add` and `mul`, both `nat ⇒ nat ⇒ nat`. -/
def sigArith : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"mul", natT ⇒ natT ⇒ natT⟩], by decide⟩

/-- The values of the declarations of `sigArith`. -/
def envArith : GlobalEnv sigArith.decls := (Nat.add, Nat.mul, PUnit.unit)

/-- Running a closed term of `sigArith`. -/
local macro:max "runArith" t:term:max : term => `(Term.run (Sg := sigArith) envArith $t)

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigArith Γ natT) : Term sigArith Γ natT :=
  .ap (.ap (.global .here) a) b

/-- `mul a b`, for two terms in hand. -/
def mulT {Γ : Ctx} (a b : Term sigArith Γ natT) : Term sigArith Γ natT :=
  .ap (.ap (.global (.there .here)) a) b

/-- The context the folds below are written in: the array they fold over. -/
abbrev ArrCtx : Ctx := [TyWf.array natT]

/-! ## 1. `cont`, written out at depth one

The lists of at most one element are answered by the `ArrayRecBases`: the empty list by
`1`, and a one-element list by its element, which the block **binds**.  The branch, at
`a :: as` with `as` non-empty, binds `a` (index `0`), `as` (index `1`), the answer at `as`
(index `2`) and the answer at `as.drop 1` (index `3`). -/

/-- The answers for the short lists: `K [] = 1` and `K [a] = a`. -/
def contBases : ArrayRecBases sigArith ArrCtx natT natT 1 :=
  .cons (.nat_mk 1) (.nil (.var (v♯0)))

/-- The branch: `a * K as + K (as.drop 1)`. -/
def contBranch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 2 ArrCtx) natT :=
  addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))

/-- The continuant, as a term of the grammar: the depth-one fold of an array. -/
def contTerm : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  .lam (.array_rec 1 (.var (v♯0)) contBases contBranch)

example : runArith contTerm [] = 1 := rfl
example : runArith contTerm [3] = 3 := rfl
example : runArith contTerm [3, 4] = 13 := rfl
example : runArith contTerm [1, 2, 3] = 10 := rfl
example : runArith contTerm [1, 1, 1, 1, 1, 1] = 13 := rfl

/-- The fold `Term.eval` runs for `contTerm`, in an arbitrary environment: the short
    lists go to `contBases` and the branch runs with the window in front of the
    environment. -/
def contEvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 1)
    (fun m => ArrayRecBases.eval envArith contBases env m (by no_rec_mk))
    (fun hd tl w => Term.eval envArith contBranch (hd, tl, Env.ofWin w env) (by no_rec_mk))

/-- That fold is the continuant — by the two equations of `LeanScript.ArrayRecFacts`,
    whatever the environment is. -/
theorem contEvalFold_eq (env : Env ArrCtx) (l : List Nat) : contEvalFold env l = cont l :=
  listFoldK_eq_cont _ _ rfl (fun _ => rfl) (fun _ _ _ => rfl) l

/-- **The term computes the continuant, at every list** — not only at the ones checked by
    `rfl` above. -/
theorem contTerm_eval (l : List Nat) : runArith contTerm l = cont l :=
  contEvalFold_eq (l, Env.nil) l

/-! ### The continuant is `fib`

On a list of `n` ones every coefficient is `1`, so the recursion is `fib`'s own. -/

/-- `K (1, …, 1)` with `n` ones is `fib (n + 1)`. -/
theorem cont_replicate_one : (n : Nat) → cont (List.replicate n 1) = fib (n + 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show 1 * cont (List.replicate (n + 1) 1) + cont (List.replicate n 1) = fib (n + 3)
      rw [cont_replicate_one (n + 1), cont_replicate_one n,
        show fib (n + 3) = fib (n + 1) + fib (n + 2) from rfl,
        show n + 1 + 1 = n + 2 from rfl]
      omega

/-- So the term of the grammar computes `fib`, on the arrays of ones. -/
theorem contTerm_eval_ones (n : Nat) :
    runArith contTerm (List.replicate n 1) = fib (n + 1) := by
  rw [contTerm_eval, cont_replicate_one]

/-! ## 2. Three and four suffixes: the same node at depth two and three

`cont3` and `cont4` are to `cont` what the tribonacci and tetranacci numbers are to
`fib`.  Nothing changes but the depth: one more short list to answer, and one more entry
in the window. -/

/-- The answers for the short lists of the depth-two fold: `1`, `a`, `a * b`.  In the
    last one the first element is bound outermost, so `a` is index `1` and `b` index
    `0`. -/
def cont3Bases : ArrayRecBases sigArith ArrCtx natT natT 2 :=
  .cons (.nat_mk 1) (.cons (.var (v♯0)) (.nil (mulT (.var (v♯1)) (.var (v♯0)))))

/-- The branch of the depth-two fold: `a * K as + K (as.drop 1) + K (as.drop 2)`. -/
def cont3Branch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 3 ArrCtx) natT :=
  addT (addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))) (.var (v♯4))

/-- `cont3`, as a term: the depth-two fold of an array. -/
def cont3Term : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  .lam (.array_rec 2 (.var (v♯0)) cont3Bases cont3Branch)

example : runArith cont3Term [] = 1 := rfl
example : runArith cont3Term [5, 6] = 30 := rfl
example : runArith cont3Term [1, 1, 1, 1, 1, 1] = 17 := rfl

/-- The fold `Term.eval` runs for `cont3Term`. -/
def cont3EvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 2)
    (fun m => ArrayRecBases.eval envArith cont3Bases env m (by no_rec_mk))
    (fun hd tl w => Term.eval envArith cont3Branch (hd, tl, Env.ofWin w env) (by no_rec_mk))

theorem cont3EvalFold_eq (env : Env ArrCtx) (l : List Nat) : cont3EvalFold env l = cont3 l :=
  listFoldK_eq_cont3 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) l

/-- The depth-two term computes `cont3`, at every list. -/
theorem cont3Term_eval (l : List Nat) : runArith cont3Term l = cont3 l :=
  cont3EvalFold_eq (l, Env.nil) l

/-- The answers for the short lists of the depth-three fold: `1`, `a`, `a * b`,
    `a * b * c`. -/
def cont4Bases : ArrayRecBases sigArith ArrCtx natT natT 3 :=
  .cons (.nat_mk 1)
    (.cons (.var (v♯0))
      (.cons (mulT (.var (v♯1)) (.var (v♯0)))
        (.nil (mulT (mulT (.var (v♯2)) (.var (v♯1))) (.var (v♯0))))))

/-- The branch of the depth-three fold: the head times the nearest answer, plus the other
    three the window holds. -/
def cont4Branch :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx natT 4 ArrCtx) natT :=
  addT (addT (addT (mulT (.var (v♯0)) (.var (v♯2))) (.var (v♯3))) (.var (v♯4)))
    (.var (v♯5))

/-- `cont4`, as a term: the depth-three fold of an array. -/
def cont4Term : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  .lam (.array_rec 3 (.var (v♯0)) cont4Bases cont4Branch)

example : runArith cont4Term [] = 1 := rfl
example : runArith cont4Term [2, 3, 4] = 24 := rfl
example : runArith cont4Term [1, 1, 1, 1, 1, 1] = 13 := rfl

/-- The fold `Term.eval` runs for `cont4Term`. -/
def cont4EvalFold (env : Env ArrCtx) : List Nat → Nat :=
  listFoldK (τ := natT) (k := 3)
    (fun m => ArrayRecBases.eval envArith cont4Bases env m (by no_rec_mk))
    (fun hd tl w => Term.eval envArith cont4Branch (hd, tl, Env.ofWin w env) (by no_rec_mk))

theorem cont4EvalFold_eq (env : Env ArrCtx) (l : List Nat) : cont4EvalFold env l = cont4 l :=
  listFoldK_eq_cont4 _ _ rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) l

/-- The depth-three term computes `cont4`, at every list. -/
theorem cont4Term_eval (l : List Nat) : runArith cont4Term l = cont4 l :=
  cont4EvalFold_eq (l, Env.nil) l

/-! ## 3. The tail-recursive loop: a fold of an array whose value is a function

```lean
def contTR : List Nat → Nat → Nat → Nat
  | [], a, _ => a
  | x :: xs, a, b => contTR xs (x * a + b) a
```

This is the array-valued `fibLoopTR`: it walks the list from the **front**, carrying the
two continuants of the prefix read so far.  It descends one element at a time, so it is
the fold at the **default** depth — but its value is not a number, it is the function of
the two accumulators.  `array_rec` folds at any type, function types included. -/

/-- The tail-recursive form. -/
def contTR : List Nat → Nat → Nat → Nat
  | [], a, _ => a
  | x :: xs, a, b => contTR xs (x * a + b) a

/-- The continuant of the tail of a list, and `0` for the empty list: the second thing
    the accumulators carry. -/
def contTail : List Nat → Nat
  | [] => 0
  | _ :: xs => cont xs

/-- One element of the continuant, in the form the accumulators use. -/
theorem cont_cons : (x : Nat) → (xs : List Nat) → cont (x :: xs) = x * cont xs + contTail xs
  | x, [] => by show x = x * 1 + 0; omega
  | _, _ :: _ => rfl

/-- The invariant of the loop: it is linear in the two accumulators, with the continuant
    of the list and the continuant of its tail as the coefficients. -/
theorem contTR_eq : (l : List Nat) → (a b : Nat) → contTR l a b = a * cont l + b * contTail l
  | [], a, b => by show a = a * 1 + b * 0; omega
  | x :: xs, a, b => by
      show contTR xs (x * a + b) a = a * cont (x :: xs) + b * contTail (x :: xs)
      rw [contTR_eq xs (x * a + b) a, cont_cons x xs,
        show contTail (x :: xs) = cont xs from rfl]
      grind

/-- Started at `(1, 0)`, the loop is the continuant. -/
theorem contTR_start (l : List Nat) : contTR l 1 0 = cont l := by
  rw [contTR_eq]
  omega

/-- The type the fold runs at: the two accumulators. -/
abbrev Acc2 : TyWf := natT ⇒ natT ⇒ natT

/-- The value for the empty list: `fun a _ => a`. -/
def loopZero {Γ : Ctx} : Term sigArith Γ Acc2 := .lam (.lam (.var (v♯1)))

/-- The step: it binds the head `x` (index `0`), the tail (index `1`) and the loop over
    the tail (index `2`), and answers `fun a b => loop (x * a + b) a`. -/
def loopStep {Γ : Ctx} :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx Acc2 1 Γ) Acc2 :=
  .lam (.lam
    (.ap (.ap (.var (v♯4)) (addT (mulT (.var (v♯2)) (.var (v♯1))) (.var (v♯0))))
      (.var (v♯1))))

/-- `contTR`, as a term: the fold of an array at a function type. -/
def contTRTerm : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  .lam (.ap (.ap (.array_rec 0 (.var (v♯0)) (.nil loopZero) loopStep) (.nat_mk 1))
    (.nat_mk 0))

example : runArith contTRTerm [] = 1 := rfl
example : runArith contTRTerm [3, 4] = 13 := rfl
example : runArith contTRTerm [1, 2, 3] = 10 := rfl

/-- **Any** depth-zero fold at the accumulator type with these two equations is the
    tail-recursive loop. -/
theorem listFoldK_eq_contTR (z : List Nat → TyWf.Den Acc2)
    (s : Nat → List Nat → NatWin Acc2 1 → TyWf.Den Acc2)
    (hz : z [] = fun a _ => a)
    (hs : ∀ x xs w, s x xs w = fun a b => w.1 (x * a + b) a) :
    (l : List Nat) → (a b : Nat) →
      listFoldK (τ := Acc2) (k := 0) z s l a b = contTR l a b
  | [], a, b => by
      rw [listFoldK_base (τ := Acc2) (k := 0) _ _ [] (by simp), hz]
      rfl
  | x :: xs, a, b => by
      rw [listFoldK_step (τ := Acc2) (k := 0) _ _ x xs (by simp), hs]
      show listFoldK (τ := Acc2) (k := 0) z s xs (x * a + b) a = contTR (x :: xs) a b
      rw [listFoldK_eq_contTR z s hz hs xs (x * a + b) a]
      rfl

/-- The fold `Term.eval` runs for the loop. -/
def loopBases : ArrayRecBases sigArith ArrCtx natT Acc2 0 := .nil loopZero

/-- The short-list answers `Term.eval` uses for the loop. -/
def loopEvalZ (env : Env ArrCtx) : List Nat → TyWf.Den Acc2 :=
  fun m => ArrayRecBases.eval envArith loopBases env m (by no_rec_mk)

/-- The branch `Term.eval` uses for the loop. -/
def loopEvalS (env : Env ArrCtx) :
    Nat → List Nat → NatWin Acc2 1 → TyWf.Den Acc2 :=
  fun hd tl w =>
    Term.eval envArith (loopStep (Γ := ArrCtx)) (hd, tl, Env.ofWin w env) (by no_rec_mk)

theorem loopEvalFold_eq (env : Env ArrCtx) (l : List Nat) (a b : Nat) :
    listFoldK (τ := Acc2) (k := 0) (loopEvalZ env) (loopEvalS env) l a b = contTR l a b :=
  listFoldK_eq_contTR _ _ rfl (fun _ _ _ => rfl) l a b

/-- The tail-recursive term computes the continuant, at every list. -/
theorem contTRTerm_eval (l : List Nat) : runArith contTRTerm l = cont l := by
  show listFoldK (τ := Acc2) (k := 0) (loopEvalZ (l, Env.nil)) (loopEvalS (l, Env.nil))
    l 1 0 = cont l
  rw [loopEvalFold_eq]
  exact contTR_start l

/-! ## 4. The pair recursion: a fold of an array whose value is a record

```lean
def contPair : List Nat → Nat × Nat
  | [] => (1, 0)
  | x :: xs => let p := contPair xs; (x * p.1 + p.2, p.1)
```

The array-valued `fibPair`: the one-element fold at a two-field record, whose fields are
the continuant of the list and the continuant of its tail. -/

/-- The pair recursion. -/
def contPair : List Nat → Nat × Nat
  | [] => (1, 0)
  | x :: xs =>
    let p := contPair xs
    (x * p.1 + p.2, p.1)

/-- The user's own invariant: the pair at `l` is `(K l, K (tail l))`. -/
theorem contPair_eq : (l : List Nat) → contPair l = (cont l, contTail l)
  | [] => rfl
  | x :: xs => by
      show ((x * (contPair xs).1 + (contPair xs).2, (contPair xs).1) : Nat × Nat) =
        (cont (x :: xs), contTail (x :: xs))
      rw [contPair_eq xs, cont_cons x xs, show contTail (x :: xs) = cont xs from rfl]

/-- The record the fold runs at: the two continuants. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨natT, natT, []⟩

/-- Its type. -/
abbrev Pair : TyWf := TyWf.record pairSchema

/-- The pair of the empty list: `(1, 0)`. -/
def pairZero {Γ : Ctx} : Term sigArith Γ Pair :=
  .record_mk pairSchema (.cons (.nat_mk 1) (.cons (.nat_mk 0) .nil))

/-- The step: it binds the head (index `0`), the tail (index `1`) and the pair at the
    tail (index `2`), takes that pair apart — so inside, index `0` is `K xs` and index
    `1` is `K (tail xs)`, and the head has moved to index `2` — and answers with the pair
    at `x :: xs`. -/
def pairStep {Γ : Ctx} :
    Term sigArith (natT :: TyWf.array natT :: natRecCtx Pair 1 Γ) Pair :=
  .record_casesOn (.var (v♯2))
    (.record_mk pairSchema
      (.cons (addT (mulT (.var (v♯2)) (.var (v♯0))) (.var (v♯1)))
        (.cons (.var (v♯0)) .nil)))

/-- `contPair`, as a term: the fold of an array at a record type. -/
def contPairTerm {Γ : Ctx} : Term sigArith Γ (TyWf.array natT ⇒ Pair) :=
  .lam (.array_rec 0 (.var (v♯0)) (.nil pairZero) pairStep)

/-- The continuant read off the pair: its first field. -/
def contFromPairTerm : Term sigArith [] (TyWf.array natT ⇒ natT) :=
  .lam (.record_casesOn (fs := pairSchema)
    (.ap (contPairTerm (Γ := ArrCtx)) (.var (v♯0))) (.var (v♯0)))

example : runArith contFromPairTerm [] = 1 := rfl
example : runArith contFromPairTerm [3, 4] = 13 := rfl
example : runArith contFromPairTerm [1, 2, 3] = 10 := rfl

/-- **Any** depth-zero fold at the record type with these two equations is the pair
    recursion. -/
theorem listFoldK_eq_contPair (z : List Nat → TyWf.Den Pair)
    (s : Nat → List Nat → NatWin Pair 1 → TyWf.Den Pair)
    (hz : z [] = (1, 0, PUnit.unit))
    (hs : ∀ x xs w, s x xs w = (x * w.1.1 + w.1.2.1, w.1.1, PUnit.unit)) :
    (l : List Nat) →
      listFoldK (τ := Pair) (k := 0) z s l = (cont l, contTail l, PUnit.unit)
  | [] => by
      rw [listFoldK_base (τ := Pair) (k := 0) _ _ [] (by simp), hz]
      rfl
  | x :: xs => by
      rw [listFoldK_step (τ := Pair) (k := 0) _ _ x xs (by simp), hs]
      show ((x * (listFoldK (τ := Pair) (k := 0) z s xs).1 +
            (listFoldK (τ := Pair) (k := 0) z s xs).2.1,
          (listFoldK (τ := Pair) (k := 0) z s xs).1, PUnit.unit) : Nat × Nat × PUnit) = _
      rw [listFoldK_eq_contPair z s hz hs xs, cont_cons x xs,
        show contTail (x :: xs) = cont xs from rfl]

/-- The short-list answers and the branch `Term.eval` uses for the pair recursion. -/
def pairBases : ArrayRecBases sigArith ArrCtx natT Pair 0 := .nil pairZero

def pairEvalZ (env : Env ArrCtx) : List Nat → TyWf.Den Pair :=
  fun m => ArrayRecBases.eval envArith pairBases env m (by no_rec_mk)

def pairEvalS (env : Env ArrCtx) : Nat → List Nat → NatWin Pair 1 → TyWf.Den Pair :=
  fun hd tl w =>
    Term.eval envArith (pairStep (Γ := ArrCtx)) (hd, tl, Env.ofWin w env) (by no_rec_mk)

theorem pairEvalFold_eq (env : Env ArrCtx) (l : List Nat) :
    listFoldK (τ := Pair) (k := 0) (pairEvalZ env) (pairEvalS env) l =
      (cont l, contTail l, PUnit.unit) :=
  listFoldK_eq_contPair _ _ rfl (fun _ _ _ => rfl) l

/-- The record-valued term **is** `contPair`, field by field. -/
theorem contPairTerm_eval (l : List Nat) :
    runArith (contPairTerm (Γ := [])) l = ((contPair l).1, (contPair l).2, PUnit.unit) := by
  show listFoldK (τ := Pair) (k := 0) (pairEvalZ (l, Env.nil)) (pairEvalS (l, Env.nil)) l = _
  rw [pairEvalFold_eq, contPair_eq l]

/-- And its first field is the continuant, at every list. -/
theorem contFromPairTerm_eval (l : List Nat) : runArith contFromPairTerm l = cont l := by
  show (listFoldK (τ := Pair) (k := 0) (pairEvalZ (l, Env.nil)) (pairEvalS (l, Env.nil))
    l).1 = cont l
  rw [pairEvalFold_eq]

/-! ## 5. The `for` loop

```lean
def contLoop (l : List Nat) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a
```

Desugared, this is `ForIn.forIn l (1, 0) …` in the identity monad: a fold over the list
whose state is the pair of mutable variables — that is, §3 and §4 written with different
syntax, and so the same term of the grammar. -/

/-- The loop, as one would write it. -/
def contLoop (l : List Nat) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a

example : contLoop [] = 1 := rfl
example : contLoop [3, 4] = 13 := rfl
example : contLoop [1, 2, 3] = 10 := rfl

/-- The same loop, started anywhere: what the induction needs. -/
def contLoopFrom (l : List Nat) (a0 b0 : Nat) : Nat := Id.run do
  let mut a := a0
  let mut b := b0
  for x in l do
    let next := x * a + b
    b := a
    a := next
  return a

/-- One turn of the loop. -/
theorem contLoopFrom_cons (x : Nat) (xs : List Nat) (a b : Nat) :
    contLoopFrom (x :: xs) a b = contLoopFrom xs (x * a + b) a := by
  simp [contLoopFrom, Id.run]

/-- The loop **is** the tail-recursive form, from any state. -/
theorem contLoopFrom_eq : (l : List Nat) → (a b : Nat) → contLoopFrom l a b = contTR l a b
  | [], _, _ => rfl
  | x :: xs, a, b => by
      rw [contLoopFrom_cons, contLoopFrom_eq xs (x * a + b) a]
      rfl

/-- So the loop is the continuant, at every list. -/
theorem contLoop_eq (l : List Nat) : contLoop l = cont l := by
  show contLoopFrom l 1 0 = cont l
  rw [contLoopFrom_eq]
  exact contTR_start l

/-! ## 6. What no depth reaches

The one program of the `fib` family that is refused is `fibFast`, whose recursive call is
at `n / 2`.  Its array analogue is a recursion that **halves the list**:

```lean
def contFast : List Nat → Nat
  | [] => 1
  | l => … contFast (l.take (l.length / 2)) … contFast (l.drop (l.length / 2)) …
```

A depth is a fixed number of *elements* to descend by, and the window the evaluator
carries holds the answers at the `k + 1` immediate suffixes.  A call at a list that is
half as long is not a call at a suffix at all, so no `k` reaches it, exactly as no depth
of `nat_rec` reaches `n / 2`.  That is a limit of the folds, not of the depth: it needs a
recursion justified by a measure, which this grammar deliberately does not have.
-/

end TyTests.ArrayRecDepth

end
