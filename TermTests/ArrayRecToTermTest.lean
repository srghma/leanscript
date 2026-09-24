module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `array_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest.lean` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci` and `pentanacci`, which descend `k + 1 = 2, 3, 4, 5` steps.
This file does the same for `LeanScript.Term.array_rec k`, the fold of an array that
descends `k + 1` elements at a time.

**Which Lean program is an `array_rec`.**  Lean cannot recurse structurally on an
`Array`: a definition by the patterns `⟨x :: xs⟩ => … f ⟨xs⟩` is compiled by well-founded
recursion (and is irreducible, so none of the `rfl` checks below could be stated about
it).  What Lean *does* compile structurally is a recursion on the list of the elements:

```lean
def f (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | …
```

The translation reads `go a.toList` — a structurally recursive function on lists applied
to the elements of an array — as `array_rec k` on `a`.  The depth `k` is read off the
compiled recursion exactly as for `nat_rec k`: it is the smallest `k` for which the branch
at `x :: y₁ :: … :: yₖ :: rest` reads only the head `x` and the values of `go` at the
`k + 1` suffixes `y₁ :: … :: rest`, …, `rest`.  The patterns for the lists of at most `k`
elements become the `LeanScript.ArrayRecBases`.

Each program below is written as ordinary Lean, with nothing added for the translation,
and each block checks that

* the translated term **is** an `array_rec` of the expected depth (`…_depth`);
* the term computes the expected numbers, by `rfl`;
* the term computes what the Lean definition computes, by `rfl`.
-/

namespace TermTests.ArrayRecToTerm

open LeanScript

/-- The empty signature: `+` is `Nat.add`, which is implemented by the extern
    `lean_nat_add`, so the translation calls it as `Term.extern .lean_nat_add` and the
    signature needs no declaration for it. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- The depth of a term that is an `array_rec`, or `none`. -/
def arrayRecDepthOf? {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {h : Head} :
    Term sig0 Γ u τ h → Option Nat
  | .array_rec k _ _ _ _ => some k
  | _ => none

/-- The depth of the `array_rec` a translated function `fun a => array_rec k …` is, or
    `none` if the translation is not of that shape. -/
def arrayRecDepth? {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {h : Head} :
    Term sig0 Γ u τ h → Option Nat
  | .lam b => arrayRecDepthOf? b
  | _ => none

/-! ## `k = 0`: the sum of an array

`go` descends one element: the branch at `x :: xs` reads `x` and `go xs`. -/

def sumArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | x :: xs => x + go xs

def sumArr_term :=
  (#leanscript_to_term sumArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : arrayRecDepth? sumArr_term = some 0 := rfl
example : run sumArr_term #[] = 0 := rfl
example : run sumArr_term #[5] = 5 := rfl
example : run sumArr_term #[1, 2, 3, 4] = 10 := rfl
example : run sumArr_term #[1, 2, 3, 4] = sumArr #[1, 2, 3, 4] := rfl
example : run sumArr_term #[7, 0, 9, 1, 1] = sumArr #[7, 0, 9, 1, 1] := rfl

/-! ## `k = 1`: a Fibonacci recursion on the elements

`go (x :: y :: xs)` reads `go (y :: xs)` and `go xs`: two suffixes, so `k = 1`, and the
lists `[]` and `[x]` are the base answers. -/

def fibArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | x :: y :: xs => x + go (y :: xs) + go xs

def fibArr_term :=
  (#leanscript_to_term fibArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : arrayRecDepth? fibArr_term = some 1 := rfl
example : run fibArr_term #[] = 0 := rfl
example : run fibArr_term #[4] = 4 := rfl
example : run fibArr_term #[1, 2] = 3 := rfl
example : run fibArr_term #[1, 2, 3, 4] = 21 := rfl
example : run fibArr_term #[1, 1, 1, 1, 1, 1] = 20 := rfl
example : run fibArr_term #[1, 2, 3, 4] = fibArr #[1, 2, 3, 4] := rfl
example : run fibArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = fibArr #[3, 1, 4, 1, 5, 9, 2, 6] :=
  rfl

/-! ## `k = 2`: a tribonacci recursion on the elements

Three suffixes: `go (y :: z :: xs)`, `go (z :: xs)` and `go xs`.  The base answers are
the lists of at most two elements; the answer at `[x, y]` itself reads `go [y]`. -/

def tribArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | [x, y] => x + go [y]
    | x :: y :: z :: xs => x + go (y :: z :: xs) + go (z :: xs) + go xs

def tribArr_term :=
  (#leanscript_to_term tribArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : arrayRecDepth? tribArr_term = some 2 := rfl
example : run tribArr_term #[] = 0 := rfl
example : run tribArr_term #[6] = 6 := rfl
example : run tribArr_term #[1, 2] = 3 := rfl
example : run tribArr_term #[1, 2, 3] = 9 := rfl
example : run tribArr_term #[1, 1, 1, 1, 1, 1] = 28 := rfl
example : run tribArr_term #[1, 2, 3, 4, 5] = tribArr #[1, 2, 3, 4, 5] := rfl
-- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
example : run tribArr_term #[3, 1, 4, 1, 5, 9, 2, 6] = tribArr #[3, 1, 4, 1, 5, 9, 2, 6] :=
  by kernel_rfl

/-! ## `k = 3`: a tetranacci recursion on the elements

Four suffixes, and the lists of at most three elements as base answers. -/

def tetraArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | [x, y] => x + y
    | [x, y, z] => x + y + z + go [z]
    | x :: y :: z :: w :: xs =>
        x + go (y :: z :: w :: xs) + go (z :: w :: xs) + go (w :: xs) + go xs

def tetraArr_term :=
  (#leanscript_to_term tetraArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : arrayRecDepth? tetraArr_term = some 3 := rfl
example : run tetraArr_term #[] = 0 := rfl
example : run tetraArr_term #[2] = 2 := rfl
example : run tetraArr_term #[1, 2] = 3 := rfl
example : run tetraArr_term #[1, 2, 3] = 9 := rfl
example : run tetraArr_term #[1, 1, 1, 1] = 8 := rfl
-- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
example : run tetraArr_term #[1, 2, 3, 4, 5] = tetraArr #[1, 2, 3, 4, 5] := by kernel_rfl
-- `kernel_rfl`, not `rfl`: the elaborator's own check of the equation is slow here (every
-- extern call goes through the case splits of `Extern.eval`), while the
-- kernel checks it quickly (see `LeanScript/KernelRfl.lean`).
example : run tetraArr_term #[3, 1, 4, 1, 5] = tetraArr #[3, 1, 4, 1, 5] := by kernel_rfl

/-! ## `k = 4`: a pentanacci recursion on the elements -/

def pentaArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [_] => 0
    | [_, _] => 0
    | [_, _, _] => 0
    | [x, _, _, _] => x
    | x :: y :: z :: w :: v :: xs =>
        x + go (y :: z :: w :: v :: xs) + go (z :: w :: v :: xs) + go (w :: v :: xs)
          + go (v :: xs) + go xs

def pentaArr_term :=
  (#leanscript_to_term pentaArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : arrayRecDepth? pentaArr_term = some 4 := rfl
example : run pentaArr_term #[] = 0 := rfl
example : run pentaArr_term #[1, 2, 3] = 0 := rfl
example : run pentaArr_term #[7, 2, 3, 4] = 7 := rfl
example : run pentaArr_term #[1, 1, 1, 1, 1, 1] = 4 := rfl
example : run pentaArr_term #[3, 1, 4, 1, 5, 9] = pentaArr #[3, 1, 4, 1, 5, 9] := rfl

/-! ## `k = 0` at a function type: an accumulator

A `go` that takes more arguments than the list is compiled with them in the motive, so
the fold is at the function type `nat ⇒ nat`, and the accumulator is passed on the way
down. -/

def sumAccArr (a : Array Nat) : Nat := go a.toList 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => go xs (acc + x)

def sumAccArr_term :=
  (#leanscript_to_term sumAccArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : run sumAccArr_term #[] = 0 := rfl
example : run sumAccArr_term #[1, 2, 3, 4] = 10 := rfl
example : run sumAccArr_term #[1, 2, 3, 4] = sumAccArr #[1, 2, 3, 4] := rfl

/-! ## What is refused

The branch of `array_rec` is given the head and the values of the fold at the suffixes —
not the elements after the head.  A `go` that reads the second element is refused. -/

def adjArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [_] => 0
    | x :: y :: xs => x + y + go (y :: xs)

/--
error: `#leanscript_to_term`: this recursion on the elements of an array is not the fold of an array — the fold `array_rec k` gives its branch the head and the values at the `k + 1` nearest suffixes of the tail, so a branch that reads an element past the head, or the tail itself, or the value at a list that is not a suffix, has no term
-/
#guard_msgs in
def adjArr_term :=
  (#leanscript_to_term adjArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

end TermTests.ArrayRecToTerm
