module

public import TermTests.NatRecDepthTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `recTaggedUnion_rec k`, produced by `#leanscript_to_term` from Lean programs

`TermTests/NatRecDepthTest/` tests `LeanScript.Term.nat_rec k` by translating `fib`,
`tribonacci`, `tetranacci`, `pentanacci`, … ; `TermTests/ArrayRecToTermTest/` does the same
for `LeanScript.Term.array_rec k` and `TermTests/RecObjectToTermTest/` for
`LeanScript.Term.recObject_rec k`.  These files do it for
`LeanScript.Term.recTaggedUnion_rec k`, the fold of a **recursive tagged union** whose
branches may look `k` constructors further down, one subvalue at a time.

**Which Lean program is a `recTaggedUnion_rec k`.**  Any structural recursion on an
inductive type whose tree is `Ty.recTaggedUnion` — several constructors, each field
either the type itself or a value that does not mention it.  Lean compiles it into
`X.brecOn`, and the translation (`LeanScript.ToTerm.TransRecUnion`) reads it as
`recTaggedUnion_rec k`, where `k` is the smallest depth at which every branch is served
by the constructor's fields, the answers at its subvalues, and at most `k` looks into one
subvalue at a time (`LeanScript.FoldKBranch.deep`).  The programs are written as ordinary
Lean, with no annotation and nothing added for the translation.

One file per datatype, each with programs at `k = 0, 1, 2, 3, 4`:

* `List.lean` — `List Nat`, one recursive point: the depth-`k` programs are the
  Fibonacci-like recursions of `TermTests/NatRecDepthTest/` on the length of the list.
* `Tree.lean` — `Tree` (`leaf | node left val right`), two recursive points: the
  deeper looks go down the left spine or the right spine.
* `Tree3.lean` — `Tree3` (`leaf val | node a b c`), three recursive points: the deeper
  looks go down the first, the middle or the last child.

Each program is checked three ways:

* the translated term **is** a `recTaggedUnion_rec` of the expected depth;
* the term computes the expected numbers;
* the term computes what the Lean definition computes.

The inputs are built by translated Lean programs too (e.g. `Tree.full n`, a `nat_rec`
whose branch builds nodes with `recTaggedUnion_mk`).

The equations are checked by `kernel_rfl` rather than `rfl`: the elaborator's own check of
such an equation fails or runs out of heartbeats, while the kernel checks it quickly (see
`LeanScript/KernelRfl.lean`).  `kernel_rfl` is still a proof by `Eq.refl`, checked by the
kernel.
-/

namespace TermTests.RecUnionToTerm

open LeanScript

/-- The depth of the `recTaggedUnion_rec` a translated function is: the fold under the
    `fun`s of its arguments, applied to the arguments that Lean put in the motive.  `none`
    if the translation is not of that shape. -/
def recUnionRecDepth? {Sg : Sig} {Γ : Ctx} {τ : TyWf} : Term Sg Γ τ → Option Nat
  | .recTaggedUnion_rec k _ _ => some k
  | .lam b => recUnionRecDepth? b
  | .ap f _ => recUnionRecDepth? f
  | _ => none

/-- A natural number of the language. -/
abbrev natT : TyWf := .prim .nat

end TermTests.RecUnionToTerm

end
