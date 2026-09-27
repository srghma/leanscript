/-
# Proof-carrying recursions the whitelist has to look at twice

Three functions that Lean accepts and that a translator asking only "is this declaration
safe, and does it return an `IO`?" would wave through.  Each shows a different way the
proof side of a declaration reaches into the termination argument.

Two dumps of what Lean stored for them are checked in beside this file:
`ExamplesProofFields/Rejected-Lcnf.txt` (the `saveBase` phase) and
`ExamplesProofFields/Rejected-Kinds.txt` (which kind of recursion was recorded, and the
measure).
-/

namespace ExamplesProofFields

/-! ## 1. Recursion that descends on an **erased** argument

`accDown` recurses on `h`, an accessibility proof — a `Prop`, and therefore erased.  If
Lean had recorded this as *structural* recursion, the whitelist's kind-S branch would
have been asked for the size of an argument that does not exist at run time.

It does not.  Lean elaborates `accDown` as **well-founded** recursion and picks the
measure itself, over the surviving argument:

```
ExamplesProofFields.accDown: well-founded recursion
  packed  : ExamplesProofFields.accDown._unary
  measure : fun x => PSigma.casesOn x fun n h => n
```

So the rank is `n`, and the declaration is an ordinary kind-W function.  Its `saveBase`
body is, apart from the erased argument `◾`, literally the same as `accDownRanked`'s.
This is the reassuring half of the finding: a recursive `def` that looks as if it
descends on a proof is handed to the front end with a runtime measure already attached.

The whitelist should still *state* the condition, because it is what makes the kind-S
branch safe: the argument at `recArgPos` must not be erased.  Nothing in the corpus
violates it, and `scripts/dump-recursion-kind.lean` reports it. -/

def accDown (n : Nat) (h : Acc (· < ·) n) : Nat :=
  match h with
  | .intro _ f => if hn : 0 < n then accDown (n - 1) (f (n - 1) (by omega)) else 0

/-- The same function with the proof argument gone and the measure written out; its
    `saveBase` body is identical to `accDown`'s. -/
def accDownRanked (n : Nat) : Nat :=
  if 0 < n then accDownRanked (n - 1) else 0
termination_by n

/-! ### The form that does slip through

`accDownRec` is the same recursion written as a direct application of `Acc.rec`.  Now
there is **no recursion information of any kind**: it is not a recursive declaration, it
has no equation info, no `termination_by`, and the whitelist's "neither structural nor
well-founded, and not recursive ⇒ no `fix` at all" branch is the one that fires.

But it is compiled, and the compiled code loops.  Lean specialises the recursor into a
generated declaration which is *itself* self-recursive and carries no measure:

```
def Acc.recC._at_.ExamplesProofFields.accDownRec.spec_0 r a t : Nat :=
  … cases … | Decidable.isTrue hx =>
    let _x.5 := Acc.recC._at_.ExamplesProofFields.accDownRec.spec_0 ◾ _x.4 ◾;
```

So the gate cannot be a question about the *declaration*; it has to be a question about
everything the declaration reaches.  Two checks catch it:

* refuse a body that mentions `Acc.rec`, `WellFounded.fix`, `WellFounded.fixF` or
  `WellFoundedRecursion.fix` — the eliminators of an erased argument;
* run the call-graph acyclicity check over the *generated* callees too, not only over the
  module's own declarations: a cycle no classifier produced is an error, not a warning. -/

def accDownRec (n : Nat) (h : Acc (fun a b => a < b) n) : Nat :=
  Acc.rec (motive := fun _ _ => Nat)
    (fun x _ ih => if hx : 0 < x then ih (x - 1) (by omega) else 0) h

/-! ## 2. Reading data out of a proof

The worry behind "should the schemas carry the proofs?" is that some quantity a function
needs — a measure, say — might live inside a proof field.  Lean closes that door itself,
and `fromProof` is the specimen.

A `Prop` is proof-irrelevant and does not eliminate into `Type`, so the only way to get a
number out of `∃ k, n < k` is `Exists.choose`, i.e. `Classical.choice` — and a definition
that uses it is `noncomputable`: Lean emits no code for it, so it never reaches the
translator at all.  (Delete the `noncomputable` keyword and Lean refuses the definition:
"failed to compile definition, consider marking it as 'noncomputable' because it depends
on 'Exists.choose'".)  A measure written in terms of such a quantity is therefore either
unavailable to the compiled function, or the function is not compiled.  Carrying the
proof fields in a schema would not change this: there is nothing inside a proof to
carry. -/

noncomputable def fromProof (n : Nat) (h : ∃ k, n < k) : Nat := h.choose

/-! ## 3. A declaration whose every argument is a proof

Not a problem, but worth recording as the boundary case: after erasure `alwaysSeven` has
no arguments at all, so it is a constant — and the two Lean-level calls below, which pass
*different* proofs at *different* types, are the same call at run time.  The binder is
named `_h` because nothing may use it; that is the point of the example.  This is
`ExamplesProofFields.measure_indep_of_proof` one level up: a function of proofs alone
cannot branch on anything. -/

def alwaysSeven {n : Nat} (_h : 0 < n) : Nat := 7

example : alwaysSeven (n := 1) (by omega) = alwaysSeven (n := 2) (by omega) := rfl

end ExamplesProofFields
