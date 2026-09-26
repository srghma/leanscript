module

public meta import LeanScript.Gen.Cache

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `leanscript_signature`: declaring the datatypes of a program once

```lean
leanscript_signature Prog where
  listNat := List Nat
  rose := Rose
  pair := Nat × Bool
```

reads the Lean types, finds the strongly connected components (SCCs) of the Lean type
instances reachable from them, and declares every SCC that has a cycle **once**, as a block
of the signature, oldest first (`LeanScript.Gen.declareBlocks`).  It adds:

| name | what it is |
| :-- | :-- |
| `Prog.ks` | the block sizes, newest first |
| `Prog.block0`, `Prog.block1`, … | the member declarations of each block (`Mems`) |
| `Prog.Δ` | the signature (`DSig Prog.ks`) |
| `Prog.listNat`, `Prog.rose`, … | the requested types (`Ty Prog.ks`) |

and records the program in the cache as the *current* program: from then on,
`#leanscript_get_ty` and `#leanscript_get_ctor` (`LeanScript.GetCtor`) translate
Lean types and constructors against it.  `leanscript_use_signature Prog` makes an earlier
program current again.

For every recursive SCC it computes a *grounding order* of the members and marks the first
grounded constructor of each union as its base: this is done once per declaration.  A
recursive type is then referred to by its name `Ty.data r`, so every use of a Lean type is
the same tree.  Everything else stays structural (see `LeanScript.Gen.toCIR`).

Proof and instance fields are erased.  It refuses, with an error: a type with no
constructor, a type with one constructor and no field (unit-like, such as `Unit`, also as a
field: `Option Unit` is refused, since two points are only ever `bool`), an inductive family with
indices, a field whose type is a type or depends on an earlier field, a recursive
occurrence in the domain of a function, a `Thunk` (a delay would give `Bool` a second
type of two values), and a recursive SCC with no
grounding order (a type with no finite value).

The whole program shares one signature (decision 2 of the proposal: *one signature per
program*).
-/

open Lean Meta Elab Command

namespace LeanScript.Gen

syntax leanscriptSigEntry := ident " := " term

/-- `leanscript_signature Prog where name := T; …` declares the datatypes of a program. -/
syntax (name := leanscriptSignature)
  "leanscript_signature " ident " where" sepByIndentSemicolon(leanscriptSigEntry) : command

/-- `leanscript_use_signature Prog` makes the program `Prog` the current one. -/
syntax (name := leanscriptUseSignature) "leanscript_use_signature " ident : command

@[command_elab leanscriptSignature]
def elabSignature : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let fullName := (← getCurrNamespace) ++ name.getId
  let entries := stx[3].getSepArgs
  let pairs : Array (Ident × Lean.Term) := entries.map fun e => (⟨e[0]⟩, ⟨e[2]⟩)
  let sub (s : Name) : Ident := mkIdentFrom name (name.getId ++ s)
  let (info, cmds) ← liftTermElabM do
    let reqs ← pairs.mapM fun (_, t) => do
      let e ← Term.elabType t
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← normType (← instantiateMVars e)
      if e.hasFVar || e.hasMVar then fail m!"the type{indentExpr e}\nis not closed"
      return e
    let ((blocks, tys), st) ← (do
        for r in reqs do discover r
        let blocks ← declareBlocks true none
        return (blocks, ← reqs.mapM toCIR)).run {}
    let nb := blocks.size
    let info : ProgInfo :=
      { name := fullName, members := blocks.map (·.members.map (st.nodes[·]!.ty)) }
    let ksOf (c : Nat) : List Nat := ((blocks.toList.take c).map (·.members.size - 1)).reverse
    let mut out : Array (TSyntax `command) := #[]
    for b in [0:nb] do
      let B := blocks[b]!
      let k := B.members.size - 1
      out := out.push (← `(def $(sub (.mkSimple s!"block{b}")) :
        Mems $(quote (ksOf b)) ($(quote k) + 1) 0 := $(← B.memsStx b)))
    out := out.push (← `(abbrev $(sub `ks) : List Nat := $(quote (ksOf nb))))
    let mut sig ← `(DSig.nil)
    for b in [0:nb] do
      sig ← `(DSig.cons $sig $(quote (blocks[b]!.members.size - 1))
        $(sub (.mkSimple s!"block{b}")))
    out := out.push (← `(def $(sub `Δ) : DSig $(sub `ks) := $sig))
    for i in [0:pairs.size] do
      out := out.push (← `(def $(sub pairs[i]!.1.getId) : Ty $(sub `ks) := $(← tys[i]!.stx nb #[])))
    return (info, out)
  for c in cmds do elabCommand c
  addEntry (.prog info)

@[command_elab leanscriptUseSignature]
def elabUseSignature : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let cands := [(← getCurrNamespace) ++ id.getId, id.getId]
  for n in cands do
    if (← findProg? n).isSome then
      addEntry (.use n)
      return
  throwErrorAt id "{errPrefix}: no program `{id.getId}` has been declared with `leanscript_signature`"

end LeanScript.Gen

end
