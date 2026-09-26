module

public import LeanScript.Nominal.Term
public meta import Lean.Elab.Command

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `leanscript_signature`: the cache that declares datatypes once

Step 6 of design **N** of `proposals/NominalTyProposal.md` (§2.6).

```lean
leanscript_signature Prog where
  listNat := List Nat
  rose := Rose
  pair := Nat × Bool
```

reads the Lean types, finds the strongly connected components (SCCs) of the Lean type
instances reachable from them, and declares every SCC that has a cycle **once**, as a block
of the signature, oldest first.  It adds:

| name | what it is |
| :-- | :-- |
| `Prog.ks` | the block sizes, newest first |
| `Prog.block₀`, `Prog.block₁`, … | the member declarations of each block (`Mems`) |
| `Prog.Δ` | the signature (`DSig Prog.ks`) |
| `Prog.listNat`, `Prog.rose`, … | the requested types (`Ty Prog.ks`) |
| `Prog.rose.node`, `Prog.listNat.cons`, … | for every requested *recursive* type, one term function per constructor: `Term.data_in` of the constructor's fields (the `#leanscript_get_ctor` of the proposal) |

For every recursive SCC it computes a *grounding order* of the members and marks the first
grounded constructor of each union as its base (the rules of `LeanScript.Nominal.Decl`):
this is done once per declaration.  A recursive type is then referred to by its name
`Ty.data r`, so every use of a Lean type is the same tree.  Everything else stays
structural:

* a leaf (`Nat`, `String`, `UInt8`, `BitVec 8`, …) is `Ty.prim`; `α → β`, `Array α` and
  `Thunk α` are `Ty.fn`, `Ty.array` and `Ty.thunk`;
* a non-recursive type with one constructor of one field is that field (the wrapper is
  erased); with two or more fields it is a record;
* a non-recursive type of two or more constructors is a union, or an enum when it has
  three or more constructors and none has a field (two field-less constructors are the
  union denoting `Bool`).

Proof fields are erased.  It refuses, with an error: a type with no constructor, a type
with one constructor and no field (unit-like), an inductive family with indices, a field
whose type is a type or depends on an earlier field, a recursive occurrence in the domain of
a function or under a `Thunk`, and a recursive SCC with no grounding order (a type with no
finite value).

The whole program shares one signature (decision 2 of the proposal: *one signature per
program*).
-/

open Lean Meta Elab Command

namespace LeanScript.Nominal.SigGen

/-- A closed type, before it is printed: datatypes are named by (absolute block, member). -/
inductive CIR where
  | prim (p : Lean.Term)
  | fn (a b : CIR)
  | array (a : CIR)
  | thunk (a : CIR)
  | enum (n : Nat)
  | record (f : CIR) (fs : Array CIR)
  | union (cs : Array (Array CIR))
  | data (b j : Nat)
  deriving Inhabited

/-- A field of a body: holes are named by node. -/
inductive FIR where
  | hole (node : Nat)
  | old (t : CIR)
  | array (f : FIR)
  | fn (a : CIR) (f : FIR)
  deriving Inhabited

/-- One Lean type instance reached from the requested types. -/
structure Node where
  ty : Expr
  ctors : Array (Array Expr)
  ctorNames : Array Name := #[]
  deriving Inhabited

/-- How a node is translated. -/
inductive Kind where
  | structural
  | recursive (b j : Nat)
  deriving Inhabited

/-- The head of a type. -/
inductive Head where
  | prim (p : Lean.Term)
  | fn (a b : Expr)
  | array (a : Expr)
  | thunk (a : Expr)
  | node (e : Expr)

/-- Normalise a type: head normal form, arguments normalised. -/
partial def normType (e : Expr) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e with
  | .forallE n a b bi =>
    if b.hasLooseBVars then return e
    return .forallE n (← normType a) (← normType b) bi
  | _ =>
    let fn := e.getAppFn
    if fn.isConst then
      let args ← e.getAppArgs.mapM fun a => do
        if (← isType a) then normType a else pure a
      return mkAppN fn args
    return e

/-- A natural number literal, if the expression evaluates to one. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let e' ← whnf e
  if let some n := e'.rawNatLit? then return some n
  return (← evalNat e).map id

/-- The head of a (normalised) type. -/
def classify (e : Expr) : MetaM Head := do
  if let .forallE _ a b _ := e then
    if b.hasLooseBVars then throwError "leanscript_signature: dependent function type{indentExpr e}"
    return .fn a b
  let some (c, _) := e.getAppFn.const? | throwError "leanscript_signature: not a type former application{indentExpr e}"
  let args := e.getAppArgs
  let p (s : Lean.Term) : MetaM Head := return .prim s
  match c, args.size with
  | ``Bool, 0 => p (← `(LeanPrimTy.bool))
  | ``Nat, 0 => p (← `(LeanPrimTy.nat))
  | ``Int, 0 => p (← `(LeanPrimTy.int))
  | ``UInt8, 0 => p (← `(LeanPrimTy.uint8))
  | ``UInt16, 0 => p (← `(LeanPrimTy.uint16))
  | ``UInt32, 0 => p (← `(LeanPrimTy.uint32))
  | ``UInt64, 0 => p (← `(LeanPrimTy.uint64))
  | ``Int8, 0 => p (← `(LeanPrimTy.int8))
  | ``Int16, 0 => p (← `(LeanPrimTy.int16))
  | ``Int32, 0 => p (← `(LeanPrimTy.int32))
  | ``Int64, 0 => p (← `(LeanPrimTy.int64))
  | ``Char, 0 => p (← `(LeanPrimTy.char))
  | ``String, 0 => p (← `(LeanPrimTy.string))
  | ``String.Pos.Raw, 0 => p (← `(LeanPrimTy.stringPosRaw))
  | ``Substring.Raw, 0 => p (← `(LeanPrimTy.substringRaw))
  | ``String.Slice, 0 => p (← `(LeanPrimTy.stringSlice))
  | ``Float, 0 => p (← `(LeanPrimTy.float))
  | ``Float32, 0 => p (← `(LeanPrimTy.float32))
  | ``Float.Model, 0 => p (← `(LeanPrimTy.floatModel))
  | ``Float32.Model, 0 => p (← `(LeanPrimTy.float32Model))
  | ``BitVec, 1 =>
    let some n ← natLit? args[0]! | throwError "leanscript_signature: the width of{indentExpr e}\nis not a numeral"
    if n = 0 then throwError "leanscript_signature: `BitVec 0` has one value"
    p (← `(LeanPrimTy.bitvec $(quote n)))
  | ``String.Pos, 1 =>
    let some s := (match (← whnf args[0]!) with | .lit (.strVal s) => some s | _ => none) | throwError "leanscript_signature: the string of{indentExpr e}\nis not a literal"
    if s = "" then throwError "leanscript_signature: `String.Pos \"\"` has one value"
    p (← `(LeanPrimTy.stringPos $(quote s)))
  | ``Array, 1 => return .array args[0]!
  | ``Thunk, 1 => return .thunk args[0]!
  | _, _ =>
    let env ← getEnv
    unless (env.find? c).any (·.isInductive) do
      throwError "leanscript_signature: `{c}` is not an inductive type{indentExpr e}"
    return .node e

/-- The relevant fields of every constructor of an inductive instance. -/
def readCtors (e : Expr) : MetaM (Array (Array Expr)) := do
  let some (c, us) := e.getAppFn.const? | unreachable!
  let info ← getConstInfoInduct c
  if info.numIndices ≠ 0 then
    throwError "leanscript_signature: `{c}` is an inductive family with indices, which is not supported{indentExpr e}"
  let params := e.getAppArgs
  unless params.size = info.numParams do
    throwError "leanscript_signature: `{c}` is not fully applied{indentExpr e}"
  info.ctors.toArray.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    forallTelescopeReducing ty fun xs _ => do
      let mut fields : Array Expr := #[]
      let mut data : Array Expr := #[]
      for x in xs do
        let t ← inferType x
        if ← isProp t then continue
        if (← whnf t).isSort then
          throwError "leanscript_signature: the constructor `{ctor}` has a field whose value is a type (existential typing is not supported)"
        if data.any (fun d => t.containsFVar d.fvarId!) then
          throwError "leanscript_signature: a field of the constructor `{ctor}` has a type that depends on an earlier field{indentExpr t}"
        if t.hasFVar then
          throwError "leanscript_signature: a field of the constructor `{ctor}` has a type that depends on a proof{indentExpr t}"
        data := data.push x
        fields := fields.push (← normType t)
      return fields

/-- The inductive instances a type mentions directly. -/
partial def occurrences (e : Expr) : MetaM (Array Expr) := do
  match ← classify e with
  | .prim _ => return #[]
  | .fn a b => return (← occurrences a) ++ (← occurrences b)
  | .array a | .thunk a => occurrences a
  | .node n => return #[n]

/-- The state of one run. -/
structure St where
  nodes : Array Node := #[]
  index : Std.HashMap Expr Nat := {}
  kinds : Array Kind := #[]
  /-- The structural translation of a non-recursive node, once computed. -/
  memo : Std.HashMap Nat CIR := {}

abbrev M := StateT St MetaM

/-- Discover every node reachable from a type. -/
partial def discover (e : Expr) : M Unit := do
  for n in ← occurrences e do
    if (← get).index.contains n then continue
    let i := (← get).nodes.size
    modify fun s => { s with nodes := s.nodes.push { ty := n, ctors := #[] }, index := s.index.insert n i }
    let ctors ← readCtors n
    let ctorNames := (← getConstInfoInduct n.getAppFn.constName!).ctors.toArray
    modify fun s => { s with nodes := s.nodes.set! i { ty := n, ctors, ctorNames } }
    for fs in ctors do
      for f in fs do discover f

/-- The nodes a node's fields mention directly. -/
def successors (i : Nat) : M (Array Nat) := do
  let s ← get
  let mut out := #[]
  for fs in s.nodes[i]!.ctors do
    for f in fs do
      for n in ← occurrences f do
        out := out.push s.index[n]!
  return out

/-- The closed translation of a type. -/
partial def toCIR (e : Expr) : M CIR := do
  match ← classify e with
  | .prim p => return .prim p
  | .fn a b => return .fn (← toCIR a) (← toCIR b)
  | .array a => return .array (← toCIR a)
  | .thunk a => return .thunk (← toCIR a)
  | .node n =>
    let i := (← get).index[n]!
    match (← get).kinds[i]! with
    | .recursive b j => return .data b j
    | .structural =>
      if let some t := (← get).memo[i]? then return t
      let node := (← get).nodes[i]!
      let t ← match node.ctors.size with
        | 0 => throwError "leanscript_signature: the type{indentExpr n}\nhas no constructor (it has no value)"
        | 1 =>
          let fs := node.ctors[0]!
          if fs.size = 0 then
            throwError "leanscript_signature: the type{indentExpr n}\nhas one constructor and no field (it has one value)"
          else if fs.size = 1 then toCIR fs[0]!
          else pure (.record (← toCIR fs[0]!) (← fs[1:].toArray.mapM toCIR))
        | m =>
          if node.ctors.all (·.isEmpty) && 3 ≤ m then pure (.enum m)
          else pure (.union (← node.ctors.mapM (·.mapM toCIR)))
      modify fun s => { s with memo := s.memo.insert i t }
      return t

/-- Does a type mention a member of the block? -/
partial def mentions (members : Array Nat) (e : Expr) : M Bool := do
  for n in ← occurrences e do
    if members.contains (← get).index[n]! then return true
  return false

/-- The translation of a field of a body. -/
partial def toFIR (members : Array Nat) (e : Expr) : M FIR := do
  unless ← mentions members e do return .old (← toCIR e)
  match ← classify e with
  | .node n => return .hole (← get).index[n]!
  | .fn a b =>
    if ← mentions members a then
      throwError "leanscript_signature: a recursive occurrence in the domain of a function{indentExpr e}"
    return .fn (← toCIR a) (← toFIR members b)
  | .array a => return .array (← toFIR members a)
  | .thunk _ =>
    throwError "leanscript_signature: a recursive occurrence under `Thunk` is not supported{indentExpr e}"
  | .prim _ => unreachable!

/-- The holes a field uses outside a guard. -/
def FIR.unguarded : FIR → List Nat
  | .hole i => [i]
  | .old _ => []
  | .array _ => []
  | .fn _ f => f.unguarded

/-! ## Printing -/

/-- A reference to member `j` of absolute block `b`, seen from `c` visible blocks. -/
def refStx (c b j : Nat) : MetaM Lean.Term := do
  let mut r ← `(Ref.here $(quote j))
  for _ in [0:c - 1 - b] do
    r ← `(Ref.there $r)
  return r

partial def CIR.stx (c : Nat) : CIR → MetaM Lean.Term
  | .prim p => `(Ty.prim $p)
  | .fn a b => do `(Ty.fn $(← a.stx c) $(← b.stx c))
  | .array a => do `(Ty.array $(← a.stx c))
  | .thunk a => do `(Ty.thunk $(← a.stx c))
  | .enum n => `(Ty.enum ⟨$(quote (n - 3)), 0⟩)
  | .record f fs => do `(Ty.record $(← f.stx c) $(← fieldsStx c fs.toList))
  | .union cs => do `(Ty.union $(← ctorsStx c cs.toList))
  | .data b j => do `(Ty.data $(← refStx c b j))
where
  fieldsStx (c : Nat) : List CIR → MetaM Lean.Term
    | [] => unreachable!
    | [t] => do `(Fields.one $(← t.stx c))
    | t :: ts => do `(Fields.cons $(← t.stx c) $(← fieldsStx c ts))
  ctorStx (c : Nat) (fs : Array CIR) : MetaM Lean.Term := do
    if fs.isEmpty then `(Ctor.nullary) else `(Ctor.fields $(← fieldsStx c fs.toList))
  ctorsStx (c : Nat) : List (Array CIR) → MetaM Lean.Term
    | [a, b] => do `(Ctors.two $(← ctorStx c a) $(← ctorStx c b))
    | a :: rest => do `(Ctors.cons $(← ctorStx c a) $(← ctorsStx c rest))
    | _ => unreachable!

partial def FIR.stx (c : Nat) (pos : Std.HashMap Nat Nat) : FIR → MetaM Lean.Term
  | .hole i => `(Fld.hole $(quote pos[i]!) (by decide))
  | .old t => do `(Fld.old $(← t.stx c))
  | .array f => do `(Fld.array $(← f.stx c pos))
  | .fn a f => do `(Fld.fn $(← a.stx c) $(← f.stx c pos))

def fldsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List FIR → MetaM Lean.Term
  | [] => unreachable!
  | [f] => do `(Flds.one $(← f.stx c pos))
  | f :: fs => do `(Flds.cons $(← f.stx c pos) $(← fldsStx c pos fs))

def bctorStx (c : Nat) (pos : Std.HashMap Nat Nat) (fs : Array FIR) : MetaM Lean.Term := do
  if fs.isEmpty then `(BCtor.nullary) else `(BCtor.fields $(← fldsStx c pos fs.toList))

def bctorsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List (Array FIR) → MetaM Lean.Term
  | [a, b] => do `(BCtors.two $(← bctorStx c pos a) $(← bctorStx c pos b))
  | a :: rest => do `(BCtors.cons $(← bctorStx c pos a) $(← bctorsStx c pos rest))
  | _ => unreachable!

/-- The constructors of a union whose base is constructor `p`. -/
def altsStx (c : Nat) (pos : Std.HashMap Nat Nat) : List (Array FIR) → Nat → MetaM Lean.Term
  | [a, b], 0 => do `(Alts.two₁ $(← bctorStx c pos a) $(← bctorStx c pos b))
  | [a, b], _ => do `(Alts.two₂ $(← bctorStx c pos a) $(← bctorStx c pos b))
  | a :: rest, 0 => do `(Alts.here $(← bctorStx c pos a) $(← bctorsStx c pos rest))
  | a :: rest, p + 1 => do `(Alts.there $(← bctorStx c pos a) $(← altsStx c pos rest p))
  | _, _ => unreachable!

/-- A block, seen from `nb` visible blocks. -/
def brefStx (nb b : Nat) : MetaM Lean.Term := do
  let mut r ← `(BRef.here)
  for _ in [0:nb - 1 - b] do
    r ← `(BRef.there $r)
  return r

/-- A field of a body as a closed type of the whole signature (its holes are names). -/
partial def FIR.fullStx (nb : Nat) (kinds : Array Kind) : FIR → MetaM Lean.Term
  | .hole i => match kinds[i]! with
    | .recursive b j => do `(Ty.data $(← refStx nb b j))
    | .structural => unreachable!
  | .old t => t.stx nb
  | .array f => do `(Ty.array $(← f.fullStx nb kinds))
  | .fn a f => do `(Ty.fn $(← a.stx nb) $(← f.fullStx nb kinds))

/-- Constructor `p` of `m` constructors, as a `CtorIx` of the unfolded union. -/
def ctorIxStx (m p : Nat) : MetaM Lean.Term := do
  let mut r ← if p + 2 < m then `(CtorIx.head) else if p + 2 = m then `(CtorIx.two₁) else `(CtorIx.two₂)
  for _ in [0:min p (m - 2)] do
    r ← `(CtorIx.tail $r)
  return r

/-- A list of terms as `Args`. -/
def argsStx (as : List Lean.Term) : MetaM Lean.Term := do
  let mut r ← `(Args.nil)
  for a in as.reverse do
    r ← `(Args.cons $a $r)
  return r

/-! ## The command -/

/-- One block: its member nodes in grounding order, and the base constructor of each. -/
structure Block where
  members : Array Nat
  bases : Array Nat
  fields : Array (Array (Array FIR))
  deriving Inhabited

/-- Order the members of a recursive SCC so that each has a constructor using only earlier
    members outside guards. -/
def groundingOrder (scc : Array Nat) (fields : Std.HashMap Nat (Array (Array FIR))) :
    M (Array Nat × Array Nat) := do
  let mut order : Array Nat := #[]
  let mut bases : Array Nat := #[]
  let mut progress := true
  while progress && order.size < scc.size do
    progress := false
    for m in scc do
      if order.contains m then continue
      let ctors := fields[m]!
      let ok (fs : Array FIR) : Bool := fs.all fun f => f.unguarded.all (order.contains ·)
      let base? := if ctors.size = 1 then (if ok ctors[0]! then some 0 else none)
        else (List.range ctors.size).find? (fun i => ok ctors[i]!)
      if let some b := base? then
        order := order.push m
        bases := bases.push b
        progress := true
        break
  if order.size < scc.size then
    let names ← scc.filter (!order.contains ·) |>.mapM fun m => do return m!"{(← get).nodes[m]!.ty}"
    throwError "leanscript_signature: these recursive types have no finite value (no grounding order): {names.toList}"
  return (order, bases)

/-- Run the whole translation. -/
def run (reqs : Array Expr) : M (Array Block × Array CIR × Array (Option Nat)) := do
  for r in reqs do discover r
  let n := (← get).nodes.size
  modify fun s => { s with kinds := Array.replicate n .structural }
  let mut succ : Array (Array Nat) := #[]
  for i in [0:n] do succ := succ.push (← successors i)
  let sccs := Lean.SCC.scc (List.range n) (fun i => succ[i]!.toList)
  -- order the SCCs so that every SCC comes after the ones it uses
  let mut placed : Array Nat := #[]
  let mut ordered : Array (List Nat) := #[]
  let mut rest := sccs
  while !rest.isEmpty do
    let some c := rest.find? (fun c => c.all fun i => succ[i]!.all fun j => c.contains j || placed.contains j)
      | throwError "leanscript_signature: internal error ordering the SCCs"
    ordered := ordered.push c
    placed := placed ++ c.toArray
    rest := rest.filter (· != c)
  let mut blocks : Array Block := #[]
  for c in ordered do
    let recursive := c.length > 1 || c.any fun i => succ[i]!.contains i
    unless recursive do continue
    let members := c.toArray
    let mut fields : Std.HashMap Nat (Array (Array FIR)) := {}
    for m in members do
      let node := (← get).nodes[m]!
      if node.ctors.size = 1 && node.ctors[0]!.isEmpty then
        throwError "leanscript_signature: the type{indentExpr node.ty}\nhas one constructor and no field"
      fields := fields.insert m (← node.ctors.mapM (·.mapM (toFIR members)))
    let (order, bases) ← groundingOrder members fields
    let b := blocks.size
    for j in [0:order.size] do
      modify fun s => { s with kinds := s.kinds.set! order[j]! (.recursive b j) }
    blocks := blocks.push { members := order, bases, fields := order.map (fields[·]!) }
  let tys ← reqs.mapM toCIR
  let info ← reqs.mapM fun r => do
    match ← classify r with
    | .node n =>
      let i := (← get).index[n]!
      match (← get).kinds[i]! with
      | .recursive _ _ => return some i
      | .structural => return none
    | _ => return none
  return (blocks, tys, info)

syntax leanscriptSigEntry := ident " := " term
syntax (name := leanscriptSignature)
  "leanscript_signature " ident " where" sepByIndentSemicolon(leanscriptSigEntry) : command

@[command_elab leanscriptSignature]
def elabSignature : CommandElab := fun stx => do
  let name : Ident := ⟨stx[1]⟩
  let entries := stx[3].getSepArgs
  let pairs : Array (Ident × Lean.Term) := entries.map fun e => (⟨e[0]⟩, ⟨e[2]⟩)
  let (blocks, tys, stxs) ← liftTermElabM do
    let reqs ← pairs.mapM fun (_, t) => do
      let e ← Term.elabType t
      Term.synthesizeSyntheticMVarsNoPostponing
      normType (← instantiateMVars e)
    let ((blocks, tys, info), st) ← (run reqs).run {}
    let nb := blocks.size
    let ksOf (c : Nat) : List Nat := ((blocks.toList.take c).map (·.members.size - 1)).reverse
    -- the blocks
    let mut out : Array (TSyntax `command) := #[]
    for b in [0:nb] do
      let B := blocks[b]!
      let pos : Std.HashMap Nat Nat := B.members.zipIdx.foldl (fun m (x, i) => m.insert x i) {}
      let mut mems ← `(Mems.nil)
      for j in (List.range B.members.size).reverse do
        let ctors := B.fields[j]!
        let d ← if ctors.size = 1 then
            let fs := ctors[0]!
            if fs.size = 1 then `(Decl.wrap $(← fs[0]!.stx b pos))
            else `(Decl.record $(← fs[0]!.stx b pos) $(← fldsStx b pos fs[1:].toArray.toList))
          else `(Decl.union $(← altsStx b pos ctors.toList B.bases[j]!))
        mems ← `(Mems.cons $d $mems)
      let bn := mkIdentFrom name (name.getId ++ Name.mkSimple s!"block{b}")
      let ksStx := quote (ksOf b)
      let k := B.members.size - 1
      out := out.push (← `(def $bn : Mems $ksStx ($(quote k) + 1) 0 := $mems))
    let ksAll := quote (ksOf nb)
    let ksName := mkIdentFrom name (name.getId ++ `ks)
    out := out.push (← `(abbrev $ksName : List Nat := $ksAll))
    let mut sig ← `(DSig.nil)
    for b in [0:nb] do
      let bn := mkIdentFrom name (name.getId ++ Name.mkSimple s!"block{b}")
      sig ← `(DSig.cons $sig $(quote (blocks[b]!.members.size - 1)) $bn)
    let sigName := mkIdentFrom name (name.getId ++ `Δ)
    out := out.push (← `(def $sigName : DSig $ksName := $sig))
    for i in [0:pairs.size] do
      let tn := mkIdentFrom name (name.getId ++ pairs[i]!.1.getId)
      out := out.push (← `(def $tn : Ty $ksName := $(← tys[i]!.stx nb)))
    -- the constructors of every requested recursive type
    for i in [0:pairs.size] do
      let some node := info[i]! | continue
      let .recursive b j := st.kinds[node]! | continue
      let B := blocks[b]!
      let ctors := B.fields[j]!
      let names := st.nodes[node]!.ctorNames
      let bstx ← brefStx nb b
      let tyName := mkIdentFrom name (name.getId ++ pairs[i]!.1.getId)
      for p in [0:ctors.size] do
        let fs := ctors[p]!
        let cn := mkIdentFrom name (name.getId ++ pairs[i]!.1.getId ++ Name.mkSimple (names[p]!.lastComponentAsString))
        let argNames : Array Ident := (Array.range fs.size).map fun q => mkIdent (Name.mkSimple s!"a{q}")
        let gam : Ident := mkIdent `Γ
        let argTys ← fs.mapM (·.fullStx nb st.kinds)
        let args : List Lean.Term := argNames.toList.map fun a => ⟨a.raw⟩
        let body ← if ctors.size = 1 then
            if fs.size = 1 then `(LeanScript.Nominal.Term.data_in $bstx $(quote j) $(args[0]!))
            else `(LeanScript.Nominal.Term.data_in $bstx $(quote j) (LeanScript.Nominal.Term.record_mk $(← argsStx args)))
          else `(LeanScript.Nominal.Term.data_in $bstx $(quote j)
            (LeanScript.Nominal.Term.union_mk $(← ctorIxStx ctors.size p) $(← argsStx args)))
        let mut ty ← `(LeanScript.Nominal.Term $sigName $gam $tyName)
        let mut fn := body
        for q in (List.range fs.size).reverse do
          ty ← `(($(argNames[q]!) : LeanScript.Nominal.Term $sigName $gam $(argTys[q]!)) → $ty)
          fn ← `(fun $(argNames[q]!) => $fn)
        ty ← `(∀ {$gam : Ctx $ksName}, $ty)
        fn ← `(fun {$gam} => $fn)
        out := out.push (← `(def $cn : $ty := $fn))
    return (blocks, tys, out)
  let _ := (blocks, tys)
  for c in stxs do elabCommand c

end LeanScript.Nominal.SigGen

end
