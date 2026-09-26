module

public meta import LeanScript.Gen.Read
public meta import Lean.Util.SCC

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Translating Lean types: strongly connected components and grounding

The second stage of the generators.  Starting from some Lean types, every inductive instance
reachable from them is a *node*.  The nodes are split into strongly connected components
(SCCs); an SCC with a cycle is a *block* of mutually recursive datatypes, declared once, in
a grounding order, with the first grounded constructor of each union as its base.  Every
other node is structural:

* one constructor of one field is that field (the wrapper is erased), of two or more fields
  a record;
* two or more constructors are a union when one of them has a field; with no field at all,
  two constructors are the leaf `bool` (false, true in declaration order) and three or more
  an enum.

The result is an intermediate form: closed types `CIR` (datatypes named by absolute block and
member, type variables by position) and body fields `FIR` (holes named by node).

A translation either *declares* new blocks (`leanscript_signature`) or runs against the
blocks of an already declared program (`ProgInfo`), and then refuses a recursive SCC that is
not declared there (`#leanscript_get_ty`, `#leanscript_get_ctor`).
-/

open Lean Meta Elab

namespace LeanScript.Gen

/-- A closed type, before it is printed. -/
inductive CIR where
  | prim (p : Lean.Term)
  | fn (a b : CIR)
  | array (a : CIR)
  /-- An enum of `n ≥ 3` constructors, the first printed as `shift`. -/
  | enum (n : Nat) (shift : Int)
  | record (f : CIR) (fs : Array CIR)
  | union (cs : Array (Array CIR))
  /-- Member `j` of the absolute block `b` (blocks counted oldest first). -/
  | data (b j : Nat)
  /-- Type variable number `i`. -/
  | var (i : Nat)
  deriving Inhabited

/-- Does a closed type name a declared datatype? -/
partial def CIR.hasData : CIR → Bool
  | .prim _ | .enum .. | .var _ => false
  | .data .. => true
  | .fn a b => a.hasData || b.hasData
  | .array a => a.hasData
  | .record f fs => f.hasData || fs.any CIR.hasData
  | .union cs => cs.any (·.any CIR.hasData)

/-- A field of a body: holes are named by node. -/
inductive FIR where
  | hole (node : Nat)
  | old (t : CIR)
  | array (f : FIR)
  | fn (a : CIR) (f : FIR)
  deriving Inhabited

/-- The holes a field uses outside a guard. -/
def FIR.unguarded : FIR → List Nat
  | .hole i => [i]
  | .old _ => []
  | .array _ => []
  | .fn _ f => f.unguarded

/-- A declared program: the Lean type instances that are the members of its blocks (oldest
    block first, members in grounding order). -/
structure ProgInfo where
  /-- The program's name: `Prog.ks`, `Prog.Δ` are its block sizes and signature. -/
  name : Name
  /-- The members of each block. -/
  members : Array (Array Expr)
  deriving Inhabited

/-- The block sizes of a program's signature, newest first. -/
def ProgInfo.ks (p : ProgInfo) : List Nat :=
  (p.members.toList.map (·.size - 1)).reverse

/-- One Lean type instance reached from the requested types. -/
structure Node where
  ty : Expr
  /-- The constructors (names and relevant fields); empty for a node of a declared block of
      the program, which is never unfolded. -/
  ctors : Array (Name × Array Expr) := #[]
  deriving Inhabited

/-- How a node is translated. -/
inductive Kind where
  | structural
  | recursive (b j : Nat)
  deriving Inhabited

/-- One block: its member nodes in grounding order, the base constructor of each, and the
    fields of each member's constructors. -/
structure Block where
  members : Array Nat
  bases : Array Nat
  fields : Array (Array (Array FIR))
  deriving Inhabited

/-- The state of one translation. -/
structure St where
  nodes : Array Node := #[]
  index : Std.HashMap Expr Nat := {}
  kinds : Std.HashMap Nat Kind := {}
  /-- The type variables, in the order they are numbered. -/
  vars : Array FVarId := #[]
  /-- The structural translation of a non-recursive node, once computed. -/
  memo : Std.HashMap Nat CIR := {}
  /-- The number of blocks declared before this translation (those of the program). -/
  oldBlocks : Nat := 0

abbrev M := StateT St MetaM

/-- Start a translation against a program: its members are nodes of known kind. -/
def St.ofProg (vars : Array FVarId) : Option ProgInfo → St
  | none => { vars }
  | some p => Id.run do
    let mut s : St := { vars, oldBlocks := p.members.size }
    for b in [0:p.members.size] do
      let ms := p.members[b]!
      for j in [0:ms.size] do
        let i := s.nodes.size
        let e := ms[j]!
        s := { s with nodes := s.nodes.push { ty := e },
                      index := s.index.insert e i,
                      kinds := s.kinds.insert i (.recursive b j) }
    return s

/-- The kind of a node. -/
def kindOf (i : Nat) : M Kind := return (← get).kinds.getD i .structural

/-- Discover every node reachable from a type. -/
partial def discover (e : Expr) : M Unit := do
  for n in ← occurrences e do
    if (← get).index.contains n then continue
    let i := (← get).nodes.size
    modify fun s => { s with nodes := s.nodes.push { ty := n }, index := s.index.insert n i }
    let ctors ← readCtors n
    modify fun s => { s with nodes := s.nodes.set! i { ty := n, ctors } }
    for (_, fs) in ctors do
      for f in fs do discover f

/-- The nodes a node's fields mention directly. -/
def successors (i : Nat) : M (Array Nat) := do
  let s ← get
  let mut out := #[]
  for (_, fs) in s.nodes[i]!.ctors do
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
  | .var x =>
    let some i := (← get).vars.idxOf? x | fail m!"unknown type variable{indentExpr e}"
    return .var i
  | .node n =>
    let i := (← get).index[n]!
    match ← kindOf i with
    | .recursive b j => return .data b j
    | .structural =>
      if let some t := (← get).memo[i]? then return t
      let node := (← get).nodes[i]!
      let t ← match node.ctors.size with
        | 0 => fail m!"the type{indentExpr n}\nhas no constructor (it has no value)"
        | 1 =>
          let fs := node.ctors[0]!.2
          if fs.size = 0 then
            fail m!"the type{indentExpr n}\nhas one constructor and no field (it has one value)"
          else if fs.size = 1 then toCIR fs[0]!
          else pure (.record (← toCIR fs[0]!) (← fs[1:].toArray.mapM toCIR))
        | m =>
          if node.ctors.all (·.2.isEmpty) then
            -- two points are `bool`, three or more an enum: never a union
            if m = 2 then pure (.prim (← `(LeanPrimTy.bool)))
            else pure (.enum m (enumShift n.getAppFn.constName!))
          else pure (.union (← node.ctors.mapM (·.2.mapM toCIR)))
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
      fail m!"a recursive occurrence in the domain of a function{indentExpr e}"
    return .fn (← toCIR a) (← toFIR members b)
  | .array a => return .array (← toFIR members a)
  | .prim _ | .var _ => unreachable!

/-- Order the members of a recursive SCC so that each has a constructor using only earlier
    members outside guards; return the order and the base constructor of each member. -/
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
    let names ← scc.filter (!order.contains ·) |>.mapM fun m => do
      return m!"{(← get).nodes[m]!.ty}"
    fail m!"these recursive types have no finite value (no grounding order): {names.toList}"
  return (order, bases)

/-- Split the newly discovered nodes into SCCs and declare every recursive one as a block
    (numbered after the program's blocks).  With `declare := false`, a recursive SCC is an
    error: it is not a datatype of the program. -/
def declareBlocks (declare : Bool) (prog : Option Name) : M (Array Block) := do
  let s ← get
  let fresh := (List.range s.nodes.size).filter fun i => !s.kinds.contains i
  let mut succ : Std.HashMap Nat (Array Nat) := {}
  for i in fresh do succ := succ.insert i (← successors i)
  let sccs := Lean.SCC.scc fresh (fun i => (succ.getD i #[]).toList.filter fresh.contains)
  -- order the SCCs so that every SCC comes after the ones it uses
  let mut placed : Array Nat := #[]
  let mut ordered : Array (List Nat) := #[]
  let mut rest := sccs
  while !rest.isEmpty do
    let some c := rest.find? (fun c => c.all fun i =>
        (succ.getD i #[]).all fun j => c.contains j || placed.contains j || !fresh.contains j)
      | fail m!"internal error ordering the SCCs"
    ordered := ordered.push c
    placed := placed ++ c.toArray
    rest := rest.filter (· != c)
  let mut blocks : Array Block := #[]
  for c in ordered do
    let recursive := c.length > 1 || c.any fun i => (succ.getD i #[]).contains i
    unless recursive do continue
    let members := c.toArray
    let tys := members.map fun m => (s.nodes[m]!).ty
    if tys.any (·.hasFVar) then
      fail m!"the layout of{indentExpr tys[0]!}\nis recursive and depends on a type parameter; \
        fix the parameter with a named argument `(α := …)`"
    unless declare do
      let where_ := match prog with
        | some p => m!"in the signature `{p}`; add it to `leanscript_signature {p}`"
        | none => m!"in any signature; declare it with `leanscript_signature`"
      fail m!"the recursive type{indentExpr tys[0]!}\nis not declared {where_}"
    let mut fields : Std.HashMap Nat (Array (Array FIR)) := {}
    for m in members do
      let node := (← get).nodes[m]!
      if node.ctors.size = 1 && node.ctors[0]!.2.isEmpty then
        fail m!"the type{indentExpr node.ty}\nhas one constructor and no field"
      fields := fields.insert m (← node.ctors.mapM (·.2.mapM (toFIR members)))
    let (order, bases) ← groundingOrder members fields
    let b := (← get).oldBlocks + blocks.size
    for j in [0:order.size] do
      modify fun s => { s with kinds := s.kinds.insert order[j]! (.recursive b j) }
    blocks := blocks.push { members := order, bases, fields := order.map (fields[·]!) }
  return blocks

end LeanScript.Gen

end
