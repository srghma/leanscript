module

public import JsTerm.Vars

@[expose] public section

set_option autoImplicit false

/-!
# Updating arrays in place

The runtime functions of the array externs (`$lean_array_push`, `$lean_array_set`,
`$lean_array_swap`, `$lean_array_pop`) never mutate their argument: they answer with a copy,
since the argument may be referred to elsewhere.  When nothing else refers to it, and nothing
reads it afterwards, the copy is wasted work (a loop pushing `n` elements copies `O(n²)` of
them), and the backend calls the `_inplace` version instead (`$lean_array_push_inplace`, …),
which mutates the array and answers with it.

The pass (`inPlaceStmts`) works on the statements of one function.  It tells the variables
apart by numbering their binders in the order it meets them, and computes the variables that
**own** their value (`owned`):

* a variable is **linear** (`linearFrom`) when, on every path from its definition (or from
  any assignment to it), it is read at most once before it is assigned again, never in a
  closure, and never in a loop that does not assign it first (a read of `v.tag`, the tag of a
  union, does not count: a tag is never changed);
* a variable **owns** its value when it is linear and every value it is given is *fresh*: an
  array just built (a literal, `new`, `$lean_array_push`, `$lean_array_pop`,
  `$lean_mk_array`, …), an owned variable (read for the last time), an update
  (`$lean_array_set`, `$lean_array_swap`) of an owned variable, a field of a record or union
  that an owned variable holds, or a record or union all of whose fields are fresh or
  primitive (numbers, strings, booleans: `primitive`).  Nothing else refers to an array an
  owning variable holds (directly, or through the fields of the records and unions it holds).

The owners are the greatest set closed under these rules (a variable is dropped until nothing
changes).  Then every call `$lean_array_push(v, …)` (and `_set`, `_swap`, `_pop`) on an
owning variable `v` becomes `$lean_array_push_inplace(v, …)`: the call is the last read of
`v`, and nothing else refers to the array.

Records and unions are never mutated, so the tag of a union another variable still refers to
stays valid.  The pass must run before the constants of the module are shared
(`MoreJs.hoistConsts`), which never shares an array.
-/

namespace MoreJs

/-! ## Reads -/

/-- The number of reads of the variable `x` in an expression that are not `x.tag`; `none` when
    one of them is inside a closure. -/
def JsExpr.readsOf (x : JsVar) (e : JsExpr) : Option Nat :=
  let os := e.occs.filter (·.is x)
  if os.any (·.inClosure) then none else some (os.filter (!·.tag)).size

/-! ## Linear variables -/

/-- The state of a variable along a path: not reached (`bot`), holding a value not read yet
    (`fresh`), read once since it was last given a value (`used`), or read too often (`bad`). -/
inductive LinSt where
  | bot | fresh | used | bad
  deriving Inhabited, BEq, Repr

/-- The state after two paths meet. -/
def LinSt.join : LinSt → LinSt → LinSt
  | .bot, s | s, .bot => s
  | .bad, _ | _, .bad => .bad
  | .used, _ | _, .used => .used
  | .fresh, .fresh => .fresh

/-- The state after `n` reads (`none`: a read in a closure). -/
def LinSt.read (s : LinSt) : Option Nat → LinSt
  | none => .bad
  | some 0 => s
  | some n => match s with
    | .bot => .bot
    | .fresh => if n == 1 then .used else .bad
    | _ => .bad

/-- The states at the jumps out of a block, by the de Bruijn index of their join point. -/
abbrev JumpSts := List (Nat × LinSt)

/-- The states at the jumps to the join point of index `0`, and the others one level up. -/
def JumpSts.pop (js : JumpSts) : LinSt × JumpSts :=
  (js.foldl (fun s (j, s') => if j == 0 then s.join s' else s) .bot,
   js.filterMap fun (j, s) => if j == 0 then none else some (j - 1, s))

/-- Is the mutable variable of index `y` the variable `x`? -/
def JsVar.isMutIdx (x : JsVar) (y : Nat) : Bool := x.isMut && x.idx == y

mutual
/-- The state of the variable `x` after a statement, from the state `s`; `joins` are the
    (indices of the) mutable variables of the enclosing join points, innermost first; with the
    states at the jumps out of the enclosing join blocks. -/
partial def linStmt (x : JsVar) (joins : List (Option Nat)) (s : LinSt) : JsStmt → LinSt × JumpSts
  | .const _ e | .destructure _ e | .destructureObj _ e | .expr e => (s.read (e.readsOf x), [])
  | .letMut _ e =>
    (match e with
      | some e => s.read (e.readsOf x)
      | none => s, [])
  | .assign y e =>
    let s := s.read (e.readsOf x)
    (if x.isMutIdx y && s != .bad then .fresh else s, [])
  | .setMember o _ e => (s.read (o.readsOf x) |>.read (e.readsOf x), [])
  | .setAt o i e => (s.read (o.readsOf x) |>.read (i.readsOf x) |>.read (e.readsOf x), [])
  | .ret e => (if s.read (e.readsOf x) == .bad then .bad else .bot, [])
  | .throw _ _ => (.bot, [])
  | .jump j e =>
    let s := s.read (e.readsOf x)
    let s := if ((joins[j]?.bind id).map x.isMutIdx) == some true && s != .bad then .fresh
      else s
    (if s == .bad then .bad else .bot, [(j, s)])
  | .ite c t e =>
    let s := s.read (c.readsOf x)
    let (s₁, j₁) := linStmts x joins s t
    let (s₂, j₂) := linStmts x joins s e
    (s₁.join s₂, j₁ ++ j₂)
  | .forRange _ _ n b => linLoop (x.under 1 0) joins (s.read (n.readsOf x)) b
  | .forOf _ xs b => linLoop (x.under 1 0) joins (s.read (xs.readsOf x)) b
  | .while c b => linLoop x joins s (.expr c :: b)
  | .join y b =>
    let (s', js) := linStmts x (some y :: joins) s b
    let (sj, js') := js.pop
    (s'.join sj, js')
/-- A loop whose body is `b` (`x` and `joins` seen from inside it): the variable must be fresh
    when an iteration starts, if the body mentions it. -/
partial def linLoop (x : JsVar) (joins : List (Option Nat)) (s : LinSt) (b : List JsStmt) :
    LinSt × JumpSts :=
  if !mentionsIn x b then (s, []) else
  if s == .bot then (.bot, []) else
  if s != .fresh then (.bad, []) else
  let (s', js) := linStmts x joins .fresh b
  if (s' == .fresh || s' == .bot) && js.all (fun (_, s) => s != .bad) then (.fresh, js)
  else (.bad, [])
/-- `linStmt` of a block (the variable and the join points seen from its start). -/
partial def linStmts (x : JsVar) (joins : List (Option Nat)) (s : LinSt) :
    List JsStmt → LinSt × JumpSts
  | [] => (s, [])
  | st :: rest =>
    if s == .bad then (.bad, []) else
    let (s₁, j₁) := linStmt x joins s st
    let (s₂, j₂) := linStmts (x.after st) (joins.map (·.map (· + st.bindsM))) s₁ rest
    (s₂, j₁ ++ j₂)
end

/-- Is `x`, given a value just before the statements `rest` (whose enclosing join points
    assign the mutable variables `joins`; all seen from the start of `rest`), linear in
    them? -/
def linearFrom (x : JsVar) (joins : List (Option Nat)) (rest : List JsStmt) : Bool :=
  let (s, js) := linStmts x joins .fresh rest
  s != .bad && js.all (fun (_, s) => s != .bad)

/-! ## Definitions

The variables of a function body are told apart by a number, given to each binder in the
order the walk meets it; the walk keeps, for every de Bruijn index in scope, the number of its
binder (`InEnv`). -/

/-- The binders in scope, by their numbers: the constants and the mutable variables (innermost
    first), and the variables of the enclosing join points (innermost first; `none` for one
    bound outside the body). -/
structure InEnv where
  c : List Nat := []
  m : List Nat := []
  joins : List (Option Nat) := []
  deriving Inhabited

/-- The number of the binder of a variable, if it is bound inside the body (a parameter of the
    function is not). -/
def InEnv.uidOf? (env : InEnv) : JsExpr → Option Nat
  | .cvar i => env.c[i]?
  | .mvar i => env.m[i]?
  | _ => none

/-- Is the expression a variable bound inside the body, of a number in `xs`? -/
def InEnv.isIn (env : InEnv) (xs : List Nat) (e : JsExpr) : Bool :=
  match env.uidOf? e with
  | some u => xs.contains u
  | none => false

/-- How a variable is given a value. -/
inductive DefOf where
  /-- `const x = e`, `let x = e`, `x = e`, or a jump to the join point of variable `x`
      (`e` seen from the binders `env`). -/
  | expr (e : JsExpr) (env : InEnv)
  /-- A field of the record or union `s` holds (`const { _1: x } = s`). -/
  | field (s : JsExpr) (env : InEnv)
  /-- A counter of a counting loop (a number or a `BigInt`). -/
  | counter
  /-- Anything else: a parameter of a closure, an element of an array, … -/
  | other
  deriving Inhabited

/-- What the walk collects: the next number, the values given to every variable, and the
    linear variables. -/
structure InSt where
  next : Nat := 0
  defs : Array (Nat × DefOf) := #[]
  linear : Array Nat := #[]

/-- The walk. -/
abbrev InM := StateM InSt

/-- A new binder, given its first value. -/
def newUid (d : DefOf) : InM Nat :=
  modifyGet fun s => (s.next, { s with next := s.next + 1, defs := s.defs.push (s.next, d) })

/-- A new binder, not given a value yet (`let x;`). -/
def newUidNoDef : InM Nat :=
  modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- A value given to the variable `x`. -/
def addDef (x : Nat) (d : DefOf) : InM Unit :=
  modify fun s => { s with defs := s.defs.push (x, d) }

/-- The variable `x` is linear. -/
def addLinear (x : Nat) : InM Unit :=
  modify fun s => { s with linear := s.linear.push x }

/-- The in-place version of a runtime function that copies an array, if it has one. -/
def inPlaceName? : String → Option String
  | "$lean_array_push" => some "$lean_array_push_inplace"
  | "$lean_array_set" | "$lean_array_fset" => some "$lean_array_set_inplace"
  | "$lean_array_swap" | "$lean_array_fswap" => some "$lean_array_swap_inplace"
  | "$lean_array_pop" => some "$lean_array_pop_inplace"
  | _ => none

/-- A part of the body, rebuilt once the owning variables (their numbers) are known: every
    copying update of an array an owning variable holds becomes the in-place update. -/
abbrev Rebuild (α : Type) := List Nat → α

mutual
/-- Collect the definitions inside the closures of an expression (each body is a scope of its
    own; its parameters are `other`), and rebuild it. -/
partial def collectE (env : InEnv) : JsExpr → InM (Rebuild JsExpr)
  | .helper h as => do
    let bs ← collectEs env as
    let y? := as.head?.bind env.uidOf?
    return fun own =>
      let as := bs own
      match inPlaceName? h, y? with
      | some h', some y => if own.contains y then .helper h' as else .helper h as
      | _, _ => .helper h as
  | .arrow ps b => do
    let uids ← ps.mapM fun _ => newUid .other
    let fb ← collectStmts { c := uids.reverse ++ env.c, m := env.m, joins := [] } b
    return fun own => .arrow ps (fb own)
  | .bin op a b => do
    let fa ← collectE env a
    let fb ← collectE env b
    return fun own => .bin op (fa own) (fb own)
  | .un op a => do
    let fa ← collectE env a
    return fun own => .un op (fa own)
  | .call f as => do
    let ff ← collectE env f
    let fs ← collectEs env as
    return fun own => .call (ff own) (fs own)
  | .array es => do
    let fs ← collectEs env es
    return fun own => .array (fs own)
  | .typedArray c es => do
    let fs ← collectEs env es
    return fun own => .typedArray c (fs own)
  | .index e i => do
    let fe ← collectE env e
    return fun own => .index (fe own) i
  | .member e m => do
    let fe ← collectE env e
    return fun own => .member (fe own) m
  | .cond c a b => do
    let fc ← collectE env c
    let fa ← collectE env a
    let fb ← collectE env b
    return fun own => .cond (fc own) (fa own) (fb own)
  | .object fs => do
    let ks := fs.map (·.1)
    let fes ← collectEs env (fs.map (·.2))
    return fun own => .object (ks.zip (fes own))
  | .at e i => do
    let fe ← collectE env e
    let fi ← collectE env i
    return fun own => .at (fe own) (fi own)
  | .new c as => do
    let fc ← collectE env c
    let fs ← collectEs env as
    return fun own => .new (fc own) (fs own)
  | .spread e => do
    let fe ← collectE env e
    return fun own => .spread (fe own)
  | e => return fun _ => e

/-- `collectE` of several expressions. -/
partial def collectEs (env : InEnv) : List JsExpr → InM (Rebuild (List JsExpr))
  | [] => return fun _ => []
  | e :: es => do
    let fe ← collectE env e
    let fs ← collectEs env es
    return fun own => fe own :: fs own

/-- Collect the linear variables of a block and the values given to every variable, and
    rebuild it. -/
partial def collectStmts (env : InEnv) : List JsStmt → InM (Rebuild (List JsStmt))
  | [] => return fun _ => []
  | st :: rest => do
    -- the (indices of the) variables of the enclosing join points, seen from `rest`
    let joinsAfter : List (Option Nat) := env.joins.map fun u? =>
      (u?.bind env.m.idxOf?).map (· + st.bindsM)
    let (fst, newUids) ← collectStmt env st joinsAfter rest
    let env' : InEnv :=
      if st.bindsM > 0 then { env with m := newUids.reverse ++ env.m }
      else { env with c := newUids.reverse ++ env.c }
    let fr ← collectStmts env' rest
    return fun own => fst own :: fr own

/-- One statement of a block, followed by `rest` (`joinsAfter`: the variables of the enclosing
    join points seen from `rest`): the statement rebuilt, and the numbers of the variables it
    binds for `rest`, in order. -/
partial def collectStmt (env : InEnv) (st : JsStmt) (joinsAfter : List (Option Nat))
    (rest : List JsStmt) : InM (Rebuild JsStmt × List Nat) := do
  match st with
  | .const x e =>
    let fe ← collectE env e
    let u ← newUid (.expr e env)
    if linearFrom ⟨false, 0⟩ joinsAfter rest then addLinear u
    return (fun own => .const x (fe own), [u])
  | .letMut x (some e) =>
    let fe ← collectE env e
    let u ← newUid (.expr e env)
    if linearFrom ⟨true, 0⟩ joinsAfter rest then addLinear u
    return (fun own => .letMut x (some (fe own)), [u])
  | .letMut x none =>
    let u ← newUidNoDef
    if linearFrom ⟨true, 0⟩ joinsAfter rest then addLinear u
    return (fun _ => .letMut x none, [u])
  | .assign x e =>
    let fe ← collectE env e
    if let some u := env.m[x]? then addDef u (.expr e env)
    return (fun own => .assign x (fe own), [])
  | .destructureObj bs e =>
    let fe ← collectE env e
    let uids ← bs.mapM fun _ => newUid (.field e env)
    let n := bs.length
    for (u, k) in uids.zipIdx do
      if linearFrom ⟨false, n - 1 - k⟩ joinsAfter rest then addLinear u
    return (fun own => .destructureObj bs (fe own), uids)
  | .destructure xs e =>
    let fe ← collectE env e
    let uids ← (xs.filterMap id).mapM fun _ => newUid .other
    return (fun own => .destructure xs (fe own), uids)
  | .jump j e =>
    let fe ← collectE env e
    if let some (some u) := env.joins[j]? then addDef u (.expr e env)
    return (fun own => .jump j (fe own), [])
  | .ite c t e =>
    let fc ← collectE env c
    let ft ← collectStmts env t
    let fe ← collectStmts env e
    return (fun own => .ite (fc own) (ft own) (fe own), [])
  | .forRange i big n b =>
    let fn ← collectE env n
    let u ← newUid .counter
    let fb ← collectStmts { env with c := u :: env.c } b
    return (fun own => .forRange i big (fn own) (fb own), [])
  | .forOf x xs b =>
    let fxs ← collectE env xs
    let u ← newUid .other
    let fb ← collectStmts { env with c := u :: env.c } b
    return (fun own => .forOf x (fxs own) (fb own), [])
  | .while c b =>
    let fc ← collectE env c
    let fb ← collectStmts env b
    return (fun own => .while (fc own) (fb own), [])
  | .join x b =>
    -- a join point whose variable is not bound inside the body has no number: its jumps
    -- define nothing the pass tracks
    let fb ← collectStmts { env with joins := env.m[x]? :: env.joins } b
    return (fun own => .join x (fb own), [])
  | .ret e =>
    let fe ← collectE env e
    return (fun own => .ret (fe own), [])
  | .expr e =>
    let fe ← collectE env e
    return (fun own => .expr (fe own), [])
  | .setMember o m e =>
    let fo ← collectE env o
    let fe ← collectE env e
    return (fun own => .setMember (fo own) m (fe own), [])
  | .setAt o i e =>
    let fo ← collectE env o
    let fi ← collectE env i
    let fe ← collectE env e
    return (fun own => .setAt (fo own) (fi own) (fe own), [])
  | .throw k m => return (fun _ => .throw k m, [])
end

/-! ## Fresh values -/

/-- The runtime functions that answer with an array they have just built, whatever their
    arguments. -/
def freshArrayFns : List String :=
  ["$lean_array_push", "$lean_array_pop", "$lean_mk_array", "$lean_mk_typed_array",
   "$lean_array_to_list", "$lean_string_data"]

/-- The runtime functions that answer with a copy of the array they are given, or with that
    array itself (when an index is out of bounds). -/
def updateArrayFns : List String :=
  ["$lean_array_set", "$lean_array_fset", "$lean_array_swap", "$lean_array_fswap"]

/-- The runtime functions that may answer with an array, a record or a union (anything that is
    not a number, a string or a boolean). -/
def structuredResultFns : List String :=
  freshArrayFns ++ updateArrayFns ++
    ["$lean_array_get", "$lean_array_get_borrowed", "$lean_thunk_get_own", "$lean_thunk_pure",
     "$lean_mk_thunk", "$lean_float_frexp", "$lean_float32_frexp", "$lean_extern_unimplemented"]

/-- Is the value of an expression a number, a string or a boolean, given the variables `prim`
    that hold one (by number; the expression seen from the binders `env`)? -/
partial def primitive (prim : List Nat) (env : InEnv) : JsExpr → Bool
  | .lit _ | .bin .. | .un .. => true
  | .member _ "tag" | .member _ "length" => true
  | e@(.cvar _) | e@(.mvar _) => env.isIn prim e
  | .cond _ a b => primitive prim env a && primitive prim env b
  | .helper h _ => (h.startsWith "$lean_" || h == "Char_ofNatAux" || h == "UInt64_toBitVec") &&
      !structuredResultFns.contains h
  | _ => false

/-- Is the value of an expression fresh (see the module documentation), given the owning
    variables `own` and the variables `prim` holding a primitive (by number; the expression
    seen from the binders `env`)? -/
partial def freshValue (own prim : List Nat) (env : InEnv) : JsExpr → Bool
  | .array _ | .typedArray _ _ | .new _ _ => true
  | e@(.cvar _) | e@(.mvar _) => env.isIn own e
  | .helper h args =>
    freshArrayFns.contains h ||
      (updateArrayFns.contains h && match args with
        | a :: _ => env.isIn own a
        | _ => false)
  | .object fs => fs.all fun (_, e) => freshValue own prim env e || primitive prim env e
  | .cond _ a b => freshValue own prim env a && freshValue own prim env b
  | _ => false

/-- The greatest set of variables all of whose definitions satisfy `ok` (given the set). -/
partial def greatestFix (defs : Array (Nat × DefOf)) (start : List Nat)
    (ok : List Nat → DefOf → Bool) : List Nat :=
  let next := start.filter fun x => defs.all fun (y, d) => y != x || ok start d
  if next.length == start.length then start else greatestFix defs next ok

/-- The variables of a function body that own their value (by number), and the body, to be
    rebuilt for them. -/
def owned (body : List JsStmt) : List Nat × Rebuild (List JsStmt) :=
  let (build, st) := (collectStmts {} body).run {}
  let names := (st.defs.map (·.1)).toList.eraseDups
  let prim := greatestFix st.defs names fun prim d => match d with
    | .expr e env => primitive prim env e
    | .counter => true
    | _ => false
  let cands := st.linear.toList.eraseDups.filter fun x => st.defs.any (·.1 == x)
  let own := greatestFix st.defs cands fun own d => match d with
    | .expr e env => freshValue own prim env e
    | .field s env => env.isIn own s
    | _ => false
  (own, build)

/-! ## The rewrite -/

mutual
/-- The runtime functions an expression calls. -/
partial def JsExpr.calls : JsExpr → List String
  | .helper h as => h :: as.flatMap JsExpr.calls
  | .arrow _ b => b.flatMap JsStmt.calls
  | .bin _ a b | .at a b => a.calls ++ b.calls
  | .un _ a | .index a _ | .member a _ | .spread a => a.calls
  | .call f as | .new f as => f.calls ++ as.flatMap JsExpr.calls
  | .array as | .typedArray _ as => as.flatMap JsExpr.calls
  | .cond c a b => c.calls ++ a.calls ++ b.calls
  | .object fs => fs.flatMap (·.2.calls)
  | _ => []
/-- The runtime functions a statement calls. -/
partial def JsStmt.calls : JsStmt → List String
  | .const _ e | .assign _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e
  | .expr e => e.calls
  | .letMut _ e => (e.map JsExpr.calls).getD []
  | .setMember o _ e => o.calls ++ e.calls
  | .setAt o i e => o.calls ++ i.calls ++ e.calls
  | .while c b => c.calls ++ b.flatMap JsStmt.calls
  | .ite c t e => c.calls ++ t.flatMap JsStmt.calls ++ e.flatMap JsStmt.calls
  | .forRange _ _ n b => n.calls ++ b.flatMap JsStmt.calls
  | .forOf _ xs b => xs.calls ++ b.flatMap JsStmt.calls
  | .throw _ _ => []
  | .join _ b => b.flatMap JsStmt.calls
end

/-- The runtime functions a body calls, each once. -/
def calledHelpers (body : List JsStmt) : List String :=
  (body.flatMap JsStmt.calls).eraseDups

/-- Update in place the arrays nothing else refers to, in the body of a function. -/
def inPlaceStmts (body : List JsStmt) : List JsStmt :=
  let (own, build) := owned body
  if own.isEmpty then body else build own

end MoreJs

end
