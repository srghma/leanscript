module

public import JsTerm.Syntax

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

The pass (`inPlaceStmts`) works on the statements of one function, whose names are all
distinct.  It computes the variables that **own** their value (`owned`):

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

/-! ## Walking the grammar -/

mutual
/-- The number of reads of `x` in an expression that are not `x.tag`; `none` when one of them
    is inside a closure. -/
partial def JsExpr.readsOf (x : String) : JsExpr → Option Nat
  | .var y => some (if y == x then 1 else 0)
  | .member (.var _) "tag" => some 0
  | .lit _ => some 0
  | .arrow _ b => if b.any (·.mentionsVar x) then none else some 0
  | .bin _ a b | .at a b => do return (← a.readsOf x) + (← b.readsOf x)
  | .un _ a | .index a _ | .member a _ | .spread a => a.readsOf x
  | .call f as => do return (← f.readsOf x) + (← sumReads x as)
  | .helper _ as | .array as | .typedArray _ as => sumReads x as
  | .new c as => do return (← c.readsOf x) + (← sumReads x as)
  | .cond c a b => do return (← c.readsOf x) + (← a.readsOf x) + (← b.readsOf x)
  | .object fs => sumReads x (fs.map (·.2))
/-- `JsExpr.readsOf` of several expressions. -/
partial def sumReads (x : String) : List JsExpr → Option Nat
  | [] => some 0
  | e :: es => do return (← e.readsOf x) + (← sumReads x es)
/-- Does a statement mention the variable `x` at all? -/
partial def JsStmt.mentionsVar (x : String) : JsStmt → Bool
  | .const y e | .assign y e => y == x || e.mentionsVar x
  | .letMut y e => y == x || e.any (·.mentionsVar x)
  | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e | .expr e => e.mentionsVar x
  | .setMember o _ e => o.mentionsVar x || e.mentionsVar x
  | .setAt o i e => o.mentionsVar x || i.mentionsVar x || e.mentionsVar x
  | .while c b => c.mentionsVar x || b.any (·.mentionsVar x)
  | .ite c t e => c.mentionsVar x || t.any (·.mentionsVar x) || e.any (·.mentionsVar x)
  | .forRange _ _ n b => n.mentionsVar x || b.any (·.mentionsVar x)
  | .forOf _ xs b => xs.mentionsVar x || b.any (·.mentionsVar x)
  | .throw _ _ => false
  | .join y b => y == x || b.any (·.mentionsVar x)
/-- Does an expression mention the variable `x`? -/
partial def JsExpr.mentionsVar (x : String) : JsExpr → Bool
  | .var y => y == x
  | .lit _ => false
  | .arrow _ b => b.any (·.mentionsVar x)
  | .bin _ a b | .at a b => a.mentionsVar x || b.mentionsVar x
  | .un _ a | .index a _ | .member a _ | .spread a => a.mentionsVar x
  | .call f as => f.mentionsVar x || as.any (·.mentionsVar x)
  | .helper _ as | .array as | .typedArray _ as => as.any (·.mentionsVar x)
  | .new c as => c.mentionsVar x || as.any (·.mentionsVar x)
  | .cond c a b => c.mentionsVar x || a.mentionsVar x || b.mentionsVar x
  | .object fs => fs.any (·.2.mentionsVar x)
end

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

mutual
/-- The state of the variable `x` after a statement, from the state `s`; `joins` are the
    variables of the enclosing join points (innermost first); with the states at the jumps
    out of the enclosing join blocks. -/
partial def linStmt (x : String) (joins : List String) (s : LinSt) : JsStmt → LinSt × JumpSts
  | .const _ e | .destructure _ e | .destructureObj _ e | .expr e => (s.read (e.readsOf x), [])
  | .letMut y e =>
    let s := match e with
      | some e => s.read (e.readsOf x)
      | none => s
    (if y == x then .fresh else s, [])
  | .assign y e =>
    let s := s.read (e.readsOf x)
    (if y == x && s != .bad then .fresh else s, [])
  | .setMember o _ e => (s.read (o.readsOf x) |>.read (e.readsOf x), [])
  | .setAt o i e => (s.read (o.readsOf x) |>.read (i.readsOf x) |>.read (e.readsOf x), [])
  | .ret e => (if s.read (e.readsOf x) == .bad then .bad else .bot, [])
  | .throw _ _ => (.bot, [])
  | .jump j e =>
    let s := s.read (e.readsOf x)
    let s := if joins[j]? == some x && s != .bad then .fresh else s
    (if s == .bad then .bad else .bot, [(j, s)])
  | .ite c t e =>
    let s := s.read (c.readsOf x)
    let (s₁, j₁) := linStmts x joins s t
    let (s₂, j₂) := linStmts x joins s e
    (s₁.join s₂, j₁ ++ j₂)
  | .forRange _ _ n b => linLoop x joins (s.read (n.readsOf x)) b
  | .forOf _ xs b => linLoop x joins (s.read (xs.readsOf x)) b
  | .while c b => linLoop x joins s (.expr c :: b)
  | .join y b =>
    let (s', js) := linStmts x (y :: joins) s b
    let (sj, js') := js.pop
    (s'.join sj, js')
/-- A loop whose body is `b`: the variable must be fresh when an iteration starts, if the
    body mentions it. -/
partial def linLoop (x : String) (joins : List String) (s : LinSt) (b : List JsStmt) :
    LinSt × JumpSts :=
  if !b.any (·.mentionsVar x) then (s, []) else
  if s == .bot then (.bot, []) else
  if s != .fresh then (.bad, []) else
  let (s', js) := linStmts x joins .fresh b
  if (s' == .fresh || s' == .bot) && js.all (fun (_, s) => s != .bad) then (.fresh, js)
  else (.bad, [])
/-- `linStmt` of a block. -/
partial def linStmts (x : String) (joins : List String) (s : LinSt) :
    List JsStmt → LinSt × JumpSts
  | [] => (s, [])
  | st :: rest =>
    if s == .bad then (.bad, []) else
    let (s₁, j₁) := linStmt x joins s st
    let (s₂, j₂) := linStmts x joins s₁ rest
    (s₂, j₁ ++ j₂)
end

/-- Is `x`, given a value just before the statements `rest` (in a function whose join points
    around them are `joins`), linear in them? -/
def linearFrom (x : String) (joins : List String) (rest : List JsStmt) : Bool :=
  let (s, js) := linStmts x joins .fresh rest
  s != .bad && js.all (fun (_, s) => s != .bad)

/-! ## Definitions -/

/-- How a variable is given a value. -/
inductive DefOf where
  /-- `const x = e`, `let x = e`, `x = e`, or a jump to the join point of variable `x`. -/
  | expr (e : JsExpr)
  /-- A field of the record or union `s` holds (`const { _1: x } = s`). -/
  | field (s : JsExpr)
  /-- A counter of a counting loop (a number or a `BigInt`). -/
  | counter
  /-- Anything else: a parameter, an element of an array, … -/
  | other
  deriving Inhabited

/-- The linear variables of a block and the values given to every variable, collected in
    `acc`; `joins` are the variables of the enclosing join points. -/
partial def collectDefs (joins : List String) (acc : Array (String × DefOf) × Array String) :
    List JsStmt → Array (String × DefOf) × Array String
  | [] => acc
  | st :: rest =>
    let lin (xs : List String) (acc : Array (String × DefOf) × Array String) :=
      (acc.1, acc.2 ++ (xs.filter fun x => linearFrom x joins rest).toArray)
    let inner (acc : Array (String × DefOf) × Array String) : Array (String × DefOf) × Array String :=
      match st with
      | .const x e => lin [x] (collectE (acc.1.push (x, .expr e), acc.2) e)
      | .letMut x e =>
        let acc := match e with
          | some e => collectE (acc.1.push (x, .expr e), acc.2) e
          | none => acc
        lin [x] acc
      | .assign x e => collectE (acc.1.push (x, .expr e), acc.2) e
      | .destructureObj bs e =>
        lin (bs.map (·.2)) (collectE (acc.1 ++ (bs.map fun (_, x) => (x, DefOf.field e)).toArray, acc.2) e)
      | .destructure xs e =>
        collectE (acc.1 ++ (xs.filterMap id |>.map fun x => (x, DefOf.other)).toArray, acc.2) e
      | .jump j e =>
        let acc := collectE acc e
        match joins[j]? with
        | some x => (acc.1.push (x, .expr e), acc.2)
        | none => acc
      | .ite c t e => collectDefs joins (collectDefs joins (collectE acc c) t) e
      | .forRange i _ n b => collectDefs joins (collectE (acc.1.push (i, .counter), acc.2) n) b
      | .forOf x xs b => collectDefs joins (collectE (acc.1.push (x, .other), acc.2) xs) b
      | .while c b => collectDefs joins (collectE acc c) b
      | .join x b => collectDefs (x :: joins) acc b
      | .ret e | .expr e => collectE acc e
      | .setMember o _ e => collectE (collectE acc o) e
      | .setAt o i e => collectE (collectE (collectE acc o) i) e
      | .throw _ _ => acc
    collectDefs joins (inner acc) rest
where
  /-- The definitions inside the closures of an expression (each body is a scope of its own;
      its parameters are `other`). -/
  collectE (acc : Array (String × DefOf) × Array String) : JsExpr → Array (String × DefOf) × Array String
    | .arrow ps b => collectDefs [] (acc.1 ++ (ps.map fun p => (p, DefOf.other)).toArray, acc.2) b
    | .bin _ a b | .at a b => collectE (collectE acc a) b
    | .un _ a | .index a _ | .member a _ | .spread a => collectE acc a
    | .call f as => as.foldl collectE (collectE acc f)
    | .helper _ as | .array as | .typedArray _ as => as.foldl collectE acc
    | .new c as => as.foldl collectE (collectE acc c)
    | .cond c a b => collectE (collectE (collectE acc c) a) b
    | .object fs => fs.foldl (fun acc (_, e) => collectE acc e) acc
    | _ => acc

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
    that hold one? -/
partial def primitive (prim : List String) : JsExpr → Bool
  | .lit _ | .bin .. | .un .. => true
  | .member _ "tag" | .member _ "length" => true
  | .var y => prim.contains y
  | .cond _ a b => primitive prim a && primitive prim b
  | .helper h _ => (h.startsWith "$lean_" || h == "Char_ofNatAux" || h == "UInt64_toBitVec") &&
      !structuredResultFns.contains h
  | _ => false

/-- Is the value of an expression fresh (see the module documentation), given the owning
    variables `own` and the variables `prim` holding a primitive? -/
partial def freshValue (own prim : List String) : JsExpr → Bool
  | .array _ | .typedArray _ _ | .new _ _ => true
  | .var y => own.contains y
  | .helper h args =>
    freshArrayFns.contains h ||
      (updateArrayFns.contains h && match args with
        | .var y :: _ => own.contains y
        | _ => false)
  | .object fs => fs.all fun (_, e) => freshValue own prim e || primitive prim e
  | .cond _ a b => freshValue own prim a && freshValue own prim b
  | _ => false

/-- The greatest set of variables all of whose definitions satisfy `ok` (given the set). -/
partial def greatestFix (defs : Array (String × DefOf)) (start : List String)
    (ok : List String → DefOf → Bool) : List String :=
  let next := start.filter fun x => defs.all fun (y, d) => y != x || ok start d
  if next.length == start.length then start else greatestFix defs next ok

/-- The variables of a function body that own their value. -/
def owned (body : List JsStmt) : List String :=
  let (defs, linear) := collectDefs [] (#[], #[]) body
  let names := (defs.map (·.1)).toList.eraseDups
  let prim := greatestFix defs names fun prim d => match d with
    | .expr e => primitive prim e
    | .counter => true
    | _ => false
  let cands := linear.toList.eraseDups.filter fun x => defs.any (·.1 == x)
  greatestFix defs cands fun own d => match d with
    | .expr e => freshValue own prim e
    | .field (.var s) => own.contains s
    | _ => false

/-! ## The rewrite -/

/-- The in-place version of a runtime function that copies an array, if it has one. -/
def inPlaceName? : String → Option String
  | "$lean_array_push" => some "$lean_array_push_inplace"
  | "$lean_array_set" | "$lean_array_fset" => some "$lean_array_set_inplace"
  | "$lean_array_swap" | "$lean_array_fswap" => some "$lean_array_swap_inplace"
  | "$lean_array_pop" => some "$lean_array_pop_inplace"
  | _ => none

mutual
/-- Call the in-place versions on the owning variables `own`, in an expression. -/
partial def inPlaceE (own : List String) : JsExpr → JsExpr
  | .helper h args =>
    let args := args.map (inPlaceE own)
    match inPlaceName? h, args with
    | some h', .var y :: _ => if own.contains y then .helper h' args else .helper h args
    | _, _ => .helper h args
  | .bin op a b => .bin op (inPlaceE own a) (inPlaceE own b)
  | .un op a => .un op (inPlaceE own a)
  | .call f as => .call (inPlaceE own f) (as.map (inPlaceE own))
  | .arrow ps b => .arrow ps (b.map (inPlaceS own))
  | .array es => .array (es.map (inPlaceE own))
  | .typedArray c es => .typedArray c (es.map (inPlaceE own))
  | .index e i => .index (inPlaceE own e) i
  | .member e m => .member (inPlaceE own e) m
  | .cond c a b => .cond (inPlaceE own c) (inPlaceE own a) (inPlaceE own b)
  | .object fs => .object (fs.map fun (k, e) => (k, inPlaceE own e))
  | .at e i => .at (inPlaceE own e) (inPlaceE own i)
  | .new c as => .new (inPlaceE own c) (as.map (inPlaceE own))
  | .spread e => .spread (inPlaceE own e)
  | e => e
/-- Call the in-place versions on the owning variables `own`, in a statement. -/
partial def inPlaceS (own : List String) : JsStmt → JsStmt
  | .const x e => .const x (inPlaceE own e)
  | .letMut x e => .letMut x (e.map (inPlaceE own))
  | .assign x e => .assign x (inPlaceE own e)
  | .destructure xs e => .destructure xs (inPlaceE own e)
  | .destructureObj xs e => .destructureObj xs (inPlaceE own e)
  | .setMember o m e => .setMember (inPlaceE own o) m (inPlaceE own e)
  | .setAt o i e => .setAt (inPlaceE own o) (inPlaceE own i) (inPlaceE own e)
  | .expr e => .expr (inPlaceE own e)
  | .while c b => .while (inPlaceE own c) (b.map (inPlaceS own))
  | .ret e => .ret (inPlaceE own e)
  | .ite c t e => .ite (inPlaceE own c) (t.map (inPlaceS own)) (e.map (inPlaceS own))
  | .forRange i big n b => .forRange i big (inPlaceE own n) (b.map (inPlaceS own))
  | .forOf x xs b => .forOf x (inPlaceE own xs) (b.map (inPlaceS own))
  | .throw k m => .throw k m
  | .join x b => .join x (b.map (inPlaceS own))
  | .jump j e => .jump j (inPlaceE own e)
end

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

/-- Update in place the arrays nothing else refers to, in the body of a function (whose names
    are all distinct). -/
def inPlaceStmts (body : List JsStmt) : List JsStmt :=
  let own := owned body
  if own.isEmpty then body else body.map (inPlaceS own)

end MoreJs

end
