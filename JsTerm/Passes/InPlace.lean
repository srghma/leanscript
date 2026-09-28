module

public import JsTerm.Syntax.Vars

@[expose] public section

set_option autoImplicit false

/-!
# Updating arrays in place

The runtime functions of the array externs (`array__lean_array_push_immutable`,
`uint53__lean_array_set_immutable`, `bigint_nat__lean_array_swap_immutable`,
`array__lean_array_pop_immutable`, …) never mutate their argument: they answer with a copy,
since the argument may be referred to elsewhere.  When nothing else refers to it, and nothing
reads it afterwards, the copy is wasted work (a loop pushing `n` elements copies `O(n²)` of
them), and the backend calls the mutable operation instead (`array__lean_array_push_mutable`,
`uint53__lean_array_set_mutable`, …: an `effectful` constructor of the same signature,
`JsOpImported.toMutable?`), which mutates the array and answers with it.  (`push` and `pop`
have a mutable version on generic arrays only: a typed array cannot grow or shrink.)

The pass (`inPlace`) works on the body of one function.  It tells the variables apart by
numbering their binders in the order it meets them, and computes the variables that **own**
their value:

* a variable is **linear** (`linearFrom`) when, on every path from its definition (or from
  any assignment to it), it is read at most once before it is assigned again, never in a
  closure, and never in a loop that does not assign it first;
* a variable **owns** its value when it is linear and every value it is given is *fresh*
  (`freshValue`): a value of a type without arrays (`JsTy.shareFree`: numbers, strings,
  booleans, enums, and records and unions of those), an array just built (a literal, an
  operation answering with a new array: `…__lean_array_push`, `…__lean_mk_array`, `[]`,
  `Uint8Array.from(a)`, …), an owned variable (read for the last time), an update
  (`…__lean_array_set`, `…__lean_array_swap`) of an owned variable, an inlined operation
  answering with its argument (`Array.mk` on generic arrays) of a fresh value, a field of a
  record or union that an owned variable holds, or a record or union all of whose fields are
  fresh.  Nothing else refers to an array an owning variable holds (directly, or through the
  fields of the records and unions it holds).

The variables are the constants (`const`, the fields of a pattern, the value of a join point,
defined by every jump to it) and the mutable variables (`let`, and every assignment); the
parameters of the function, of its closures and the elements of the loops are never owned.
The owners are the greatest set closed under these rules (a variable is dropped until nothing
changes).  Then every copying update on an owning variable `v` becomes the in-place update:
the call is the last read of `v`, and nothing else refers to the array.

Records and unions are never mutated.  The pass runs before the constants of the module are
shared (`MoreJs.hoistConsts`), which never shares an array.
-/

namespace MoreJs

/-! ## The array operations -/

/-- Does the name of an operation contain `part`? -/
def nameHas (name part : String) : Bool := (name.splitOn part).length > 1

/-- Does the imported operation answer with an array it has just built, whatever its
    arguments? -/
def JsOpImported.buildsArray {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpImported e t σs τ) : Bool :=
  ["lean_array_push", "lean_array_pop", "lean_mk_array", "lean_array_to_list",
   "lean_string_data"].any (nameHas op.name)

/-- Does the imported operation answer with a copy of the array it is given (or that array
    itself, when an index is out of bounds)? -/
def JsOpImported.updatesArray {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpImported e t σs τ) : Bool :=
  ["lean_array_set_immutable", "lean_array_swap_immutable"].any (nameHas op.name)

/-- Is every value of the type free of arrays (so that no two values of it can share a mutable
    part)?  Numbers, strings, booleans, enums, and records and unions of those. -/
partial def JsTy.shareFree : JsTy → Bool
  | .terminal _ | .enum .. => true
  | .record f₁ f₂ fs => (f₁ :: f₂ :: fs).all JsTy.shareFree
  | .union c₀ c₁ cs => (c₀ :: c₁ :: cs).all (·.all JsTy.shareFree)
  | _ => false

/-! ## Reads -/

/-- The number of reads of the variable `x` in an expression; `none` when one of them is
    inside a closure. -/
def JsExpr.readsOf {C M : List JsTy} {τ : JsTy} (x : JsVar) (e : JsExpr C M τ) : Option Nat :=
  let os := e.occs.filter (·.is x)
  if os.any (·.inClosure) then none else some os.size

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

/-- What the paths of a block end in, for a variable: a read too many somewhere (`bad`), the
    state at the ends of the iteration (`next`), and at the jumps (by the de Bruijn index of
    their join point). -/
structure LinRes where
  bad : Bool := false
  nexts : LinSt := .bot
  jumps : List (Nat × LinSt) := []
  deriving Inhabited

/-- The ends of two sets of paths. -/
def LinRes.merge (a b : LinRes) : LinRes :=
  { bad := a.bad || b.bad, nexts := a.nexts.join b.nexts, jumps := a.jumps ++ b.jumps }

/-- A read too many. -/
def LinRes.isBad : LinRes := { bad := true }

/-- The states at the jumps to the join point of index `0`, and the others one level up. -/
def popJumps (js : List (Nat × LinSt)) : LinSt × List (Nat × LinSt) :=
  (js.foldl (fun s (j, s') => if j == 0 then s.join s' else s) .bot,
   js.filterMap fun (j, s) => if j == 0 then none else some (j - 1, s))

mutual
/-- The ends of the paths of a block for the variable `x`, from the state `s`. -/
partial def linB {C M J : List JsTy} {k : JsEnd} (x : JsVar) (s : LinSt) :
    JsBlock C M J k → LinRes
  | .ret e => if s.read (e.readsOf x) == .bad then .isBad else {}
  | .next => { nexts := s }
  | .jump j e =>
    let s := s.read (e.readsOf x)
    if s == .bad then .isBad else { jumps := [(j.index, s)] }
  | .throw _ => {}
  | .const _ e rest => linThen x s (e.readsOf x) fun s => linB (x.under 1 0) s rest
  | .letMut _ e rest => linThen x s (e.readsOf x) fun s => linB (x.under 0 1) s rest
  | .assign y e rest => linThen x s (e.readsOf x) fun s =>
    linB x (if x.isMut && x.idx == y.index then .fresh else s) rest
  | .destructure (us := us) e _ rest =>
    linThen x s (e.readsOf x) fun s => linB (x.under us.length 0) s rest
  | .ite c t e => linThen x s (c.readsOf x) fun s => (linB x s t).merge (linB x s e)
  | .enumCases e arms => linThen x s (e.readsOf x) fun s => linEnumArms x s arms
  | .unionCases e arms => linThen x s (e.readsOf x) fun s => linUnionArms x s arms
  | .join _ b rest =>
    let r := linB x s b
    if r.bad then .isBad else
    let (s₀, others) := popJumps r.jumps
    let r' : LinRes := if s₀ == .bot then {} else linB (x.under 1 0) s₀ rest
    ({ nexts := r.nexts, jumps := others } : LinRes).merge r'
  | .forRange _ _ n body rest => linThen x s (n.readsOf x) fun s =>
    linLoop x s (body.mentions (x.under 1 0)) (linB (x.under 1 0) .fresh body) rest
  | .forOf _ _ xs body rest => linThen x s (xs.readsOf x) fun s =>
    linLoop x s (body.mentions (x.under 1 0)) (linB (x.under 1 0) .fresh body) rest
  | .lastIter _ _ n body rest => linThen x s (n.readsOf x) fun s =>
    let r := linB (x.under 1 0) s body
    if r.bad then .isBad else linB x (s.join r.nexts) rest

/-- Read the variable `n` times, then go on (unless it is read too often). -/
partial def linThen (_x : JsVar) (s : LinSt) (n : Option Nat) (k : LinSt → LinRes) : LinRes :=
  let s := s.read n
  if s == .bad then .isBad else k s

/-- A loop whose body (`mentions`: does it mention the variable; `body`: its ends from a fresh
    state) is run any number of times, then `rest`: the variable must be fresh when an
    iteration starts, if the body mentions it, and again at the end of every iteration. -/
partial def linLoop {C M J : List JsTy} {k : JsEnd} (x : JsVar) (s : LinSt) (mentions : Bool)
    (body : LinRes) (rest : JsBlock C M J k) : LinRes :=
  if !mentions then linB x s rest else
  if s == .bot then linB x .bot rest else
  if s != .fresh then .isBad else
  if !body.bad && (body.nexts == .fresh || body.nexts == .bot) then linB x .fresh rest
  else .isBad

/-- `linB` of the arms of an enum's case analysis. -/
partial def linEnumArms {C M J : List JsTy} {k : JsEnd} {n : Nat} (x : JsVar) (s : LinSt) :
    JsEnumArms C M J k n → LinRes
  | .nil => {}
  | .cons b rest => (linB x s b).merge (linEnumArms x s rest)

/-- `linB` of the arms of a union's case analysis (each under the fields it binds). -/
partial def linUnionArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (x : JsVar)
    (s : LinSt) : JsUnionArms C M J k cs → LinRes
  | .nil => {}
  | .cons (us := us) _ b rest => (linB (x.under us.length 0) s b).merge (linUnionArms x s rest)
end

/-- Is `x`, given a value just before the block `rest` (seen from the start of `rest`), linear
    in it? -/
def linearFrom {C M J : List JsTy} {k : JsEnd} (x : JsVar) (rest : JsBlock C M J k) : Bool :=
  !(linB x .fresh rest).bad

/-! ## Definitions

The variables of a function body are told apart by a number, given to each binder in the
order the walk meets it; the walk keeps, for every de Bruijn index in scope, the number of its
binder (`InEnv`; `none` for a variable bound outside the body). -/

/-- The binders in scope, by their numbers: the constants, the mutable variables and the join
    points (innermost first). -/
structure InEnv where
  c : List (Option Nat) := []
  m : List (Option Nat) := []
  joins : List (Option Nat) := []
  deriving Inhabited

/-- The number of the binder of a variable, if it is bound inside the body. -/
def InEnv.uidOf? {C M : List JsTy} {τ : JsTy} (env : InEnv) : JsExpr C M τ → Option Nat
  | .cvar x => (env.c[x.index]?).bind id
  | .mvar x => (env.m[x.index]?).bind id
  | _ => none

/-- Is the expression a variable bound inside the body, of a number in `xs`? -/
def InEnv.isIn {C M : List JsTy} {τ : JsTy} (env : InEnv) (xs : List Nat) (e : JsExpr C M τ) :
    Bool :=
  match env.uidOf? e with
  | some u => xs.contains u
  | none => false

/-- The number of the variable the first argument is, if any. -/
def InEnv.firstArgUid {C M σs : List JsTy} (env : InEnv) : JsArgs C M σs → Option Nat
  | .cons a _ => env.uidOf? a
  | .nil => none

mutual
/-- Is the value of an expression fresh (see the module documentation), given the owning
    variables `own` (the expression seen from the binders `env`)? -/
partial def freshValue {C M : List JsTy} {τ : JsTy} (own : List Nat) (env : InEnv)
    (e : JsExpr C M τ) : Bool :=
  τ.shareFree ||
  match e with
  | .array_mk .. | .list_mk .. => true
  | .cvar _ | .mvar _ => env.isIn own e
  | .imported op args =>
    op.buildsArray || (op.updatesArray && (env.firstArgUid args).any own.contains)
  | .inlined op args => freshTemplate own env args op.template
  | .record_mk fs => freshArgs own env fs
  | .union_mk _ as => freshArgs own env as
  | .cond _ a b => freshValue own env a && freshValue own env b
  | _ => false

/-- Are all the arguments fresh? -/
partial def freshArgs {C M σs : List JsTy} (own : List Nat) (env : InEnv) :
    JsArgs C M σs → Bool
  | .nil => true
  | .cons a as => freshValue own env a && freshArgs own env as

/-- Is the value of an inlined operation of template `t` on the arguments `args` fresh? -/
partial def freshTemplate {C M σs : List JsTy} (own : List Nat) (env : InEnv)
    (args : JsArgs C M σs) : JsInline → Bool
  | .emptyArray | .new .. => true
  | .call f _ => f.endsWith ".from"
  | .arg i => freshNth own env args i
  | _ => false

/-- Is the argument of position `i` fresh? -/
partial def freshNth {C M σs : List JsTy} (own : List Nat) (env : InEnv) :
    JsArgs C M σs → Nat → Bool
  | .nil, _ => false
  | .cons a _, 0 => freshValue own env a
  | .cons _ as, i + 1 => freshNth own env as i
end

/-- How a variable is given a value: whether the value is fresh, given the owning variables. -/
abbrev DefOf := List Nat → Bool

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

/-- A new binder, not given a value yet (the value of a join point). -/
def newUidNoDef : InM Nat :=
  modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- A value given to the variable `x`. -/
def addDef (x : Nat) (d : DefOf) : InM Unit :=
  modify fun s => { s with defs := s.defs.push (x, d) }

/-- The variable `x` is linear if `b`. -/
def addLinearIf (x : Nat) (b : Bool) : InM Unit :=
  if b then modify fun s => { s with linear := s.linear.push x } else pure ()

/-- A never-owned binder (a parameter, a counter, an element of a loop). -/
def otherUid : InM Nat := newUid fun _ => false

/-- A part of the body, rebuilt once the owning variables (their numbers) are known. -/
abbrev Rebuild (α : Type) := List Nat → α

/-- The binders of the fields a pattern keeps (`n` of them, in order), each a field of the
    value of `e`, linear or not in `rest`: their numbers, in order. -/
def fieldUids {C M C' M' J : List JsTy} {k : JsEnd} {τ : JsTy} (env : InEnv) (e : JsExpr C M τ)
    (n : Nat) (rest : JsBlock C' M' J k) : InM (List Nat) := do
  let mut uids : List Nat := []
  for i in [0:n] do
    let u ← newUid fun own => env.isIn own e
    addLinearIf u (linearFrom ⟨false, n - 1 - i⟩ rest)
    uids := uids ++ [u]
  return uids

mutual
/-- Collect the definitions inside an expression (each closure is a scope of its own; its
    parameter is never owned), and rebuild it. -/
partial def collectE {C M : List JsTy} {τ : JsTy} (env : InEnv) :
    JsExpr C M τ → InM (Rebuild (JsExpr C M τ))
  | .imported op args => do
    let fa ← collectA env args
    let y? := env.firstArgUid args
    return fun own =>
      let as := fa own
      match op.toMutable?, y? with
      | some ⟨_, op'⟩, some y => if own.contains y then .imported op' as else .imported op as
      | _, _ => .imported op as
  | .inlined op args => do
    let fa ← collectA env args
    return fun own => .inlined op (fa own)
  | .app f as => do
    let ff ← collectE env f
    let fa ← collectA env as
    return fun own => .app (ff own) (fa own)
  | .lam (σs := σs) xs b => do
    let mut c := env.c
    for _ in σs do
      c := some (← otherUid) :: c
    let fb ← collectB { c, m := env.m } b
    return fun own => .lam xs (fb own)
  | .record_mk fs => do
    let fa ← collectA env fs
    return fun own => .record_mk (fa own)
  | .union_mk ix as => do
    let fa ← collectA env as
    return fun own => .union_mk ix (fa own)
  | .array_mk l ps => do
    let fp ← collectP env ps
    return fun own => .array_mk l (fp own)
  | .list_mk ps => do
    let fp ← collectP env ps
    return fun own => .list_mk (fp own)
  | .cond c a b => do
    let fc ← collectE env c
    let fa ← collectE env a
    let fb ← collectE env b
    return fun own => .cond (fc own) (fa own) (fb own)
  | e => return fun _ => e

/-- `collectE` of arguments. -/
partial def collectA {C M σs : List JsTy} (env : InEnv) :
    JsArgs C M σs → InM (Rebuild (JsArgs C M σs))
  | .nil => return fun _ => .nil
  | .cons a as => do
    let fa ← collectE env a
    let fs ← collectA env as
    return fun own => .cons (fa own) (fs own)

/-- `collectE` of the parts of an array literal. -/
partial def collectP {C M : List JsTy} {A E : JsTy} (env : InEnv) :
    JsParts C M A E → InM (Rebuild (JsParts C M A E))
  | .nil => return fun _ => .nil
  | .elem e rest => do
    let fe ← collectE env e
    let fr ← collectP env rest
    return fun own => .elem (fe own) (fr own)
  | .spread a rest => do
    let fa ← collectE env a
    let fr ← collectP env rest
    return fun own => .spread (fa own) (fr own)

/-- Collect the linear variables of a block and the values given to every variable, and
    rebuild it. -/
partial def collectB {C M J : List JsTy} {k : JsEnd} (env : InEnv) :
    JsBlock C M J k → InM (Rebuild (JsBlock C M J k))
  | .ret e => do
    let fe ← collectE env e
    return fun own => .ret (fe own)
  | .next => return fun _ => .next
  | .jump j e => do
    let fe ← collectE env e
    if let some (some u) := env.joins[j.index]? then addDef u fun own => freshValue own env e
    return fun own => .jump j (fe own)
  | .throw msg => return fun _ => .throw msg
  | .const x e rest => do
    let fe ← collectE env e
    let u ← newUid fun own => freshValue own env e
    addLinearIf u (linearFrom ⟨false, 0⟩ rest)
    let fr ← collectB { env with c := some u :: env.c } rest
    return fun own => .const x (fe own) (fr own)
  | .letMut x e rest => do
    let fe ← collectE env e
    let u ← newUid fun own => freshValue own env e
    addLinearIf u (linearFrom ⟨true, 0⟩ rest)
    let fr ← collectB { env with m := some u :: env.m } rest
    return fun own => .letMut x (fe own) (fr own)
  | .assign x e rest => do
    let fe ← collectE env e
    if let some (some u) := env.m[x.index]? then addDef u fun own => freshValue own env e
    let fr ← collectB env rest
    return fun own => .assign x (fe own) (fr own)
  | .destructure (us := us) e sel rest => do
    let fe ← collectE env e
    let uids ← fieldUids env e us.length rest
    let fr ← collectB { env with c := uids.reverse.map some ++ env.c } rest
    return fun own => .destructure (fe own) sel (fr own)
  | .ite c t e => do
    let fc ← collectE env c
    let ft ← collectB env t
    let fe ← collectB env e
    return fun own => .ite (fc own) (ft own) (fe own)
  | .enumCases e arms => do
    let fe ← collectE env e
    let fa ← collectEnumArms env arms
    return fun own => .enumCases (fe own) (fa own)
  | .unionCases e arms => do
    let fe ← collectE env e
    let fa ← collectUnionArms env e arms
    return fun own => .unionCases (fe own) (fa own)
  | .join x b rest => do
    let u ← newUidNoDef
    addLinearIf u (linearFrom ⟨false, 0⟩ rest)
    let fb ← collectB { env with joins := some u :: env.joins } b
    let fr ← collectB { env with c := some u :: env.c } rest
    return fun own => .join x (fb own) (fr own)
  | .forRange x nt n b rest => do
    let fn ← collectE env n
    let u ← otherUid
    let fb ← collectB { c := some u :: env.c, m := env.m } b
    let fr ← collectB env rest
    return fun own => .forRange x nt (fn own) (fb own) (fr own)
  | .lastIter x nt n b rest => do
    let fn ← collectE env n
    let u ← otherUid
    let fb ← collectB { c := some u :: env.c, m := env.m } b
    let fr ← collectB env rest
    return fun own => .lastIter x nt (fn own) (fb own) (fr own)
  | .forOf x l xs b rest => do
    let fxs ← collectE env xs
    let u ← otherUid
    let fb ← collectB { c := some u :: env.c, m := env.m } b
    let fr ← collectB env rest
    return fun own => .forOf x l (fxs own) (fb own) (fr own)

/-- `collectB` of the arms of an enum's case analysis. -/
partial def collectEnumArms {C M J : List JsTy} {k : JsEnd} {n : Nat} (env : InEnv) :
    JsEnumArms C M J k n → InM (Rebuild (JsEnumArms C M J k n))
  | .nil => return fun _ => .nil
  | .cons b rest => do
    let fb ← collectB env b
    let fr ← collectEnumArms env rest
    return fun own => .cons (fb own) (fr own)

/-- `collectB` of the arms of a union's case analysis on `e`: each binds fields of `e`. -/
partial def collectUnionArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} {τ : JsTy}
    (env : InEnv) (e : JsExpr C M τ) :
    JsUnionArms C M J k cs → InM (Rebuild (JsUnionArms C M J k cs))
  | .nil => return fun _ => .nil
  | .cons (us := us) sel b rest => do
    let uids ← fieldUids env e us.length b
    let fb ← collectB { env with c := uids.reverse.map some ++ env.c } b
    let fr ← collectUnionArms env e rest
    return fun own => .cons sel (fb own) (fr own)
end

/-! ## The owners, and the rewrite -/

/-- The greatest set of variables all of whose definitions satisfy their predicate (given the
    set). -/
partial def greatestFix (defs : Array (Nat × DefOf)) (start : List Nat) : List Nat :=
  let next := start.filter fun x => defs.all fun (y, d) => y != x || d start
  if next.length == start.length then start else greatestFix defs next

/-- Update in place the arrays nothing else refers to, in the body of a function. -/
def inPlace {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  let (build, st) := (collectB {} b).run {}
  let cands := st.linear.toList.eraseDups.filter fun x => st.defs.any (·.1 == x)
  let own := greatestFix st.defs cands
  if own.isEmpty then b else build own

end MoreJs

end
