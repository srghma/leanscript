module

public import JsTerm.Syntax.Vars

@[expose] public section

set_option autoImplicit false

/-!
# Updating arrays in place: the array operations, and linear variables

The first half of the analysis of `MoreJs.inPlace` (`JsTerm.Passes.InPlace`): which operations
build or update an array (`JsOpImported.buildsArray`, `JsOpImported.updatesArray`), which types
hold no array (`JsTy.shareFree`), and whether a variable is **linear** after a point
(`linearFrom`): on every path it is read at most once before it is assigned again, never in a
closure, and never in a loop that does not assign it first.
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
  ["lean_array_set_immutable", "lean_array_swap_immutable", "lean_array_fset_immutable",
   "lean_array_fswap_immutable"].any (nameHas op.name)

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

end MoreJs

end
