module

public import JsTerm.Passes.InPlace.Linear

@[expose] public section

set_option autoImplicit false

/-!
# Updating arrays in place: the definitions of the variables

The second half of the analysis of `MoreJs.inPlace` (`JsTerm.Passes.InPlace`): one walk over
the body of a function (`collectB`) numbers the binders, records for every variable whether it
is linear and, for each of its definitions, the condition under which the value it is given
is fresh (`freshValue`), and returns the body rebuilt for any set of owning variables.

The variables of a function body are told apart by a number, given to each binder in the
order the walk meets it; the walk keeps, for every de Bruijn index in scope, the number of its
binder (`InEnv`; `none` for a variable bound outside the body).
-/

namespace MoreJs

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
  | .listOp op as => do
    let fa ← collectA env as
    return fun own => .listOp op (fa own)
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

end MoreJs

end
