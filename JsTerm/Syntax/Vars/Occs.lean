module

public import JsTerm.Syntax.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Occurrences of the variables of the JavaScript grammar

`JsBlock.occs`: every read and assignment of a variable, with whether it is inside a closure
or a loop (where it may be evaluated more than once).
-/

namespace MoreJs

variable {S : JsSig}

/-- An occurrence of a variable: a constant or a mutable variable, by its de Bruijn index
    where the walk started; whether it is an assignment, inside a closure, or inside a loop or
    a closure (evaluated possibly more than once). -/
structure JsOcc where
  isMut : Bool
  idx : Nat
  write : Bool := false
  inClosure : Bool := false
  again : Bool := false
  /-- The function called (`x(…)`). -/
  callee : Bool := false
  deriving Inhabited, Repr

/-- A variable, where a walk started: a constant or a mutable variable, by its index. -/
structure JsVar where
  isMut : Bool
  idx : Nat
  deriving Inhabited, BEq, Repr

/-- Is the occurrence one of the variable? -/
def JsOcc.is (o : JsOcc) (x : JsVar) : Bool := o.isMut == x.isMut && o.idx == x.idx

/-- The variable, seen from under `dc` more constants and `dm` more mutable variables. -/
def JsVar.under (x : JsVar) (dc dm : Nat) : JsVar :=
  if x.isMut then { x with idx := x.idx + dm } else { x with idx := x.idx + dc }

/-- Where a walk is: how many constants and mutable variables it went under, and whether it
    is inside a closure, or a loop or a closure. -/
structure OccCtx where
  dc : Nat := 0
  dm : Nat := 0
  inClosure : Bool := false
  again : Bool := false

namespace OccCtx

/-- Under `c` more constants and `m` more mutable variables. -/
def under (o : OccCtx) (c m : Nat) : OccCtx := { o with dc := o.dc + c, dm := o.dm + m }

/-- Inside a closure (under `c` more constants). -/
def closure (o : OccCtx) (c : Nat) : OccCtx :=
  { o with dc := o.dc + c, inClosure := true, again := true }

/-- Inside the body of a counting-down loop (under its counter, a mutable variable). -/
def countLoop (o : OccCtx) : OccCtx := { o with dm := o.dm + 1, again := true }

/-- Inside the body of a loop (under `c` more constants). -/
def loop (o : OccCtx) (c : Nat) : OccCtx := { o with dc := o.dc + c, again := true }

/-- An occurrence of the constant of index `i` here (none if it is bound inside the walk). -/
def cOcc (o : OccCtx) (i : Nat) (write : Bool := false) : Array JsOcc :=
  if i < o.dc then #[] else
  #[{ isMut := false, idx := i - o.dc, write, inClosure := o.inClosure, again := o.again }]

/-- An occurrence of the mutable variable of index `i` here. -/
def mOcc (o : OccCtx) (i : Nat) (write : Bool := false) : Array JsOcc :=
  if i < o.dm then #[] else
  #[{ isMut := true, idx := i - o.dm, write, inClosure := o.inClosure, again := o.again }]

end OccCtx

mutual
/-- The occurrences of the variables of an expression. -/
def JsExpr.occsAt {C M : List JsTy} {τ : JsTy} (o : OccCtx) : JsExpr S C M τ → Array JsOcc
  | .cvar x => o.cOcc x.index
  | .mvar x => o.mOcc x.index
  | .lit _ | .unreachable _ | .enum_mk .. => #[]
  | .imported _ as | .inlined _ as | .listOp _ as => as.occsAt o
  | .fold _ e | .unfold _ e | .enumIndex _ e => e.occsAt o
  | .enumEq a b => a.occsAt o ++ b.occsAt o
  | .app f as =>
    let fo := match f with
      | .cvar x => (o.cOcc x.index).map fun oc => { oc with callee := true }
      | f => f.occsAt o
    fo ++ as.occsAt o
  | .lam (σs := σs) _ b => b.occsAt (o.closure σs.length)
  | .record_mk fs => fs.occsAt o
  | .union_mk _ as => as.occsAt o
  | .array_mk _ ps => ps.occsAt o
  | .list_mk ps => ps.occsAt o
  | .cond c a b => c.occsAt o ++ a.occsAt o ++ b.occsAt o

/-- The occurrences of the variables of arguments. -/
def JsArgs.occsAt {C M σs : List JsTy} (o : OccCtx) : JsArgs S C M σs → Array JsOcc
  | .nil => #[]
  | .cons a as => a.occsAt o ++ as.occsAt o

/-- The occurrences of the variables of the parts of an array literal. -/
def JsParts.occsAt {C M : List JsTy} {A E : JsTy} (o : OccCtx) : JsParts S C M A E → Array JsOcc
  | .nil => #[]
  | .elem e rest => e.occsAt o ++ rest.occsAt o
  | .spread a rest => a.occsAt o ++ rest.occsAt o

/-- The occurrences of the variables of a block. -/
def JsBlock.occsAt {C M J : List JsTy} {k : JsEnd} (o : OccCtx) : JsBlock S C M J k → Array JsOcc
  | .ret e | .jump _ e => e.occsAt o
  | .next | .throw _ => #[]
  | .const _ e rest => e.occsAt o ++ rest.occsAt (o.under 1 0)
  | .letMut _ e rest => e.occsAt o ++ rest.occsAt (o.under 0 1)
  | .assign x e rest => o.mOcc x.index true ++ e.occsAt o ++ rest.occsAt o
  | .destructure (us := us) e _ rest => e.occsAt o ++ rest.occsAt (o.under us.length 0)
  | .ite c t e => c.occsAt o ++ t.occsAt o ++ e.occsAt o
  | .enumCases e arms => e.occsAt o ++ arms.occsAt o
  | .unionCases e arms => e.occsAt o ++ arms.occsAt o
  | .join _ b rest => b.occsAt o ++ rest.occsAt (o.under 1 0)
  | .forRange _ _ n b rest =>
    n.occsAt o ++ b.occsAt (o.loop 1) ++ rest.occsAt o
  | .forOf _ _ xs b rest => xs.occsAt o ++ b.occsAt (o.loop 1) ++ rest.occsAt o
  | .countdown _ _ n b s rest =>
    n.occsAt o ++ b.occsAt o.countLoop ++ s.occsAt o.countLoop ++ rest.occsAt (o.under 1 0)
  | .funs (τs := τs) _ defs rest =>
    defs.occsAt (o.under τs.length 0) ++ rest.occsAt (o.under τs.length 0)

/-- The occurrences of the variables of the arms of a case analysis on an enum. -/
def JsEnumArms.occsAt {C M J : List JsTy} {k : JsEnd} {n : Nat} (o : OccCtx) :
    JsEnumArms S C M J k n → Array JsOcc
  | .nil => #[]
  | .cons b rest => b.occsAt o ++ rest.occsAt o

/-- The occurrences of the variables of the arms of a case analysis on a union. -/
def JsUnionArms.occsAt {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (o : OccCtx) :
    JsUnionArms S C M J k cs → Array JsOcc
  | .nil => #[]
  | .cons (us := us) _ b rest => b.occsAt (o.under us.length 0) ++ rest.occsAt o
end

/-- The occurrences of the variables of an expression. -/
def JsExpr.occs {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) : Array JsOcc := e.occsAt {}

/-- The occurrences of the variables of a block. -/
def JsBlock.occs {C M J : List JsTy} {k : JsEnd} (b : JsBlock S C M J k) : Array JsOcc := b.occsAt {}

/-- Does the expression mention the variable? -/
def JsExpr.mentions {C M : List JsTy} {τ : JsTy} (x : JsVar) (e : JsExpr S C M τ) : Bool :=
  e.occs.any (·.is x)

/-- Does the block mention the variable? -/
def JsBlock.mentions {C M J : List JsTy} {k : JsEnd} (x : JsVar) (b : JsBlock S C M J k) : Bool :=
  b.occs.any (·.is x)

/-! ## Moving the computation of a constant to its use -/

mutual
/-- Can the expression be computed later instead of now: it has no effect, cannot throw, reads
    no mutable variable (a closure only reads them when it is called), and reads nothing in an
    array or a record that an update in place could change (no operation at all: it only builds
    values from constants, literals and closures)? -/
def JsExpr.movable {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .lit _ | .enum_mk .. | .unreachable _ | .lam .. => true
  | .fold _ e | .unfold _ e | .enumIndex _ e => e.movable
  | .enumEq a b => a.movable && b.movable
  | .record_mk fs => fs.movable
  | .union_mk _ as => as.movable
  | .cond c a b => c.movable && a.movable && b.movable
  | .array_mk _ ps | .list_mk ps => ps.movable
  | _ => false
/-- `movable` of arguments. -/
def JsArgs.movable {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => true
  | .cons a as => a.movable && as.movable
/-- `movable` of the parts of an array literal. -/
def JsParts.movable {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → Bool
  | .nil => true
  | .elem e rest => e.movable && rest.movable
  | .spread a rest => a.movable && rest.movable
end

mutual
/-- Has the expression no effect (it may throw): no call of a function (which may update an
    argument in place) and no update in place? -/
def JsExpr.noEffect {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .mvar _ | .lit _ | .enum_mk .. | .unreachable _ | .lam .. => true
  | .fold _ e | .unfold _ e | .enumIndex _ e => e.noEffect
  | .enumEq a b => a.noEffect && b.noEffect
  | .record_mk fs => fs.noEffect
  | .union_mk _ as => as.noEffect
  | .inlined (e := .pure) _ as => as.noEffect
  | .imported (e := .pure) _ as => as.noEffect
  | .listOp _ as => as.noEffect
  | .cond c a b => c.noEffect && a.noEffect && b.noEffect
  | .array_mk _ ps | .list_mk ps => ps.noEffect
  | _ => false
/-- `noEffect` of arguments. -/
def JsArgs.noEffect {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => true
  | .cons a as => a.noEffect && as.noEffect
/-- `noEffect` of the parts of an array literal. -/
def JsParts.noEffect {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → Bool
  | .nil => true
  | .elem e rest => e.noEffect && rest.noEffect
  | .spread a rest => a.noEffect && rest.noEffect
end

/-- Is the expression a constant, a literal or `undefined`, whose value nothing can change? -/
def JsExpr.inert {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .lit _ | .enum_mk .. | .unreachable _ => true
  | .fold _ e | .unfold _ e => e.inert
  | _ => false

mutual
/-- Is the constant of index `x` read first when the expression is computed, nothing before it
    but expressions that can be computed later (`movable`; with `strict`, only `inert` ones)?
    Then the computation of the constant can be done there instead. -/
partial def JsExpr.readFirst {C M : List JsTy} {τ : JsTy} (strict : Bool) (x : Nat) :
    JsExpr S C M τ → Bool
  | .cvar y => y.index == x
  | .fold _ e | .unfold _ e | .enumIndex _ e => e.readFirst strict x
  | .enumEq a b => JsExpr.readFirst2 strict x a b
  | .app f as =>
    if f.mentions ⟨false, x⟩ then false
    else (if strict then f.inert else f.movable) && as.readFirst strict x
  | .imported _ as | .listOp _ as => as.readFirst strict x
  -- an inlined operation may write its arguments in another order: the others must all wait
  | .inlined _ as => as.readFirstAny strict x
  | .record_mk fs => fs.readFirst strict x
  | .union_mk _ as => as.readFirst strict x
  | .cond c a b =>
    if c.mentions ⟨false, x⟩ then c.readFirst strict x
    else (if strict then c.inert else c.movable) &&
      (if a.mentions ⟨false, x⟩ then a.readFirst strict x else b.readFirst strict x)
  | _ => false
/-- `readFirst` of two operands, in order. -/
partial def JsExpr.readFirst2 {C M : List JsTy} {τ τ' : JsTy} (strict : Bool) (x : Nat)
    (a : JsExpr S C M τ) (b : JsExpr S C M τ') : Bool :=
  if a.mentions ⟨false, x⟩ then a.readFirst strict x
  else (if strict then a.inert else a.movable) && b.readFirst strict x
/-- `readFirst` of arguments, computed in order. -/
partial def JsArgs.readFirst {C M σs : List JsTy} (strict : Bool) (x : Nat) : JsArgs S C M σs → Bool
  | .nil => false
  | .cons a as =>
    if a.mentions ⟨false, x⟩ then a.readFirst strict x
    else (if strict then a.inert else a.movable) && as.readFirst strict x
/-- `readFirst` of arguments computed in any order: the one reading the constant reads it
    first, and all the others can wait. -/
partial def JsArgs.readFirstAny {C M σs : List JsTy} (strict : Bool) (x : Nat) : JsArgs S C M σs → Bool
  | .nil => false
  | .cons a as =>
    if a.mentions ⟨false, x⟩ then a.readFirst strict x && as.allWait strict
    else (if strict then a.inert else a.movable) && as.readFirstAny strict x
/-- Can all the arguments wait? -/
partial def JsArgs.allWait {C M σs : List JsTy} (strict : Bool) : JsArgs S C M σs → Bool
  | .nil => true
  | .cons a as => (if strict then a.inert else a.movable) && as.allWait strict
end

/-- Is the constant of index `x` read (once) where the computation of a value `e` put in it can be
    moved to: before any effect or throw of the block, and before any assignment of a mutable
    variable `e` reads (`reads`)?  With `strict` (`e` has an effect), nothing may be computed
    before it (only constants and literals may be read). -/
partial def JsBlock.useFirst {C M J : List JsTy} {k : JsEnd} (strict : Bool) (reads : List Nat)
    (x : Nat) : JsBlock S C M J k → Bool
  | .ret a | .jump _ a => a.readFirst strict x
  | .const _ a r =>
    if a.mentions ⟨false, x⟩ then a.readFirst strict x
    else !strict && a.movable && r.useFirst strict reads (x + 1)
  | .assign y a r =>
    if a.mentions ⟨false, x⟩ then a.readFirst strict x
    else !strict && a.movable && !reads.contains y.index && r.useFirst strict reads x
  | .destructure (us := us) a _ r =>
    if a.mentions ⟨false, x⟩ then a.readFirst strict x
    else !strict && a.movable && r.useFirst strict reads (x + us.length)
  | .ite c t e =>
    if c.mentions ⟨false, x⟩ then c.readFirst strict x
    else !strict && c.movable &&
      (if t.mentions ⟨false, x⟩ then t.useFirst strict reads x else e.useFirst strict reads x)
  | _ => false

/-- Is the expression a variable or a literal (one that can be repeated without
    recomputing anything)? -/
def JsExpr.isAtom {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .mvar _ | .lit _ | .enum_mk .. => true
  | .fold _ e | .unfold _ e => e.isAtom
  | _ => false

end MoreJs

end
