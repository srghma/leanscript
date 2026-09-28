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

/-- An occurrence of a variable: a constant or a mutable variable, by its de Bruijn index
    where the walk started; whether it is an assignment, inside a closure, or inside a loop or
    a closure (evaluated possibly more than once). -/
structure JsOcc where
  isMut : Bool
  idx : Nat
  write : Bool := false
  inClosure : Bool := false
  again : Bool := false
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
def JsExpr.occsAt {C M : List JsTy} {τ : JsTy} (o : OccCtx) : JsExpr C M τ → Array JsOcc
  | .cvar x => o.cOcc x.index
  | .mvar x => o.mOcc x.index
  | .global .. | .lit _ | .unreachable _ | .enum_mk .. => #[]
  | .imported _ as | .inlined _ as => as.occsAt o
  | .app f as => f.occsAt o ++ as.occsAt o
  | .lam (σs := σs) _ b => b.occsAt (o.closure σs.length)
  | .record_mk fs => fs.occsAt o
  | .union_mk _ as => as.occsAt o
  | .array_mk _ ps => ps.occsAt o
  | .list_mk ps => ps.occsAt o
  | .cond c a b => c.occsAt o ++ a.occsAt o ++ b.occsAt o

/-- The occurrences of the variables of arguments. -/
def JsArgs.occsAt {C M σs : List JsTy} (o : OccCtx) : JsArgs C M σs → Array JsOcc
  | .nil => #[]
  | .cons a as => a.occsAt o ++ as.occsAt o

/-- The occurrences of the variables of the parts of an array literal. -/
def JsParts.occsAt {C M : List JsTy} {A E : JsTy} (o : OccCtx) : JsParts C M A E → Array JsOcc
  | .nil => #[]
  | .elem e rest => e.occsAt o ++ rest.occsAt o
  | .spread a rest => a.occsAt o ++ rest.occsAt o

/-- The occurrences of the variables of a block. -/
def JsBlock.occsAt {C M J : List JsTy} {k : JsEnd} (o : OccCtx) : JsBlock C M J k → Array JsOcc
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
  | .forRange _ _ n b rest | .lastIter _ _ n b rest =>
    n.occsAt o ++ b.occsAt (o.loop 1) ++ rest.occsAt o
  | .forOf _ _ xs b rest => xs.occsAt o ++ b.occsAt (o.loop 1) ++ rest.occsAt o

/-- The occurrences of the variables of the arms of a case analysis on an enum. -/
def JsEnumArms.occsAt {C M J : List JsTy} {k : JsEnd} {n : Nat} (o : OccCtx) :
    JsEnumArms C M J k n → Array JsOcc
  | .nil => #[]
  | .cons b rest => b.occsAt o ++ rest.occsAt o

/-- The occurrences of the variables of the arms of a case analysis on a union. -/
def JsUnionArms.occsAt {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (o : OccCtx) :
    JsUnionArms C M J k cs → Array JsOcc
  | .nil => #[]
  | .cons (us := us) _ b rest => b.occsAt (o.under us.length 0) ++ rest.occsAt o
end

/-- The occurrences of the variables of an expression. -/
def JsExpr.occs {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : Array JsOcc := e.occsAt {}

/-- The occurrences of the variables of a block. -/
def JsBlock.occs {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : Array JsOcc := b.occsAt {}

/-- Does the expression mention the variable? -/
def JsExpr.mentions {C M : List JsTy} {τ : JsTy} (x : JsVar) (e : JsExpr C M τ) : Bool :=
  e.occs.any (·.is x)

/-- Does the block mention the variable? -/
def JsBlock.mentions {C M J : List JsTy} {k : JsEnd} (x : JsVar) (b : JsBlock C M J k) : Bool :=
  b.occs.any (·.is x)

/-- Is the expression a variable, a global or a literal (one that can be repeated without
    recomputing anything)? -/
def JsExpr.isAtom {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .cvar _ | .mvar _ | .global .. | .lit _ | .enum_mk .. => true
  | _ => false

end MoreJs

end
