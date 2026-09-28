module

public import JsTerm.Syntax

@[expose] public section

set_option autoImplicit false

/-!
# The variables of the grammar: binders, substitution, occurrences

The local variables of the grammar are de Bruijn indices into two contexts, the constants
(`JsExpr.cvar`) and the mutable variables (`JsExpr.mvar`), plus the join points, a third
context only `JsStmt.join` and `JsStmt.jump` use (see `JsTerm.Syntax`).  This file has the
operations every pass needs on them:

* how many variables of each context a statement binds for the statements after it
  (`JsStmt.bindsC`, `JsStmt.bindsM`);
* the substitution of the free variables of an expression or of a block (`JsSubst`,
  `JsExpr.subst`, `substStmts`), and its special case, the shift of the free variables
  (`JsExpr.shift`, `shiftStmts`);
* the free occurrences of the variables of a block (`occsStmts`): where each is read or
  assigned, and whether it is read inside a loop or a closure.
-/

namespace MoreJs

/-! ## Binders -/

/-- How many constants a statement binds for the statements after it in its block. -/
def JsStmt.bindsC : JsStmt → Nat
  | .const .. => 1
  | .destructure xs _ => (xs.filterMap id).length
  | .destructureObj bs _ => bs.length
  | _ => 0

/-- How many mutable variables a statement binds for the statements after it in its block. -/
def JsStmt.bindsM : JsStmt → Nat
  | .letMut .. => 1
  | _ => 0

/-- How many constants a block binds, in total, for what follows it (only meaningful for a
    prefix of a block). -/
def bindsCAll (ss : List JsStmt) : Nat := (ss.map JsStmt.bindsC).sum

/-- How many mutable variables a block binds, in total, for what follows it. -/
def bindsMAll (ss : List JsStmt) : Nat := (ss.map JsStmt.bindsM).sum

/-! ## Substitution -/

/-- A substitution of the free variables: an expression for every free constant and every
    free mutable variable, each seen from the place the substitution is applied at (outside
    every binder of the term it is applied to).  A mutable variable that is assigned (by `x =
    e;` or as the variable of a join point) must be sent to a mutable variable. -/
structure JsSubst where
  c : Nat → JsExpr
  m : Nat → JsExpr

namespace JsSubst

/-- The substitution that shifts every free constant by `dc` and every free mutable variable
    by `dm`. -/
def shift (dc dm : Nat) : JsSubst := ⟨fun i => .cvar (i + dc), fun i => .mvar (i + dm)⟩

/-- The substitution sending the free constant `0` to `e` and every other free constant one
    down: the instantiation of the innermost constant (removing its binder). -/
def instC (e : JsExpr) : JsSubst :=
  ⟨fun i => if i == 0 then e else .cvar (i - 1), .mvar⟩

end JsSubst

mutual
/-- Apply a substitution to an expression, under `dc` constants and `dm` mutable variables
    bound inside the term (those are left alone, and the expressions substituted are shifted
    over them). -/
partial def JsExpr.substAt (σ : JsSubst) (dc dm : Nat) : JsExpr → JsExpr
  | .cvar i => if i < dc then .cvar i else JsExpr.shiftOut dc dm (σ.c (i - dc))
  | .mvar i => if i < dm then .mvar i else JsExpr.shiftOut dc dm (σ.m (i - dm))
  | .global x => .global x
  | .lit l => .lit l
  | .bin op a b => .bin op (a.substAt σ dc dm) (b.substAt σ dc dm)
  | .un op a => .un op (a.substAt σ dc dm)
  | .helper n as => .helper n (as.map (·.substAt σ dc dm))
  | .call f as => .call (f.substAt σ dc dm) (as.map (·.substAt σ dc dm))
  | .arrow ps b => .arrow ps (substStmtsAt σ (dc + ps.length) dm b)
  | .array es => .array (es.map (·.substAt σ dc dm))
  | .typedArray c es => .typedArray c (es.map (·.substAt σ dc dm))
  | .index e i => .index (e.substAt σ dc dm) i
  | .member e n => .member (e.substAt σ dc dm) n
  | .cond c a b => .cond (c.substAt σ dc dm) (a.substAt σ dc dm) (b.substAt σ dc dm)
  | .object fs => .object (fs.map fun (k, e) => (k, e.substAt σ dc dm))
  | .at e i => .at (e.substAt σ dc dm) (i.substAt σ dc dm)
  | .new c as => .new (c.substAt σ dc dm) (as.map (·.substAt σ dc dm))
  | .spread e => .spread (e.substAt σ dc dm)

/-- An expression substituted for a free variable, moved under the `dc` constants and `dm`
    mutable variables bound around the occurrence. -/
partial def JsExpr.shiftOut (dc dm : Nat) (e : JsExpr) : JsExpr :=
  if dc == 0 && dm == 0 then e else e.substAt (.shift dc dm) 0 0

/-- The mutable variable a substitution sends an assigned mutable variable to (unchanged if
    it is not sent to one, which a well-formed substitution never does). -/
partial def substMutAt (σ : JsSubst) (dc dm : Nat) (x : Nat) : Nat :=
  match (JsExpr.mvar x).substAt σ dc dm with
  | .mvar y => y
  | _ => x

/-- Apply a substitution to a statement (see `JsExpr.substAt`). -/
partial def JsStmt.substAt (σ : JsSubst) (dc dm : Nat) : JsStmt → JsStmt
  | .const x e => .const x (e.substAt σ dc dm)
  | .letMut x e => .letMut x (e.map (·.substAt σ dc dm))
  | .assign x e => .assign (substMutAt σ dc dm x) (e.substAt σ dc dm)
  | .destructure xs e => .destructure xs (e.substAt σ dc dm)
  | .destructureObj bs e => .destructureObj bs (e.substAt σ dc dm)
  | .setMember o n e => .setMember (o.substAt σ dc dm) n (e.substAt σ dc dm)
  | .setAt o i e => .setAt (o.substAt σ dc dm) (i.substAt σ dc dm) (e.substAt σ dc dm)
  | .expr e => .expr (e.substAt σ dc dm)
  | .while c b => .while (c.substAt σ dc dm) (substStmtsAt σ dc dm b)
  | .ret e => .ret (e.substAt σ dc dm)
  | .ite c t e => .ite (c.substAt σ dc dm) (substStmtsAt σ dc dm t) (substStmtsAt σ dc dm e)
  | .forRange i big n b => .forRange i big (n.substAt σ dc dm) (substStmtsAt σ (dc + 1) dm b)
  | .forOf x xs b => .forOf x (xs.substAt σ dc dm) (substStmtsAt σ (dc + 1) dm b)
  | .throw k m => .throw k m
  | .join x b => .join (substMutAt σ dc dm x) (substStmtsAt σ dc dm b)
  | .jump j e => .jump j (e.substAt σ dc dm)

/-- Apply a substitution to a block: each statement under the binders of the ones before it. -/
partial def substStmtsAt (σ : JsSubst) (dc dm : Nat) : List JsStmt → List JsStmt
  | [] => []
  | s :: ss => s.substAt σ dc dm :: substStmtsAt σ (dc + s.bindsC) (dm + s.bindsM) ss
end

/-- Apply a substitution to the free variables of an expression. -/
def JsExpr.subst (σ : JsSubst) (e : JsExpr) : JsExpr := e.substAt σ 0 0

/-- Apply a substitution to the free variables of a block. -/
def substStmts (σ : JsSubst) (ss : List JsStmt) : List JsStmt := substStmtsAt σ 0 0 ss

/-- Shift the free constants of an expression by `dc` and its free mutable variables by `dm`
    (to move it under `dc` more constants and `dm` more mutable variables). -/
def JsExpr.shift (dc dm : Nat) (e : JsExpr) : JsExpr :=
  if dc == 0 && dm == 0 then e else e.subst (.shift dc dm)

/-- Shift the free variables of a block (see `JsExpr.shift`). -/
def shiftStmts (dc dm : Nat) (ss : List JsStmt) : List JsStmt :=
  if dc == 0 && dm == 0 then ss else substStmts (.shift dc dm) ss

/-! ## Occurrences -/

/-- A free occurrence of a variable. -/
structure Occ where
  /-- A mutable variable (otherwise a constant). -/
  isMut : Bool
  /-- Its de Bruijn index, seen from the start of the term. -/
  idx : Nat
  /-- An assignment (`x = e;`, or the variable of a join point). -/
  write : Bool := false
  /-- Inside the body of a loop or of a closure: evaluated again and again. -/
  again : Bool := false
  /-- Inside a closure. -/
  inClosure : Bool := false
  /-- A read of the tag of a union, `x.tag` (a tag never changes). -/
  tag : Bool := false
  deriving Inhabited, Repr, BEq

/-- Where the occurrences are collected: the variables bound inside the term so far, and
    whether it is inside a loop body or a closure. -/
structure OccCtx where
  dc : Nat := 0
  dm : Nat := 0
  again : Bool := false
  inClosure : Bool := false

mutual
/-- The free occurrences of the variables of an expression, pushed onto `acc`. -/
partial def JsExpr.occsAt (c : OccCtx) (acc : Array Occ) : JsExpr → Array Occ
  | .cvar i => if i < c.dc then acc else
      acc.push { isMut := false, idx := i - c.dc, again := c.again, inClosure := c.inClosure }
  | .mvar i => if i < c.dm then acc else
      acc.push { isMut := true, idx := i - c.dm, again := c.again, inClosure := c.inClosure }
  | .member (.cvar i) "tag" => if i < c.dc then acc else
      acc.push { isMut := false, idx := i - c.dc, again := c.again, inClosure := c.inClosure,
                 tag := true }
  | .member (.mvar i) "tag" => if i < c.dm then acc else
      acc.push { isMut := true, idx := i - c.dm, again := c.again, inClosure := c.inClosure,
                 tag := true }
  | .global _ | .lit _ => acc
  | .bin _ a b | .at a b => b.occsAt c (a.occsAt c acc)
  | .un _ a | .index a _ | .member a _ | .spread a => a.occsAt c acc
  | .call f as | .new f as => as.foldl (fun acc a => a.occsAt c acc) (f.occsAt c acc)
  | .helper _ as | .array as | .typedArray _ as => as.foldl (fun acc a => a.occsAt c acc) acc
  | .cond k a b => b.occsAt c (a.occsAt c (k.occsAt c acc))
  | .object fs => fs.foldl (fun acc (_, e) => e.occsAt c acc) acc
  | .arrow ps b =>
    occsStmtsAt { c with dc := c.dc + ps.length, again := true, inClosure := true } acc b

/-- The free occurrences of the variables of a statement. -/
partial def JsStmt.occsAt (c : OccCtx) (acc : Array Occ) : JsStmt → Array Occ
  | .const _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e | .expr e =>
    e.occsAt c acc
  | .letMut _ e => match e with
    | some e => e.occsAt c acc
    | none => acc
  | .assign x e =>
    let acc := e.occsAt c acc
    if x < c.dm then acc else
    acc.push { isMut := true, idx := x - c.dm, write := true, again := c.again,
               inClosure := c.inClosure }
  | .setMember o _ e => e.occsAt c (o.occsAt c acc)
  | .setAt o i e => e.occsAt c (i.occsAt c (o.occsAt c acc))
  | .while k b => occsStmtsAt { c with again := true } (k.occsAt { c with again := true } acc) b
  | .ite k t e => occsStmtsAt c (occsStmtsAt c (k.occsAt c acc) t) e
  | .forRange _ _ n b => occsStmtsAt { c with dc := c.dc + 1, again := true } (n.occsAt c acc) b
  | .forOf _ xs b => occsStmtsAt { c with dc := c.dc + 1, again := true } (xs.occsAt c acc) b
  | .throw _ _ => acc
  | .join x b =>
    let acc := if x < c.dm then acc else
      acc.push { isMut := true, idx := x - c.dm, write := true, again := c.again,
                 inClosure := c.inClosure }
    occsStmtsAt c acc b

/-- The free occurrences of the variables of a block. -/
partial def occsStmtsAt (c : OccCtx) (acc : Array Occ) : List JsStmt → Array Occ
  | [] => acc
  | s :: ss =>
    occsStmtsAt { c with dc := c.dc + s.bindsC, dm := c.dm + s.bindsM } (s.occsAt c acc) ss
end

/-- The free occurrences of the variables of an expression. -/
def JsExpr.occs (e : JsExpr) : Array Occ := e.occsAt {} #[]

/-- The free occurrences of the variables of a block. -/
def occsStmts (ss : List JsStmt) : Array Occ := occsStmtsAt {} #[] ss

/-- A variable: a constant or a mutable variable, by its de Bruijn index. -/
structure JsVar where
  isMut : Bool
  idx : Nat
  deriving Inhabited, Repr, BEq

/-- Is an occurrence one of the variable `x`? -/
def Occ.is (o : Occ) (x : JsVar) : Bool := o.isMut == x.isMut && o.idx == x.idx

/-- The variable `x`, seen from under `dc` more constants and `dm` more mutable variables. -/
def JsVar.under (x : JsVar) (dc dm : Nat) : JsVar :=
  { x with idx := x.idx + (if x.isMut then dm else dc) }

/-- The variable `x`, seen from after the statement `s` (in the same block). -/
def JsVar.after (x : JsVar) (s : JsStmt) : JsVar := x.under s.bindsC s.bindsM

/-- Does a block mention the variable `x` (free in it)? -/
def mentionsIn (x : JsVar) (ss : List JsStmt) : Bool := (occsStmts ss).any (·.is x)

/-- Does an expression mention the variable `x`? -/
def JsExpr.mentions (x : JsVar) (e : JsExpr) : Bool := e.occs.any (·.is x)

/-- Is an expression closed: no free local variable? -/
def JsExpr.isClosed (e : JsExpr) : Bool := e.occs.isEmpty

end MoreJs

end
