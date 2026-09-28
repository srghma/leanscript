module

public import JsTerm.Syntax.Vars.Rename

@[expose] public section

set_option autoImplicit false

/-!
# Substitution of the constants of the JavaScript grammar

`JsBlock.subst`: an expression for every constant, the mutable variables being renamed only
(they are assigned, so only a variable can stand for one).
-/

namespace MoreJs

/-- A substitution: an expression for every constant, a mutable variable for every mutable
    variable. -/
structure JsSubst (C M C' M' : List JsTy) where
  c : ∀ {τ : JsTy}, JsMem C τ → JsExpr C' M' τ
  m : JsRenM Id M M'

namespace JsSubst

variable {C M C' M' : List JsTy}

/-- The substitution under a new constant. -/
def liftC {σ : JsTy} (s : JsSubst C M C' M') : JsSubst (σ :: C) M (σ :: C') M' where
  c := fun x => match x with
    | .zero => .cvar .zero
    | .succ x => (s.c x).wkC
  m := s.m

/-- The substitution under a new mutable variable. -/
def liftM {σ : JsTy} (s : JsSubst C M C' M') : JsSubst C (σ :: M) C' (σ :: M') where
  c := fun x => (s.c x).wkM
  m := JsRenM.lift s.m

/-- The substitution under the constants of a pattern. -/
def liftCAll {C M C' M' : List JsTy} :
    (us : List JsTy) → JsSubst C M C' M' → JsSubst (pushAll us C) M (pushAll us C') M'
  | [], s => s
  | _ :: us, s => liftCAll us s.liftC

/-- The substitution of `e` for the innermost constant. -/
def inst {σ : JsTy} (e : JsExpr C M σ) : JsSubst (σ :: C) M C M where
  c := fun x => match x with
    | .zero => e
    | .succ x => .cvar x
  m := JsRen.id

end JsSubst

mutual
/-- Substitute the constants of an expression. -/
def JsExpr.subst {C M C' M' : List JsTy} (s : JsSubst C M C' M') {τ : JsTy} :
    JsExpr C M τ → JsExpr C' M' τ
  | .cvar x => s.c x
  | .mvar x => .mvar (s.m x)
  | .global n t => .global n t
  | .lit l => .lit l
  | .imported op as => .imported op (as.subst s)
  | .inlined op as => .inlined op (as.subst s)
  | .unreachable t => .unreachable t
  | .app f as => .app (f.subst s) (as.subst s)
  | .lam (σs := σs) xs b => .lam xs (b.subst (s.liftCAll σs))
  | .record_mk fs => .record_mk (fs.subst s)
  | .union_mk ix as => .union_mk ix (as.subst s)
  | .enum_mk n sh i => .enum_mk n sh i
  | .array_mk l ps => .array_mk l (ps.subst s)
  | .list_mk ps => .list_mk (ps.subst s)
  | .cond c a b => .cond (c.subst s) (a.subst s) (b.subst s)

/-- Substitute the constants of arguments. -/
def JsArgs.subst {C M C' M' : List JsTy} (s : JsSubst C M C' M') {σs : List JsTy} :
    JsArgs C M σs → JsArgs C' M' σs
  | .nil => .nil
  | .cons a as => .cons (a.subst s) (as.subst s)

/-- Substitute the constants of the parts of an array literal. -/
def JsParts.subst {C M C' M' : List JsTy} (s : JsSubst C M C' M') {A E : JsTy} :
    JsParts C M A E → JsParts C' M' A E
  | .nil => .nil
  | .elem e rest => .elem (e.subst s) (rest.subst s)
  | .spread a rest => .spread (a.subst s) (rest.subst s)

/-- Substitute the constants of a block. -/
def JsBlock.subst {C M C' M' J : List JsTy} (s : JsSubst C M C' M') {k : JsEnd} :
    JsBlock C M J k → JsBlock C' M' J k
  | .ret e => .ret (e.subst s)
  | .next => .next
  | .jump j e => .jump j (e.subst s)
  | .throw msg => .throw msg
  | .const x e rest => .const x (e.subst s) (rest.subst s.liftC)
  | .letMut x e rest => .letMut x (e.subst s) (rest.subst s.liftM)
  | .assign x e rest => .assign (s.m x) (e.subst s) (rest.subst s)
  | .destructure (us := us) e sel rest => .destructure (e.subst s) sel (rest.subst (s.liftCAll us))
  | .ite c t e => .ite (c.subst s) (t.subst s) (e.subst s)
  | .enumCases e arms => .enumCases (e.subst s) (arms.subst s)
  | .unionCases e arms => .unionCases (e.subst s) (arms.subst s)
  | .join x b rest => .join x (b.subst s) (rest.subst s.liftC)
  | .forRange x nt n b rest => .forRange x nt (n.subst s) (b.subst s.liftC) (rest.subst s)
  | .lastIter x nt n b rest => .lastIter x nt (n.subst s) (b.subst s.liftC) (rest.subst s)
  | .forOf x l xs b rest => .forOf x l (xs.subst s) (b.subst s.liftC) (rest.subst s)

/-- Substitute the constants of the arms of a case analysis on an enum. -/
def JsEnumArms.subst {C M C' M' J : List JsTy} (s : JsSubst C M C' M') {k : JsEnd} {n : Nat} :
    JsEnumArms C M J k n → JsEnumArms C' M' J k n
  | .nil => .nil
  | .cons b rest => .cons (b.subst s) (rest.subst s)

/-- Substitute the constants of the arms of a case analysis on a union. -/
def JsUnionArms.subst {C M C' M' J : List JsTy} (s : JsSubst C M C' M') {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms C M J k cs → JsUnionArms C' M' J k cs
  | .nil => .nil
  | .cons (us := us) sel b rest => .cons sel (b.subst (s.liftCAll us)) (rest.subst s)
end

end MoreJs

end
