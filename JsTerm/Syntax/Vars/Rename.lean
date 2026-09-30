module

public import JsTerm.Syntax.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Renaming the variables of the JavaScript grammar

Renaming (`JsExpr.renameM`) in any monad: in `Id` it moves a term to a larger context
(`JsExpr.wkC`, under a new binder); in `Option` it moves a term to a smaller one when it does
not mention the variables left out (`JsExpr.closed?`: a term that mentions no variable at all
is valid in every context).
-/

namespace MoreJs

variable {S : JsSig}

/-- A renaming of a context of variables, in a monad `m`. -/
abbrev JsRenM (m : Type → Type) (Γ Δ : List JsTy) : Type := ∀ {τ : JsTy}, JsMem Γ τ → m (JsMem Δ τ)

namespace JsRenM

variable {m : Type → Type} [Monad m]

/-- A renaming under a new binder (which is renamed to itself). -/
def lift {Γ Δ : List JsTy} {σ : JsTy} (r : JsRenM m Γ Δ) : JsRenM m (σ :: Γ) (σ :: Δ) := fun x =>
  match x with
  | .zero => pure .zero
  | .succ x => JsMem.succ <$> r x

/-- A renaming under the binders of a pattern. -/
def liftAll {Γ Δ : List JsTy} :
    (us : List JsTy) → JsRenM m Γ Δ → JsRenM m (pushAll us Γ) (pushAll us Δ)
  | [], r => r
  | _ :: us, r => liftAll us (lift r)

end JsRenM

mutual
/-- Rename the variables of an expression. -/
def JsExpr.renameM {m : Type → Type} [Monad m] {C M C' M' : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {τ : JsTy} : JsExpr S C M τ → m (JsExpr S C' M' τ)
  | .cvar x => .cvar <$> rc x
  | .mvar x => .mvar <$> rm x
  | .lit l => pure (.lit l)
  | .imported op as => .imported op <$> as.renameM rc rm
  | .inlined op as => .inlined op <$> as.renameM rc rm
  | .unreachable t => pure (.unreachable t)
  | .app f as => return .app (← f.renameM rc rm) (← as.renameM rc rm)
  | .lam (σs := σs) xs b => .lam xs <$> b.renameM (JsRenM.liftAll σs rc) rm
  | .record_mk fs => .record_mk <$> fs.renameM rc rm
  | .union_mk ix as => .union_mk ix <$> as.renameM rc rm
  | .enum_mk n s i => pure (.enum_mk n s i)
  | .enumIndex nt e => .enumIndex nt <$> e.renameM rc rm
  | .enumEq a b => return .enumEq (← a.renameM rc rm) (← b.renameM rc rm)
  | .array_mk l ps => .array_mk l <$> ps.renameM rc rm
  | .list_mk ps => .list_mk <$> ps.renameM rc rm
  | .cond c a b => return .cond (← c.renameM rc rm) (← a.renameM rc rm) (← b.renameM rc rm)
  | .listOp op as => .listOp op <$> as.renameM rc rm
  | .fold i e => .fold i <$> e.renameM rc rm
  | .unfold i e => .unfold i <$> e.renameM rc rm

/-- Rename the variables of arguments. -/
def JsArgs.renameM {m : Type → Type} [Monad m] {C M C' M' : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {σs : List JsTy} :
    JsArgs S C M σs → m (JsArgs S C' M' σs)
  | .nil => pure .nil
  | .cons a as => return .cons (← a.renameM rc rm) (← as.renameM rc rm)

/-- Rename the variables of the parts of an array literal. -/
def JsParts.renameM {m : Type → Type} [Monad m] {C M C' M' : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {A E : JsTy} :
    JsParts S C M A E → m (JsParts S C' M' A E)
  | .nil => pure .nil
  | .elem e rest => return .elem (← e.renameM rc rm) (← rest.renameM rc rm)
  | .spread a rest => return .spread (← a.renameM rc rm) (← rest.renameM rc rm)

/-- Rename the variables of a block. -/
def JsBlock.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} :
    JsBlock S C M J k → m (JsBlock S C' M' J k)
  | .ret e => .ret <$> e.renameM rc rm
  | .next => pure .next
  | .jump j e => .jump j <$> e.renameM rc rm
  | .throw msg => pure (.throw msg)
  | .const x e rest => return .const x (← e.renameM rc rm) (← rest.renameM (JsRenM.lift rc) rm)
  | .letMut x e rest => return .letMut x (← e.renameM rc rm) (← rest.renameM rc (JsRenM.lift rm))
  | .assign x e rest => return .assign (← rm x) (← e.renameM rc rm) (← rest.renameM rc rm)
  | .destructure (us := us) e sel rest =>
    return .destructure (← e.renameM rc rm) sel (← rest.renameM (JsRenM.liftAll us rc) rm)
  | .ite c t e => return .ite (← c.renameM rc rm) (← t.renameM rc rm) (← e.renameM rc rm)
  | .enumCases e arms => return .enumCases (← e.renameM rc rm) (← arms.renameM rc rm)
  | .unionCases e arms => return .unionCases (← e.renameM rc rm) (← arms.renameM rc rm)
  | .join x b rest => return .join x (← b.renameM rc rm) (← rest.renameM (JsRenM.lift rc) rm)
  | .forRange x nt n b rest =>
    return .forRange x nt (← n.renameM rc rm) (← b.renameM (JsRenM.lift rc) rm) (← rest.renameM rc rm)
  | .forOf x l xs b rest =>
    return .forOf x l (← xs.renameM rc rm) (← b.renameM (JsRenM.lift rc) rm) (← rest.renameM rc rm)
  | .countdown x nt n b s rest =>
    return .countdown x nt (← n.renameM rc rm) (← b.renameM rc (JsRenM.lift rm))
      (← s.renameM rc (JsRenM.lift rm)) (← rest.renameM (JsRenM.lift rc) rm)
  | .funs (τs := τs) xs defs rest =>
    return .funs xs (← defs.renameM (JsRenM.liftAll τs rc) rm)
      (← rest.renameM (JsRenM.liftAll τs rc) rm)

/-- Rename the variables of the arms of a case analysis on an enum. -/
def JsEnumArms.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → m (JsEnumArms S C' M' J k n)
  | .nil => pure .nil
  | .cons b rest => return .cons (← b.renameM rc rm) (← rest.renameM rc rm)

/-- Rename the variables of the arms of a case analysis on a union. -/
def JsUnionArms.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → m (JsUnionArms S C' M' J k cs)
  | .nil => pure .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.renameM (JsRenM.liftAll us rc) rm) (← rest.renameM rc rm)
end

/-- The identity renaming. -/
def JsRen.id {Γ : List JsTy} : JsRenM Id Γ Γ := fun x => x

/-- The renaming that skips the innermost variable. -/
def JsRen.succ {Γ : List JsTy} {σ : JsTy} : JsRenM Id Γ (σ :: Γ) := fun x => JsMem.succ x

/-- An expression under a new constant. -/
def JsExpr.wkC {C M : List JsTy} {σ τ : JsTy} (e : JsExpr S C M τ) : JsExpr S (σ :: C) M τ :=
  Id.run (e.renameM JsRen.succ JsRen.id)

/-- Arguments under a new constant. -/
def JsArgs.wkC {C M σs : List JsTy} {σ : JsTy} (as : JsArgs S C M σs) : JsArgs S (σ :: C) M σs :=
  Id.run (as.renameM JsRen.succ JsRen.id)

/-- An expression under a new mutable variable. -/
def JsExpr.wkM {C M : List JsTy} {σ τ : JsTy} (e : JsExpr S C M τ) : JsExpr S C (σ :: M) τ :=
  Id.run (e.renameM JsRen.id JsRen.succ)

/-- An expression that mentions no variable, in the empty contexts. -/
def JsExpr.closed? {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) : Option (JsExpr S [] [] τ) :=
  e.renameM (fun _ => none) (fun _ => none)

/-- An expression that mentions no variable, in any contexts. -/
def JsExpr.embed {C M : List JsTy} {τ : JsTy} (e : JsExpr S [] [] τ) : JsExpr S C M τ :=
  Id.run (e.renameM (fun x => nomatch x) (fun x => nomatch x))

/-- A block that mentions no join point bound outside it, under join points `J`. -/
def JsBlock.embedJ? {C M J : List JsTy} {k : JsEnd} (J' : List JsTy) :
    JsBlock S C M J k → Option (JsBlock S C M J' k) :=
  fun b => if h : J = J' then some (h ▸ b) else none

end MoreJs

end
