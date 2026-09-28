module

public import JsTerm.Syntax.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Variables of the JavaScript grammar: renaming, substitution, occurrences

The variables of `JsTerm` are typed de Bruijn indices into two contexts of variables (the
constants and the mutable variables) and one of join points.  This module gives the passes
of the backend the operations on them:

* **renaming** (`JsExpr.renameM`), in any monad: in `Id` it moves a term to a larger context
  (`JsExpr.wkC`, under a new binder); in `Option` it moves a term to a smaller one when it
  does not mention the variables left out (`JsExpr.closed?`: a term that mentions no variable
  at all is valid in every context);
* **substitution** of the constants (`JsBlock.subst`), the mutable variables being renamed
  only (they are assigned, so only a variable can stand for one);
* **occurrences** (`JsBlock.occs`): every read and assignment of a variable, with whether it
  is inside a closure or a loop (where it may be evaluated more than once).
-/

namespace MoreJs

/-! ## Renaming -/

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
    (rc : JsRenM m C C') (rm : JsRenM m M M') {τ : JsTy} : JsExpr C M τ → m (JsExpr C' M' τ)
  | .cvar x => .cvar <$> rc x
  | .mvar x => .mvar <$> rm x
  | .global n t => pure (.global n t)
  | .lit l => pure (.lit l)
  | .imported op as => .imported op <$> as.renameM rc rm
  | .inlined op as => .inlined op <$> as.renameM rc rm
  | .unreachable t => pure (.unreachable t)
  | .app f as => return .app (← f.renameM rc rm) (← as.renameM rc rm)
  | .lam (σs := σs) xs b => .lam xs <$> b.renameM (JsRenM.liftAll σs rc) rm
  | .record_mk fs => .record_mk <$> fs.renameM rc rm
  | .union_mk ix as => .union_mk ix <$> as.renameM rc rm
  | .enum_mk n s i => pure (.enum_mk n s i)
  | .array_mk l ps => .array_mk l <$> ps.renameM rc rm
  | .list_mk ps => .list_mk <$> ps.renameM rc rm
  | .cond c a b => return .cond (← c.renameM rc rm) (← a.renameM rc rm) (← b.renameM rc rm)

/-- Rename the variables of arguments. -/
def JsArgs.renameM {m : Type → Type} [Monad m] {C M C' M' : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {σs : List JsTy} :
    JsArgs C M σs → m (JsArgs C' M' σs)
  | .nil => pure .nil
  | .cons a as => return .cons (← a.renameM rc rm) (← as.renameM rc rm)

/-- Rename the variables of the parts of an array literal. -/
def JsParts.renameM {m : Type → Type} [Monad m] {C M C' M' : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {A E : JsTy} :
    JsParts C M A E → m (JsParts C' M' A E)
  | .nil => pure .nil
  | .elem e rest => return .elem (← e.renameM rc rm) (← rest.renameM rc rm)
  | .spread a rest => return .spread (← a.renameM rc rm) (← rest.renameM rc rm)

/-- Rename the variables of a block. -/
def JsBlock.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} :
    JsBlock C M J k → m (JsBlock C' M' J k)
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
  | .lastIter x nt n b rest =>
    return .lastIter x nt (← n.renameM rc rm) (← b.renameM (JsRenM.lift rc) rm) (← rest.renameM rc rm)
  | .forOf x l xs b rest =>
    return .forOf x l (← xs.renameM rc rm) (← b.renameM (JsRenM.lift rc) rm) (← rest.renameM rc rm)

/-- Rename the variables of the arms of a case analysis on an enum. -/
def JsEnumArms.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} {n : Nat} :
    JsEnumArms C M J k n → m (JsEnumArms C' M' J k n)
  | .nil => pure .nil
  | .cons b rest => return .cons (← b.renameM rc rm) (← rest.renameM rc rm)

/-- Rename the variables of the arms of a case analysis on a union. -/
def JsUnionArms.renameM {m : Type → Type} [Monad m] {C M C' M' J : List JsTy}
    (rc : JsRenM m C C') (rm : JsRenM m M M') {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → m (JsUnionArms C' M' J k cs)
  | .nil => pure .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.renameM (JsRenM.liftAll us rc) rm) (← rest.renameM rc rm)
end

/-- The identity renaming. -/
def JsRen.id {Γ : List JsTy} : JsRenM Id Γ Γ := fun x => x

/-- The renaming that skips the innermost variable. -/
def JsRen.succ {Γ : List JsTy} {σ : JsTy} : JsRenM Id Γ (σ :: Γ) := fun x => JsMem.succ x

/-- An expression under a new constant. -/
def JsExpr.wkC {C M : List JsTy} {σ τ : JsTy} (e : JsExpr C M τ) : JsExpr (σ :: C) M τ :=
  Id.run (e.renameM JsRen.succ JsRen.id)

/-- An expression under a new mutable variable. -/
def JsExpr.wkM {C M : List JsTy} {σ τ : JsTy} (e : JsExpr C M τ) : JsExpr C (σ :: M) τ :=
  Id.run (e.renameM JsRen.id JsRen.succ)

/-- An expression that mentions no variable, in the empty contexts. -/
def JsExpr.closed? {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : Option (JsExpr [] [] τ) :=
  e.renameM (fun _ => none) (fun _ => none)

/-- An expression that mentions no variable, in any contexts. -/
def JsExpr.embed {C M : List JsTy} {τ : JsTy} (e : JsExpr [] [] τ) : JsExpr C M τ :=
  Id.run (e.renameM (fun x => nomatch x) (fun x => nomatch x))

/-- A block that mentions no join point bound outside it, under join points `J`. -/
def JsBlock.embedJ? {C M J : List JsTy} {k : JsEnd} (J' : List JsTy) :
    JsBlock C M J k → Option (JsBlock C M J' k) :=
  fun b => if h : J = J' then some (h ▸ b) else none

/-! ## Substitution of the constants -/

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

/-! ## Occurrences -/

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
