module

public import JsTerm.Lower.Tail

@[expose] public section

set_option autoImplicit false

/-!
# The accumulator of a loop, read where it lives

The body of a fold (`Comp.nat_rec`, `Comp.array_foldl`) reads the accumulator as a parameter;
the conversion binds it to a constant at the start of every iteration
(`const a = acc; …; acc = e; continue;`, `MoreJs.loopBody`).  The accumulator is only assigned
at the end of an iteration (`JsBlock.retToNext`), after everything the iteration computes has
been computed, so every read of the constant `a` reads the value `acc` holds: the constant can
be replaced by the mutable variable itself (`JsBlock.cToM`), and an iteration that answers the
accumulator unchanged is then `acc = acc;`, which is nothing (`continue;`).  That is

```
for (const e of xs) { if (p(e)) { acc = push(acc, e); } }
```

instead of `const a = acc; if (p(e)) { acc = push(a, e); continue; } acc = a;`.

A closure (`.lam`, the definitions of `.funs`) may run after the accumulator changed, so it must
not read the constant: the replacement fails when it does (and when the body assigns the
accumulator itself, which the conversion never builds), and the constant is kept.
-/

namespace MoreJs

variable {S : JsSig}

/-- Where the constants `C` of a block go: to a constant of `C'`, or to a mutable variable of
    `M` that holds the same value. -/
abbrev CToM (C C' M : List JsTy) : Type := ∀ {τ : JsTy}, JsMem C τ → JsMem C' τ ⊕ JsMem M τ

namespace CToM

/-- Under one more constant (renamed to itself). -/
def liftC {C C' M : List JsTy} {σ : JsTy} (r : CToM C C' M) : CToM (σ :: C) (σ :: C') M :=
  fun x => match x with
    | .zero => .inl .zero
    | .succ y => (r y).elim (fun z => .inl z.succ) .inr

/-- Under the constants `us` of a pattern. -/
def liftAllC {C C' M : List JsTy} : (us : List JsTy) → CToM C C' M →
    CToM (pushAll us C) (pushAll us C') M
  | [], r => r
  | _ :: us, r => liftAllC us (liftC r)

/-- Under one more mutable variable. -/
def liftM {C C' M : List JsTy} {σ : JsTy} (r : CToM C C' M) : CToM C C' (σ :: M) :=
  fun x => (r x).elim .inl (fun z => .inr z.succ)

/-- The constants only: a renaming that fails on a constant sent to a mutable variable. -/
def consts {C C' M : List JsTy} (r : CToM C C' M) : JsRenM Option C C' :=
  fun x => (r x).elim some (fun _ => none)

end CToM

/-- The mutable variables renamed to themselves. -/
def JsRen.someM {M : List JsTy} : JsRenM Option M M := fun x => some x

mutual
/-- Replace the constants of an expression along `r` (`none` if a closure reads a constant
    sent to a mutable variable). -/
partial def JsExpr.cToM {C C' M : List JsTy} (r : CToM C C' M) {τ : JsTy} :
    JsExpr S C M τ → Option (JsExpr S C' M τ)
  | .cvar x => some ((r x).elim .cvar .mvar)
  | .mvar x => some (.mvar x)
  | .lit l => some (.lit l)
  | .imported op as => .imported op <$> as.cToM r
  | .inlined op as => .inlined op <$> as.cToM r
  | .unreachable t => some (.unreachable t)
  | .app f as => return .app (← f.cToM r) (← as.cToM r)
  | e@(.lam ..) => e.renameM r.consts JsRen.someM
  | .record_mk fs => .record_mk <$> fs.cToM r
  | .union_mk ix as => .union_mk ix <$> as.cToM r
  | .enum_mk n s i => some (.enum_mk n s i)
  | .enumIndex nt e => .enumIndex nt <$> e.cToM r
  | .enumEq a b => return .enumEq (← a.cToM r) (← b.cToM r)
  | .boolCmp op a b => return .boolCmp op (← a.cToM r) (← b.cToM r)
  | .index l nt a i => return .index l nt (← a.cToM r) (← i.cToM r)
  | .indexOr l nt a i d => return .indexOr l nt (← a.cToM r) (← i.cToM r) (← d.cToM r)
  | .array_mk l ps => .array_mk l <$> ps.cToM r
  | .list_mk ps => .list_mk <$> ps.cToM r
  | .cond c a b => return .cond (← c.cToM r) (← a.cToM r) (← b.cToM r)
  | .listOp op as => .listOp op <$> as.cToM r
  | .fold i e => .fold i <$> e.cToM r
  | .unfold i e => .unfold i <$> e.cToM r
  | .global name => some (.global name)

/-- `JsExpr.cToM` in arguments. -/
partial def JsArgs.cToM {C C' M : List JsTy} (r : CToM C C' M) {σs : List JsTy} :
    JsArgs S C M σs → Option (JsArgs S C' M σs)
  | .nil => some .nil
  | .cons a as => return .cons (← a.cToM r) (← as.cToM r)

/-- `JsExpr.cToM` in the parts of an array literal. -/
partial def JsParts.cToM {C C' M : List JsTy} (r : CToM C C' M) {A E : JsTy} :
    JsParts S C M A E → Option (JsParts S C' M A E)
  | .nil => some .nil
  | .elem e rest => return .elem (← e.cToM r) (← rest.cToM r)
  | .spread a rest => return .spread (← a.cToM r) (← rest.cToM r)

/-- Replace the constants of a block along `r`; `none` if a closure reads a constant sent to a
    mutable variable, or if the block assigns the mutable variable at position `acc`. -/
partial def JsBlock.cToM {C C' M J : List JsTy} (r : CToM C C' M) (acc : Nat) {k : JsEnd} :
    JsBlock S C M J k → Option (JsBlock S C' M J k)
  | .ret e => .ret <$> e.cToM r
  | .next => some .next
  | .jump j e => .jump j <$> e.cToM r
  | .throw msg => some (.throw msg)
  | .raise e => .raise <$> e.cToM r
  | .const x e rest => return .const x (← e.cToM r) (← rest.cToM r.liftC acc)
  | .letMut x e rest => return .letMut x (← e.cToM r) (← rest.cToM r.liftM (acc + 1))
  | .assign x e rest =>
    if x.index == acc then none else return .assign x (← e.cToM r) (← rest.cToM r acc)
  | .destructure (us := us) e sel rest =>
    return .destructure (← e.cToM r) sel (← rest.cToM (CToM.liftAllC us r) acc)
  | .ite c t e => return .ite (← c.cToM r) (← t.cToM r acc) (← e.cToM r acc)
  | .enumCases e arms => return .enumCases (← e.cToM r) (← arms.cToM r acc)
  | .unionCases e arms => return .unionCases (← e.cToM r) (← arms.cToM r acc)
  | .join x b rest => return .join x (← b.cToM r acc) (← rest.cToM r.liftC acc)
  | .forRange x nt n b rest =>
    return .forRange x nt (← n.cToM r) (← b.cToM r.liftC acc) (← rest.cToM r acc)
  | .forOf x l xs b rest =>
    return .forOf x l (← xs.cToM r) (← b.cToM r.liftC acc) (← rest.cToM r acc)
  | .countdown x nt n b s rest =>
    return .countdown x nt (← n.cToM r) (← b.cToM r.liftM (acc + 1))
      (← s.cToM r.liftM (acc + 1)) (← rest.cToM r.liftC acc)
  | .forExit x nt n b d rest =>
    return .forExit x nt (← n.cToM r) (← b.cToM r.liftC acc) (← d.cToM r acc)
      (← rest.cToM r.liftC acc)
  | .tick nt j b rest => return .tick nt j (← b.cToM r acc) (← rest.cToM r acc)
  | .natCase x nt n z s =>
    return .natCase x nt (← n.cToM r) (← z.cToM r acc) (← s.cToM r.liftC acc)
  | .funs (τs := τs) xs defs rest =>
    return .funs xs (← defs.renameM (JsRenM.liftAll τs r.consts) JsRen.someM)
      (← rest.cToM (CToM.liftAllC τs r) acc)

/-- `JsBlock.cToM` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.cToM {C C' M J : List JsTy} (r : CToM C C' M) (acc : Nat) {k : JsEnd}
    {n : Nat} : JsEnumArms S C M J k n → Option (JsEnumArms S C' M J k n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.cToM r acc) (← rest.cToM r acc)

/-- `JsBlock.cToM` in the arms of a case analysis on a union. -/
partial def JsUnionArms.cToM {C C' M J : List JsTy} (r : CToM C C' M) (acc : Nat) {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms S C M J k cs → Option (JsUnionArms S C' M J k cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.cToM (CToM.liftAllC us r) acc) (← rest.cToM r acc)
end

/-- The body of a loop whose accumulator, the innermost constant, is the mutable variable
    `acc`: the constant replaced by the variable (`none` when that is not possible). -/
def JsBlock.accAsMut? {C M J : List JsTy} {α E : JsTy} {k : JsEnd} (acc : JsMem M α)
    (body : JsBlock S (α :: E :: C) M J k) : Option (JsBlock S (E :: C) M J k) :=
  let r : CToM (α :: E :: C) (E :: C) M := fun x => match x with
    | .zero => .inr acc
    | .succ y => .inl y
  body.cToM r acc.index

end MoreJs

end
