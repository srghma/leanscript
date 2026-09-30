module

public import JsTerm.Syntax.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Additions of literals, folded through constants

After the conversion and the rewrites of loops (`JsTerm.Lower.Unroll`), a block may add two
literals one after the other to the same value, through a constant:

```js
const x = p + 2;            // …
if (j === 0) { return x; }
j--;
p = x + 3;                  // is `p = p + 5;`
```

The `Term` optimiser (`Term.arithWalk`) folds such chains when they are one expression; here the
chain goes through a `const` (or appears only once two iterations of a loop are put in one step),
which `Term` does not see.  `JsBlock.foldAdds` rewrites every `x + c₂` (`x` a constant holding
`a + c₁`, `a` a variable and `c₁`, `c₂` literals; on integers, a subtraction of a literal is an
addition of its opposite) to `a + (c₁ + c₂)`: the value only depends on
`a` (not on `x`), so the constant `x` is read less, and two dependent additions become one.

**When.**  The rewrite reads `a` where the program read `x`:

* a constant `a` never changes;
* a mutable variable `a` must not have been assigned since `x` was bound: every fact about
  mutable variables is forgotten at an assignment of the variable, at a test of a loop counter
  (`tick`, `j--`), after a call (`f(…)`, which could run a closure assigning it), inside a loop
  or a closure (which run later, maybe after an assignment), and after a loop or a join point
  (whose body may have assigned it).

**Numbers.**  On `BigInt`s, `+` is exact: `(a + c₁) + c₂ = a + (c₁ + c₂)` always.  On safe
integers (`int53__lean_int_add`, `uint53__lean_nat_add`, which throw on a result that is not a
safe integer), the two literals must have the same sign (a natural number always has): then
`a + (c₁ + c₂)` is not safe whenever `a + c₁` is not, so the rewritten program throws whenever
the original did (the constant `x`, if still read, is still computed first), and when neither
throws the values are equal.  The sum of the literals must itself be a safe integer.
-/

namespace MoreJs

variable {S : JsSig}

/-- An addition of a literal: at which representation. -/
inductive AddKind where
  | int53
  | uint53
  | bigInt
  | bigNat
  deriving BEq, DecidableEq, Repr

/-- The addition may throw (on a result that is not a safe integer). -/
def AddKind.mayThrow : AddKind → Bool
  | .int53 | .uint53 => true
  | .bigInt | .bigNat => false

/-- `a + c` (`c` a literal, on either side) or, on integers, `a - c` (as `a + (-c)`), as
    `(kind, a, c)`. -/
def JsExpr.addLit? {C M : List JsTy} {τ : JsTy} :
    JsExpr S C M τ → Option (AddKind × JsExpr S C M τ × Int)
  | .imported .int53__lean_int_add (.cons a (.cons (.lit (.int53 c _)) .nil)) => some (.int53, a, c)
  | .imported .int53__lean_int_add (.cons (.lit (.int53 c _)) (.cons a .nil)) => some (.int53, a, c)
  | .imported .uint53__lean_nat_add (.cons a (.cons (.lit (.uint53 c _)) .nil)) =>
    some (.uint53, a, c)
  | .imported .uint53__lean_nat_add (.cons (.lit (.uint53 c _)) (.cons a .nil)) =>
    some (.uint53, a, c)
  | .inlined .bigint_int__lean_int_add (.cons a (.cons (.lit (.bigint_int c)) .nil)) =>
    some (.bigInt, a, c)
  | .inlined .bigint_int__lean_int_add (.cons (.lit (.bigint_int c)) (.cons a .nil)) =>
    some (.bigInt, a, c)
  | .inlined .bigint_nat__lean_nat_add (.cons a (.cons (.lit (.bigint_nat c)) .nil)) =>
    some (.bigNat, a, c)
  | .inlined .bigint_nat__lean_nat_add (.cons (.lit (.bigint_nat c)) (.cons a .nil)) =>
    some (.bigNat, a, c)
  | .imported .int53__lean_int_sub (.cons a (.cons (.lit (.int53 c _)) .nil)) => some (.int53, a, -c)
  | .inlined .bigint_int__lean_int_sub (.cons a (.cons (.lit (.bigint_int c)) .nil)) =>
    some (.bigInt, a, -c)
  | _ => none

/-- `a + c` at the representation `k`, written `a - (-c)` when `c < 0` (`none` when `τ` is not
    `k`'s type, or `c` does not fit). -/
def JsExpr.mkAddLit? {C M : List JsTy} : (k : AddKind) → {τ : JsTy} → JsExpr S C M τ → Int →
    Option (JsExpr S C M τ)
  | .int53, .terminal .int53, a, c =>
    if h : c.natAbs ≤ maxSafe then
      if c < 0 then
        some (.imported .int53__lean_int_sub
          (.cons a (.cons (.lit (.int53 (-c) (by rw [Int.natAbs_neg]; exact h))) .nil)))
      else some (.imported .int53__lean_int_add (.cons a (.cons (.lit (.int53 c h)) .nil)))
    else none
  | .uint53, .terminal .uint53, a, c =>
    if h : 0 ≤ c ∧ c.toNat ≤ maxSafe then
      some (.imported .uint53__lean_nat_add (.cons a (.cons (.lit (.uint53 c.toNat h.2)) .nil)))
    else none
  | .bigInt, .terminal .bigint_int, a, c =>
    if c < 0 then some (.inlined .bigint_int__lean_int_sub (.cons a (.cons (.lit (.bigint_int (-c))) .nil)))
    else some (.inlined .bigint_int__lean_int_add (.cons a (.cons (.lit (.bigint_int c)) .nil)))
  | .bigNat, .terminal .bigint_nat, a, c =>
    if 0 ≤ c then
      some (.inlined .bigint_nat__lean_nat_add (.cons a (.cons (.lit (.bigint_nat c.toNat)) .nil)))
    else none
  | _, _, _, _ => none

/-- What is known of a constant (by its level): it holds `base + c` at representation `kind`,
    `base` a variable (`isMut`, by its level). -/
structure AddFact where
  /-- The level of the constant. -/
  lvl : Nat
  kind : AddKind
  /-- The variable added to: a mutable variable? -/
  isMut : Bool
  /-- The level of the variable added to. -/
  base : Nat
  c : Int
  deriving Repr

/-- The facts known at a point of a block. -/
abbrev AddEnv := List AddFact

namespace AddEnv

/-- Forget the facts about every mutable variable. -/
def dropMut (env : AddEnv) : AddEnv := env.filter (!·.isMut)

/-- Forget the facts about the mutable variable of level `l` (just assigned). -/
def kill (env : AddEnv) (l : Nat) : AddEnv := env.filter fun f => !(f.isMut && f.base == l)

end AddEnv

mutual
/-- Does the expression call a function (which might assign a mutable variable)? -/
partial def JsExpr.calls {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .app .. => true
  | .imported _ as => as.calls
  | .inlined _ as => as.calls
  | .record_mk fs => fs.calls
  | .union_mk _ as => as.calls
  | .listOp _ as => as.calls
  | .fold _ e => e.calls
  | .unfold _ e => e.calls
  | .enumIndex _ e => e.calls
  | .enumEq a b => a.calls || b.calls
  | .index _ _ a i => a.calls || i.calls
  | .cond c a b => c.calls || a.calls || b.calls
  | .array_mk _ ps => ps.calls
  | .list_mk ps => ps.calls
  | _ => false
/-- `calls` of arguments. -/
partial def JsArgs.calls {C M : List JsTy} {σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => false
  | .cons a as => a.calls || as.calls
/-- `calls` of the parts of an array literal. -/
partial def JsParts.calls {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → Bool
  | .nil => false
  | .elem e rest => e.calls || rest.calls
  | .spread a rest => a.calls || rest.calls
end

/-- The variable of level `l` (a mutable variable or a constant), at type `τ`. -/
def varAt? {C M : List JsTy} (isMut : Bool) (l : Nat) (τ : JsTy) : Option (JsExpr S C M τ) :=
  if isMut then (JsMem.ofIndex? M (M.length - 1 - l) τ).map .mvar
  else (JsMem.ofIndex? C (C.length - 1 - l) τ).map .cvar

/-- The level of a variable read by the expression (a constant or a mutable variable). -/
def JsExpr.varLevel? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option (Bool × Nat)
  | .cvar x => some (false, C.length - 1 - x.index)
  | .mvar x => some (true, M.length - 1 - x.index)
  | _ => none

/-- `x + c₂` with `x` a constant holding `a + c₁`, as `a + (c₁ + c₂)` (else as it is). -/
def JsExpr.foldAddTop {C M : List JsTy} {τ : JsTy} (env : AddEnv) (e : JsExpr S C M τ) :
    JsExpr S C M τ :=
  (go).getD e
where
  go : Option (JsExpr S C M τ) := do
    let (k, x, c2) ← e.addLit?
    let .cvar v := x | none
    let f ← env.find? (·.lvl == C.length - 1 - v.index)
    unless f.kind == k do none
    if k.mayThrow && f.c * c2 < 0 then none
    let a ← varAt? f.isMut f.base τ
    JsExpr.mkAddLit? k a (f.c + c2)

mutual
/-- `foldAddTop` everywhere in the expression, bottom-up (in a closure, only the facts about
    constants hold). -/
partial def JsExpr.foldAdds {C M : List JsTy} (env : AddEnv) {τ : JsTy} :
    JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => JsExpr.foldAddTop env (.imported op (as.foldAdds env))
  | .inlined op as => JsExpr.foldAddTop env (.inlined op (as.foldAdds env))
  | .app f as => .app (f.foldAdds env) (as.foldAdds env)
  | .lam hints body => .lam hints (body.foldAdds env.dropMut)
  | .record_mk fs => .record_mk (fs.foldAdds env)
  | .union_mk ix as => .union_mk ix (as.foldAdds env)
  | .enumIndex nt e => .enumIndex nt (e.foldAdds env)
  | .enumEq a b => .enumEq (a.foldAdds env) (b.foldAdds env)
  | .index l nt a i => .index l nt (a.foldAdds env) (i.foldAdds env)
  | .array_mk l ps => .array_mk l (ps.foldAdds env)
  | .list_mk ps => .list_mk (ps.foldAdds env)
  | .cond c a b => .cond (c.foldAdds env) (a.foldAdds env) (b.foldAdds env)
  | .listOp op as => .listOp op (as.foldAdds env)
  | .fold i e => .fold i (e.foldAdds env)
  | .unfold i e => .unfold i (e.foldAdds env)
  | e => e
/-- `foldAdds` of arguments. -/
partial def JsArgs.foldAdds {C M : List JsTy} (env : AddEnv) {σs : List JsTy} :
    JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons (a.foldAdds env) (as.foldAdds env)
/-- `foldAdds` of the parts of an array literal. -/
partial def JsParts.foldAdds {C M : List JsTy} (env : AddEnv) {A E : JsTy} :
    JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem (e.foldAdds env) (rest.foldAdds env)
  | .spread a rest => .spread (a.foldAdds env) (rest.foldAdds env)
/-- `foldAddTop` everywhere in the block, with the facts `env` known at its start (each
    `const x = a + c;` adds one). -/
partial def JsBlock.foldAdds {C M J : List JsTy} {k : JsEnd} (env : AddEnv) :
    JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret (e.foldAdds env)
  | .next => .next
  | .jump j e => .jump j (e.foldAdds env)
  | .throw m => .throw m
  | .const x e rest =>
    let e' := e.foldAdds env
    let env := if e.calls then env.dropMut else env
    let env := match e'.addLit? with
      | some (kd, a, c) => match a.varLevel? with
        | some (isMut, base) => { lvl := C.length, kind := kd, isMut, base, c } :: env
        | none => env
      | none => env
    .const x e' (rest.foldAdds env)
  | .letMut x e rest =>
    let env' := if e.calls then env.dropMut else env
    .letMut x (e.foldAdds env) (rest.foldAdds env')
  | .assign x e rest =>
    let env' := if e.calls then env.dropMut else env
    .assign x (e.foldAdds env) (rest.foldAdds (env'.kill (M.length - 1 - x.index)))
  | .destructure e sel rest =>
    let env' := if e.calls then env.dropMut else env
    .destructure (e.foldAdds env) sel (rest.foldAdds env')
  | .ite c t e =>
    let env' := if c.calls then env.dropMut else env
    .ite (c.foldAdds env) (t.foldAdds env') (e.foldAdds env')
  | .enumCases e arms =>
    let env' := if e.calls then env.dropMut else env
    .enumCases (e.foldAdds env) (arms.foldAdds env')
  | .unionCases e arms =>
    let env' := if e.calls then env.dropMut else env
    .unionCases (e.foldAdds env) (arms.foldAdds env')
  | .join x block rest => .join x (block.foldAdds env) (rest.foldAdds env.dropMut)
  | .forRange x nt n body rest =>
    .forRange x nt (n.foldAdds env) (body.foldAdds env.dropMut) (rest.foldAdds env.dropMut)
  | .forOf x l xs body rest =>
    .forOf x l (xs.foldAdds env) (body.foldAdds env.dropMut) (rest.foldAdds env.dropMut)
  | .countdown x nt n base step rest =>
    .countdown x nt (n.foldAdds env) (base.foldAdds env.dropMut) (step.foldAdds env.dropMut)
      (rest.foldAdds env.dropMut)
  | .tick nt j base rest =>
    .tick nt j (base.foldAdds env) (rest.foldAdds (env.kill (M.length - 1 - j.index)))
  | .natCase x nt n zero succ =>
    let env' := if n.calls then env.dropMut else env
    .natCase x nt (n.foldAdds env) (zero.foldAdds env') (succ.foldAdds env')
  | .funs hints defs rest => .funs hints (defs.foldAdds env.dropMut) (rest.foldAdds env.dropMut)
/-- `foldAdds` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.foldAdds {C M J : List JsTy} {k : JsEnd} {n : Nat} (env : AddEnv) :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons (b.foldAdds env) (rest.foldAdds env)
/-- `foldAdds` in the arms of a case analysis on a union. -/
partial def JsUnionArms.foldAdds {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (env : AddEnv) : JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.foldAdds env) (rest.foldAdds env)
end

/-- The function with its additions of literals folded through constants. -/
def JsFun.foldAdds (f : JsFun) : JsFun := { f with body := f.body.foldAdds [] }

end MoreJs

end
