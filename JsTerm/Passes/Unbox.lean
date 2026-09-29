module

public import JsTerm.Passes.Cleanup

@[expose] public section

set_option autoImplicit false

/-!
# Unboxed accumulators, flattened join points, dead constants

More clean-ups of `JsTerm`, type-preserving like the others (a `JsBlock C M J k` to a
`JsBlock C M J k`); none of them has a proof (`JsTerm` has no semantics), they are checked by
the snapshots and their differential checks.

* **accumulators of one constructor** (`unboxNode`): `let acc = { tag: i, _1: a };` whose every
  assignment is a constructor of the same tag `i` (`acc = { tag: i, _1: e };`), and which is
  only read as the subject of case analyses, always holds the constructor `i`.  It becomes
  `let acc = a;` (`acc = e;`), and a case analysis of it is its arm `i`, reading the field from
  `acc` (`const f = acc;`).  This is the state of a `for … in` loop of `Id.run do` that never
  breaks (`ForInStep.yield`); a constructor without fields needs no variable at all.  A read
  of `acc` anywhere else (in a closure, as a value) leaves it alone;
* **join points of one jump** (`flattenJoinNode`): `let x; L: { S }` and the rest `R`, when `S`
  jumps to it exactly once: `S` with `const x = e; R` in place of that jump (`R` is written
  once either way, and runs right after the jump did);
* **copies of a mutable variable read before it changes** (`copyMutNode`): `const y = acc;`
  when every read of `y` comes before any assignment of `acc` (on every path, not in a
  closure): the reads read `acc` (`const f = acc; acc = push(f, x);` is
  `acc = push(acc, x);`);
* **dead constants** (`deadConstNode`): `const x = e;` nothing reads, when `e` has no effect
  and cannot throw.
-/

namespace MoreJs

/-! ## Expressions without effect -/

mutual
/-- Can the expression be dropped: it has no effect and cannot throw (a call of a closure
    could do anything; an operation of the runtime or an inlined one says). -/
partial def JsExpr.discardable {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .cvar _ | .mvar _ | .global .. | .lit _ | .enum_mk .. | .unreachable _ | .lam .. => true
  | .imported (e := e) (t := t) _ as | .inlined (e := e) (t := t) _ as =>
    e == .pure && t == .doesntThrow && as.discardable
  | .app .. => false
  | .record_mk fs => fs.discardable
  | .union_mk _ as => as.discardable
  | .array_mk _ ps | .list_mk ps => ps.discardable
  | .cond c a b => c.discardable && a.discardable && b.discardable
/-- `discardable` of arguments. -/
partial def JsArgs.discardable {C M σs : List JsTy} : JsArgs C M σs → Bool
  | .nil => true
  | .cons a as => a.discardable && as.discardable
/-- `discardable` of the parts of an array literal. -/
partial def JsParts.discardable {C M : List JsTy} {A E : JsTy} : JsParts C M A E → Bool
  | .nil => true
  | .elem e rest | .spread e rest => e.discardable && rest.discardable
end

/-- `const x = e; rest` with `x` not read in `rest` and `e` without effect: `rest`. -/
def deadConstNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if e.discardable && !rest.mentions ⟨false, 0⟩ then
      match rest.renameM JsRen.strengthen (fun x => some x) with
      | some r => r
      | none => b
    else b
  | b => b

/-! ## Accumulators of one constructor -/

/-- What `unboxBlock` knows: the renaming of the other mutable variables (the accumulator is
    renamed to nothing), the index of the accumulator, its tag, and the variable that holds its
    field (none when the constructor has no field). -/
structure Unbox (M M' : List JsTy) (F : JsTy) where
  ren : JsRenM Option M M'
  acc : Nat
  tag : Nat
  new : Option (JsMem M' F)

/-- Under one more mutable variable. -/
def Unbox.lift {M M' : List JsTy} {F σ : JsTy} (u : Unbox M M' F) : Unbox (σ :: M) (σ :: M') F where
  ren := JsRenM.lift u.ren
  acc := u.acc + 1
  tag := u.tag
  new := u.new.map .succ

/-- An expression, which must not read the accumulator. -/
def Unbox.expr {M M' : List JsTy} {F : JsTy} (u : Unbox M M' F) {C : List JsTy} {τ : JsTy}
    (e : JsExpr C M τ) : Option (JsExpr C M' τ) :=
  e.renameM (fun x => some x) u.ren

/-- The field of a constructor of one field. -/
def JsArgs.single? {C M σs : List JsTy} {F : JsTy} : JsArgs C M σs → Option (JsExpr C M F)
  | .cons (σ := σ) a .nil => if h : σ = F then some (h ▸ a) else none
  | _ => none

mutual
/-- The block with the accumulator unboxed (see above), or `none` if it is used otherwise. -/
partial def JsBlock.unbox {M M' : List JsTy} {F : JsTy} (u : Unbox M M' F) {C J : List JsTy}
    {k : JsEnd} : JsBlock C M J k → Option (JsBlock C M' J k)
  | .ret e => .ret <$> u.expr e
  | .next => some .next
  | .jump j e => .jump j <$> u.expr e
  | .throw msg => some (.throw msg)
  | .const x e rest => return .const x (← u.expr e) (← rest.unbox u)
  | .letMut x e rest => return .letMut x (← u.expr e) (← rest.unbox u.lift)
  | .assign x e rest =>
    if x.index == u.acc then
      match e with
      | .union_mk ix args =>
        if ix.index != u.tag then none else
        match u.new with
        | none => rest.unbox u
        | some v => do
          let a ← JsArgs.single? (F := F) args
          return .assign v (← u.expr a) (← rest.unbox u)
      | _ => none
    else return .assign (← u.ren x) (← u.expr e) (← rest.unbox u)
  | .destructure e sel rest => return .destructure (← u.expr e) sel (← rest.unbox u)
  | .ite c t e => return .ite (← u.expr c) (← t.unbox u) (← e.unbox u)
  | .enumCases e arms => return .enumCases (← u.expr e) (← arms.unbox u)
  | .unionCases (.mvar x) arms =>
    if x.index == u.acc then arms.pick u 0 else
    return .unionCases (.mvar (← u.ren x)) (← arms.unboxArms u)
  | .unionCases e arms => return .unionCases (← u.expr e) (← arms.unboxArms u)
  | .join x b rest => return .join x (← b.unbox u) (← rest.unbox u)
  | .forRange x nt n b rest => return .forRange x nt (← u.expr n) (← b.unbox u) (← rest.unbox u)
  | .lastIter x nt n b rest => return .lastIter x nt (← u.expr n) (← b.unbox u) (← rest.unbox u)
  | .forOf x l xs b rest => return .forOf x l (← u.expr xs) (← b.unbox u) (← rest.unbox u)
/-- `unbox` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.unbox {M M' : List JsTy} {F : JsTy} (u : Unbox M M' F) {C J : List JsTy}
    {k : JsEnd} {n : Nat} : JsEnumArms C M J k n → Option (JsEnumArms C M' J k n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.unbox u) (← rest.unbox u)
/-- `unbox` in the arms of a case analysis on a union. -/
partial def JsUnionArms.unboxArms {M M' : List JsTy} {F : JsTy} (u : Unbox M M' F)
    {C J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → Option (JsUnionArms C M' J k cs)
  | .nil => some .nil
  | .cons sel b rest => return .cons sel (← b.unbox u) (← rest.unboxArms u)
/-- The arm of the accumulator's tag (the arms from the `i`-th), reading its field from the
    variable holding it. -/
partial def JsUnionArms.pick {M M' : List JsTy} {F : JsTy} (u : Unbox M M' F) {C J : List JsTy}
    {k : JsEnd} {cs : List (List JsTy)} (i : Nat) :
    JsUnionArms C M J k cs → Option (JsBlock C M' J k)
  | .nil => none
  | .cons (us := us) sel b rest =>
    if i != u.tag then rest.pick u (i + 1) else do
    let b' ← b.unbox u
    match us, b' with
    | [], b' => some b'
    | [σ], b' =>
      match u.new with
      | some v => if h : F = σ then some (.const ((sel.binds.head?.map (·.2)).getD "f")
          (.mvar (h ▸ v)) b') else none
      | none => none
    | _, _ => none
end

/-- The renaming that drops the innermost variable (which must not occur) for another one. -/
def JsRen.replaceHead {Γ : List JsTy} {σ σ' : JsTy} : JsRenM Option (σ :: Γ) (σ' :: Γ) := fun x =>
  match x with
  | .zero => none
  | .succ x => some (.succ x)

/-- `let acc = { tag: i, … }; rest` with `acc` of one constructor: unboxed (see above). -/
def unboxNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.letMut (τ := .union _ _ _) x (.union_mk ix args) rest) =>
    match args with
    | .nil =>
      let u : Unbox _ M (.terminal .bool) :=
        { ren := JsRen.strengthen, acc := 0, tag := ix.index, new := none }
      (rest.unbox u).getD b
    | .cons (σ := σ) a .nil =>
      let u : Unbox _ (σ :: M) σ :=
        { ren := JsRen.replaceHead, acc := 0, tag := ix.index, new := some .zero }
      match rest.unbox u with
      | some r => .letMut x a r
      | none => b
    | _ => b
  | b => b

/-! ## Accumulators that are records -/

/-- Mutable variables of the types `ts`, in order. -/
inductive JsVars (M : List JsTy) : List JsTy → Type where
  | nil : JsVars M []
  | cons {t : JsTy} {ts : List JsTy} : JsMem M t → JsVars M ts → JsVars M (t :: ts)

/-- The variables under one more mutable variable. -/
def JsVars.succ {M : List JsTy} {σ : JsTy} : {ts : List JsTy} → JsVars M ts → JsVars (σ :: M) ts
  | _, .nil => .nil
  | _, .cons v vs => .cons (.succ v) vs.succ

/-- The variables `let x₁ = e₁; …; let xₙ = eₙ;` binds (the last one innermost). -/
def JsVars.init {M : List JsTy} : (ts : List JsTy) → JsVars (pushAll ts M) ts
  | [] => .nil
  | _ :: ts => .cons (JsRen.skipAll ts .zero) (JsVars.init (M := _ :: M) ts)

/-- Arguments under one more mutable variable. -/
def JsArgs.wkM {C M σs : List JsTy} {σ : JsTy} (as : JsArgs C M σs) : JsArgs C (σ :: M) σs :=
  Id.run (as.renameM JsRen.id JsRen.succ)

/-- `let x₁ = e₁; …; let xₙ = eₙ; rest` (each `eᵢ` evaluated before `xᵢ` is bound). -/
def JsArgs.letChain {C J : List JsTy} {k : JsEnd} (hint : String) :
    {M ts : List JsTy} → JsArgs C M ts → JsBlock C (pushAll ts M) J k → JsBlock C M J k
  | _, [], .nil, rest => rest
  | _, _ :: _, .cons a as, rest => .letMut hint a (JsArgs.letChain hint as.wkM rest)

/-- `x₁ = e₁; …; xₙ = eₙ; rest`. -/
def JsArgs.assignChain {C M J : List JsTy} {k : JsEnd} :
    {ts : List JsTy} → JsVars M ts → JsArgs C M ts → JsBlock C M J k → JsBlock C M J k
  | [], .nil, .nil, rest => rest
  | _ :: _, .cons v vs, .cons a as, rest => .assign v a (JsArgs.assignChain vs as rest)

/-- `const y₁ = x₁; …` for the fields a pattern keeps, then `rest`. -/
def JsSel.readVars {M J : List JsTy} {k : JsEnd} :
    {C ts us : List JsTy} → JsSel ts us → JsVars M ts → JsBlock (pushAll us C) M J k →
      JsBlock C M J k
  | _, [], [], .nil, .nil, rest => rest
  | _, _ :: _, _ :: _, .keep h s, .cons v vs, rest => .const h (.mvar v) (JsSel.readVars s vs rest)
  | _, _ :: _, _, .skip s, .cons _ vs, rest => JsSel.readVars s vs rest

/-- What `JsBlock.scalar` knows: the renaming of the other mutable variables (the accumulator
    is renamed to nothing), the index of the accumulator, and the variables of its fields. -/
structure Scalar (M M' : List JsTy) (ts : List JsTy) where
  ren : JsRenM Option M M'
  acc : Nat
  vars : JsVars M' ts

/-- Under one more mutable variable. -/
def Scalar.lift {M M' ts : List JsTy} {σ : JsTy} (u : Scalar M M' ts) :
    Scalar (σ :: M) (σ :: M') ts where
  ren := JsRenM.lift u.ren
  acc := u.acc + 1
  vars := u.vars.succ

/-- An expression, which must not read the accumulator. -/
def Scalar.expr {M M' ts : List JsTy} (u : Scalar M M' ts) {C : List JsTy} {τ : JsTy}
    (e : JsExpr C M τ) : Option (JsExpr C M' τ) :=
  e.renameM (fun x => some x) u.ren

/-- Arguments, which must not read the accumulator. -/
def Scalar.args {M M' ts : List JsTy} (u : Scalar M M' ts) {C σs : List JsTy}
    (as : JsArgs C M σs) : Option (JsArgs C M' σs) :=
  as.renameM (fun x => some x) u.ren

mutual
/-- The block with the accumulator, a record, replaced by one variable per field: every
    assignment of it must be a record literal, and every read a pattern (`none` otherwise). -/
partial def JsBlock.scalar {M M' ts : List JsTy} (u : Scalar M M' ts) {C J : List JsTy}
    {k : JsEnd} : JsBlock C M J k → Option (JsBlock C M' J k)
  | .ret e => .ret <$> u.expr e
  | .next => some .next
  | .jump j e => .jump j <$> u.expr e
  | .throw msg => some (.throw msg)
  | .const x e rest => return .const x (← u.expr e) (← rest.scalar u)
  | .letMut x e rest => return .letMut x (← u.expr e) (← rest.scalar u.lift)
  | .assign x e rest =>
    if x.index == u.acc then
      match e with
      | .record_mk (f₁ := f₁) (f₂ := f₂) (fs := fs) args =>
        if h : f₁ :: f₂ :: fs = ts then do
          let args ← u.args args
          return JsArgs.assignChain u.vars (h ▸ args) (← rest.scalar u)
        else none
      | _ => none
    else return .assign (← u.ren x) (← u.expr e) (← rest.scalar u)
  | .destructure (f₁ := f₁) (f₂ := f₂) (fs := fs) (.mvar x) sel rest =>
    if x.index == u.acc then
      if h : ts = f₁ :: f₂ :: fs then do
        return JsSel.readVars sel (h ▸ u.vars) (← rest.scalar u)
      else none
    else return .destructure (.mvar (← u.ren x)) sel (← rest.scalar u)
  | .destructure e sel rest => return .destructure (← u.expr e) sel (← rest.scalar u)
  | .ite c t e => return .ite (← u.expr c) (← t.scalar u) (← e.scalar u)
  | .enumCases e arms => return .enumCases (← u.expr e) (← arms.scalar u)
  | .unionCases e arms => return .unionCases (← u.expr e) (← arms.scalar u)
  | .join x b rest => return .join x (← b.scalar u) (← rest.scalar u)
  | .forRange x nt n b rest => return .forRange x nt (← u.expr n) (← b.scalar u) (← rest.scalar u)
  | .lastIter x nt n b rest => return .lastIter x nt (← u.expr n) (← b.scalar u) (← rest.scalar u)
  | .forOf x l xs b rest => return .forOf x l (← u.expr xs) (← b.scalar u) (← rest.scalar u)
/-- `scalar` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.scalar {M M' ts : List JsTy} (u : Scalar M M' ts) {C J : List JsTy}
    {k : JsEnd} {n : Nat} : JsEnumArms C M J k n → Option (JsEnumArms C M' J k n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.scalar u) (← rest.scalar u)
/-- `scalar` in the arms of a case analysis on a union. -/
partial def JsUnionArms.scalar {M M' ts : List JsTy} (u : Scalar M M' ts) {C J : List JsTy}
    {k : JsEnd} {cs : List (List JsTy)} : JsUnionArms C M J k cs → Option (JsUnionArms C M' J k cs)
  | .nil => some .nil
  | .cons sel b rest => return .cons sel (← b.scalar u) (← rest.scalar u)
end

/-- The renaming that drops the innermost variable (which must not occur) under the
    variables `ts`. -/
def JsRen.replaceHeadAll {Γ : List JsTy} {σ : JsTy} (ts : List JsTy) :
    JsRenM Option (σ :: Γ) (pushAll ts Γ) := fun x =>
  match x with
  | .zero => none
  | .succ x => some (JsRen.skipAll ts x)

/-- `let acc = { _1: a, _2: b }; rest` where every assignment of `acc` is a record literal and
    every read of it a pattern: one mutable variable per field (`let acc = a; let acc$1 = b;`,
    `acc = e; acc$1 = f;`, `const f = acc;` for a pattern). -/
def scalarNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.letMut x (.record_mk (f₁ := f₁) (f₂ := f₂) (fs := fs) args) rest) =>
    let ts := f₁ :: f₂ :: fs
    let u : Scalar _ (pushAll ts M) ts :=
      { ren := JsRen.replaceHeadAll ts, acc := 0, vars := JsVars.init ts }
    match rest.scalar u with
    | some r => JsArgs.letChain x args r
    | none => b
  | b => b

/-! ## Join points of one jump -/

/-- A renaming of join points. -/
abbrev JsJRen (J J' : List JsTy) : Type := ∀ {τ : JsTy}, JsMem J τ → Option (JsMem J' τ)

/-- The renaming under one more join point. -/
def JsJRen.lift {J J' : List JsTy} {σ : JsTy} (r : JsJRen J J') : JsJRen (σ :: J) (σ :: J') :=
  fun x => match x with
    | .zero => some .zero
    | .succ x => JsMem.succ <$> r x

/-- The renaming that drops the innermost join point (which must not be jumped to). -/
def JsJRen.drop {J : List JsTy} {σ : JsTy} : JsJRen (σ :: J) J := fun x =>
  match x with
  | .zero => none
  | .succ x => some x

mutual
/-- Rename the join points of a block (the bodies of loops and closures have their own). -/
partial def JsBlock.renameJ {C M J J' : List JsTy} {k : JsEnd} (r : JsJRen J J') :
    JsBlock C M J k → Option (JsBlock C M J' k)
  | .ret e => some (.ret e)
  | .next => some .next
  | .jump j e => return .jump (← r j) e
  | .throw msg => some (.throw msg)
  | .const x e rest => .const x e <$> rest.renameJ r
  | .letMut x e rest => .letMut x e <$> rest.renameJ r
  | .assign x e rest => .assign x e <$> rest.renameJ r
  | .destructure e sel rest => .destructure e sel <$> rest.renameJ r
  | .ite c t e => return .ite c (← t.renameJ r) (← e.renameJ r)
  | .enumCases e arms => .enumCases e <$> arms.renameJ r
  | .unionCases e arms => .unionCases e <$> arms.renameJ r
  | .join x b rest => return .join x (← b.renameJ r.lift) (← rest.renameJ r)
  | .forRange x nt n b rest => .forRange x nt n b <$> rest.renameJ r
  | .lastIter x nt n b rest => .lastIter x nt n b <$> rest.renameJ r
  | .forOf x l xs b rest => .forOf x l xs b <$> rest.renameJ r
/-- `renameJ` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.renameJ {C M J J' : List JsTy} {k : JsEnd} {n : Nat} (r : JsJRen J J') :
    JsEnumArms C M J k n → Option (JsEnumArms C M J' k n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.renameJ r) (← rest.renameJ r)
/-- `renameJ` in the arms of a case analysis on a union. -/
partial def JsUnionArms.renameJ {C M J J' : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (r : JsJRen J J') : JsUnionArms C M J k cs → Option (JsUnionArms C M J' k cs)
  | .nil => some .nil
  | .cons sel b rest => return .cons sel (← b.renameJ r) (← rest.renameJ r)
end

mutual
/-- The number of jumps to join point `i` (bodies of loops and closures have their own). -/
partial def JsBlock.jumpsTo {C M J : List JsTy} {k : JsEnd} (i : Nat) : JsBlock C M J k → Nat
  | .jump j _ => if j.index == i then 1 else 0
  | .ret _ | .next | .throw _ => 0
  | .const _ _ rest | .letMut _ _ rest | .assign _ _ rest | .destructure _ _ rest
  | .forRange _ _ _ _ rest | .lastIter _ _ _ _ rest | .forOf _ _ _ _ rest => rest.jumpsTo i
  | .ite _ t e => t.jumpsTo i + e.jumpsTo i
  | .enumCases _ arms => arms.jumpsTo i
  | .unionCases _ arms => arms.jumpsTo i
  | .join _ b rest => b.jumpsTo (i + 1) + rest.jumpsTo i
/-- `jumpsTo` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.jumpsTo {C M J : List JsTy} {k : JsEnd} {n : Nat} (i : Nat) :
    JsEnumArms C M J k n → Nat
  | .nil => 0
  | .cons b rest => b.jumpsTo i + rest.jumpsTo i
/-- `jumpsTo` of the arms of a case analysis on a union. -/
partial def JsUnionArms.jumpsTo {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (i : Nat) : JsUnionArms C M J k cs → Nat
  | .nil => 0
  | .cons _ b rest => b.jumpsTo i + rest.jumpsTo i
end

mutual
/-- The block of a join point with its only jump (to join point `0`) replaced by
    `const x = e; rest`; `rest` is moved under the binders the path to the jump goes through
    (`rc`, `rm`).  `none` if the jump is inside a nested join block. -/
partial def JsBlock.flatJoin {C₀ M₀ J : List JsTy} {τ : JsTy} {k : JsEnd} {C M : List JsTy} :
    JsBlock C M (τ :: J) k → (hint : String) → (rest : JsBlock (τ :: C₀) M₀ J k) →
    (rc : JsRenM Id C₀ C) → (rm : JsRenM Id M₀ M) → Option (JsBlock C M J k)
  | .jump .zero e, hint, rest, rc, rm =>
    some (.const hint e (Id.run (rest.renameM (JsRenM.lift rc) rm)))
  | .jump (.succ j) e, _, _, _, _ => some (.jump j e)
  | .ret e, _, _, _, _ => some (.ret e)
  | .next, _, _, _, _ => some .next
  | .throw msg, _, _, _, _ => some (.throw msg)
  | .const x e b, hint, rest, rc, rm =>
    .const x e <$> b.flatJoin hint rest (fun y => JsMem.succ (rc y)) rm
  | .letMut x e b, hint, rest, rc, rm =>
    .letMut x e <$> b.flatJoin hint rest rc (fun y => JsMem.succ (rm y))
  | .assign x e b, hint, rest, rc, rm => .assign x e <$> b.flatJoin hint rest rc rm
  | .destructure (us := us) e sel b, hint, rest, rc, rm =>
    .destructure e sel <$> b.flatJoin hint rest (fun y => JsRen.skipAll us (rc y)) rm
  | .ite c t e, hint, rest, rc, rm =>
    if t.jumpsTo 0 == 0 then return .ite c (← t.renameJ JsJRen.drop) (← e.flatJoin hint rest rc rm)
    else return .ite c (← t.flatJoin hint rest rc rm) (← e.renameJ JsJRen.drop)
  | .enumCases e arms, hint, rest, rc, rm => .enumCases e <$> arms.flatJoin hint rest rc rm
  | .unionCases e arms, hint, rest, rc, rm => .unionCases e <$> arms.flatJoin hint rest rc rm
  | .join x b r, hint, rest, rc, rm =>
    if b.jumpsTo 1 == 0 then
      return .join x (← b.renameJ JsJRen.drop.lift)
        (← r.flatJoin hint rest (fun y => JsMem.succ (rc y)) rm)
    else none
  | .forRange x nt n b r, hint, rest, rc, rm => .forRange x nt n b <$> r.flatJoin hint rest rc rm
  | .lastIter x nt n b r, hint, rest, rc, rm => .lastIter x nt n b <$> r.flatJoin hint rest rc rm
  | .forOf x l xs b r, hint, rest, rc, rm => .forOf x l xs b <$> r.flatJoin hint rest rc rm
/-- `flatJoin` in the arms of a case analysis on an enum (one of which jumps). -/
partial def JsEnumArms.flatJoin {C₀ M₀ J : List JsTy} {τ : JsTy} {k : JsEnd} {C M : List JsTy}
    {n : Nat} : JsEnumArms C M (τ :: J) k n → (hint : String) → (rest : JsBlock (τ :: C₀) M₀ J k) →
    (rc : JsRenM Id C₀ C) → (rm : JsRenM Id M₀ M) → Option (JsEnumArms C M J k n)
  | .nil, _, _, _, _ => some .nil
  | .cons b arms, hint, rest, rc, rm =>
    if b.jumpsTo 0 == 0 then return .cons (← b.renameJ JsJRen.drop) (← arms.flatJoin hint rest rc rm)
    else return .cons (← b.flatJoin hint rest rc rm) (← arms.renameJ JsJRen.drop)
/-- `flatJoin` in the arms of a case analysis on a union (one of which jumps). -/
partial def JsUnionArms.flatJoin {C₀ M₀ J : List JsTy} {τ : JsTy} {k : JsEnd} {C M : List JsTy}
    {cs : List (List JsTy)} : JsUnionArms C M (τ :: J) k cs → (hint : String) →
    (rest : JsBlock (τ :: C₀) M₀ J k) → (rc : JsRenM Id C₀ C) → (rm : JsRenM Id M₀ M) →
    Option (JsUnionArms C M J k cs)
  | .nil, _, _, _, _ => some .nil
  | .cons (us := us) sel b arms, hint, rest, rc, rm =>
    if b.jumpsTo 0 == 0 then
      return .cons sel (← b.renameJ JsJRen.drop) (← arms.flatJoin hint rest rc rm)
    else
      return .cons sel (← b.flatJoin hint rest (fun y => JsRen.skipAll us (rc y)) rm)
        (← arms.renameJ JsJRen.drop)
end

/-- A join point whose block jumps to it once: the block, going on with the rest after the
    jump (see above). -/
def flattenJoinNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.join x block rest) =>
    if block.jumpsTo 0 != 1 then b else
    (block.flatJoin x rest (fun y => y) (fun y => y)).getD b
  | b => b

/-! ## Copies of a mutable variable read before it changes -/

mutual
/-- Is every read of the constant `y` in the block before any assignment of the mutable
    variable `m` (indices where the block starts)? -/
partial def JsBlock.readsBefore {C M J : List JsTy} {k : JsEnd} (y m : Nat) :
    JsBlock C M J k → Bool
  | .ret _ | .jump _ _ | .next | .throw _ => true
  | .const _ _ rest => rest.readsBefore (y + 1) m
  | .letMut _ _ rest => rest.readsBefore y (m + 1)
  | .destructure (us := us) _ _ rest => rest.readsBefore (y + us.length) m
  | .assign x _ rest =>
    if x.index == m then !rest.mentions ⟨false, y⟩ else rest.readsBefore y m
  | .ite _ t e => t.readsBefore y m && e.readsBefore y m
  | .enumCases _ arms => arms.readsBefore y m
  | .unionCases _ arms => arms.readsBefore y m
  | .join _ b rest =>
    if b.mentions ⟨true, m⟩ then b.readsBefore y m && !rest.mentions ⟨false, y + 1⟩
    else b.readsBefore y m && rest.readsBefore (y + 1) m
  | .forRange _ _ _ b rest | .lastIter _ _ _ b rest | .forOf _ _ _ b rest =>
    if b.occs.any (fun o => o.write && o.is ⟨true, m⟩) then
      !b.mentions ⟨false, y + 1⟩ && !rest.mentions ⟨false, y⟩
    else rest.readsBefore y m
/-- `readsBefore` of every arm of a case analysis on an enum. -/
partial def JsEnumArms.readsBefore {C M J : List JsTy} {k : JsEnd} {n : Nat} (y m : Nat) :
    JsEnumArms C M J k n → Bool
  | .nil => true
  | .cons b rest => b.readsBefore y m && rest.readsBefore y m
/-- `readsBefore` of every arm of a case analysis on a union. -/
partial def JsUnionArms.readsBefore {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (y m : Nat) : JsUnionArms C M J k cs → Bool
  | .nil => true
  | .cons (us := us) _ b rest => b.readsBefore (y + us.length) m && rest.readsBefore y m
end

/-- `const y = acc; rest` where `rest` reads `y` only before it assigns `acc`, and not inside a
    closure: `rest` with `acc` for `y`.  No closure of `rest` may assign a mutable variable
    (calling it could change `acc`). -/
def copyMutNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ (.mvar m) rest) =>
    if !rest.occs.any (fun o => o.inClosure && o.is ⟨false, 0⟩) && !rest.closureWrites &&
        rest.readsBefore 0 m.index then
      rest.subst (JsSubst.inst (.mvar m))
    else b
  | b => b

/-! ## Coalescing mutable variables -/

mutual
/-- Does a closure of the expression read or assign a mutable variable around it? -/
partial def JsExpr.capturesMut {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .cvar _ | .mvar _ | .global .. | .lit _ | .enum_mk .. | .unreachable _ => false
  | .imported _ as | .inlined _ as => as.capturesMut
  | .app f as => f.capturesMut || as.capturesMut
  | e@(.lam _ b) => e.occs.any (·.isMut) || b.capturesMut
  | .record_mk fs => fs.capturesMut
  | .union_mk _ as => as.capturesMut
  | .array_mk _ ps | .list_mk ps => ps.capturesMut
  | .cond c a b => c.capturesMut || a.capturesMut || b.capturesMut
/-- `capturesMut` of arguments. -/
partial def JsArgs.capturesMut {C M σs : List JsTy} : JsArgs C M σs → Bool
  | .nil => false
  | .cons a as => a.capturesMut || as.capturesMut
/-- `capturesMut` of the parts of an array literal. -/
partial def JsParts.capturesMut {C M : List JsTy} {A E : JsTy} : JsParts C M A E → Bool
  | .nil => false
  | .elem e rest | .spread e rest => e.capturesMut || rest.capturesMut
/-- `capturesMut` of a block. -/
partial def JsBlock.capturesMut {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → Bool
  | .ret e | .jump _ e => e.capturesMut
  | .next | .throw _ => false
  | .const _ e rest | .letMut _ e rest | .assign _ e rest | .destructure e _ rest =>
    e.capturesMut || rest.capturesMut
  | .ite c t e => c.capturesMut || t.capturesMut || e.capturesMut
  | .enumCases e arms => e.capturesMut || arms.capturesMut
  | .unionCases e arms => e.capturesMut || arms.capturesMut
  | .join _ b rest => b.capturesMut || rest.capturesMut
  | .forRange _ _ n b rest | .lastIter _ _ n b rest =>
    n.capturesMut || b.capturesMut || rest.capturesMut
  | .forOf _ _ xs b rest => xs.capturesMut || b.capturesMut || rest.capturesMut
/-- `capturesMut` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.capturesMut {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms C M J k n → Bool
  | .nil => false
  | .cons b rest => b.capturesMut || rest.capturesMut
/-- `capturesMut` of the arms of a case analysis on a union. -/
partial def JsUnionArms.capturesMut {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.capturesMut || rest.capturesMut
end

mutual
/-- Does the block only leave by `return` or `throw` (no jump to a join point around it, no end
    of an iteration)?  `d` join points are bound inside the walk. -/
partial def JsBlock.onlyReturns {C M J : List JsTy} {k : JsEnd} (d : Nat) :
    JsBlock C M J k → Bool
  | .ret _ | .throw _ => true
  | .next => false
  | .jump j _ => j.index < d
  | .const _ _ rest | .letMut _ _ rest | .assign _ _ rest | .destructure _ _ rest
  | .forRange _ _ _ _ rest | .lastIter _ _ _ _ rest | .forOf _ _ _ _ rest => rest.onlyReturns d
  | .ite _ t e => t.onlyReturns d && e.onlyReturns d
  | .enumCases _ arms => arms.onlyReturns d
  | .unionCases _ arms => arms.onlyReturns d
  | .join _ b rest => b.onlyReturns (d + 1) && rest.onlyReturns d
/-- `onlyReturns` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.onlyReturns {C M J : List JsTy} {k : JsEnd} {n : Nat} (d : Nat) :
    JsEnumArms C M J k n → Bool
  | .nil => true
  | .cons b rest => b.onlyReturns d && rest.onlyReturns d
/-- `onlyReturns` of the arms of a case analysis on a union. -/
partial def JsUnionArms.onlyReturns {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (d : Nat) : JsUnionArms C M J k cs → Bool
  | .nil => true
  | .cons _ b rest => b.onlyReturns d && rest.onlyReturns d
end

/-- The statements of a block that run one after the other, down to the first `x = y;` (`y`
    the mutable variable of index `y`): the index of `x` where the walk started, when nothing
    after it reads `y`.  The walk does not enter branches or join points, so nothing leaves
    the block before that assignment (but by throwing). -/
partial def JsBlock.finalCopy? {C M J : List JsTy} {k : JsEnd} (y dm : Nat) :
    JsBlock C M J k → Option Nat
  | .assign x (.mvar y') rest =>
    if y'.index == y && x.index > y then
      if rest.mentions ⟨true, y⟩ then none else some (x.index - dm)
    else rest.finalCopy? y dm
  | .assign _ _ rest | .const _ _ rest | .destructure _ _ rest
  | .forRange _ _ _ _ rest | .lastIter _ _ _ _ rest | .forOf _ _ _ _ rest => rest.finalCopy? y dm
  | .letMut _ _ rest => rest.finalCopy? (y + 1) (dm + 1)
  | _ => none

/-- The first `x = y;` of the statements of a block that run one after the other, dropped. -/
partial def JsBlock.dropCopy {C M J : List JsTy} {k : JsEnd} (y : Nat) :
    JsBlock C M J k → JsBlock C M J k
  | .assign x (.mvar y') rest =>
    if y'.index == y && x.index > y then rest else .assign x (.mvar y') (rest.dropCopy y)
  | .assign x e rest => .assign x e (rest.dropCopy y)
  | .const h e rest => .const h e (rest.dropCopy y)
  | .destructure e sel rest => .destructure e sel (rest.dropCopy y)
  | .forRange h nt n b rest => .forRange h nt n b (rest.dropCopy y)
  | .lastIter h nt n b rest => .lastIter h nt n b (rest.dropCopy y)
  | .forOf h l xs b rest => .forOf h l xs b (rest.dropCopy y)
  | .letMut h e rest => .letMut h e (rest.dropCopy (y + 1))
  | b => b

/-- The renaming of a mutable variable `y` (the innermost) to `x`. -/
def JsRen.merge {Γ : List JsTy} {σ : JsTy} (x : JsMem Γ σ) : JsRenM Id (σ :: Γ) Γ := fun z =>
  match z with
  | .zero => x
  | .succ z => z

/-- Two mutable variables made one (when no closure of the function captures a mutable
    variable, `noCapture`):
    * `let y = x; rest` where `rest` does not mention `x` and only leaves by `return` or
      `throw` (so `x` is not read afterwards): `rest` with `x` for `y`;
    * `let y = e; rest` where the statements of `rest` that run one after the other end with
      `x = y;`, `x` is not mentioned before, and `y` is not read after: `x = e; rest` with `x`
      for `y` and without that assignment. -/
def coalesceNode (noCapture : Bool) {C M J : List JsTy} {k : JsEnd} :
    JsBlock C M J k → JsBlock C M J k
  | b@(.letMut (τ := σ) _ e rest) =>
    if !noCapture then b else
    let copyOf : Option (JsMem M σ) := match e with
      | .mvar x => if !rest.mentions ⟨true, x.index + 1⟩ && rest.onlyReturns 0 then some x
        else none
      | _ => none
    match copyOf with
    | some x => Id.run (rest.renameM JsRen.id (JsRen.merge x))
    | none =>
      match rest.finalCopy? 0 0 with
      | some i =>
        if i == 0 then b else
        match JsMem.ofIndex? M (i - 1) σ with
        | some x =>
          if (rest.occs.filter (·.is ⟨true, i⟩)).size == 1 then
            .assign x e (Id.run ((rest.dropCopy 0).renameM JsRen.id (JsRen.merge x)))
          else b
        | none => b
      | none => b
  | b => b

end MoreJs

end
