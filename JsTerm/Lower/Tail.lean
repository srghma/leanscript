module

public import JsTerm.Syntax.Vars

@[expose] public section

set_option autoImplicit false

/-!
# The tails of the blocks the conversion builds

Two structural rewrites the conversion from `Term` (`JsTerm.Lower.FromTerm`) needs to build
the shapes of JavaScript it emits (they are not optimisations: the conversion cannot write
these statements otherwise):

* **the end of a loop body** (`JsBlock.retToNext`): the body of a loop is converted from a
  statement that returns the new accumulator; each `return e` becomes `acc = e;` and the end
  of the iteration;
* **returns as jumps** (`JsBlock.retToJump`): each `return e` becomes a jump to a new join
  point (how a block computing a function is applied to more arguments).
-/

namespace MoreJs

variable {S : JsSig}

/-! ## The end of a loop body -/


mutual
/-- Every `return e` of a loop body becomes `acc = e;` and the end of the iteration. -/
partial def JsBlock.retToNext {C M J : List JsTy} {α : JsTy} (acc : JsMem M α) :
    JsBlock S C M J (.ret α) → JsBlock S C M J .loop
  | .ret e => .assign acc e .next
  | .jump j e => .jump j e
  | .throw msg => .throw msg
  | .raise e => .raise e
  | .const x e rest => .const x e (rest.retToNext acc)
  | .letMut x e rest => .letMut x e (rest.retToNext acc.succ)
  | .assign x e rest => .assign x e (rest.retToNext acc)
  | .destructure e sel rest => .destructure e sel (rest.retToNext acc)
  | .ite c t e => .ite c (t.retToNext acc) (e.retToNext acc)
  | .enumCases e arms => .enumCases e (arms.retToNext acc)
  | .unionCases e arms => .unionCases e (arms.retToNext acc)
  | .join x b rest => .join x (b.retToNext acc) (rest.retToNext acc)
  | .forRange x nt n b rest => .forRange x nt n b (rest.retToNext acc)
  | .forOf x l xs b rest => .forOf x l xs b (rest.retToNext acc)
  | .countdown x nt n b s rest => .countdown x nt n b s (rest.retToNext acc)
  | .tick nt j b rest => .tick nt j (b.retToNext acc) (rest.retToNext acc)
  | .natCase x nt n z s => .natCase x nt n (z.retToNext acc) (s.retToNext acc)
  | .funs xs defs rest => .funs xs defs (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToNext {C M J : List JsTy} {α : JsTy} {n : Nat} (acc : JsMem M α) :
    JsEnumArms S C M J (.ret α) n → JsEnumArms S C M J .loop n
  | .nil => .nil
  | .cons b rest => .cons (b.retToNext acc) (rest.retToNext acc)
/-- `retToNext` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToNext {C M J : List JsTy} {α : JsTy} {cs : List (List JsTy)} (acc : JsMem M α) :
    JsUnionArms S C M J (.ret α) cs → JsUnionArms S C M J .loop cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.retToNext acc) (rest.retToNext acc)
end

/-! ## Returns as jumps -/

/-- A position in `J`, in `J ++ K`. -/
def JsMem.appendR {α : Type} {J : List α} {x : α} (K : List α) : JsMem J x → JsMem (J ++ K) x
  | .zero => .zero
  | .succ m => .succ (m.appendR K)

/-- The position of `x` in `J ++ [x]`. -/
def JsMem.last {α : Type} {x : α} : (J : List α) → JsMem (J ++ [x]) x
  | [] => .zero
  | _ :: J => .succ (JsMem.last J)

mutual
/-- Every `return e` of a block becomes a jump passing `e` to a new join point, outside the
    ones of the block (`join x (b.retToJump) rest` computes what `b` returns into `x`, then
    runs `rest`). -/
partial def JsBlock.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} :
    JsBlock S C M J (.ret τ) → JsBlock S C M (J ++ [τ]) k
  | .ret e => .jump (JsMem.last J) e
  | .jump j e => .jump (j.appendR [τ]) e
  | .throw msg => .throw msg
  | .raise e => .raise e
  | .const x e rest => .const x e rest.retToJump
  | .letMut x e rest => .letMut x e rest.retToJump
  | .assign x e rest => .assign x e rest.retToJump
  | .destructure e sel rest => .destructure e sel rest.retToJump
  | .ite c t e => .ite c t.retToJump e.retToJump
  | .enumCases e arms => .enumCases e arms.retToJump
  | .unionCases e arms => .unionCases e arms.retToJump
  | .join x b rest => .join x b.retToJump rest.retToJump
  | .forRange x nt n b rest => .forRange x nt n b rest.retToJump
  | .forOf x l xs b rest => .forOf x l xs b rest.retToJump
  | .countdown x nt n b s rest => .countdown x nt n b s rest.retToJump
  | .tick nt j b rest => .tick nt j b.retToJump rest.retToJump
  | .natCase x nt n z s => .natCase x nt n z.retToJump s.retToJump
  | .funs xs defs rest => .funs xs defs rest.retToJump
/-- `retToJump` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J (.ret τ) n → JsEnumArms S C M (J ++ [τ]) k n
  | .nil => .nil
  | .cons b rest => .cons b.retToJump rest.retToJump
/-- `retToJump` in the arms of a case analysis on a union. -/
partial def JsUnionArms.retToJump {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    {cs : List (List JsTy)} : JsUnionArms S C M J (.ret τ) cs → JsUnionArms S C M (J ++ [τ]) k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.retToJump rest.retToJump
end

/-! ## Tail calls as the iterations of a loop -/

/-- The call `f(args)` of the constant of index `acc`: its arguments. -/
def JsExpr.callOf? {C M : List JsTy} {τ : JsTy} (acc : Nat) :
    JsExpr S C M τ → Option ((σs : List JsTy) × JsArgs S C M σs)
  | .app (σs := σs) (.cvar x) args => if x.index == acc then some ⟨σs, args⟩ else none
  | _ => none

mutual
/-- The body of a tail-recursive function as the body of a loop: every `return f(args)` (also
    `const x = f(args); return x;`) of the function `f`, the constant of index `acc`, becomes
    the next iteration on the arguments (`emit`, which assigns them to the variables of the
    loop), and every other `return e` the end of the loop, a jump passing `e` to a new join
    point outside the join points of the block.  The other occurrences of `f` are left: the
    caller removes `f` from the constants, which fails when one is left (a call that is not a
    tail call). -/
partial def JsBlock.tailToLoop {C M J : List JsTy} {τ : JsTy} (acc : Nat)
    (emit : {C M J : List JsTy} → (σs : List JsTy) → JsArgs S C M σs →
      Option (JsBlock S C M J .loop)) :
    JsBlock S C M J (.ret τ) → Option (JsBlock S C M (J ++ [τ]) .loop)
  | .ret e => match e.callOf? acc with
    | some ⟨σs, args⟩ => emit σs args
    | none => some (.jump (JsMem.last J) e)
  | .jump j e => some (.jump (j.appendR [τ]) e)
  | .throw msg => some (.throw msg)
  | .raise e => some (.raise e)
  | .const x e rest =>
    let tail : Bool := match rest with
      | .ret (.cvar .zero) => true
      | _ => false
    match tail, e.callOf? acc with
    | true, some ⟨σs, args⟩ => emit σs args
    | _, _ => (.const x e ·) <$> rest.tailToLoop (acc + 1) emit
  | .letMut x e rest => (.letMut x e ·) <$> rest.tailToLoop acc emit
  | .assign x e rest => (.assign x e ·) <$> rest.tailToLoop acc emit
  | .destructure (us := us) e sel rest =>
    (.destructure e sel ·) <$> rest.tailToLoop (acc + us.length) emit
  | .ite c t e => return .ite c (← t.tailToLoop acc emit) (← e.tailToLoop acc emit)
  | .enumCases e arms => (.enumCases e ·) <$> arms.tailToLoop acc emit
  | .unionCases e arms => (.unionCases e ·) <$> arms.tailToLoop acc emit
  | .join x b rest => return .join x (← b.tailToLoop acc emit) (← rest.tailToLoop (acc + 1) emit)
  | .forRange x nt n b rest => (.forRange x nt n b ·) <$> rest.tailToLoop acc emit
  | .forOf x l xs b rest => (.forOf x l xs b ·) <$> rest.tailToLoop acc emit
  | .countdown x nt n b s rest => (.countdown x nt n b s ·) <$> rest.tailToLoop (acc + 1) emit
  | .tick nt j b rest => return .tick nt j (← b.tailToLoop acc emit) (← rest.tailToLoop acc emit)
  | .natCase x nt n z s =>
    return .natCase x nt n (← z.tailToLoop acc emit) (← s.tailToLoop (acc + 1) emit)
  | .funs (τs := τs) xs defs rest => (.funs xs defs ·) <$> rest.tailToLoop (acc + τs.length) emit
/-- `tailToLoop` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.tailToLoop {C M J : List JsTy} {τ : JsTy} {n : Nat} (acc : Nat)
    (emit : {C M J : List JsTy} → (σs : List JsTy) → JsArgs S C M σs →
      Option (JsBlock S C M J .loop)) :
    JsEnumArms S C M J (.ret τ) n → Option (JsEnumArms S C M (J ++ [τ]) .loop n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.tailToLoop acc emit) (← rest.tailToLoop acc emit)
/-- `tailToLoop` in the arms of a case analysis on a union. -/
partial def JsUnionArms.tailToLoop {C M J : List JsTy} {τ : JsTy} {cs : List (List JsTy)}
    (acc : Nat)
    (emit : {C M J : List JsTy} → (σs : List JsTy) → JsArgs S C M σs →
      Option (JsBlock S C M J .loop)) :
    JsUnionArms S C M J (.ret τ) cs → Option (JsUnionArms S C M (J ++ [τ]) .loop cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.tailToLoop (acc + us.length) emit) (← rest.tailToLoop acc emit)
end

/-- The arguments, as a list. -/
def JsArgs.toList {C M : List JsTy} : {σs : List JsTy} → JsArgs S C M σs →
    List ((σ : JsTy) × JsExpr S C M σ)
  | [], .nil => []
  | _ :: _, .cons a as => ⟨_, a⟩ :: as.toList

/-- Arguments under a new mutable variable. -/
def JsArgs.wkM {C M σs : List JsTy} {σ : JsTy} (as : JsArgs S C M σs) : JsArgs S C (σ :: M) σs :=
  Id.run (as.renameM JsRen.id JsRen.succ)

/-- `let p₁ = a₁; …; let pₙ = aₙ;` and the block `b`, which reads and assigns them as its
    innermost mutable variables (`pₙ` innermost). -/
def letMutsThen {C M J : List JsTy} {k : JsEnd} (hint : String) :
    {σs : List JsTy} → JsArgs S C M σs → JsBlock S C (pushAll σs M) J k → JsBlock S C M J k
  | [], .nil, b => b
  | _ :: _, .cons e rest, b => .letMut hint e (letMutsThen hint rest.wkM b)

/-- An assignment of a variable of a loop: the variable and its new value. -/
abbrev LoopAssign (S : JsSig) (C M : List JsTy) := (σ : JsTy) × JsMem M σ × JsExpr S C M σ

/-- The assignment under a new constant. -/
def LoopAssign.wkC {C M : List JsTy} {σ : JsTy} (a : LoopAssign S C M) : LoopAssign S (σ :: C) M :=
  ⟨a.1, a.2.1, a.2.2.wkC⟩

/-- The assignments `x = e;` in order, then the next iteration.  An assignment marked (`true`)
    first has its value put in a constant (`const t = e;`, before any assignment), because an
    earlier assignment changes a variable it reads. -/
partial def assignThenNext {C M J : List JsTy} (done : List (LoopAssign S C M)) :
    List (LoopAssign S C M × Bool) → JsBlock S C M J .loop
  | [] => done.reverse.foldr (fun a b => .assign a.2.1 a.2.2 b) .next
  | (a, false) :: rest => assignThenNext (a :: done) rest
  | (a, true) :: rest =>
    .const "t" a.2.2 (assignThenNext (⟨a.1, a.2.1, .cvar .zero⟩ :: done.map LoopAssign.wkC)
      (rest.map fun (x, b) => (x.wkC, b)))

/-- The next iteration of a loop whose variables are the mutable variables of levels `lvls`
    (their positions counting from the outside of the function), of types `ds`, on the new
    values `args`: the assignments of the variables that change (a value computed from a
    variable an earlier assignment changes is computed before), then `next`.  `none` when the
    types do not match. -/
def loopNext {C M J : List JsTy} (ds : List JsTy) (lvls : List Nat) (σs : List JsTy)
    (args : JsArgs S C M σs) : Option (JsBlock S C M J .loop) := do
  unless σs == ds do none
  let pairs := args.toList.zip lvls
  let items ← pairs.mapM fun (⟨σ, e⟩, l) => do
    let x ← JsMem.ofIndex? M (M.length - 1 - l) σ
    return ((⟨σ, x, e⟩ : LoopAssign S C M), l)
  -- `x = x;` changes nothing
  let items := items.filter fun (⟨_, x, e⟩, _) => match e with
    | .mvar y => y.index != x.index
    | _ => true
  let marked := items.zipIdx.map fun ((a, _), i) =>
    let earlier := (items.take i).map fun (_, l) => M.length - 1 - l
    (a, earlier.any fun idx => a.2.2.mentions ⟨true, idx⟩)
  return assignThenNext [] marked

/-- The arguments of a call as the values of the variables of a loop that keeps some of its
    parameters (`flat` says which) in one variable per field: the fields of a record literal
    passed for such a parameter, in order.  `none` when such an argument is not a record
    literal. -/
def flattenArgs {C M : List JsTy} :
    List Bool → List ((σ : JsTy) × JsExpr S C M σ) → Option (List ((σ : JsTy) × JsExpr S C M σ))
  | [], [] => some []
  | false :: fl, a :: as => (a :: ·) <$> flattenArgs fl as
  | true :: fl, ⟨_, .record_mk fs⟩ :: as => (fs.toList ++ ·) <$> flattenArgs fl as
  | _, _ => none

/-- `loopNext` for a loop whose variables (of types `ds`, at levels `lvls`) keep the parameters
    `flat` says in one variable per field: the call's arguments are flattened
    (`flattenArgs`). -/
def loopNextFlat {C M J : List JsTy} (flat : List Bool) (ds : List JsTy) (lvls : List Nat)
    (σs : List JsTy) (args : JsArgs S C M σs) : Option (JsBlock S C M J .loop) := do
  let items ← flattenArgs flat args.toList
  let rec toArgs : List ((σ : JsTy) × JsExpr S C M σ) → (τs : List JsTy) → Option (JsArgs S C M τs)
    | [], [] => some .nil
    | ⟨σ, e⟩ :: es, τ :: τs => if h : σ = τ then (JsArgs.cons (h ▸ e) ·) <$> toArgs es τs else none
    | _, _ => none
  loopNext ds lvls ds (← toArgs items ds)

end MoreJs

end
