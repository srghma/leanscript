module

public import LeanScript.Term.Ownership.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Ownership of whole statements, and the versions of a function

The decisions of `LeanScript.Term.Ownership.Basic` for each construct of `Term`, and the walk
over whole statements that uses them.  The conversion to JavaScript (`JsTerm.Lower.FromTerm`)
threads the same environments through a statement and calls the same functions, so the
JavaScript updates in place exactly the arrays this walk says it does.

* **Expressions** (`Own.PExpr.owned`, `Own.Neu.owned`): is the value of the expression owned,
  in the context of its statement?  An update in place (`Own.updateInPlace`) answers an owned
  array, and so do the copies the updates `push`, `pop`, `set` and `swap` make.
* **Loops** (`Own.natRecAcc`, `Own.foldlAcc`): the body of a loop owns its accumulator when the
  initial value is owned and every path of the body answers an owned value (so each iteration
  hands an owned value to the next one); then so is the result of the loop.
* **Join points** (`Own.joinParam`): a join point owns its parameter when every jump to it
  passes an owned value.
* **Statements** (`Own.Term.walk`): a `Summary` of a statement — whether every `ret` answers
  an owned value, whether every jump to each join point passes one, and how many updates are
  done in place.

## The versions of a function

`ClosedTerm.ownVersions` decides which versions of a translated function are worth
generating: the one that **borrows** every parameter (what a caller outside the program gets:
it may keep using its arguments), and, when owning some parameters lets more updates be done
in place, one that owns all of those, and (for two or three of them) one owning each of them
alone.  A caller that gives up an argument calls the version owning it.
-/

namespace LeanScript

namespace Own

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Expressions -/

/-- What a piece of code costs in copies of arrays: the updates it does in place, and the
    copies of whole arrays it makes (an update not done in place, a copy made before a loop). -/
structure Cost where
  inPlace : Nat := 0
  copies : Nat := 0
  deriving Inhabited, Repr, BEq

instance : Add Cost := ⟨fun a b => ⟨a.inPlace + b.inPlace, a.copies + b.copies⟩⟩

/-- One copy of an array. -/
def Cost.copy : Cost := ⟨0, 1⟩

/-- Is the type an array type? -/
def isArrayTy {d : Bool} : Ty ks d → Bool
  | .array _ => true
  | _ => false

mutual
/-- Is the value of the neutral expression owned? -/
partial def Neu.owned {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (e : Neu Δ Φ Γ τ ℓ) : Bool :=
  !Ty.needsOwn τ ||
  match e with
  | .var x => c.consumable (.u x.index)
  | .data_out _ _ n => Neu.owned c n
  | .cond _ _ _ => false
  | .extern ex args _ =>
    let nm := externName ex
    isFresh nm || (isUpdate nm && updateInPlace c nm args)
/-- Is the value of the pure expression owned? -/
partial def PExpr.owned {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx)
    (e : PExpr Δ Φ Γ τ o) : Bool :=
  !Ty.needsOwn τ ||
  match e with
  | .neu n => Neu.owned c n
  | .kvar x => c.consumable (.k x.index)
  | .lit _ _ => true
  | .enum_mk _ _ => true
  | .record_mk args => Args.owned c args
  | .union_mk _ args => Args.owned c args
  | .array_mk _ => true
  | .list_mk _ => true
  | .data_in _ _ e => PExpr.owned c e
/-- Are the values of all the arguments owned? -/
partial def Args.owned {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (c : Ctx) :
    Args Δ Φ Γ σs o → Bool
  | .nil => true
  | .cons a as => PExpr.owned c a && Args.owned c as
/-- Is the call of the extern `nm` on `args` an update done in place?  Its array (the first
    argument) is an owned variable used for the last time here, whose other occurrences in the
    statement are reads inside the other arguments, or the owned value of an extern. -/
partial def updateInPlace {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (c : Ctx)
    (nm : String) (args : Args Δ Φ Γ σs o) : Bool :=
  isUpdate nm &&
  match args with
  | .nil => false
  | .cons a rest =>
    match a with
    | .neu (.var x) => c.updatable (.u x.index) (Args.occAt (.u x.index) none 1 rest)
    | .kvar x => c.updatable (.k x.index) (Args.occAt (.k x.index) none 1 rest)
    | .neu n@(.extern _ _ _) => Neu.owned c n
    | _ => false
/-- The cost of a neutral expression: each update is done in place or copies. -/
partial def Neu.cost {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx) :
    Neu Δ Φ Γ τ ℓ → Cost
  | .var _ => {}
  | .data_out _ _ n => Neu.cost c n
  | .cond n a b => Neu.cost c n + PExpr.cost c a + PExpr.cost c b
  | .extern ex args _ =>
    let nm := externName ex
    (if !isUpdate nm then {} else if updateInPlace c nm args then ⟨1, 0⟩ else Cost.copy) +
      Args.cost c args
/-- The cost of a pure expression. -/
partial def PExpr.cost {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx) :
    PExpr Δ Φ Γ τ o → Cost
  | .neu n => Neu.cost c n
  | .kvar _ => {}
  | .lit _ _ => {}
  | .enum_mk _ _ => {}
  | .record_mk args => Args.cost c args
  | .union_mk _ args => Args.cost c args
  | .array_mk es => Elems.cost c es
  | .list_mk es => Elems.cost c es
  | .data_in _ _ e => PExpr.cost c e
/-- The cost of arguments. -/
partial def Args.cost {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (c : Ctx) :
    Args Δ Φ Γ σs o → Cost
  | .nil => {}
  | .cons a as => PExpr.cost c a + Args.cost c as
/-- The cost of the elements of a literal. -/
partial def Elems.cost {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} (c : Ctx) :
    Elems Δ Φ Γ t o → Cost
  | .nil => {}
  | .cons e es => PExpr.cost c e + Elems.cost c es
end

mutual
/-- Can the value of the expression be made owned by copying arrays (the owned parts as they
    are, each other array copied: `[...a]`)?  A record, union or datatype must be a literal
    whose fields can. -/
partial def PExpr.copyable {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx)
    (e : PExpr Δ Φ Γ τ o) : Bool :=
  PExpr.owned c e ||
  match e with
  | .record_mk args => Args.copyable c args
  | .union_mk _ args => Args.copyable c args
  | .data_in _ _ e => PExpr.copyable c e
  | _ => isArrayTy τ
/-- `PExpr.copyable` of all the arguments. -/
partial def Args.copyable {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (c : Ctx) :
    Args Δ Φ Γ σs o → Bool
  | .nil => true
  | .cons a as => PExpr.copyable c a && Args.copyable c as
end

mutual
/-- The copies of arrays `PExpr.copyable` makes of an expression. -/
partial def PExpr.copyCost {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx)
    (e : PExpr Δ Φ Γ τ o) : Cost :=
  if PExpr.owned c e then {} else
  match e with
  | .record_mk args => Args.copyCost c args
  | .union_mk _ args => Args.copyCost c args
  | .data_in _ _ e => PExpr.copyCost c e
  | _ => Cost.copy
/-- `PExpr.copyCost` of all the arguments. -/
partial def Args.copyCost {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} (c : Ctx) :
    Args Δ Φ Γ σs o → Cost
  | .nil => {}
  | .cons a as => PExpr.copyCost c a + Args.copyCost c as
end

/-- How the body of a loop gets its accumulator: borrowed; owned (its initial value is owned);
    or owned after a copy of the initial value made before the loop (`PExpr.copyable`), when
    that saves copies in the body. -/
inductive AccMode where
  | borrowed
  | owned
  | copy
  deriving BEq, Inhabited, Repr

/-- Does the body own its accumulator? -/
def AccMode.owns : AccMode → Bool
  | .borrowed => false
  | _ => true

/-- Is the value of known shape owned (a literal built from owned parts)? -/
def Val.owned {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx)
    (v : Val Δ d Φ Γ τ o) : Bool :=
  !Ty.needsOwn τ ||
  match v with
  | .record_mk args => Args.owned c args
  | .union_mk _ args => Args.owned c args
  | .array_mk _ => true
  | .data_in _ _ e => PExpr.owned c e
  | _ => false

/-! ## Summaries of statements -/

/-- What a statement does with ownership: whether every `ret` answers an owned value, whether
    every jump to each join point (innermost first; a join point not listed is never jumped to
    with a value that is not owned) passes one, and its cost in copies of arrays (a static
    count: an update in a loop counts once). -/
structure Summary where
  ret : Bool := true
  jumps : List Bool := []
  cost : Cost := {}
  deriving Inhabited, Repr

namespace Summary

/-- Both summaries (two parts of a statement, or two arms of a branch). -/
def both (a b : Summary) : Summary :=
  let n := max a.jumps.length b.jumps.length
  { ret := a.ret && b.ret
    jumps := (List.range n).map fun i => a.jumps.getD i true && b.jumps.getD i true
    cost := a.cost + b.cost }

/-- A jump to the join point `j` passing an owned value (`b`) or not. -/
def jumpTo (j : Nat) (b : Bool) : Summary :=
  { jumps := List.replicate j true ++ [b] }

/-- More cost. -/
def addCost (s : Summary) (c : Cost) : Summary := { s with cost := s.cost + c }

end Summary

/-- The environment of the body of a loop, a closure or a delay, seen from `env` outside it:
    nothing from outside is owned there (the body may run many times, or later), its
    parameters `ps` are as given (innermost first). -/
def Env.body (env : Env) (closed : Bool) (ps : List Bool) : Env :=
  if closed then { u := ps, k := env.none.k } else env.none.pushU ps

/-- The unknowns bound by the fields of a case analysis, all owned or not. -/
def fieldsOwned (n : Nat) (b : Bool) : List Bool := List.replicate n b

mutual
/-- The summary of a statement in the environment `env`. -/
partial def Term.walk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (env : Env) : Term Δ d Φ Γ τ js o → Summary
  | .ret e =>
    let (c, _) := env.stmt (fun v => PExpr.occ v e) (fun _ => false)
    { ret := PExpr.owned c e, cost := PExpr.cost c e }
  | .letV _ val b =>
    let (c, env') := env.stmt (fun v => Val.occ v val) (fun v => (Term.occ (v.upK 1) b).n > 0)
    (Term.walk (env'.pushK (Val.owned c val)) b).addCost (Val.cost c val)
  | .letE _ cp b =>
    let (c, env') := env.stmt (fun v => Comp.occ v cp) (fun v => (Term.occ (v.upU 1) b).n > 0)
    (Term.walk (env'.pushU [Comp.owned c cp]) b).addCost (Comp.cost c cp)
  | .record_casesOn (t := t) (fs := fs) _ n b =>
    let m := (t :: fs.toList).length
    let (c, env') := env.stmt (fun v => Neu.occ v n) (fun v => (Term.occ (v.upU m) b).n > 0)
    (Term.walk (env'.pushU (fieldsOwned m (Neu.owned c n))) b).addCost (Neu.cost c n)
  | .branch br => Branch.walk env br
  | .jump j e =>
    let (c, _) := env.stmt (fun v => PExpr.occ v e) (fun _ => false)
    (Summary.jumpTo j.index (PExpr.owned c e)).addCost (PExpr.cost c e)
/-- The summary of a branch in the environment `env`. -/
partial def Branch.walk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (env : Env) : Branch Δ d Φ Γ τ js ℓ → Summary
  | .ite cn t e =>
    let (c, env') := env.stmt (fun v => Neu.occ v cn)
      (fun v => (Term.occ v t).n > 0 || (Term.occ v e).n > 0)
    ((Term.walk env' t).both (Term.walk env' e)).addCost (Neu.cost c cn)
  | .enum_casesOn e bs =>
    let (c, env') := env.stmt (fun v => Neu.occ v e)
      (fun v => (List.finRange _).any fun j => (Term.occ v (bs j)).n > 0)
    ((List.finRange _).foldl (fun (acc : Summary) j => acc.both (Term.walk env' (bs j))) {}).addCost
      (Neu.cost c e)
  | .union_casesOn e brs =>
    let (c, env') := env.stmt (fun v => Neu.occ v e) (fun v => (Branches.occ v brs).n > 0)
    (Branches.walk env' (Neu.owned c e) brs).addCost (Neu.cost c e)
  | .join σ _ _ body br =>
    let envBr := joinBranchEnv env body
    let sbr := Branch.walk envBr br
    let p := !Ty.needsOwn σ || sbr.jumps.headD true
    let sbody := Term.walk ((joinBodyEnv env br).pushU [p]) body
    { sbr with jumps := sbr.jumps.tail }.both sbody
/-- The summary of the arms of a union's case analysis, whose fields are owned (`ow`) or not. -/
partial def Branches.walk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (env : Env) (ow : Bool) :
    Branches Δ d Φ Γ cs τ js o → Summary
  | .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
    (Term.walk (env.pushU (fieldsOwned c₁.binds.length ow)) b₁).both
      (Term.walk (env.pushU (fieldsOwned c₂.binds.length ow)) b₂)
  | .cons (c := c) _ b rest =>
    (Term.walk (env.pushU (fieldsOwned c.binds.length ow)) b).both (Branches.walk env ow rest)
/-- The environment of the branch of a join point: the variables its body uses are not owned
    there (they are used after the branch). -/
partial def joinBranchEnv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {uₓ : Usage01ω} {o : Lvl} (env : Env) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) : Env :=
  env.kill fun v => (Term.occ (v.upU 1) body).n > 0
/-- The environment of the body of a join point (before its parameter): the variables that
    escaped in the branch are not owned there. -/
partial def joinBodyEnv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (env : Env) (br : Branch Δ d Φ Γ τ js ℓ) : Env :=
  env.kill fun v => (Branch.occ v br).esc > 0
/-- The summary of a body whose parameters are owned or not (`ps`, innermost first), seen from
    the environment `env` outside it. -/
partial def Body.walk {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (env : Env) (ps : List Bool) : Body Δ d Φ Γ bs τ o → Summary
  | .closed t => Term.walk (env.body true ps) t
  | .opened t _ => Term.walk (env.body false ps) t
/-- The cost of a value of known shape (its arguments, and the body of a closure — whose
    parameter is borrowed — or of a delay). -/
partial def Val.cost {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx) :
    Val Δ d Φ Γ τ o → Cost
  | .lam b => (Body.walk c.env [false] b).cost
  | .thunk_mk b => (Body.walk c.env [] b).cost
  | .lazy_mk b => (Body.walk c.env [] b).cost
  | .record_mk args => Args.cost c args
  | .union_mk _ args => Args.cost c args
  | .array_mk es => Elems.cost c es
  | .list_mk es => Elems.cost c es
  | .data_in _ _ e => PExpr.cost c e
/-- How the body of a loop gets its accumulator (of type `τ`, initial value `z`): the body
    **owns** it when every path of the body answers an owned value when it does (so each
    iteration hands an owned value to the next), and `z` is owned — or can be made owned by
    copies made once, before the loop (`PExpr.copyable`), when owning it saves copies in the
    body (made at every iteration).  `walk b` is the summary of the body
    when it owns its accumulator (`b`) or not. -/
partial def accMode {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {oz : Lvl} (c : Ctx)
    (z : PExpr Δ Φ Γ τ oz) (walk : Bool → Summary) : AccMode :=
  if !Ty.needsOwn τ then .borrowed else
  let so := walk true
  if !so.ret then .borrowed
  else if PExpr.owned c z then .owned
  else if PExpr.copyable c z && so.cost.copies < (walk false).cost.copies then .copy
  else .borrowed
/-- How the body of `Nat.rec` gets its accumulator (`accMode`). -/
partial def natRecAcc {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage01ω}
    {oz os : Lvl} (c : Ctx) (z : PExpr Δ Φ Γ τ oz)
    (s : Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ os) : AccMode :=
  accMode c z fun b => Body.walk c.env [b, false] s
/-- How the body of `Array.foldl` gets its accumulator (`accMode`). -/
partial def foldlAcc {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t ρ : Ty ks} {u₁ u₂ : Usage01ω}
    {oz os : Lvl} (c : Ctx) (z : PExpr Δ Φ Γ ρ oz)
    (s : Body Δ d Φ Γ [⟨t, u₁, d + 1⟩, ⟨ρ, u₂, d + 1⟩] ρ os) : AccMode :=
  accMode c z fun b => Body.walk c.env [false, b] s
/-- Is the result of a computation owned? -/
partial def Comp.owned {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (cp : Comp Δ d Φ Γ τ ℓ) : Bool :=
  !Ty.needsOwn τ ||
  match cp with
  | .share n => Neu.owned c n
  | .nat_rec _ z s _ => (natRecAcc c z s).owns
  | .array_foldl _ z s _ => (foldlAcc c z s).owns
  | _ => false
/-- The cost of a computation. -/
partial def Comp.cost {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx) :
    Comp Δ d Φ Γ τ ℓ → Cost
  | .app f a _ => PExpr.cost c f + PExpr.cost c a
  | .share n => Neu.cost c n
  | .nat_rec n z s _ =>
    let m := natRecAcc c z s
    PExpr.cost c n + PExpr.cost c z + (if m == .copy then PExpr.copyCost c z else {}) +
      (Body.walk c.env [m.owns, false] s).cost
  | .array_foldl a z s _ =>
    let m := foldlAcc c z s
    PExpr.cost c a + PExpr.cost c z + (if m == .copy then PExpr.copyCost c z else {}) +
      (Body.walk c.env [false, m.owns] s).cost
  | .data_rec _ _ _ brs _ e _ =>
    (List.finRange _).foldl (fun acc j => acc + (Body.walk c.env [false] (brs j)).cost)
      (PExpr.cost c e)
  | .data_brec _ _ _ _ brs _ e _ =>
    (List.finRange _).foldl (fun acc j => acc + (Body.walk c.env [false] (brs j)).cost)
      (PExpr.cost c e)
  | .thunk_force e => PExpr.cost c e
  | .lazy_force e => PExpr.cost c e
end

/-- Does the join point in front of `br` own its parameter (of type `σ`), in the environment
    `env` of the branch (`joinBranchEnv`)? -/
def joinParam {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    (σ : Ty ks) (env : Env) (br : Branch Δ d Φ Γ τ js ℓ) : Bool :=
  !Ty.needsOwn σ || (Branch.walk env br).jumps.headD true

/-! ## Versions of functions -/

/-- A version of a function: the parameters it **owns** (`owned`, one per parameter of its
    type, the first one first: its callers give those values up, so it may update them in
    place) and its cost in copies of arrays (`Own.Cost`: a static count, an update in a loop
    counts once). -/
structure Version where
  owned : List Bool
  cost : Cost
  deriving Inhabited, Repr, BEq

/-- The versions of a function of parameters `ps` worth generating, where `costWith fl` is its
    cost when it owns the parameters `fl`: the one borrowing every parameter (first); when
    owning some parameters (each of a type that holds arrays) saves copies of arrays, the one
    owning all of those; and, for two or three of them, one owning each of them alone. -/
def Version.select (ps : List (Ty ks)) (costWith : List Bool → Cost) : List Version :=
  let none := ps.map fun _ => false
  let base := costWith none
  let only (is : List Nat) : List Bool := (List.range ps.length).map fun i => is.contains i
  let gains := (List.range ps.length).filter fun i =>
    Ty.needsOwn (ps.getD i (.prim .bool)) && (costWith (only [i])).copies < base.copies
  let first : Version := ⟨none, base⟩
  if gains.isEmpty then [first] else
  let all : Version := ⟨only gains, costWith (only gains)⟩
  let singles := if gains.length ≥ 2 && gains.length ≤ 3 then
      gains.map fun i => (⟨only [i], costWith (only [i])⟩ : Version)
    else []
  first :: all :: singles

/-! ## Functions -/

/-- The parameters of a function type, all of them (a JavaScript function takes them at once). -/
def fnParams {d : Bool} : Ty ks d → List (Ty ks)
  | .fn σ τ => σ :: fnParams τ
  | _ => []

mutual
/-- The summary of a statement answering a function, applied to parameters owned or not (`ps`,
    the first one outermost), as the conversion applies it (`cApplyTerm`): the chain of lambdas
    `val k := fun x => …; ret k` takes the parameters one after the other; any other statement
    is examined as it is (the parameters it is applied to afterwards are borrowed). -/
partial def Term.walkApplied {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (env : Env) (ps : List Bool) (t : Term Δ d Φ Γ τ [] o) : Summary :=
  if ps.isEmpty then Term.walk env t else
  match t with
  | .letV _ v (.ret (.kvar k)) =>
    if k.index != 0 then Term.walk env t else
    match v with
    | .lam b => Body.walkApplied env ps b
    | _ => Term.walk env t
  | _ => Term.walk env t
/-- `Term.walkApplied` of the body of a lambda (its own parameter first). -/
partial def Body.walkApplied {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (env : Env) (ps : List Bool) (b : Body Δ d Φ Γ bs τ o) : Summary :=
  match ps with
  | [] => {}
  | p :: ps' => match b with
    | .closed t => Term.walkApplied { u := [p], k := env.k } ps' t
    | .opened t _ => Term.walkApplied (env.pushU [p]) ps' t
end

end Own

/-- A version of a translated function (`Own.Version`). -/
abbrev OwnVersion := Own.Version

/-- A translated function (`term`, the optimised one) and the versions of it worth generating:
    `versions` is never empty, and its first version borrows every parameter (what a caller
    outside the program gets). -/
structure OwnedTerm where
  term : ClosedTerm
  versions : List OwnVersion

namespace ClosedTerm

/-- The cost in copies of arrays of the program when it owns the parameters `ps`. -/
def costWith (ct : ClosedTerm) (ps : List Bool) : Own.Cost :=
  (Own.Term.walkApplied {} ps ct.term).cost

/-- The versions of a function worth generating (`Own.Version.select`). -/
def ownVersions (ct : ClosedTerm) : List OwnVersion :=
  Own.Version.select (Own.fnParams ct.τ) ct.costWith

/-- The function with the versions of it worth generating (`ownVersions`). -/
def withOwnership (ct : ClosedTerm) : OwnedTerm := { term := ct, versions := ct.ownVersions }

end ClosedTerm

/-- The suffix of the JavaScript name of a version: none for the version borrowing everything,
    `$$mut_0_2` for the one owning the first and third parameters (`$$` never occurs in the name
    of an exported function, whose components are joined by one `$`). -/
def OwnVersion.suffix (v : OwnVersion) : String :=
  let is := (v.owned.zipIdx.filter (·.1)).map (·.2)
  if is.isEmpty then "" else "$$mut_" ++ "_".intercalate (is.map toString)

end LeanScript

end
