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
  /-- The calls of local functions with versions, and their uses as values (`CallRec`): they
      decide which versions of each function are generated. -/
  calls : List CallRec := []
  deriving Inhabited, Repr, BEq

instance : Add Cost :=
  ⟨fun a b => ⟨a.inPlace + b.inPlace, a.copies + b.copies, a.calls ++ b.calls⟩⟩

/-- One copy of an array. -/
def Cost.copy : Cost := { copies := 1 }

/-- A use of the function `id` as a value (it needs the version borrowing everything). -/
def Cost.use (id : Nat) : Cost := { calls := [⟨id, [], 0, true⟩] }

/-- Does the cost record a use of the owning closure `id` as a value (which it forbids)? -/
def Cost.usesAsValue (x : Cost) (id : Nat) : Bool := x.calls.any fun r => r.isUse && r.id == id

/-- Is the type a function type? -/
def isFnTy {d : Bool} : Ty ks d → Bool
  | .fn _ _ => true
  | _ => false

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
  | .cond _ a b => PExpr.owned c a && PExpr.owned c b
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
    | .array_mk _ => true
    | _ => false
/-- The cost of a neutral expression: each update is done in place or copies. -/
partial def Neu.cost {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx) :
    Neu Δ Φ Γ τ ℓ → Cost
  | .var x => match c.env.uf.getD x.index none with
    | some fi => Cost.use fi.id
    | none => {}
  | .data_out _ _ n => Neu.cost c n
  | .cond n a b => Neu.cost c n + PExpr.cost c a + PExpr.cost c b
  | .extern ex args _ =>
    let nm := externName ex
    (if !isUpdate nm then {} else if updateInPlace c nm args then { inPlace := 1 }
      else Cost.copy) +
      Args.cost c args
/-- The cost of a pure expression. -/
partial def PExpr.cost {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx) :
    PExpr Δ Φ Γ τ o → Cost
  | .neu n => Neu.cost c n
  | .kvar x => match c.env.kf.getD x.index none with
    | some fi => Cost.use fi.id
    | none => {}
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

/-- The parameters of a function type, all of them (a JavaScript function takes them at once). -/
def fnParams {d : Bool} : Ty ks d → List (Ty ks)
  | .fn σ τ => σ :: fnParams τ
  | _ => []


/-- What is known of the function a call calls (a local function with versions, or a partial
    application of one), if anything. -/
def fnInfo? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (env : Env) :
    PExpr Δ Φ Γ τ o → Option FnOwn
  | .kvar x => env.kf.getD x.index none
  | .neu (.var x) => env.uf.getD x.index none
  | _ => none

/-- A call `f a` of a function with versions: what is known of `f`, and whether each argument
    passed so far (`a` last) is given up by the caller (`PExpr.owned`). -/
def appOffer {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Lvl} (c : Ctx)
    (f : PExpr Δ Φ Γ (.fn σ τ) of) (a : PExpr Δ Φ Γ σ oa) : Option (FnOwn × List Bool) :=
  (fnInfo? c.env f).map fun fi => (fi, fi.passed ++ [PExpr.owned c a])

/-- The partial application of a function with versions that a computation `cp` is (named by a
    `let` whose continuation has the occurrences `occT` of it).  The arguments it holds are given
    up by it only when the continuation uses it once, outside loops and closures (they then go to
    one call); otherwise they are not (every call borrows them, or copies them for an owning
    closure). -/
def papInfo {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (cp : Comp Δ d Φ Γ τ ℓ) (occT : Occ) : Option FnOwn × Cost :=
  match cp with
  | .app (τ := ρ) f a _ =>
    if !isFnTy ρ then (none, {}) else
    match appOffer c f a with
    | some (fi, off) =>
      let single := occT.n == 1 && occT.inBody == 0 && occT.inClosure == 0
      (some { fi with passed := if single then off else off.map fun _ => false }, {})
    | none => (none, {})
  | _ => (none, {})

/-- The version of a function with versions that a call calls: its index and the version. -/
def FnOwn.chosen (fi : FnOwn) (off : List Bool) : Nat × FnVer :=
  let j := fi.choose off
  (j, fi.vers.getD j default)

/-- The arguments a call of an owning closure copies (`FnOwn.must`): those it owns that the
    caller does not give up (`off`). -/
def FnOwn.copyMask (fi : FnOwn) (off : List Bool) : List Bool :=
  if !fi.must then [] else
  ((fi.vers.headD default).mask.zipIdx).map fun (b, i) => b && !off.getD i false

/-- The cost of the copies a call of an owning closure makes (`copyMask`); an argument that is not
    an array cannot be copied, which forbids the owning closure (`Cost.use`). -/
def FnOwn.copyCost (fi : FnOwn) (off : List Bool) : Cost :=
  (fi.copyMask off).zipIdx.foldl (fun acc (b, i) =>
    if !b then acc else if fi.copyable.getD i false then acc + Cost.copy
    else acc + Cost.use fi.id) {}

/-- The owning-closure mask of a function type: which of its parameters need owning (none when the
    type is not a function, or no parameter needs owning). -/
def fnMask {d : Bool} (τ : Ty ks d) : Option (List Bool) :=
  match τ with
  | .fn σ ρ =>
    let m := (σ :: fnParams ρ).map Ty.needsOwn
    if m.any (·) then some m else none
  | _ => none

/-- The owning closure `id` of the function type `τ`, owning the parameters `m`, whose answer is
    owned (`r`) or not. -/
def mustFn {d : Bool} (id : Nat) (τ : Ty ks d) (m : List Bool) (r : Bool) : FnOwn :=
  let ps := match τ with
    | .fn σ ρ => σ :: fnParams ρ
    | _ => []
  { id, vers := [⟨m, r⟩], must := true, copyable := ps.map isArrayTy }

/-- Is the expression, answered where an owning closure owning `m` is expected (`Env.retFn`), one:
    a local function with versions (the version owning the most of `m` is used; with `r`, its
    answer must be owned) or an owning closure of the same mask.  And the call record of the
    version used. -/
def retFnOk {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} (c : Ctx) (m : List Bool)
    (r : Bool) (e : PExpr Δ Φ Γ τ o) : Bool × Cost :=
  match e with
  | .kvar x => match c.env.kf.getD x.index none with
    | some fi =>
      let (j, v) := fi.chosen m
      (!r || v.ret, { calls := [⟨fi.id, m, j, false⟩] })
    | none => (false, PExpr.cost c e)
  | .neu (.var x) => match c.env.uf.getD x.index none with
    | some fi =>
      let v := fi.vers.headD default
      (fi.must && fi.passed.isEmpty && v.mask == m && (!r || v.ret), {})
    | none => (false, PExpr.cost c e)
  | _ => (false, PExpr.cost c e)

/-- The number of the owning closure that is the accumulator of a loop at depth `d` (its body
    is at depth `d + 1`), in the environment `env` of the loop. -/
def accFnId (d : Nat) (env : Env) : Nat := mustBase + 1000 * (d + 1) + env.u.length

/-- The number of the owning closure that a loop at depth `d` answers. -/
def resFnId (d : Nat) (env : Env) : Nat := mustBase + 1000 * d + env.u.length + 500

/-- The environment of the body of a loop whose accumulator (the parameter `idx`) is the owning
    closure `fi`, owning `m` (answer owned: `r`): its answers must be such closures too. -/
def Env.withAccFn (idx : Nat) (fi : FnOwn) (m : List Bool) (r : Bool) (e : Env) : Env :=
  { e with uf := e.uf.set idx (some fi), retFn := some (m, r) }

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
  /-- The accumulator is a function: every value it takes is an **owning closure**
      (`FnOwn.must`) owning the parameters of the mask, whose answer is owned when the flag is
      set. -/
  | ownFn (mask : List Bool) (ret : Bool)
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

/-- The versions of a local function worth generating (`lamPlan`): what its calls know of it
    (`info`), which versions are generated (`emit`, one per version of `info.vers`: those some
    call calls), what their bodies cost, and the summary of the statement after it (`rest`). -/
structure LamPlan where
  info : FnOwn
  emit : List Bool
  cost : Cost
  rest : Summary
  deriving Inhabited

/-- The environment of the body of a loop, a closure or a delay, seen from `env` outside it:
    nothing from outside is owned there (the body may run many times, or later), its
    parameters `ps` are as given (innermost first). -/
def Env.body (env : Env) (closed : Bool) (ps : List Bool) : Env :=
  if closed then env.closedBody ps else env.none.pushU ps

/-- The unknowns bound by the fields of a case analysis, all owned or not. -/
def fieldsOwned (n : Nat) (b : Bool) : List Bool := List.replicate n b

/-- Is the neutral expression a partly owned unknown (`Env.uh`) taken apart for the last time? -/
def Neu.partOwned {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx) :
    Neu Δ Φ Γ τ ℓ → Bool
  | .var x => c.partConsumable (.u x.index)
  | _ => false

/-- The fields of the record `n` (of type `.record t fs`) taken apart: which are owned and which
    partly owned.  All of them are owned when `n` is; when `n` is partly owned, the answer of the
    fold in a pair of a subvalue and that answer (`Env.isHole`) is owned (not the subvalue), and
    the fields of any other record are partly owned. -/
def recordFields {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} (c : Ctx) (t : Ty ks) (fs : Fields ks)
    (n : Neu Δ Φ Γ (.record t fs) ℓ) : List Bool × List Bool :=
  let m := (t :: fs.toList).length
  if Neu.owned c n then (fieldsOwned m true, fieldsOwned m false)
  else if Neu.partOwned c n then
    if c.env.isHole (Ty.record t fs) && m == 2 then ([false, true], [false, false])
    else (fieldsOwned m false, fieldsOwned m true)
  else (fieldsOwned m false, fieldsOwned m false)

/-- The pairs of a subvalue and the answer of a fold over block `b` answering `ρ` (the holes of
    its layers). -/
def recHoles (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) : List ((ks : List Nat) × Ty ks) :=
  (List.finRange _).map fun i => ⟨ks, Ty.pair (.data ((Δ.block b).ref i)) (ρ i)⟩

/-- The environment of a branch of a fold whose answers are owned: its layer (the parameter) is
    partly owned, the answers at the holes `hs` being owned. -/
def Env.withHoles (hs : List ((ks : List Nat) × Ty ks)) (e : Env) : Env :=
  { e with uh := e.uh.set 0 true, holes := hs }

mutual
/-- The summary of a statement in the environment `env`. -/
partial def Term.walk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (env : Env) : Term Δ d Φ Γ τ js o → Summary
  | .ret e =>
    let (c, _) := env.stmt (fun v => PExpr.occ v e) (fun _ => false)
    match env.retFn with
    | some (m, r) =>
      let (ok, cost) := retFnOk c m r e
      { ret := ok, cost }
    | none => { ret := PExpr.owned c e, cost := PExpr.cost c e }
  | .letV uk val b =>
    let (c, env') := env.stmt (fun v => Val.occ v val) (fun v => (Term.occ (v.upK 1) b).n > 0)
    match val, b with
    | .lam bd, b =>
      let plan := lamPlan uk c env' bd b
      { plan.rest with cost := plan.rest.cost + plan.cost }
    | val, b => (Term.walk (env'.pushK (Val.owned c val)) b).addCost (Val.cost c val)
  | .letE _ cp b =>
    let (c, env') := env.stmt (fun v => Comp.occ v cp) (fun v => (Term.occ (v.upU 1) b).n > 0)
    let (pf, pc) := papInfo c cp (Term.occ (.u 0) b)
    let allow := fnAllow c env' cp b
    let f := (Comp.fnResult c cp allow).or pf
    (Term.walk (env'.pushUF (Comp.owned c cp allow) f) b).addCost (Comp.cost c cp allow + pc)
  | .record_casesOn (t := t) (fs := fs) _ n b =>
    let m := (t :: fs.toList).length
    let (c, env') := env.stmt (fun v => Neu.occ v n) (fun v => (Term.occ (v.upU m) b).n > 0)
    let (bs, hs) := recordFields c t fs n
    (Term.walk (env'.pushUH bs hs) b).addCost (Neu.cost c n)
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
    (Branches.walk env' (Neu.owned c e) (Neu.partOwned c e) brs).addCost (Neu.cost c e)
  | .join σ _ _ body br =>
    let envBr := joinBranchEnv env body
    let sbr := Branch.walk envBr br
    let p := !Ty.needsOwn σ || sbr.jumps.headD true
    let sbody := Term.walk ((joinBodyEnv env br).pushU [p]) body
    { sbr with jumps := sbr.jumps.tail }.both sbody
/-- The summary of the arms of a union's case analysis, whose fields are owned (`ow`) or partly
    owned (`ph`) or not. -/
partial def Branches.walk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (env : Env) (ow ph : Bool) :
    Branches Δ d Φ Γ cs τ js o → Summary
  | .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
    (Term.walk (env.pushUH (fieldsOwned c₁.binds.length ow) (fieldsOwned c₁.binds.length ph))
      b₁).both
      (Term.walk (env.pushUH (fieldsOwned c₂.binds.length ow) (fieldsOwned c₂.binds.length ph))
        b₂)
  | .cons (c := c) _ b rest =>
    (Term.walk (env.pushUH (fieldsOwned c.binds.length ow) (fieldsOwned c.binds.length ph))
      b).both (Branches.walk env ow ph rest)
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
/-- `Body.walk`, the environment of the body changed by `f`. -/
partial def Body.walkMod {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (env : Env) (ps : List Bool) (f : Env → Env) : Body Δ d Φ Γ bs τ o → Summary
  | .closed t => Term.walk (f (env.body true ps)) t
  | .opened t _ => Term.walk (f (env.body false ps)) t
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
    (s : Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ os) (allow : Bool := true) :
    AccMode :=
  let id := accFnId d c.env
  match fnAccMode c τ z allow id fun m r =>
      Body.walkMod c.env [false, false] (Env.withAccFn 0 (mustFn id τ m r) m r) s with
  | some mode => mode
  | none => accMode c z fun b => Body.walk c.env [b, false] s
/-- How the body of `Array.foldl` gets its accumulator (`accMode`). -/
partial def foldlAcc {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t ρ : Ty ks} {u₁ u₂ : Usage01ω}
    {oz os : Lvl} (c : Ctx) (z : PExpr Δ Φ Γ ρ oz)
    (s : Body Δ d Φ Γ [⟨t, u₁, d + 1⟩, ⟨ρ, u₂, d + 1⟩] ρ os) (allow : Bool := true) :
    AccMode :=
  let id := accFnId d c.env
  match fnAccMode c ρ z allow id fun m r =>
      Body.walkMod c.env [false, false] (Env.withAccFn 1 (mustFn id ρ m r) m r) s with
  | some mode => mode
  | none => accMode c z fun b => Body.walk c.env [false, b] s
/-- Can the accumulator of a loop (of type `τ`, initial value `z`) be an owning closure
    (`AccMode.ownFn`)?  `τ` is a function type some parameters of which need owning (`fnMask`),
    `z` is a local function with versions or an owning closure (`retFnOk`), and the body (walked
    by `walk m r`, its accumulator the owning closure `id`) answers only such closures and never
    uses its accumulator as a value.  Tried with answers owned, then not. -/
partial def fnAccMode {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {oz : Lvl} (c : Ctx)
    (τ' : Ty ks) (z : PExpr Δ Φ Γ τ oz) (allow : Bool) (id : Nat)
    (walk : List Bool → Bool → Summary) : Option AccMode :=
  if !allow then none else
  match fnMask τ' with
  | none => none
  | some m =>
    let attempt (r : Bool) : Bool :=
      let sb := walk m r
      sb.ret && !sb.cost.usesAsValue id && (retFnOk c m r z).1
    if attempt true then some (.ownFn m true)
    else if attempt false then some (.ownFn m false)
    else none
/-- Does the fold `data_rec` over block `b` answer owned values?  Some answer type needs owning,
    and every branch answers an owned value when the answers at the holes of its layer are
    owned (`Env.withHoles`): each is the answer of one call of the fold, held only by the
    layer. -/
partial def dataRecOwns {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (c : Ctx) (b : BRef ks)
    (ρ : Fin ((Δ.block b).k + 1) → Ty ks) {us : Fin ((Δ.block b).k + 1) → Usage01ω}
    {os : Fin ((Δ.block b).k + 1) → Lvl}
    (brs : (i : Fin ((Δ.block b).k + 1)) →
      Body Δ d Φ Γ [⟨(Δ.block b).recBody ρ i, us i, d + 1⟩] (ρ i) (os i)) : Bool :=
  (List.finRange _).any (fun i => Ty.needsOwn (ρ i)) &&
  (List.finRange _).all fun i =>
    (Body.walkMod c.env [false] (Env.withHoles (recHoles b ρ)) (brs i)).ret
/-- The owning closure answered by a loop whose accumulator is one (`AccMode.ownFn`), if the loop
    is allowed to have one (`allow`). -/
partial def Comp.fnResult {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (cp : Comp Δ d Φ Γ τ ℓ) (allow : Bool) : Option FnOwn :=
  let id := resFnId d c.env
  match cp with
  | .nat_rec _ z s _ => match natRecAcc c z s allow with
    | .ownFn m r => some (mustFn id τ m r)
    | _ => none
  | .array_foldl _ z s _ => match foldlAcc c z s allow with
    | .ownFn m r => some (mustFn id τ m r)
    | _ => none
  | _ => none
/-- May the loop `cp` answer an owning closure (`Comp.fnResult`), followed by `b`?  Only if `b`
    never uses the closure as a value. -/
partial def fnAllow {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {u : Usage1ω} {o' : Lvl} (c : Ctx) (env' : Env) (cp : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') : Bool :=
  match Comp.fnResult c cp true with
  | none => true
  | some fi => !(Term.walk (env'.pushUF true (some fi)) b).cost.usesAsValue fi.id
/-- Is the result of a computation owned? -/
partial def Comp.owned {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (cp : Comp Δ d Φ Γ τ ℓ) (allow : Bool := true) : Bool :=
  !Ty.needsOwn τ ||
  match cp with
  | .share n => Neu.owned c n
  | .app (τ := ρ) f a _ =>
    !isFnTy ρ && match appOffer c f a with
      | some (fi, off) => (fi.chosen off).2.ret
      | none => false
  | .nat_rec _ z s _ => (natRecAcc c z s allow).owns
  | .array_foldl _ z s _ => (foldlAcc c z s allow).owns
  | .data_rec b ρ _ brs _ _ _ => dataRecOwns c b ρ brs
  | _ => false
/-- The cost of a computation. -/
partial def Comp.cost {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (c : Ctx)
    (cp : Comp Δ d Φ Γ τ ℓ) (allow : Bool := true) : Cost :=
  match cp with
  | .app (τ := ρ) f a _ =>
    match appOffer c f a with
    | some (fi, off) =>
      -- a call of a function with versions: the version it calls (a partial application is
      -- recorded where it is used, `papInfo`); a call of an owning closure copies the
      -- arguments it owns that the caller does not give up
      (if isFnTy ρ then {} else
        { calls := [⟨fi.id, off, (fi.chosen off).1, false⟩] } + fi.copyCost off) + PExpr.cost c a
    | none => PExpr.cost c f + PExpr.cost c a
  | .share n => Neu.cost c n
  | .nat_rec (τ := ρ) n z s _ =>
    match natRecAcc c z s allow with
    | .ownFn m r =>
      let id := accFnId d c.env
      PExpr.cost c n + (retFnOk c m r z).2 +
        (Body.walkMod c.env [false, false] (Env.withAccFn 0 (mustFn id ρ m r) m r) s).cost
    | m =>
    PExpr.cost c n + PExpr.cost c z + (if m == .copy then PExpr.copyCost c z else {}) +
      (Body.walk c.env [m.owns, false] s).cost
  | .array_foldl (ρ := ρ) a z s _ =>
    match foldlAcc c z s allow with
    | .ownFn m r =>
      let id := accFnId d c.env
      PExpr.cost c a + (retFnOk c m r z).2 +
        (Body.walkMod c.env [false, false] (Env.withAccFn 1 (mustFn id ρ m r) m r) s).cost
    | m =>
    PExpr.cost c a + PExpr.cost c z + (if m == .copy then PExpr.copyCost c z else {}) +
      (Body.walk c.env [false, m.owns] s).cost
  | .data_rec b ρ _ brs _ e _ =>
    let f := if dataRecOwns c b ρ brs then Env.withHoles (recHoles b ρ) else fun e => e
    (List.finRange _).foldl (fun acc j => acc + (Body.walkMod c.env [false] f (brs j)).cost)
      (PExpr.cost c e)
  | .data_brec _ _ _ _ brs _ e _ =>
    (List.finRange _).foldl (fun acc j => acc + (Body.walk c.env [false] (brs j)).cost)
      (PExpr.cost c e)
  | .thunk_force e => PExpr.cost c e
  | .lazy_force e => PExpr.cost c e
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
    | .closed t => Term.walkApplied (env.closedBody [p]) ps' t
    | .opened t _ => Term.walkApplied (env.pushU [p]) ps' t
/-- The versions of the local function `val k := fun x => bd` (in the context `c` of the value;
    `env'` is the environment after it) worth generating, followed by the statement `t`, and
    which of them are used (`LamPlan`): the version borrowing every parameter; and, when owning
    some parameters saves copies of arrays in the body (`gains`), for each way the calls in `t`
    give up those parameters, the version owning the ones given up (at most three).  Each call
    calls the version owning the most parameters its caller gives up (`FnOwn.choose`); a use of
    the function as a value gets the version borrowing everything.  A version no call calls is
    not generated. -/
partial def lamPlan {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ ρ : Ty ks} {js : JCtx ks}
    {u : Usage01ω} {o o' : Lvl} (uk : Usage1ω) (c : Ctx) (env' : Env)
    (bd : Body Δ d Φ Γ [⟨σ, u, d + 1⟩] τ o) (t : Term Δ d (⟨.fn σ τ, uk, o, true⟩ :: Φ) Γ ρ js o') :
    LamPlan :=
  let ps := σ :: fnParams τ
  let n := ps.length
  let id := env'.k.length
  let benv := c.env.none
  let bodyWith (m : List Bool) : Summary := Body.walkApplied benv m bd
  let none := ps.map fun _ => false
  let sb := bodyWith none
  let only (i : Nat) : List Bool := (List.range n).map (· == i)
  let gains := (List.range n).filter fun i =>
    Ty.needsOwn (ps.getD i (.prim .bool)) && (bodyWith (only i)).cost.copies < sb.cost.copies
  let walkT (vers : List FnVer) : Summary := Term.walk (env'.pushKF true (some { id, vers })) t
  let strip (x : Cost) : Cost := { x with calls := x.calls.filter fun r => r.id < id || r.id ≥ mustBase }
  let v0 : FnVer := ⟨none, sb.ret⟩
  if gains.isEmpty then
    let rest := walkT [v0]
    { info := { id, vers := [v0] }, emit := [true], cost := strip sb.cost,
      rest := { rest with cost := strip rest.cost } }
  else
    let offers := ((walkT [v0]).cost.calls.filter (·.id == id)).map (·.offered)
    let cands := offers.foldl (fun (acc : List (List Bool)) m =>
      let m' := (List.range n).map fun i => m.getD i false && gains.contains i
      if m'.any fun b => b && !acc.contains m' then acc ++ [m'] else acc) []
    let vers := v0 :: (cands.take 3).map fun m => (⟨m, (bodyWith m).ret⟩ : FnVer)
    let rest := walkT vers
    let recs := rest.cost.calls.filter (·.id == id)
    let emit := (List.range vers.length).map fun j => recs.any (·.chosen == j)
    let cost := (vers.zip emit).foldl (fun acc (v, e) =>
      if e then acc + (if v.mask.any fun b => b then (bodyWith v.mask).cost else sb.cost) else acc) {}
    { info := { id, vers }, emit, cost := strip cost, rest := { rest with cost := strip rest.cost } }
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
