module

public import LeanScript.Term.Build
public import LeanScript.TermElab.Relvl
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Reduce

@[expose] public section

meta section

set_option autoImplicit false

/-!
# The normaliser: from direct-style source trees to the syntax of normal-form `Term`s

`LeanScript.Term` is a grammar of **normal forms**: every redex that can be computed has been,
a known value is never taken apart, called or forced, and every call has an open operand.  It
is convenient to *write* a term in direct style (`f (if c then g x else 0) + 1`), so the
notation `[Term| …]` (`LeanScript.TermElab.Notation`), the translator `#leanscript_to_term`
(`LeanScript.TermElab.ToTerm`) build a direct-style source tree `Src` (whose variables are de
Bruijn indices of the source), and this module normalises it into the syntax of a `Term`.

The normaliser is a **normaliser by evaluation**, in continuation-passing style.  A source tree
is evaluated to a *semantic value* `Sem`:

* an unknown (a variable of the output, or of the enclosing context) or a neutral expression
  built on one (`data_out`, `cond`, a call of an extern with an open argument);
* a value of known shape: a literal, a record, a constructor of a union, an array or list
  literal, `data_in`, a closure or a delay (with its environment and its source body), or the
  application of a constructor function (`#leanscript_get_ctor`).

A known value is reduced as soon as it is eliminated: `data_out` of `data_in`, a case analysis
of a constructor or a literal, a call of a **closed** closure on a **closed** argument
(β-reduction: the body is evaluated with the argument), the force of a closed delay, a fold
over a closed count or array literal with a closed body (unrolled), a call of an extern on
closed arguments (`PExpr.externLit`).  What cannot be reduced is emitted, in evaluation order:

* a closure or a delay is bound by `Term.letV` (so it is shared by name, `PExpr.kvar`); its
  body is normalised on its own, one level deeper, and is `Body.closed` exactly when it
  mentions nothing bound outside of it (the level of what the body mentions is tracked, so the
  choice is exact);
* a computation with an open operand (a call, a fold, a force) is bound by `Term.letE`;
* a source `let` of a compound neutral expression is `Comp.share`d; of a data literal, bound by
  `Term.letV` (still known, so later case analyses are reduced);
* a branch on a neutral value in tail position gets the continuation in each branch; anywhere
  else it is the pure conditional `Neu.cond` when it is an `if` whose branches are pure, and
  otherwise gets a **join point** for the rest of the computation.  A join point is only
  allowed in front of a branch (`Branch.join`), so join points are kept *pending* until the
  next branch, where they are placed; a pending join point that is jumped to in straight-line
  code is inlined instead (it is jumped to only there).

Every binder is annotated `many` (`Usage1ω.many`, `Usage01ω.many`): the annotations are sound
and a later pass (`Term.dce`) can make them exact.

Variables are resolved to indices only when rendered: a semantic value names an output
variable by its *position* (the number of binders of its context outside it), so it stays
valid under the binders the normaliser adds.  A variable of the enclosing context (free in the
source) is an unknown, and is taken to be open.
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

/-! ## Source trees -/

/-- The value of a literal, when it is known while normalising. -/
inductive LitVal where
  | nat (n : Nat)
  | bool (b : Bool)
  | other
  deriving Inhabited, Repr, BEq

/-- What the constructor function of a Lean constructor builds (`#leanscript_get_ctor`). -/
inductive CtorKind where
  /-- `false`/`true` of a type of two points. -/
  | bool (b : Bool)
  /-- Constructor `i` of an enum. -/
  | enum (i : Nat)
  /-- The only field of a one-constructor, one-field type: the field itself. -/
  | wrap
  /-- The record of the fields of a one-constructor type. -/
  | record
  /-- The constructor at position `pos` of a union. -/
  | union (pos : Nat)
  deriving Inhabited, Repr

/-- The shape of a constructor function: its kind, and the block and member of `data_in` when
    the type is recursive. -/
structure CtorShape where
  kind : CtorKind
  data? : Option (Lean.Term × Lean.Term) := none
  deriving Inhabited

/-- A direct-style source tree.  Variables and join points are de Bruijn indices of the
    source. -/
inductive Src where
  /-- Variable `i`. -/
  | var (i : Nat)
  /-- A literal (the syntax of a closed `PExpr`), and its value when known. -/
  | lit (stx : Lean.Term) (val : LitVal)
  /-- Constructor `i` of an enum (when known), and its syntax. -/
  | enumMk (i : Option Nat) (stx : Lean.Term)
  /-- A record, from its fields. -/
  | record (args : Array Src)
  /-- A constructor of a union (at position `pos` when known; `ix` a `CtorIx`). -/
  | union (pos : Option Nat) (ix : Lean.Term) (args : Array Src)
  /-- An array literal. -/
  | array (es : Array Src)
  /-- A list literal. -/
  | list (es : Array Src)
  /-- One layer in. -/
  | dataIn (b j : Lean.Term) (e : Src)
  /-- A Lean function of pure expressions, whose level is the smallest of its arguments' (a
      constructor function of `#leanscript_get_ctor`), applied; with its shape when known. -/
  | ctor (f : Lean.Term) (args : Array Src) (shape : Option CtorShape)
  /-- A closed Lean term of type `PExpr`, generic in its contexts. -/
  | embed (stx : Lean.Term)
  /-- One layer out. -/
  | dataOut (b j : Lean.Term) (e : Src)
  /-- The pure conditional. -/
  | cond (c a b : Src)
  /-- A call of an extern (`e` the syntax of an `Extern`). -/
  | extern (e : Lean.Term) (args : Array Src)
  /-- An operand at a given type. -/
  | ascribe (s : Src) (ty : Lean.Term)
  /-- An application. -/
  | app (f a : Src)
  /-- `fun x => body` (`ty?` the type of `x`). -/
  | lam (ty? : Option Lean.Term) (body : Src)
  /-- A delay of `body` (`lazy`: recomputed; else memoised), of contents `τ?`. -/
  | delayMk (lazy : Bool) (τ? : Option Lean.Term) (body : Src)
  /-- The value of a delay. -/
  | force (lazy : Bool) (τ? : Option Lean.Term) (e : Src)
  /-- `Nat.rec`: the step binds the answer (`#0`) and the predecessor (`#1`). -/
  | natRec (τ? : Option Lean.Term) (n z s : Src)
  /-- `Array.foldl`: the step binds the element (`#0`) and the accumulator (`#1`). -/
  | arrayFoldl (a z s : Src)
  /-- The fold of block `b` (course-of-values of depth `k?` when given), one branch per member
      (binding its body). -/
  | dataRec (Δ? : Option Lean.Term) (b ρ : Lean.Term) (k? : Option Lean.Term) (brs : Array Src)
      (j : Lean.Term) (e : Src)
  /-- `let x := v; b`. -/
  | letE (v b : Src)
  /-- Take a record of `n` fields apart; the body binds them (the first field innermost). -/
  | recordCases (scrut : Src) (n : Nat) (body : Src)
  /-- `if c then a else b`. -/
  | ite (ty? : Option Lean.Term) (c a b : Src)
  /-- A case analysis of an enum: branch `k` is the one of constructor `pats[k]`; the last
      branch is the default. -/
  | enumCases (ty? : Option Lean.Term) (scrut : Src) (pats : Array (Option Nat)) (brs : Array Src)
  /-- A case analysis of a union, one branch per constructor (binding its fields). -/
  | unionCases (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src))
  /-- `join j (x : ty) := body; main`: `body` binds `x`, `main` sees the join point `j`. -/
  | join (ty? : Option Lean.Term) (body main : Src)
  /-- Jump to join point `j` of the source. -/
  | jump (j : Nat) (arg : Src)
  deriving Inhabited

/-- The head and the arguments of an application. -/
def Src.spine (s : Src) : Src × List Src :=
  go s []
where
  go : Src → List Src → Src × List Src
    | .app f a, as => go f (a :: as)
    | f, as => (f, as)

/-- The number of leading `fun`s. -/
def Src.lams : Src → Nat
  | .lam _ b => b.lams + 1
  | _ => 0

/-- The types of the first `n` leading `fun`s, and what is under them. -/
def Src.peel : Src → Nat → List (Option Lean.Term) × Src
  | .lam ty? b, n + 1 => let (tys, r) := b.peel n; (ty? :: tys, r)
  | s, _ => ([], s)

/-! ## Semantic values -/

/-- A known value bound by `letV`: its position in the known context, and its level. -/
structure KRef where
  pos : Nat
  lv : Lvl
  deriving Inhabited, Repr, BEq

/-- An unknown: at position `pos` of the output's context of unknowns, bound at level `lv`; or
    variable `i` of the enclosing context. -/
inductive URef where
  | out (pos lv : Nat)
  | free (i : Nat)
  deriving Inhabited, Repr, BEq

/-- Semantic values. -/
inductive Sem where
  | unk (r : URef)
  | dataOut (b j : Lean.Term) (e : Sem)
  | cond (c a b : Sem)
  | extern (e : Lean.Term) (args : Array Sem)
  | lit (stx : Lean.Term) (val : LitVal)
  | enum (i : Option Nat) (stx : Lean.Term)
  | record (fs : Array Sem) (name : Option KRef)
  | union (pos : Option Nat) (ix : Lean.Term) (fs : Array Sem) (name : Option KRef)
  | array (es : Array Sem) (name : Option KRef)
  | list (es : Array Sem) (name : Option KRef)
  | dataIn (b j : Lean.Term) (e : Sem) (name : Option KRef)
  | ctor (f : Lean.Term) (fs : Array Sem) (shape : Option CtorShape)
  | embed (stx : Lean.Term)
  | clo (env : List Sem) (ty? : Option Lean.Term) (body : Src) (k : KRef)
  | delay (lazy : Bool) (τ? : Option Lean.Term) (env : List Sem) (body : Src) (k : KRef)
  | ascribe (s : Sem) (ty : Lean.Term)
  deriving Inhabited

/-- The smaller of two levels (`none` is the unit). -/
def lmeet : Lvl → Lvl → Lvl
  | none, o => o
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

/-- The value without its type ascriptions. -/
partial def Sem.strip : Sem → Sem
  | .ascribe s _ => s.strip
  | s => s

/-- The name of a value bound by `letV`. -/
def Sem.name? : Sem → Option KRef
  | .record _ n | .union _ _ _ n | .array _ n | .list _ n | .dataIn _ _ _ n => n
  | .clo _ _ _ k | .delay _ _ _ _ k => some k
  | _ => none

mutual
/-- The level of a semantic value: the smallest level of the unknowns it mentions. -/
partial def Sem.lv (s : Sem) : Lvl :=
  match s with
  | .unk (.out _ l) => some l
  | .unk (.free _) => some 0
  | .dataOut _ _ e => e.lv
  | .cond c a b => lmeet c.lv (lmeet a.lv b.lv)
  | .extern _ as => Sem.lvAll as.toList
  | .lit .. | .enum .. | .embed _ => none
  | .ctor _ fs _ => Sem.lvAll fs.toList
  | .ascribe s _ => s.lv
  | s => match s.name? with
    | some k => k.lv
    | none => match s with
      | .record fs _ | .union _ _ fs _ | .array fs _ | .list fs _ => Sem.lvAll fs.toList
      | .dataIn _ _ e _ => e.lv
      | _ => none
/-- The level of several values together. -/
partial def Sem.lvAll : List Sem → Lvl
  | [] => none
  | s :: ss => lmeet s.lv (Sem.lvAll ss)
end

/-- Is a value neutral: an unknown, or an elimination stuck on one? -/
partial def Sem.isNeutral : Sem → Bool
  | .unk _ | .dataOut .. | .cond .. | .extern .. => true
  | .ascribe s _ => s.isNeutral
  | _ => false

/-- Is a value used in place when bound by a source `let` (never shared)? -/
def Sem.trivial (s : Sem) : Bool :=
  match s.strip with
  | .unk _ | .lit .. | .enum .. | .embed _ | .ctor .. => true
  | s => s.name?.isSome

/-! ## Positions, join points, results -/

/-- Where the output is: the numbers of unknowns, known values and join points in scope, the
    depth (the number of bodies around), and the join points placed so far (by identifier,
    with their positions). -/
structure Core where
  du : Nat := 0
  dk : Nat := 0
  jd : Nat := 0
  depth : Nat := 0
  placed : List (Name × Nat) := []
  deriving Inhabited

/-- A statement produced by the normaliser, and its level. -/
structure Out where
  stx : Lean.Term
  lv : Lvl
  deriving Inhabited

/-- A pending join point: the continuation it stands for, placed in front of the next branch or
    inlined where it is jumped to. -/
structure Pend where
  id : Name
  ty? : Option Lean.Term
  k : Sem → Core → TermElabM Out

/-- A position, with the join points still pending (innermost first). -/
structure Pos where
  core : Core := {}
  pend : List Pend := []

/-- The source variables and join points in scope, innermost first. -/
structure Scope where
  vars : List Sem := []
  joins : List Name := []
  deriving Inhabited

/-- The value of source variable `i`: an unknown of the enclosing context past the end. -/
def Scope.var (sc : Scope) (i : Nat) : Sem :=
  if h : i < sc.vars.length then sc.vars[i] else .unk (.free (i - sc.vars.length))

/-- Bind source variables to the values `ss`, the first one innermost (index `0`). -/
def Scope.pushAll (sc : Scope) (ss : List Sem) : Scope := { sc with vars := ss ++ sc.vars }

/-- Bind one more source variable. -/
def Scope.push (sc : Scope) (s : Sem) : Scope := sc.pushAll [s]

/-- The unknowns at positions `du`, …, `du + n - 1`, at level `lv`, the last one innermost:
    the binders of a pattern or a body. -/
def unknowns (n du lv : Nat) : List Sem :=
  (List.range n).reverse.map fun i => .unk (.out (du + i) lv)

/-- What is done with the value of a statement: return it, jump with it to a join point, or
    continue with it. -/
inductive Kont where
  | ret
  | jump (id : Name)
  | fn (k : Sem → Pos → TermElabM Out)

/-! ## Rendering -/

/-- A variable of the context of unknowns, by index. -/
def uvarStx : Nat → TermElabM Lean.Term
  | 0 => `(LeanScript.UVar.head (by decide))
  | n + 1 => do `(LeanScript.UVar.tail $(← uvarStx n))

/-- A variable of the context of known values, by index. -/
def kvarStx : Nat → TermElabM Lean.Term
  | 0 => `(LeanScript.KVar.head)
  | n + 1 => do `(LeanScript.KVar.tail $(← kvarStx n))

/-- A join point, by index. -/
def jvarStx : Nat → TermElabM Lean.Term
  | 0 => `(LeanScript.JVar.head)
  | n + 1 => do `(LeanScript.JVar.tail $(← jvarStx n))

/-- The arguments of a constructor or an extern. -/
def argsStx : List Lean.Term → TermElabM Lean.Term
  | [] => `(LeanScript.Args.nil)
  | t :: ts => do `(LeanScript.Args.cons $t $(← argsStx ts))

/-- The elements of an array or list literal. -/
def elemsStx : List Lean.Term → TermElabM Lean.Term
  | [] => `(LeanScript.Elems.nil)
  | t :: ts => do `(LeanScript.Elems.cons $t $(← elemsStx ts))

/-- The payload of a constructor function under its `data_in`, as a semantic value. -/
def payloadOf (sh : CtorShape) (fs : Array Sem) : TermElabM Sem := do
  match sh.kind with
  | .bool b => return .lit (← if b then `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)
      else `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)) (.bool b)
  | .enum i => return .enum (some i) (← `(LeanScript.PExpr.enum_mk _ ⟨$(quote i), by decide⟩))
  | .wrap => return fs[0]!
  | .record => return .record fs none
  | .union pos => return .union (some pos) (← `(LeanScript.Ctors.ix _ $(quote pos) (by decide))) fs none

mutual
/-- The syntax of a neutral value (`Neu`) at `c`. -/
partial def renderNeu (s : Sem) (c : Core) (inline : Bool) : TermElabM Lean.Term := do
  match s with
  | .unk (.out pos _) => `(LeanScript.Neu.var $(← uvarStx (c.du - 1 - pos)))
  | .unk (.free i) => `(LeanScript.Neu.var $(← uvarStx (i + c.du)))
  | .dataOut b j e => `(LeanScript.Neu.data_out $b $j $(← renderNeu e c inline))
  | .cond x a b =>
      `(LeanScript.Neu.cond $(← renderNeu x c inline) $(← render a c inline) $(← render b c inline))
  | .extern e as => do
      `(LeanScript.Neu.extern $e $(← argsStx (← as.toList.mapM (render · c inline))) rfl)
  | .ascribe s ty => `(($(← renderNeu s c inline) : LeanScript.Neu _ _ _ $ty _))
  | _ => throwError "internal error of the normaliser: a value of known shape is not neutral"

/-- The syntax of a value as a pure expression (`PExpr`) at `c`.  A value bound by `letV` is
    named (`PExpr.kvar`), unless `inline` (for the closed arguments of an extern, in empty
    contexts). -/
partial def render (s : Sem) (c : Core) (inline : Bool) : TermElabM Lean.Term := do
  if s.isNeutral then
    if let .ascribe s' ty := s then
      return ← `(($(← render s' c inline) : LeanScript.PExpr _ _ _ $ty _))
    return ← `(LeanScript.PExpr.neu $(← renderNeu s c inline))
  if !inline then
    if let some k := s.name? then
      return ← `(LeanScript.PExpr.kvar $(← kvarStx (c.dk - 1 - k.pos)))
  match s with
  | .lit stx _ | .enum _ stx | .embed stx => pure stx
  | .record fs _ => `(LeanScript.PExpr.record_mk $(← argsStx (← fs.toList.mapM (render · c inline))))
  | .union _ ix fs _ =>
      `(LeanScript.PExpr.union_mk $ix $(← argsStx (← fs.toList.mapM (render · c inline))))
  | .array es _ => `(LeanScript.PExpr.array_mk $(← elemsStx (← es.toList.mapM (render · c inline))))
  | .list es _ => `(LeanScript.PExpr.list_mk $(← elemsStx (← es.toList.mapM (render · c inline))))
  | .dataIn b j e _ => `(LeanScript.PExpr.data_in $b $j $(← render e c inline))
  | .ctor f fs _ => do
      let xs ← fs.mapM (render · c inline)
      `($f $xs*)
  | .ascribe s ty => `(($(← render s c inline) : LeanScript.PExpr _ _ _ $ty _))
  | .clo .. | .delay .. =>
      throwError "a closure or a delay cannot be an argument of an extern called at elaboration \
        time"
  | _ => throwError "internal error of the normaliser: unexpected value"
end

/-! ## Values known while normalising -/

/-- Evaluate a closed pure expression of a leaf type while normalising, to a literal value. -/
def evalLit (stx : Lean.Term) : TermElabM LitVal := do
  try
    withoutModifyingState do
      let e ← elabTerm (← `(LeanScript.PExpr.eval (Δ := LeanScript.DSig.nil) (Φ := [])
        (Γ := []) $stx PUnit.unit PUnit.unit)) none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let v ← withTransparency .all <| whnf e
      if v.isConstOf ``Bool.true then return .bool true
      if v.isConstOf ``Bool.false then return .bool false
      match v with
      | .lit (.natVal n) => return .nat n
      | _ =>
        let v ← withTransparency .all <| Meta.reduce e
        if v.isConstOf ``Bool.true then return .bool true
        if v.isConstOf ``Bool.false then return .bool false
        match v with
        | .lit (.natVal n) => return .nat n
        | _ => return .other
  catch _ => return .other

/-- The value of a boolean known while normalising. -/
partial def Sem.boolVal? (s : Sem) : TermElabM (Option Bool) := do
  match s with
  | .lit _ (.bool b) => return some b
  | .lit stx .other => match ← evalLit stx with
    | .bool b => return some b
    | _ => return none
  | .ctor _ _ (some { kind := .bool b, data? := none }) => return some b
  | .ascribe s _ => s.boolVal?
  | _ => return none

/-- The value of a natural number known while normalising. -/
partial def Sem.natVal? (s : Sem) : TermElabM (Option Nat) := do
  match s with
  | .lit _ (.nat n) => return some n
  | .lit stx .other => match ← evalLit stx with
    | .nat n => return some n
    | _ => return none
  | .ascribe s _ => s.natVal?
  | _ => return none

/-- One layer out of a value: the payload of `data_in` (or of a constructor function of a
    recursive type), else `data_out` of a neutral value. -/
def dataOutSem (b j : Lean.Term) (s : Sem) : TermElabM Sem := do
  match s.strip with
  | .dataIn _ _ x _ => return x
  | .ctor _ fs (some sh) =>
      if sh.data?.isSome then payloadOf { sh with data? := none } fs
      else throwError "`data_out` of a value that is not of a recursive type"
  | _ =>
    unless s.isNeutral do
      throwError "cannot take apart a value of unknown shape (a Lean term) while normalising"
    return .dataOut b j s

/-- A call of an extern: computed when every argument is closed (`PExpr.externLit`), else a
    neutral call. -/
def externSem (e : Lean.Term) (fs : Array Sem) : TermElabM Sem := do
  if (Sem.lvAll fs.toList).isNone then
    let args ← argsStx (← fs.toList.mapM (render · {} true))
    let stx ← `(LeanScript.PExpr.externLit $e $args)
    -- its value, as a literal, when it is found while normalising
    match ← evalLit stx with
    | .nat n => return .lit (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.nat $(quote n))) (.nat n)
    | .bool b => return .lit (← if b then `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)
        else `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)) (.bool b)
    | .other => return .lit stx .other
  return .extern e fs

/-- The branch a value selects in an `if` (`0` for `true`), when it is known. -/
def iteSel (s : Sem) : TermElabM (Option Nat) := do
  return (← s.boolVal?).map fun b => if b then 0 else 1

/-- The branch a value selects in a case analysis of an enum, when it is known. -/
def enumSel (pats : Array (Option Nat)) (s : Sem) : Option Nat :=
  let pick (i : Nat) := (pats.findIdx? (· == some i)).getD (pats.size - 1)
  match s.strip with
  | .enum (some i) _ => some (pick i)
  | .ctor _ _ (some { kind := .enum i, data? := none }) => some (pick i)
  | _ => none

/-- The branch and the fields a value selects in a case analysis of a union, when it is a
    known constructor. -/
def unionSel (brs : Array Nat) (s : Sem) : Option (Nat × Array Sem) :=
  match s.strip with
  | .union (some pos) _ fs _ => if brs[pos]? == some fs.size then some (pos, fs) else none
  | .ctor _ fs (some { kind := .union pos, data? := none }) =>
      if brs[pos]? == some fs.size then some (pos, fs) else none
  | _ => none

/-- The fields of a known record of `n` fields. -/
def recordSel (n : Nat) (s : Sem) : Option (Array Sem) :=
  match s.strip with
  | .record fs _ => if fs.size == n then some fs else none
  | .ctor _ fs (some { kind := .record, data? := none }) => if fs.size == n then some fs else none
  | _ => none

/-! ## Emitting -/

/-- `let x := c; …` of a computation of level `ℓ`. -/
def emitComp (cs : Lean.Term) (ℓ : Nat) (p : Pos) (k : Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  let c := p.core
  let r ← k (.unk (.out c.du c.depth)) { p with core := { c with du := c.du + 1 } }
  return { stx := ← `(LeanScript.Term.letE (d := $(quote c.depth)) .many $cs $(r.stx)), lv := lmeet (some ℓ) r.lv }

/-- `val %k := v; …` of a value of level `o`, known as `mk` of its name afterwards. -/
def emitVal (vs : Lean.Term) (o : Lvl) (mk : KRef → Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  let c := p.core
  let r ← k (mk { pos := c.dk, lv := o }) { p with core := { c with dk := c.dk + 1 } }
  return { stx := ← `(LeanScript.Term.letV .many $vs $(r.stx)), lv := lmeet o r.lv }

/-- The operand level of a computation, which must be open. -/
def openLv (o : Lvl) (what : String) : TermElabM Nat :=
  match o with
  | some ℓ => pure ℓ
  | none => throwError "internal error of the normaliser: {what} with no open operand"

/-- `return v`. -/
def retOut (s : Sem) (p : Pos) : TermElabM Out := do
  return { stx := ← `(LeanScript.Term.ret $(← render s p.core false)), lv := s.lv }

/-- Jump with `s` to the join point `id`: `Term.jump` when it is placed, its body (inlined)
    when it is pending. -/
def jumpTo (id : Name) (s : Sem) (p : Pos) : TermElabM Out := do
  let c := p.core
  if let some l := c.placed.lookup id then
    return { stx := ← `(LeanScript.Term.jump $(← jvarStx (c.jd - 1 - l)) $(← render s c false)),
             lv := s.lv }
  match p.pend.find? (·.id == id) with
  | some pj => pj.k s c
  | none => throwError "internal error of the normaliser: unknown join point"

/-- Give the value `s` to `K`. -/
def Kont.apply (K : Kont) (s : Sem) (p : Pos) : TermElabM Out :=
  match K with
  | .ret => retOut s p
  | .jump id => jumpTo id s p
  | .fn f => f s p

/-- The join points pending at `p` (not placed yet), outermost first. -/
def Pos.pending (p : Pos) : List Pend :=
  (p.pend.filter fun pj => (p.core.placed.lookup pj.id).isNone).reverse

/-- Place the pending join points in front of a branch: `arms c` renders the branch at the
    position `c` where they are all in scope. -/
def placeJoins (p : Pos) (arms : Core → TermElabM Out) : TermElabM Out := do
  let c := p.core
  let pends := p.pending
  let rec go (c : Core) : List Pend → TermElabM Out
    | [] => arms c
    | pj :: rest => do
        let body ← pj.k (.unk (.out c.du c.depth)) { c with du := c.du + 1 }
        let main ← go { c with jd := c.jd + 1, placed := (pj.id, c.jd) :: c.placed } rest
        let ty ← match pj.ty? with | some t => pure t | none => `(_)
        return { stx := ← `(LeanScript.Branch.join (d := $(quote c.depth)) $ty .many .many $(body.stx) $(main.stx)),
                 lv := lmeet body.lv main.lv }
  let br ← go c pends
  return { stx := ← `(LeanScript.Term.branch $(br.stx)), lv := br.lv }

/-- The union branches `Branches.two`/`Branches.cons` of rendered branches. -/
def branchesStx (d : Nat) : List Lean.Term → TermElabM Lean.Term
  | [a, b] => `(LeanScript.Branches.two (d := $(quote d)) [] [] $a $b)
  | a :: rest => do `(LeanScript.Branches.cons (d := $(quote d)) [] $a $(← branchesStx d rest))
  | [] => throwError "a union has at least two constructors"

/-- A case analysis of a union (or a record) of `n` fields: the error when the scrutinee is not
    neutral. -/
def needNeutral (s : Sem) (what : String) : TermElabM Unit := do
  unless s.isNeutral do
    throwError "cannot take apart a value of unknown shape (a Lean term) while normalising: {what}"

/-! ## The normaliser -/

mutual

/-- Normalise the operands `ss` in order, then continue with their values. -/
partial def values (ss : List Src) (sc : Scope) (p : Pos)
    (k : List Sem → Pos → TermElabM Out) : TermElabM Out :=
  match ss with
  | [] => k [] p
  | s :: ss => value s sc p fun v p => values ss sc p fun vs p => k (v :: vs) p

/-- Bind a value by a source `let`: in place when trivial, a compound neutral expression
    shared (`Comp.share`), a data literal bound by `letV`. -/
partial def bindSem (s : Sem) (p : Pos) (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if s.trivial then return ← k s p
  if s.isNeutral then
    return ← emitComp (← `(LeanScript.Comp.share $(← renderNeu s p.core false)))
      (← openLv s.lv "a shared expression") p k
  let (s', ty?) := match s with
    | .ascribe s ty => (s.strip, some ty)
    | s => (s, none)
  let c := p.core
  let asc (v : Lean.Term) : TermElabM Lean.Term := match ty? with
    | some ty => `(($v : LeanScript.Val _ _ _ _ $ty _))
    | none => pure v
  match s' with
  | .record fs _ =>
      let vs ← asc (← `(LeanScript.Val.record_mk $(← argsStx (← fs.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .record fs (some kr)) p k
  | .union pos ix fs _ =>
      let vs ← asc (← `(LeanScript.Val.union_mk $ix $(← argsStx (← fs.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .union pos ix fs (some kr)) p k
  | .array es _ =>
      let vs ← asc (← `(LeanScript.Val.array_mk $(← elemsStx (← es.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .array es (some kr)) p k
  | .list es _ =>
      let vs ← asc (← `(LeanScript.Val.list_mk $(← elemsStx (← es.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .list es (some kr)) p k
  | .dataIn b j e _ =>
      let vs ← asc (← `(LeanScript.Val.data_in $b $j $(← render e c false)))
      emitVal vs s.lv (fun kr => .dataIn b j e (some kr)) p k
  | _ => k s p

/-- Bind values in order (`bindSem`). -/
partial def bindSems (ss : List Sem) (p : Pos) (k : List Sem → Pos → TermElabM Out) :
    TermElabM Out :=
  match ss with
  | [] => k [] p
  | s :: ss => bindSem s p fun s p => bindSems ss p fun ss p => k (s :: ss) p

/-- The body of a closure, a delay or a fold, binding `n` unknowns: normalised one level
    deeper, and `Body.closed` exactly when it mentions nothing bound outside of it.  Returns
    the syntax of the `Body` and its level. -/
partial def mkBody (n : Nat) (body : Src) (sc : Scope) (p : Pos) : TermElabM (Lean.Term × Lvl) := do
  let c := p.core
  let inner : Core := { du := c.du + n, dk := c.dk, jd := 0, depth := c.depth + 1, placed := [] }
  let sc' : Scope := { vars := unknowns n c.du (c.depth + 1) ++ sc.vars, joins := [] }
  let o ← stmt body sc' { core := inner } .ret
  match o.lv with
  | some m =>
      if m ≤ c.depth then return (← `(LeanScript.Body.opened (d := $(quote c.depth)) (ls_relvl% $(o.stx)) (by ls_lvl)), some m)
      else return (← `(LeanScript.Body.closed (d := $(quote c.depth)) $(o.stx)), none)
  | none => return (← `(LeanScript.Body.closed (d := $(quote c.depth)) $(o.stx)), none)

/-- Apply the value `f` to `a`: β-reduce a closed closure on a closed argument, else call it. -/
partial def apply (f a : Sem) (p : Pos) (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if let .clo env _ body kr := f.strip then
    if kr.lv.isNone && a.lv.isNone then
      return ← value body { vars := a :: env } p k
  let ℓ ← match lmeet f.lv a.lv with
    | some ℓ => pure ℓ
    | none => throwError "cannot call a closed function that is not a closure while normalising"
  emitComp (← `(LeanScript.Comp.app $(← render f p.core false) $(← render a p.core false) rfl)) ℓ p k

/-- A statement in the middle of a computation: a pending join point for the continuation
    `k`, and the statement jumping to it. -/
partial def reify (ty? : Option Lean.Term) (run : Pos → Kont → TermElabM Out) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  let id ← mkFreshId
  let saved := p.pend
  let pj : Pend := { id, ty?, k := fun s c => k s { core := c, pend := saved } }
  run { p with pend := pj :: p.pend } (.jump id)

/-- Normalise `s` to a value, and continue with it. -/
partial def value (s : Src) (sc : Scope) (p : Pos) (k : Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  match s with
  | .var i => k (sc.var i) p
  | .lit stx v => k (.lit stx v) p
  | .enumMk i stx => k (.enum i stx) p
  | .record args => values args.toList sc p fun fs p => k (.record fs.toArray none) p
  | .union pos ix args => values args.toList sc p fun fs p => k (.union pos ix fs.toArray none) p
  | .array es => values es.toList sc p fun fs p => k (.array fs.toArray none) p
  | .list es => values es.toList sc p fun fs p => k (.list fs.toArray none) p
  | .dataIn b j e => value e sc p fun v p => k (.dataIn b j v none) p
  | .ctor f args shape => (values args.toList sc p fun fs p => do
      match shape with
      | some { kind := .wrap, data? := none } => k fs[0]! p
      | _ => k (.ctor f fs.toArray shape) p)
  | .embed stx => k (.embed stx) p
  | .dataOut b j e => value e sc p fun v p => do k (← dataOutSem b j v) p
  | .cond c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => value a sc p k
      | some _ => value b sc p k
      | none =>
        needNeutral cv "the condition of `cond`"
        values [a, b] sc p fun vs p => k (.cond cv vs[0]! vs[1]!) p)
  | .extern e args => values args.toList sc p fun fs p => do k (← externSem e fs.toArray) p
  | .ascribe s ty => value s sc p fun v p => k (.ascribe v ty) p
  | .app f a => (do
      -- `(fun x₁ … xₙ => b) a₁ … aₖ` (`k ≤ n`) is `let x₁ := a₁; …`: no closure is built
      let (hd, as) := Src.spine s
      if as.length ≤ Src.lams hd then
        values as sc p fun avs p => do
          let (tys, body) := Src.peel hd as.length
          let avs := (avs.zip tys).map fun (a, ty?) => match ty? with
            | some ty => Sem.ascribe a ty
            | none => a
          bindSems avs p fun avs p => value body (sc.pushAll avs.reverse) p k
      else
        value f sc p fun fv p => value a sc p fun av p => apply fv av p k)
  | .lam ty? body => (do
      let (bs, o) ← mkBody 1 body sc p
      let vs ← match ty? with
        | some τ => `(LeanScript.Val.lam (σ := $τ) (u := .many) $bs)
        | none => `(LeanScript.Val.lam (u := .many) $bs)
      emitVal vs o (fun kr => .clo sc.vars ty? body kr) p k)
  | .delayMk lazy τ? body => (do
      let (bs, o) ← mkBody 0 body sc p
      let vs ← match lazy, τ? with
        | false, some τ => `(LeanScript.Val.thunk_mk (τ := $τ) $bs)
        | false, none => `(LeanScript.Val.thunk_mk $bs)
        | true, some τ => `(LeanScript.Val.lazy_mk (τ := $τ) $bs)
        | true, none => `(LeanScript.Val.lazy_mk $bs)
      emitVal vs o (fun kr => .delay lazy τ? sc.vars body kr) p k)
  | .force lazy τ? e => (value e sc p fun v p => do
      if let .delay _ _ env body kr := v.strip then
        if kr.lv.isNone then return ← value body { vars := env } p k
      let ℓ ← match v.lv with
        | some ℓ => pure ℓ
        | none => throwError "cannot force a closed delay of unknown shape while normalising"
      let e ← `(ls_relvl% $(← render v p.core false))
      let cs ← match lazy, τ? with
        | false, some τ => `(LeanScript.Comp.thunk_force (τ := $τ) $e)
        | false, none => `(LeanScript.Comp.thunk_force $e)
        | true, some τ => `(LeanScript.Comp.lazy_force (τ := $τ) $e)
        | true, none => `(LeanScript.Comp.lazy_force $e)
      emitComp cs ℓ p k)
  | .natRec τ? n z st => (values [n, z] sc p fun vs p => do
      let nv := vs[0]!
      let zv := vs[1]!
      let (bs, o) ← mkBody 2 st sc p
      match lmeet (lmeet nv.lv zv.lv) o with
      | none =>
        let some N ← nv.natVal?
          | throwError "cannot unroll a closed `nat_rec` whose count is not known while normalising"
        unrollNat st sc N 0 zv p k
      | some ℓ =>
        let c := p.core
        let cs ← match τ? with
          | some τ => `(LeanScript.Comp.nat_rec (τ := $τ) (u₁ := .many) (u₂ := .many)
              $(← render nv c false) $(← render zv c false) $bs rfl)
          | none => `(LeanScript.Comp.nat_rec (u₁ := .many) (u₂ := .many)
              $(← render nv c false) $(← render zv c false) $bs rfl)
        emitComp cs ℓ p k)
  | .arrayFoldl a z st => (values [a, z] sc p fun vs p => do
      let av := vs[0]!
      let zv := vs[1]!
      let (bs, o) ← mkBody 2 st sc p
      match lmeet (lmeet av.lv zv.lv) o with
      | none =>
        let .array es _ := av.strip
          | throwError "cannot unroll a closed `array_foldl` over an array of unknown shape"
        unrollArray st sc es.toList zv p k
      | some ℓ =>
        let c := p.core
        emitComp (← `(LeanScript.Comp.array_foldl (u₁ := .many) (u₂ := .many)
          $(← render av c false) $(← render zv c false) $bs rfl)) ℓ p k)
  | .dataRec Δ? b ρ k? brs j e => (value e sc p fun ev p => do
      let bodies ← brs.mapM fun br => mkBody 1 br sc p
      let o := bodies.foldl (fun o (_, o') => lmeet o o') ev.lv
      let some ℓ := o
        | throwError "cannot compute a closed fold of a datatype while normalising"
      let c := p.core
      let pairs ← bodies.mapM fun (bs, _) => `(⟨_, $bs⟩)
      let pats ← (List.range pairs.size).toArray.mapM fun i => `(⟨$(quote i), _⟩)
      let brFun ← `(fun $[| $pats => $pairs]*)
      let ev' ← render ev c false
      let cs ← match Δ?, k? with
        | some Δ, none => `(LeanScript.Comp.dataRecS (Δ := $Δ) $b $ρ (fun _ => .many) $brFun $j $ev' rfl)
        | none, none => `(LeanScript.Comp.dataRecS $b $ρ (fun _ => .many) $brFun $j $ev' rfl)
        | some Δ, some kk =>
            `(LeanScript.Comp.dataBrecS (Δ := $Δ) $b $ρ $kk (fun _ => .many) $brFun $j $ev' rfl)
        | none, some kk => `(LeanScript.Comp.dataBrecS $b $ρ $kk (fun _ => .many) $brFun $j $ev' rfl)
      emitComp cs ℓ p k)
  | .letE v b => value v sc p fun vv p => bindSem vv p fun vv p => value b (sc.push vv) p k
  | .recordCases scrut n body => (value scrut sc p fun sv p =>
      takeApart sv n p fun fs p => value body (sc.pushAll fs) p k)
  | .ite ty? c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => value a sc p k
      | some _ => value b sc p k
      | none =>
        needNeutral cv "the condition of `if`"
        match ← pureSem? a sc, ← pureSem? b sc with
        | some av, some bv =>
            let r := Sem.cond cv av bv
            k (match ty? with | some ty => .ascribe r ty | none => r) p
        | _, _ => reify ty? (fun p K => branchOn cv s sc p K) p k)
  | .enumCases ty? scrut pats brs => (value scrut sc p fun sv p => do
      match enumSel pats sv with
      | some i => value brs[i]! sc p k
      | none => reify ty? (fun p K => branchOn sv s sc p K) p k)
  | .unionCases ty? scrut brs => (value scrut sc p fun sv p => do
      match unionSel (brs.map (·.1)) sv with
      | some (i, fs) => bindSems fs.toList p fun fs p => value brs[i]!.2 (sc.pushAll fs) p k
      | none => reify ty? (fun p K => branchOn sv s sc p K) p k)
  | .join ty? .. => reify ty? (fun p K => stmt s sc p K) p k
  | .jump .. => stmt s sc p .ret

/-- Unroll a closed `nat_rec` from `i` to `N`. -/
partial def unrollNat (st : Src) (sc : Scope) (N i : Nat) (acc : Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if i ≥ N then k acc p
  else
    let pred := Sem.lit (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.nat $(quote i))) (.nat i)
    value st (sc.pushAll [acc, pred]) p fun acc p => unrollNat st sc N (i + 1) acc p k

/-- Unroll a closed `array_foldl` over the elements `es`. -/
partial def unrollArray (st : Src) (sc : Scope) (es : List Sem) (acc : Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out :=
  match es with
  | [] => k acc p
  | e :: es => value st (sc.pushAll [e, acc]) p fun acc p => unrollArray st sc es acc p k

/-- Take a value apart as a record of `n` fields: its fields when it is a known record, else
    `Term.record_casesOn` of a neutral value. -/
partial def takeApart (sv : Sem) (n : Nat) (p : Pos) (k : List Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  if let some fs := recordSel n sv then
    return ← bindSems fs.toList p k
  needNeutral sv "the scrutinee of a record"
  let c := p.core
  let ns ← renderNeu sv c false
  let r ← k (unknowns n c.du c.depth) { p with core := { c with du := c.du + n } }
  return { stx := ← `(LeanScript.Term.record_casesOn (d := $(quote c.depth)) [] $ns $(r.stx)),
           lv := lmeet sv.lv r.lv }

/-- The value of a pure source tree, when it needs no computation, binding or branch (other
    than pure conditionals). -/
partial def pureSem? (s : Src) (sc : Scope) : TermElabM (Option Sem) := do
  try
    let all (ss : Array Src) : TermElabM (Option (Array Sem)) := do
      let mut out := #[]
      for s in ss do
        let some v ← pureSem? s sc | return none
        out := out.push v
      return some out
    match s with
    | .var i => return some (sc.var i)
    | .lit stx v => return some (.lit stx v)
    | .enumMk i stx => return some (.enum i stx)
    | .embed stx => return some (.embed stx)
    | .record args => return (← all args).map (.record · none)
    | .union pos ix args => return (← all args).map (.union pos ix · none)
    | .array es => return (← all es).map (.array · none)
    | .list es => return (← all es).map (.list · none)
    | .dataIn b j e => return (← pureSem? e sc).map (.dataIn b j · none)
    | .ctor f args shape => (return (← all args).map fun fs =>
        (match shape with
         | some { kind := .wrap, data? := none } => fs[0]!
         | _ => .ctor f fs shape))
    | .dataOut b j e => (do
        let some v ← pureSem? e sc | return none
        return some (← dataOutSem b j v))
    | .cond c a b | .ite _ c a b => (do
        let some cv ← pureSem? c sc | return none
        match ← iteSel cv with
        | some 0 => pureSem? a sc
        | some _ => pureSem? b sc
        | none =>
          unless cv.isNeutral do return none
          let some av ← pureSem? a sc | return none
          let some bv ← pureSem? b sc | return none
          let r := Sem.cond cv av bv
          match s with
          | .ite (some ty) .. => return some (.ascribe r ty)
          | _ => return some r)
    | .extern e args => (do
        let some fs ← all args | return none
        return some (← externSem e fs))
    | .ascribe s ty => return (← pureSem? s sc).map (.ascribe · ty)
    | _ => return none
  catch _ => return none

/-- A branch on the value `sv` (the scrutinee of `s`, not a known value), in tail position:
    the pending join points are placed in front of it, and each branch goes to `K`. -/
partial def branchOn (sv : Sem) (s : Src) (sc : Scope) (p : Pos) (K : Kont) : TermElabM Out := do
  needNeutral sv "the scrutinee of a branch"
  placeJoins p fun c => do
    let p' : Pos := { core := c }
    let ns ← renderNeu sv c false
    match s with
    | .ite _ _ a b =>
        let ta ← stmt a sc p' K
        let tb ← stmt b sc p' K
        return { stx := ← `(LeanScript.Branch.ite $ns $(ta.stx) $(tb.stx)),
                 lv := lmeet sv.lv (lmeet ta.lv tb.lv) }
    | .enumCases _ _ pats brs =>
        let outs ← brs.mapM fun b => stmt b sc p' K
        -- the branch of each constructor up to the largest one named; the default past it
        let dflt := outs[outs.size - 1]!
        let top := pats.foldl (fun m q => match q with | some i => max m (i + 1) | none => m) 0
        let listed ← (List.range top).toArray.mapM fun i => do
          let o := outs[enumSel pats (.enum (some i) default) |>.getD (outs.size - 1)]!
          `(⟨_, $(o.stx)⟩)
        let lv := outs.foldl (fun o r => lmeet o r.lv) sv.lv
        return { stx := ← `(LeanScript.Branch.enumList $ns [$listed,*] ⟨_, $(dflt.stx)⟩), lv }
    | .unionCases _ _ brs =>
        let outs ← brs.mapM fun (n, b) =>
          stmt b (sc.pushAll (unknowns n c.du c.depth)) { core := { c with du := c.du + n } } K
        let lv := outs.foldl (fun o r => lmeet o r.lv) sv.lv
        return { stx := ← `(LeanScript.Branch.union_casesOn $ns
                   $(← branchesStx c.depth (outs.map (·.stx)).toList)), lv }
    | _ => throwError "internal error of the normaliser: not a branch"

/-- Normalise `s` to a statement whose value goes to `K`. -/
partial def stmt (s : Src) (sc : Scope) (p : Pos) (K : Kont) : TermElabM Out := do
  if let .fn f := K then return ← value s sc p f
  match s with
  | .letE v b => value v sc p fun vv p => bindSem vv p fun vv p => stmt b (sc.push vv) p K
  | .recordCases scrut n body => (value scrut sc p fun sv p =>
      takeApart sv n p fun fs p => stmt body (sc.pushAll fs) p K)
  | .ite _ c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => stmt a sc p K
      | some _ => stmt b sc p K
      | none => branchOn cv s sc p K)
  | .enumCases _ scrut pats brs => (value scrut sc p fun sv p => do
      match enumSel pats sv with
      | some i => stmt brs[i]! sc p K
      | none => branchOn sv s sc p K)
  | .unionCases _ scrut brs => (value scrut sc p fun sv p => do
      match unionSel (brs.map (·.1)) sv with
      | some (i, fs) => bindSems fs.toList p fun fs p => stmt brs[i]!.2 (sc.pushAll fs) p K
      | none => branchOn sv s sc p K)
  | .join ty? body main => (do
      let id ← mkFreshId
      let saved := p.pend
      let pj : Pend := { id, ty?, k := fun v c => stmt body (sc.push v) { core := c, pend := saved } K }
      stmt main { sc with joins := id :: sc.joins } { p with pend := pj :: p.pend } K)
  | .jump j arg => (value arg sc p fun v p => do
      let some id := sc.joins[j]? | throwError "unknown join point ^{j}"
      jumpTo id v p)
  | _ => value s sc p K.apply

end

/-! ## Entry points -/

/-- The syntax of the statement (`Term`) that a source tree denotes. -/
def Src.toTerm (s : Src) : TermElabM Lean.Term := do
  `(ls_relvl% $((← stmt s {} {} .ret).stx))

/-- The syntax of the pure expression (`PExpr`) that a source tree denotes; fails when it needs
    a computation, a binding or a branch. -/
def Src.toPExpr (s : Src) : TermElabM Lean.Term := do
  let o ← value s {} {} fun v p => do
    unless p.core.du == 0 && p.core.dk == 0 do
      throwError "this term is not a pure expression: it makes a call, binds or branches"
    return { stx := ← render v p.core false, lv := v.lv }
  `(ls_relvl% $(o.stx))

/-- The syntax of the neutral expression (`Neu`) that a source tree denotes. -/
def Src.toNeu (s : Src) : TermElabM Lean.Term := do
  let o ← value s {} {} fun v p => do
    unless p.core.du == 0 && p.core.dk == 0 && v.isNeutral do
      throwError "this term is not a neutral pure expression: it makes a call, binds, \
        branches, or is a literal or a constructor"
    return { stx := ← renderNeu v p.core false, lv := v.lv }
  `(ls_relvl% $(o.stx))

/-! ## Building source trees -/

namespace Src

/-- An application of a function value. -/
def apps (f : Src) (as : Array Src) : Src := as.foldl .app f

/-- A literal `PExpr.lit p v`. -/
def lit' (p v : Lean.Term) (val : LitVal := .other) : MetaM Src := do
  return .lit (← `(LeanScript.PExpr.lit $p $v)) val

/-- The literal `true` or `false`. -/
def boolLit (b : Bool) : Src :=
  .lit (if b then Unhygienic.run `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)
    else Unhygienic.run `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)) (.bool b)

/-- Take a record of `n` fields apart. -/
def recordMk (args : Array Src) : Src := .record args

/-- A constructor of a union (`ix` a `CtorIx`, at position `pos` when known). -/
def unionMk (pos? : Option Nat) (ix : Lean.Term) (args : Array Src) : Src := .union pos? ix args

/-- An array literal. -/
def arrayMk (es : Array Src) : Src := .array es

/-- The case analysis of a union. -/
def unionCases' (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src)) : Src :=
  .unionCases ty? scrut brs

/-- A memoised delay of `e` (contents `τ`). -/
def thunkMk (τ : Lean.Term) (e : Src) : Src := .delayMk false (some τ) e

/-- The value a memoised delay holds (contents `τ`). -/
def thunkForce (τ : Lean.Term) (e : Src) : Src := .force false (some τ) e

/-- A lazy delay of `e` (contents `τ`). -/
def lazyMk (τ : Lean.Term) (e : Src) : Src := .delayMk true (some τ) e

/-- The value a lazy delay holds (contents `τ`). -/
def lazyForce (τ : Lean.Term) (e : Src) : Src := .force true (some τ) e

end Src

end LeanScript.Anf

end
