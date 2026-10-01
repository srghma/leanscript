module

public import LeanScript.TermElab.Anf.Sem

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Rendering semantic values, and values known while normalising
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

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

/-- The name of the entry of the catalogue an extern `e` is (`lean_array_append` of
    `LeanInitPureExtern.lean_array_append _`). -/
def entryName (e : Lean.Term) : String :=
  let f := if e.raw.isIdent then e.raw else e.raw[0]
  if f.isIdent then f.getId.getString! else ""

/-- Is the extern `e` (`LeanInitPureExtern.lean_panic_fn _`) the one of `panicCore`? -/
def isPanicEntry (e : Lean.Term) : Bool :=
  entryName e == "lean_panic_fn"

/-- Is the extern `e` one of `Array.emptyWithCapacity` / `Array.mkEmpty`? -/
def isEmptyArrayEntry (e : Lean.Term) : Bool :=
  (entryName e).startsWith "lean_mk_empty_array_with_capacity"

/-- A call of an extern building a sequence from closed sequence literals, as the literal it
    computes: `#[a] ++ #[b]` is `#[a, b]`, `#[a].push b` is `#[a, b]`, and the same for lists
    (`[a] ++ [b]`, `b :: [a]` is no extern).  Its result is no leaf, so it cannot be a
    `PExpr.externLit`, and with no open argument it cannot be a call (`Neu.extern`) either. -/
def seqLitSem? (e : Lean.Term) (fs : Array Sem) : Option Sem :=
  match entryName e, fs.toList.map Sem.strip with
  | "lean_array_append", [.array xs _, .array ys _] => some (.array (xs ++ ys) none)
  | "lean_array_push", [.array xs _, _] => some (.array (xs.push fs[1]!) none)
  | "lean_list_append", [.list xs _, .list ys _] => some (.list (xs ++ ys) none)
  | _, _ => none

/-- A call of an extern: computed when every argument is closed (`PExpr.externLit`), else a
    neutral call. -/
def externSem (e : Lean.Term) (fs : Array Sem) : TermElabM Sem := do
  if (Sem.lvAll fs.toList).isNone then
    if let some s := seqLitSem? e fs then return s
    -- `panicCore d msg` on a closed message is its value `d` (the language has no call on
    -- closed arguments; the JavaScript of an open one throws)
    if isPanicEntry e && fs.size == 2 then return fs[0]!
    -- an empty array of a closed capacity (`∅`, `Array.empty`, `Array.emptyWithCapacity n`) is
    -- the array literal `#[]` (the capacity is not observable); its result is no leaf, so it is
    -- no `PExpr.externLit`
    if isEmptyArrayEntry e then return .array #[] none
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

end LeanScript.Anf

end
