module

public import JsTerm.Syntax.Vars
public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Constants computed once per module, and the imports of a module

An expression of a function that mentions no variable of the function — a constructor
without fields (`{ tag: 0 }`), a record or union of literals (`{ tag: 1, _1: 3n }`), a
closure that captures nothing — has the same value every time it is evaluated.
`hoistConsts` moves each such expression to the top of the module, once
(`const $tag0 = { tag: 0 };`, `const $k1 = (x$3) => …;`), and every occurrence of it, in
every function of the module, refers to that constant (a `JsExpr.global` of the same type):
the value is built once instead of at every evaluation, and equal constants are shared (the
variables being de Bruijn indices, two closures that differ only in the names of their
variables are the same constant).

Only values that are never mutated are shared: records, unions and closures.  An array is
never moved, since the backend updates arrays in place (`MoreJs.inPlace`); a call of a runtime
function is not moved either (it could throw, and must only do so when the code that calls it
runs).  A record or union is moved only when its fields are literals, enums or constants moved
before it (it is evaluated when the module is loaded); a closure only reads what it refers to
when it is called.

The constants of a constructor without fields are named after their tag (`$tag0`); the others
are numbered (`$k1`, `$k2`, …).  The printer names the local variables `x$1`, `k$2`, …, and
the exported functions are named without a leading `$`, so the names cannot collide.

`JsModule.collectImports` lists the functions of the runtime a module calls: the imported
operations (by `JsOpImported.runtimeName`).
-/

namespace MoreJs

/-- The state of the pass: the constants so far, and the rendering of each (to share equal
    ones). -/
structure HoistState where
  consts : Array JsConst := #[]
  keys : Array String := #[]
  next : Nat := 1

/-- The pass. -/
abbrev HoistM := StateM HoistState

/-- Is the expression a literal, an enum or a constant (a field of a shared record)? -/
def JsExpr.isConstLeaf {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .lit _ | .global .. | .enum_mk .. => true
  | _ => false

/-- Are all the arguments literals, enums or constants? -/
def JsArgs.allConstLeaves {C M σs : List JsTy} : JsArgs C M σs → Bool
  | .nil => true
  | .cons a as => a.isConstLeaf && as.allConstLeaves

/-- Is an expression (whose parts are already rewritten) worth sharing, if it is closed? -/
def JsExpr.shareable {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .record_mk fs => fs.allConstLeaves
  | .union_mk _ as => as.allConstLeaves
  | .lam .. => true
  | _ => false

/-- The name of the constant of an expression: `$tag{i}` for a constructor without fields. -/
def constName {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) (n : Nat) : String :=
  match e with
  | .union_mk ix .nil => s!"$tag{ix.index}"
  | _ => s!"$k{n}"

/-- Share the expression `e` if it is a closed constant worth sharing. -/
def hoistNode {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : HoistM (JsExpr C M τ) := do
  if !e.shareable then return e
  let some ce := e.closed? | return e
  let st ← get
  let key := ce.pretty ""
  match st.keys.idxOf? key with
  | some i => return .global ((st.consts[i]?.map (·.name)).getD "undefined") τ
  | none =>
    let name := constName e st.next
    -- two different constants cannot get the same name (`$tag{i}` is only ever the
    -- constant `{ tag: i }`)
    set ({ consts := st.consts.push { name, ty := τ, e := ce }, keys := st.keys.push key,
           next := st.next + 1 } : HoistState)
    return .global name τ

mutual
/-- Share the constants of an expression, bottom-up. -/
partial def hoistE {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → HoistM (JsExpr C M τ)
  | .imported op as => do return .imported op (← hoistA as)
  | .inlined op as => do return .inlined op (← hoistA as)
  | .app f as => do return .app (← hoistE f) (← hoistA as)
  | .lam xs b => do hoistNode (.lam xs (← hoistB b))
  | .record_mk fs => do hoistNode (.record_mk (← hoistA fs))
  | .union_mk ix as => do hoistNode (.union_mk ix (← hoistA as))
  | .array_mk l ps => do return .array_mk l (← hoistP ps)
  | .list_mk ps => do return .list_mk (← hoistP ps)
  | .cond c a b => do return .cond (← hoistE c) (← hoistE a) (← hoistE b)
  | e => return e
/-- Share the constants of arguments. -/
partial def hoistA {C M σs : List JsTy} : JsArgs C M σs → HoistM (JsArgs C M σs)
  | .nil => pure .nil
  | .cons a as => do return .cons (← hoistE a) (← hoistA as)
/-- Share the constants of the parts of an array literal. -/
partial def hoistP {C M : List JsTy} {A E : JsTy} : JsParts C M A E → HoistM (JsParts C M A E)
  | .nil => pure .nil
  | .elem e rest => do return .elem (← hoistE e) (← hoistP rest)
  | .spread a rest => do return .spread (← hoistE a) (← hoistP rest)
/-- Share the constants of a block. -/
partial def hoistB {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → HoistM (JsBlock C M J k)
  | .ret e => do return .ret (← hoistE e)
  | .next => pure .next
  | .jump j e => do return .jump j (← hoistE e)
  | .throw msg => pure (.throw msg)
  | .const x e rest => do return .const x (← hoistE e) (← hoistB rest)
  | .letMut x e rest => do return .letMut x (← hoistE e) (← hoistB rest)
  | .assign x e rest => do return .assign x (← hoistE e) (← hoistB rest)
  | .destructure e sel rest => do return .destructure (← hoistE e) sel (← hoistB rest)
  | .ite c t e => do return .ite (← hoistE c) (← hoistB t) (← hoistB e)
  | .enumCases e arms => do return .enumCases (← hoistE e) (← hoistEnumArms arms)
  | .unionCases e arms => do return .unionCases (← hoistE e) (← hoistUnionArms arms)
  | .join x b rest => do return .join x (← hoistB b) (← hoistB rest)
  | .forRange x nt n b rest => do return .forRange x nt (← hoistE n) (← hoistB b) (← hoistB rest)
  | .lastIter x nt n b rest => do return .lastIter x nt (← hoistE n) (← hoistB b) (← hoistB rest)
  | .forOf x l xs b rest => do return .forOf x l (← hoistE xs) (← hoistB b) (← hoistB rest)
/-- Share the constants of the arms of an enum's case analysis. -/
partial def hoistEnumArms {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms C M J k n → HoistM (JsEnumArms C M J k n)
  | .nil => pure .nil
  | .cons b rest => do return .cons (← hoistB b) (← hoistEnumArms rest)
/-- Share the constants of the arms of a union's case analysis. -/
partial def hoistUnionArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → HoistM (JsUnionArms C M J k cs)
  | .nil => pure .nil
  | .cons sel b rest => do return .cons sel (← hoistB b) (← hoistUnionArms rest)
end

/-- Move the constants of the functions of a module to the top of the module (see above):
    the constants, in an order where each is defined before it is used, and the functions
    referring to them. -/
def hoistConsts (funs : List JsFun) : List JsConst × List JsFun :=
  let go : HoistM (List JsFun) := funs.mapM fun (f : JsFun) => do
    let body ← hoistB f.body
    return { f with body }
  let (funs', st) := go.run {}
  (st.consts.toList, funs')

/-! ## The imports -/

/-- Add a name to a list of names, once. -/
def addName (acc : Array String) (n : String) : Array String :=
  if acc.contains n then acc else acc.push n

mutual
/-- The functions of the runtime an expression calls, added to `acc`. -/
partial def JsExpr.runtimeNames {C M : List JsTy} {τ : JsTy} (acc : Array String) :
    JsExpr C M τ → Array String
  | .imported op as => as.runtimeNames (addName acc op.runtimeName)
  | .inlined _ as => as.runtimeNames acc
  | .app f as => as.runtimeNames (f.runtimeNames acc)
  | .lam _ b => b.runtimeNames acc
  | .record_mk fs => fs.runtimeNames acc
  | .union_mk _ as => as.runtimeNames acc
  | .array_mk _ ps | .list_mk ps => ps.runtimeNames acc
  | .cond c a b => b.runtimeNames (a.runtimeNames (c.runtimeNames acc))
  | _ => acc
/-- `runtimeNames` of arguments. -/
partial def JsArgs.runtimeNames {C M σs : List JsTy} (acc : Array String) :
    JsArgs C M σs → Array String
  | .nil => acc
  | .cons a as => as.runtimeNames (a.runtimeNames acc)
/-- `runtimeNames` of the parts of an array literal. -/
partial def JsParts.runtimeNames {C M : List JsTy} {A E : JsTy} (acc : Array String) :
    JsParts C M A E → Array String
  | .nil => acc
  | .elem e rest => rest.runtimeNames (e.runtimeNames acc)
  | .spread a rest => rest.runtimeNames (a.runtimeNames acc)
/-- `runtimeNames` of a block. -/
partial def JsBlock.runtimeNames {C M J : List JsTy} {k : JsEnd} (acc : Array String) :
    JsBlock C M J k → Array String
  | .ret e | .jump _ e => e.runtimeNames acc
  | .next | .throw _ => acc
  | .const _ e rest | .letMut _ e rest | .assign _ e rest | .destructure e _ rest =>
    rest.runtimeNames (e.runtimeNames acc)
  | .ite c t e => e.runtimeNames (t.runtimeNames (c.runtimeNames acc))
  | .enumCases e arms => arms.runtimeNames (e.runtimeNames acc)
  | .unionCases e arms => arms.runtimeNames (e.runtimeNames acc)
  | .join _ b rest => rest.runtimeNames (b.runtimeNames acc)
  | .forRange _ _ n b rest | .lastIter _ _ n b rest =>
    rest.runtimeNames (b.runtimeNames (n.runtimeNames acc))
  | .forOf _ _ xs b rest => rest.runtimeNames (b.runtimeNames (xs.runtimeNames acc))
/-- `runtimeNames` of the arms of an enum's case analysis. -/
partial def JsEnumArms.runtimeNames {C M J : List JsTy} {k : JsEnd} {n : Nat}
    (acc : Array String) : JsEnumArms C M J k n → Array String
  | .nil => acc
  | .cons b rest => rest.runtimeNames (b.runtimeNames acc)
/-- `runtimeNames` of the arms of a union's case analysis. -/
partial def JsUnionArms.runtimeNames {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (acc : Array String) : JsUnionArms C M J k cs → Array String
  | .nil => acc
  | .cons _ b rest => rest.runtimeNames (b.runtimeNames acc)
end

/-- The functions of the runtime the constants and functions call, each once, in order of
    first use. -/
def collectImports (consts : List JsConst) (funs : List JsFun) : List String :=
  let acc := consts.foldl (fun acc c => c.e.runtimeNames acc) #[]
  (funs.foldl (fun acc f => f.body.runtimeNames acc) acc).toList

/-- A module of the functions `funs`: their constants shared (`hoistConsts`) and the imports
    they need. -/
def mkModule (config : JsConfig) (funs : List JsFun) : JsModule :=
  let (consts, funs) := hoistConsts funs
  { config, imports := collectImports consts funs, consts, funs }

end MoreJs

end
