module

public import JsTerm.Syntax.Vars
public import JsTerm.Syntax.Pretty
public import JsTerm.Passes.Cleanup
public import JsTerm.Passes.InlineConsts
public import JsTerm.Passes.InPlace

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

/-- Cons cells whose elements are all literals, enums or constants, down to a tail that is one
    too (`[]` is shared as `$tag0` before its cells are looked at). -/
def JsExpr.isConstSpine {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .listOp (.nil _) _ => true
  | .listOp (.cons _) (.cons h (.cons t .nil)) => h.isConstLeaf && t.isConstSpine
  | e => e.isConstLeaf

/-- Is an expression (whose parts are already rewritten) worth sharing, if it is closed? -/
def JsExpr.shareable {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .record_mk fs => fs.allConstLeaves
  | .union_mk _ as => as.allConstLeaves
  | .lam .. => true
  | .listOp (.nil _) _ => true
  | e@(.listOp (.cons _) _) => e.isConstSpine
  | _ => false

/-- The name of the constant of an expression: `$tag{i}` for a constructor without fields
    (`[]` of cons cells is `{ tag: 0 }`, the same object as a constructor `0` without fields). -/
def constName {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) (n : Nat) : String :=
  match e with
  | .union_mk ix .nil => s!"$tag{ix.index}"
  | .listOp (.nil _) _ => "$tag0"
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
  | e@(.listOp (.cons _) _) => do
    let (e', whole) ← hoistCons e
    if whole then hoistNode e' else return e'
  | .listOp op as => do hoistNode (.listOp op (← hoistA as))
  | e => return e
/-- Share the constants of cons cells, keeping a run of constant cells in one piece: the cells
    rebuilt, and whether they are all constant down to their tail (`JsExpr.isConstSpine`: then
    the caller shares them whole, `{ tag: 1, _1: 1, _2: { tag: 1, _1: 2, _2: $tag0 } }`, rather
    than one constant per cell). -/
partial def hoistCons {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) :
    HoistM (JsExpr C M τ × Bool) :=
  match e with
  | .listOp (.cons α) (.cons h (.cons t .nil)) => do
    let h' ← hoistE h
    let (t', tailConst) ← match t with
      | .listOp (.cons _) _ => hoistCons t
      | t => do
        let t' ← hoistE t
        pure (t', t'.isConstLeaf)
    if h'.isConstLeaf && tailConst then
      return (.listOp (.cons α) (.cons h' (.cons t' .nil)), true)
    -- this cell is not constant: a constant run of cells after it is shared here
    let t'' ← if tailConst then hoistNode t' else pure t'
    return (.listOp (.cons α) (.cons h' (.cons t'' .nil)), false)
  | e => do return (← hoistE e, false)
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
  | .listOp op as =>
    as.runtimeNames (match op.runtimeName? with | some n => addName acc n | none => acc)
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

/-! ## Constants and functions that are the same function -/

mutual
/-- The module constants an expression reads when it is evaluated (not inside its closures,
    which only read them when they are called). -/
partial def JsExpr.globalsNow {C M : List JsTy} {τ : JsTy} (acc : Array String) :
    JsExpr C M τ → Array String
  | .global n _ => acc.push n
  | .imported _ as | .inlined _ as | .record_mk as | .union_mk _ as | .listOp _ as =>
    as.globalsNow acc
  | .app f as => as.globalsNow (f.globalsNow acc)
  | .array_mk _ ps | .list_mk ps => ps.globalsNow acc
  | .cond c a b => b.globalsNow (a.globalsNow (c.globalsNow acc))
  | _ => acc
/-- `globalsNow` of arguments. -/
partial def JsArgs.globalsNow {C M σs : List JsTy} (acc : Array String) :
    JsArgs C M σs → Array String
  | .nil => acc
  | .cons a as => as.globalsNow (a.globalsNow acc)
/-- `globalsNow` of the parts of an array literal. -/
partial def JsParts.globalsNow {C M : List JsTy} {A E : JsTy} (acc : Array String) :
    JsParts C M A E → Array String
  | .nil => acc
  | .elem e rest | .spread e rest => rest.globalsNow (e.globalsNow acc)
end

/-- The module constants renamed as `ren` says (in a whole block or expression). -/
def renameGlobalsRw (ren : String → Option String) : JsExprRewrite :=
  ⟨fun _ _ τ e => match e with
    | .global n _ => match ren n with
      | some n' => .global n' τ
      | none => e
    | e => e⟩

/-- The type of a function. -/
def JsFun.ty (f : JsFun) : JsTy := .fn (f.params.map (·.2)) f.ret

/-- The dump of the body of a function (its parameters are its outermost constants, their
    names left out): two functions of the same type with the same key are the same function. -/
def JsFun.key (f : JsFun) : String := f.body.pretty "  "

/-- The dump of the body of a closure that is a module constant (its parameters' hints left
    out), as `JsFun.key`. -/
def JsConst.key? (c : JsConst) : Option String :=
  match c.ty, c.e with
  | _, .lam _ body => some (body.pretty "  ")
  | _, _ => none

/-- Sharing the functions of a module:

* a module constant that is a closure equal to an exported function (`const $k3 = (x$1, x$2)
  => …;`, the copy of a function a call inlined) is dropped, and the function is read instead
  (`hyperBase`).  This is only done when no module constant reads it when the module is
  loaded (only closures do, when they are called), so that the function is never read before
  it is defined;
* an exported function equal to one before it is written as that one
  (`export const test1 = appendR;`, `JsFun.alias`), and one that only passes its parameters
  on to a function of the runtime as that function. -/
def JsModule.shareFuns (m : JsModule) : JsModule :=
  let funs := m.funs.toArray
  let readNow := m.consts.foldl (fun acc c => c.e.globalsNow acc) #[]
  let dropped : Array (String × String) := m.consts.foldl (init := #[]) fun acc c =>
    match c.key? with
    | none => acc
    | some k =>
      if readNow.contains c.name then acc else
      match funs.find? fun f => f.alias.isNone && f.ty == c.ty && f.key == k with
      | some f => acc.push (c.name, f.name)
      | none => acc
  let ren : String → Option String := fun n => (dropped.find? (·.1 == n)).map (·.2)
  let consts := (m.consts.filter fun c => (ren c.name).isNone).map fun c =>
    { c with e := c.e.mapBU (renameGlobalsRw ren) .id }
  let funs := funs.map fun f => { f with body := f.body.mapBU (renameGlobalsRw ren) .id }
  -- equal functions: the first one of each body is kept
  let funs := (List.range funs.size).foldl (init := funs) fun fs i =>
    match fs[i]? with
    | none => fs
    | some f =>
      let k := f.key
      match (fs.extract 0 i).find? fun g => g.alias.isNone && g.ty == f.ty && g.key == k with
      | some g => fs.set! i { f with alias := some g.name }
      | none => fs
  -- a function that only passes its parameters, in order, to a function of the runtime is
  -- that function (`export const add = (a, b) => uint8__lean_uint8_add(a, b);` is
  -- `export const add = uint8__lean_uint8_add;`)
  let funs := funs.map fun f =>
    if f.alias.isSome then f else
    match f.body with
    | .ret (.imported op args) =>
      if op.extraArgs.isEmpty && args.areFields f.params.length 0 then
        { f with alias := some op.runtimeName }
      else f
    | _ => f
  -- (the body of a function written as another one is kept: it calls what that one calls)
  { m with consts, funs := funs.toList, imports := collectImports consts funs.toList }

/-- A module of the functions `funs`: their constants shared (`hoistConsts`), the copies of
    the constants this leaves propagated (`cleanup`), the constants used once right away
    inlined (`inlineOnce`), the constants and functions that are the same function shared
    (`JsModule.shareFuns`), and the imports they need. -/
def mkModule (config : JsConfig) (funs : List JsFun) : JsModule :=
  let (consts, funs) := hoistConsts funs
  -- hoisting leaves copies of the module constants (`const k$1 = $k1;`)
  let consts := consts.map fun c =>
    { c with e := inlineOnceExpr ((cleanupExpr c.e).mapBU .id ⟨fun _ _ _ _ b => peepholeNode b⟩) }
  let funs := funs.map fun f => { f with body := inlineOnce (peephole (cleanup f.body)) }
  -- the calls of closures of the module inlined (`inlineConsts`); an array a body inlined
  -- builds may now be updated in place (`inPlace`: the module constants are never arrays)
  let before := funs.map JsFun.key
  let isFun : JsConst → Bool := fun c => match c.key? with
    | some k => funs.any fun f => f.ty == c.ty && f.key == k
    | none => false
  let (consts, funs') := inlineConsts isFun consts funs
  let funs := (funs'.zip before).map fun (f, k) =>
    if f.key == k then f else { f with body := inlineOnce (peephole (cleanup (inPlace f.body))) }
  -- conditionals and arithmetic with a unit simplified, and the copies this leaves propagated
  let funs := funs.map fun f => { f with body := inlineOnce (cleanup (simplifyExprs f.body)) }
  JsModule.shareFuns { config, imports := collectImports consts funs, consts, funs }

end MoreJs

end
