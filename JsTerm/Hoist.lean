module

public import JsTerm.Vars

@[expose] public section

set_option autoImplicit false

/-!
# Constants computed once per module

An expression of a function that depends on no variable of the function — a constructor
without fields (`{ tag: 0 }`), a record or union of constants (`{ tag: 1, _1: 3n }`), a
closure that captures nothing, an arithmetic expression of literals — has the same value
every time it is evaluated.  `hoistConsts` moves each such expression to the top of the
module, once (`const $tag0 = { tag: 0 };`, `const $k1 = (x$3) => x$3 + 1n;`), and every
occurrence of it, in every function of the module, refers to that constant (a
`JsExpr.global`): the value is built once instead of at every evaluation, and equal constants
are shared (the variables being de Bruijn indices, two closures that differ only in the names
of their variables are the same constant).

Only values that are never mutated are shared: records, unions and closures.  An array
(literal, typed or `new`) is never moved, since the backend updates arrays in place
(`MoreJs.inPlaceStmts`); a call of a runtime function is not moved either (it could throw,
and must only do so when the code that calls it runs).  A constant refers to no local
variable.  A closure may refer to the imports, the other constants and the exported functions
of the module (it only reads them when it is called); any other constant only to the imports,
the globals of JavaScript and the constants defined before it (it is evaluated when the module
is loaded).

The constants of a constructor without fields are named after their tag (`$tag0`); the others
are numbered (`$k1`, `$k2`, …).  The printer names the local variables `x$1`, `k$2`, …, and
the exported functions are named without a leading `$`, so the names cannot collide.
-/

namespace MoreJs

/-- The globals of JavaScript a constant may refer to. -/
def jsGlobals : List String :=
  ["undefined", "Infinity", "NaN", "Math", "Number", "BigInt", "String", "Array", "Object",
   "Error", "RangeError", "TextEncoder", "Uint8Array", "Uint16Array", "Uint32Array",
   "Int8Array", "Int16Array", "Int32Array", "Float32Array", "Float64Array", "BigUint64Array",
   "BigInt64Array"]

/-- Can the binary operator throw (a `BigInt` division or remainder by zero, a shift too
    large for a `BigInt`)? -/
def JsBinOp.mayThrow : JsBinOp → Bool
  | .bigint .div | .bigint .mod | .bigint .shl => true
  | _ => false

mutual
/-- The globals an expression refers to (inside its closures too). -/
partial def JsExpr.globals : JsExpr → List String
  | .global y => [y]
  | .cvar _ | .mvar _ | .lit _ => []
  | .arrow _ b => b.flatMap JsStmt.globals
  | .bin _ a b | .at a b => a.globals ++ b.globals
  | .un _ a | .index a _ | .member a _ | .spread a => a.globals
  | .call f as | .new f as => f.globals ++ as.flatMap JsExpr.globals
  | .helper _ as | .array as | .typedArray _ as => as.flatMap JsExpr.globals
  | .cond c a b => c.globals ++ a.globals ++ b.globals
  | .object fs => fs.flatMap (·.2.globals)
/-- The globals a statement refers to (inside its blocks and closures too). -/
partial def JsStmt.globals : JsStmt → List String
  | .const _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e | .expr e
  | .assign _ e => e.globals
  | .letMut _ e => (e.map JsExpr.globals).getD []
  | .setMember o _ e => o.globals ++ e.globals
  | .setAt o i e => o.globals ++ i.globals ++ e.globals
  | .while c b | .forRange _ _ c b | .forOf _ c b =>
    c.globals ++ b.flatMap JsStmt.globals
  | .ite c t e => c.globals ++ t.flatMap JsStmt.globals ++ e.flatMap JsStmt.globals
  | .throw _ _ => []
  | .join _ b => b.flatMap JsStmt.globals
end

/-- The state of the pass: the constants so far, and the rendering of each (to share equal
    ones). -/
structure HoistState where
  consts : Array (String × JsExpr) := #[]
  keys : Array String := #[]
  next : Nat := 1

/-- The pass, over a module whose imports are `imports` and exported functions `exports`. -/
abbrev HoistM := ReaderT (List String × List String) (StateM HoistState)

/-- Is an expression (whose parts are already rewritten) a constant, and worth sharing? -/
def constKind (imports exports hoisted : List String) (e : JsExpr) : Option Bool :=
  let eager (y : String) := imports.contains y || hoisted.contains y || jsGlobals.contains y
  let isConst : JsExpr → Bool
    | .lit _ => true
    | .global y => eager y
    | _ => false
  match e with
  | .object fs => if fs.all (isConst ·.2) then some true else none
  | .arrow _ _ =>
    if e.isClosed && e.globals.all fun y => eager y || exports.contains y then some true
    else none
  | .bin op a b => if !op.mayThrow && isConst a && isConst b then some false else none
  | .cond c a b => if isConst c && isConst a && isConst b then some false else none
  | _ => none

/-- The name of the constant of an expression: `$tag{i}` for a constructor without fields. -/
def constName (e : JsExpr) (n : Nat) : String :=
  match e with
  | .object [("tag", .lit (.number f))] =>
    match floatSmallInt? f with
    | some i => if i ≥ 0 then s!"$tag{i}" else s!"$k{n}"
    | none => s!"$k{n}"
  | _ => s!"$k{n}"

/-- Share the expression `e` if it is a constant worth sharing. -/
def hoistNode (e : JsExpr) : HoistM JsExpr := do
  let (imports, exports) ← read
  let st ← get
  let hoisted := st.consts.toList.map (·.1)
  match constKind imports exports hoisted e with
  | none => return e
  | some _ =>
    let key := e.pretty ""
    match st.keys.idxOf? key with
    | some i => return .global st.consts[i]!.1
    | none =>
      let name := constName e st.next
      -- two different constants cannot get the same name (`$tag{i}` is only ever the
      -- constant `{ tag: i }`)
      set ({ consts := st.consts.push (name, e), keys := st.keys.push key, next := st.next + 1 } :
        HoistState)
      return .global name

mutual
/-- Share the constants of an expression, bottom-up. -/
partial def hoistE : JsExpr → HoistM JsExpr
  | .bin op a b => do hoistNode (.bin op (← hoistE a) (← hoistE b))
  | .un op a => do return .un op (← hoistE a)
  | .helper n as => do return .helper n (← as.mapM hoistE)
  | .call f as => do return .call (← hoistE f) (← as.mapM hoistE)
  | .arrow ps b => do hoistNode (.arrow ps (← b.mapM hoistS))
  | .array es => do return .array (← es.mapM hoistE)
  | .typedArray c es => do return .typedArray c (← es.mapM hoistE)
  | .index e i => do return .index (← hoistE e) i
  | .member e m => do return .member (← hoistE e) m
  | .cond c a b => do hoistNode (.cond (← hoistE c) (← hoistE a) (← hoistE b))
  | .object fs => do hoistNode (.object (← fs.mapM fun (k, e) => do return (k, ← hoistE e)))
  | .at e i => do return .at (← hoistE e) (← hoistE i)
  | .new c as => do return .new (← hoistE c) (← as.mapM hoistE)
  | .spread e => do return .spread (← hoistE e)
  | e => return e
/-- Share the constants of a statement. -/
partial def hoistS : JsStmt → HoistM JsStmt
  | .const x e => do return .const x (← hoistE e)
  | .letMut x e => do return .letMut x (← e.mapM hoistE)
  | .assign x e => do return .assign x (← hoistE e)
  | .destructure xs e => do return .destructure xs (← hoistE e)
  | .destructureObj xs e => do return .destructureObj xs (← hoistE e)
  | .setMember o m e => do return .setMember (← hoistE o) m (← hoistE e)
  | .setAt o i e => do return .setAt (← hoistE o) (← hoistE i) (← hoistE e)
  | .expr e => do return .expr (← hoistE e)
  | .while c b => do return .while (← hoistE c) (← b.mapM hoistS)
  | .ret e => do return .ret (← hoistE e)
  | .ite c t e => do return .ite (← hoistE c) (← t.mapM hoistS) (← e.mapM hoistS)
  | .forRange i big n b => do return .forRange i big (← hoistE n) (← b.mapM hoistS)
  | .forOf x xs b => do return .forOf x (← hoistE xs) (← b.mapM hoistS)
  | .throw k m => return .throw k m
  | .join x b => do return .join x (← b.mapM hoistS)
  | .jump j e => do return .jump j (← hoistE e)
end

/-- Move the constants of the functions of a module to the top of the module (see above):
    the constants, in an order where each is defined before it is used, and the functions
    referring to them.  `imports` are the names the module imports. -/
def hoistConsts (imports : List String) (funs : List JsFun) :
    List (String × JsExpr) × List JsFun :=
  let exports := funs.map (·.name)
  let go : HoistM (List JsFun) := funs.mapM fun (f : JsFun) => do
    let body ← f.body.mapM hoistS
    return { f with body }
  let (funs', st) := (go.run (imports, exports)).run {}
  (st.consts.toList, funs')

end MoreJs

end
