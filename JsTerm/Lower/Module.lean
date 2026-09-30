module

public import JsTerm.Syntax.Basic
public import JsTerm.Lower.LocalHelpers

@[expose] public section

set_option autoImplicit false

/-!
# A module of functions

`mkModule` puts the functions converted from `Term` (`termToJs`) together as one `.js`
module: the functions, in order, and the operations of the runtime they call (the imports),
each once, in order of first use; the operations over the cons cells of `List` are written
into the module instead of imported (`JsTerm.Lower.LocalHelpers`).  Nothing is rewritten: every optimisation is done on `Term`
(`Term.optimize`) before the conversion.
-/

namespace MoreJs

variable {S : JsSig}

/-! ## The imports -/

/-- Add a name to a list of names, once. -/
def addName (acc : Array String) (n : String) : Array String :=
  if acc.contains n then acc else acc.push n

mutual
/-- The functions of the runtime an expression calls, added to `acc`. -/
partial def JsExpr.runtimeNames {C M : List JsTy} {τ : JsTy} (acc : Array String) :
    JsExpr S C M τ → Array String
  | .imported op as => as.runtimeNames (addName acc op.runtimeName)
  | .inlined _ as => as.runtimeNames acc
  | .app f as => as.runtimeNames (f.runtimeNames acc)
  | .lam _ b => b.runtimeNames acc
  | .record_mk fs => fs.runtimeNames acc
  | .union_mk _ as => as.runtimeNames acc
  | .array_mk _ ps | .list_mk ps => ps.runtimeNames acc
  | .cond c a b => b.runtimeNames (a.runtimeNames (c.runtimeNames acc))
  | .listOp op as => as.runtimeNames (addName acc op.runtimeName)
  | .fold _ e | .unfold _ e | .enumIndex _ e => e.runtimeNames acc
  | .enumEq a b => b.runtimeNames (a.runtimeNames acc)
  | .index _ _ a i => i.runtimeNames (a.runtimeNames acc)
  | _ => acc
/-- `runtimeNames` of arguments. -/
partial def JsArgs.runtimeNames {C M σs : List JsTy} (acc : Array String) :
    JsArgs S C M σs → Array String
  | .nil => acc
  | .cons a as => as.runtimeNames (a.runtimeNames acc)
/-- `runtimeNames` of the parts of an array literal. -/
partial def JsParts.runtimeNames {C M : List JsTy} {A E : JsTy} (acc : Array String) :
    JsParts S C M A E → Array String
  | .nil => acc
  | .elem e rest => rest.runtimeNames (e.runtimeNames acc)
  | .spread a rest => rest.runtimeNames (a.runtimeNames acc)
/-- `runtimeNames` of a block. -/
partial def JsBlock.runtimeNames {C M J : List JsTy} {k : JsEnd} (acc : Array String) :
    JsBlock S C M J k → Array String
  | .ret e | .jump _ e | .raise e => e.runtimeNames acc
  | .next | .throw _ => acc
  | .const _ e rest | .letMut _ e rest | .assign _ e rest | .destructure e _ rest =>
    rest.runtimeNames (e.runtimeNames acc)
  | .ite c t e => e.runtimeNames (t.runtimeNames (c.runtimeNames acc))
  | .enumCases e arms => arms.runtimeNames (e.runtimeNames acc)
  | .unionCases e arms => arms.runtimeNames (e.runtimeNames acc)
  | .join _ b rest => rest.runtimeNames (b.runtimeNames acc)
  | .forRange _ _ n b rest =>
    rest.runtimeNames (b.runtimeNames (n.runtimeNames acc))
  | .forOf _ _ xs b rest => rest.runtimeNames (b.runtimeNames (xs.runtimeNames acc))
  | .countdown _ _ n b s rest =>
    rest.runtimeNames (s.runtimeNames (b.runtimeNames (n.runtimeNames acc)))
  | .tick _ _ b rest => rest.runtimeNames (b.runtimeNames acc)
  | .natCase _ _ n z s => s.runtimeNames (z.runtimeNames (n.runtimeNames acc))
  | .funs _ defs rest => rest.runtimeNames (defs.runtimeNames acc)
/-- `runtimeNames` of the arms of an enum's case analysis. -/
partial def JsEnumArms.runtimeNames {C M J : List JsTy} {k : JsEnd} {n : Nat}
    (acc : Array String) : JsEnumArms S C M J k n → Array String
  | .nil => acc
  | .cons b rest => rest.runtimeNames (b.runtimeNames acc)
/-- `runtimeNames` of the arms of a union's case analysis. -/
partial def JsUnionArms.runtimeNames {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (acc : Array String) : JsUnionArms S C M J k cs → Array String
  | .nil => acc
  | .cons _ b rest => rest.runtimeNames (b.runtimeNames acc)
end

/-- The functions of the runtime the functions call, each once, in order of first use. -/
def collectImports (funs : List JsFun) : List String :=
  (funs.foldl (fun acc f => f.body.runtimeNames acc) #[]).toList

/-- The module of the functions `funs`, with the imports they need; the operations the module
    defines itself (`localHelper?`) are not imported but written with it (`locals`). -/
def mkModule (config : JsConfig) (funs : List JsFun) : JsModule :=
  let all := collectImports funs
  { config, imports := all.filter (!isLocalHelper ·), locals := all.filter isLocalHelper, funs }

end MoreJs

end
