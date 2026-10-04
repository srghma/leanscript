module

public import JsTerm.Syntax.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The dump of `JsTerm` (`-JsTerm-*.txt`)

The grammar of `JsTerm.Syntax.Basic` written as text, close to the JavaScript it stands for:
the variables are shown as their de Bruijn indices (`c0` the innermost constant, `m0` the
innermost mutable variable), an operation by its name.  `leanscript` writes it next to the
`.js` file (`FILE-JsTerm-<preset>.txt`).
-/

namespace MoreJs

variable {S : JsSig}

mutual
/-- An expression, on one line (arrows break lines).  The variables are shown as their de
    Bruijn indices: `c0` the innermost constant, `m0` the innermost mutable variable (the
    binders show their hints); an operation by its name (an inlined one marked `inline:`). -/
partial def JsExpr.pretty {C M : List JsTy} {τ : JsTy} (ind : String) : JsExpr S C M τ → String
  | .cvar i => s!"c{i.index}"
  | .mvar i => s!"m{i.index}"
  | .lit l => l.shape.pretty
  | .imported op args => op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .inlined op args => "inline:" ++ op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .unreachable _ => "undefined"
  | .app f as => s!"{f.pretty ind}(" ++ ", ".intercalate (as.pretty ind) ++ ")"
  | .lam xs body => "(" ++ ", ".intercalate xs ++ ") => {\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}"
  | .record_mk fs =>
    "{ " ++ ", ".intercalate ((fs.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}") ++ " }"
  | .union_mk (id := id) ix args =>
    if args.pretty ind |>.isEmpty then
      if S.reprOf id == .smallIntNullary then toString ix.index else s!"\{ tag: {ix.index} }"
    else
    "{ " ++ ", ".intercalate (s!"tag: {ix.index}" ::
      ((args.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}")) ++ " }"
  | .enum_mk _ shift i => toString (shift + i.val)
  | .enumIndex _ e => s!"enumIndex({e.pretty ind})"
  | .enumEq a b => s!"({a.pretty ind} === {b.pretty ind})"
  | .index _ _ a i => s!"{a.pretty ind}[{i.pretty ind}]"
  | .array_mk (.generic _) ps => "[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .array_mk (.typed t) ps => t.kind.ctorName ++ ".of(" ++ ", ".intercalate (ps.pretty ind) ++ ")"
  | .list_mk ps => "list[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .cond c a b => s!"({c.pretty ind} ? {a.pretty ind} : {b.pretty ind})"
  | .listOp op args => op.runtimeName ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .fold i e => s!"fold<{JsTy.declName i}>({e.pretty ind})"
  | .unfold i e => s!"unfold<{JsTy.declName i}>({e.pretty ind})"
  | .global name => name

/-- Arguments. -/
partial def JsArgs.pretty {C M σs : List JsTy} (ind : String) : JsArgs S C M σs → List String
  | .nil => []
  | .cons a as => a.pretty ind :: as.pretty ind

/-- The parts of an array literal. -/
partial def JsParts.pretty {C M : List JsTy} {A E : JsTy} (ind : String) :
    JsParts S C M A E → List String
  | .nil => []
  | .elem e rest => e.pretty ind :: rest.pretty ind
  | .spread a rest => ("..." ++ a.pretty ind) :: rest.pretty ind

/-- A block, each statement indented by `ind` and ending in a new line. -/
partial def JsBlock.pretty {C M J : List JsTy} {k : JsEnd} (ind : String) :
    JsBlock S C M J k → String
  | .ret e => s!"{ind}return {e.pretty ind};\n"
  | .next => s!"{ind}next;\n"
  | .jump j e => s!"{ind}jump {j.index} {e.pretty ind};\n"
  | .throw msg => s!"{ind}throw new Error({msg.quote});\n"
  | .raise e => s!"{ind}throw new Error({e.pretty ind});\n"
  | .const x e rest => s!"{ind}const {x} = {e.pretty ind};\n" ++ rest.pretty ind
  | .letMut x e rest => s!"{ind}let {x} = {e.pretty ind};\n" ++ rest.pretty ind
  | .assign x e rest => s!"{ind}m{x.index} = {e.pretty ind};\n" ++ rest.pretty ind
  | .destructure e sel rest =>
    let b := sel.binds.map fun (i, x) => s!"{fieldKey i}: {x}"
    s!"{ind}const \{ {", ".intercalate b} } = {e.pretty ind};\n" ++ rest.pretty ind
  | .ite c t e =>
    s!"{ind}if ({c.pretty ind}) \{\n{t.pretty (ind ++ "  ")}{ind}} else \{\n" ++
      e.pretty (ind ++ "  ") ++ ind ++ "}\n"
  | .enumCases e arms =>
    s!"{ind}switch ({e.pretty ind}) \{\n" ++ arms.pretty ind 0 ++ ind ++ "}\n"
  | .unionCases e arms =>
    s!"{ind}switch ({e.pretty ind}.tag) \{\n" ++ arms.pretty ind 0 ++ ind ++ "}\n"
  | .join x block rest =>
    s!"{ind}join {x} \{\n" ++ block.pretty (ind ++ "  ") ++ ind ++ "}\n" ++ rest.pretty ind
  | .forRange i _ n body rest =>
    s!"{ind}for ({i} < {n.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind
  | .countdown j _ n base step rest =>
    s!"{ind}countdown ({j} from {n.pretty ind}) \{\n" ++ base.pretty (ind ++ "  ") ++
      ind ++ "} step {\n" ++ step.pretty (ind ++ "  ") ++ ind ++ "}\n" ++ rest.pretty ind
  | .forExit i _ n body done rest =>
    s!"{ind}for ({i} < {n.pretty ind}) exit \{\n" ++ body.pretty (ind ++ "  ") ++
      ind ++ "} done {\n" ++ done.pretty (ind ++ "  ") ++ ind ++ "}\n" ++ rest.pretty ind
  | .forOf x _ xs body rest =>
    s!"{ind}for ({x} of {xs.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind
  | .tick _ j base rest =>
    s!"{ind}if (m{j.index} === 0) \{\n" ++ base.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      s!"{ind}m{j.index}--;\n" ++ rest.pretty ind
  | .natCase x _ n z s =>
    s!"{ind}if ({n.pretty ind} === 0) \{\n" ++ z.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      s!"{ind}const {x} = {n.pretty ind} - 1;\n" ++ s.pretty ind
  | .funs xs defs rest =>
    let ds := (xs.zip (defs.pretty ind)).map fun (x, d) => s!"{ind}const {x} = {d};\n"
    s!"{ind}rec \{\n" ++ String.join ds ++ ind ++ "}\n" ++ rest.pretty ind

/-- The arms of a case analysis on an enum. -/
partial def JsEnumArms.pretty {C M J : List JsTy} {k : JsEnd} {n : Nat} (ind : String) (i : Nat) :
    JsEnumArms S C M J k n → String
  | .nil => ""
  | .cons b rest => s!"{ind}case {i}:\n" ++ b.pretty (ind ++ "  ") ++ rest.pretty ind (i + 1)

/-- The arms of a case analysis on a union. -/
partial def JsUnionArms.pretty {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (ind : String) (i : Nat) : JsUnionArms S C M J k cs → String
  | .nil => ""
  | .cons sel b rest =>
    let bs := sel.binds.map fun (j, x) => s!"{fieldKey j}: {x}"
    s!"{ind}case {i} \{ {", ".intercalate bs} }:\n" ++ b.pretty (ind ++ "  ") ++
      rest.pretty ind (i + 1)
end

/-- A function, for the dump (its parameters are its outermost constants). -/
def JsFun.pretty (f : JsFun) : String :=
  let ps := f.params.map fun (x, t) => s!"{x} : {t}"
  s!"// {f.leanName}\nexport const {f.name} = ({", ".intercalate ps}) : {f.ret} => \{\n" ++
    f.body.pretty "  " ++ "};\n"

/-- A module, for the dump. -/
def JsModule.pretty (m : JsModule) : String :=
  (if m.imports.isEmpty then "" else
    s!"import \{ {", ".intercalate m.imports} } from \"runtime.js\";\n\n") ++
  (if m.locals.isEmpty then "" else
    s!"// defined in the module: {", ".intercalate m.locals}\n\n") ++
  "\n".intercalate (m.funs.map JsFun.pretty)

end MoreJs

end
