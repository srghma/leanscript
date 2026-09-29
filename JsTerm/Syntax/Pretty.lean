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

mutual
/-- An expression, on one line (arrows break lines).  The variables are shown as their de
    Bruijn indices: `c0` the innermost constant, `m0` the innermost mutable variable (the
    binders show their hints); an operation by its name (an inlined one marked `inline:`). -/
partial def JsExpr.pretty {C M : List JsTy} {τ : JsTy} (ind : String) : JsExpr C M τ → String
  | .cvar i => s!"c{i.index}"
  | .mvar i => s!"m{i.index}"
  | .global x _ => x
  | .lit l => l.shape.pretty
  | .imported op args => op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .inlined op args => "inline:" ++ op.name ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
  | .unreachable _ => "undefined"
  | .app f as => s!"{f.pretty ind}(" ++ ", ".intercalate (as.pretty ind) ++ ")"
  | .lam xs body => "(" ++ ", ".intercalate xs ++ ") => {\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}"
  | .record_mk fs =>
    "{ " ++ ", ".intercalate ((fs.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}") ++ " }"
  | .union_mk ix args =>
    "{ " ++ ", ".intercalate (s!"tag: {ix.index}" ::
      ((args.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}")) ++ " }"
  | .enum_mk _ shift i => toString (shift + i.val)
  | .array_mk (.generic _) ps => "[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .array_mk (.typed t) ps => t.kind.ctorName ++ ".of(" ++ ", ".intercalate (ps.pretty ind) ++ ")"
  | .list_mk ps => "list[" ++ ", ".intercalate (ps.pretty ind) ++ "]"
  | .cond c a b => s!"({c.pretty ind} ? {a.pretty ind} : {b.pretty ind})"
  | .listOp op args =>
    match op.runtimeName? with
    | some f => f ++ "(" ++ ", ".intercalate (args.pretty ind) ++ ")"
    | none =>
      -- the same text as the constructor of a union (`{ tag: 0 }`), which it is at run time
      "{ " ++ ", ".intercalate (s!"tag: {args.pretty ind |>.length |> min 1}" ::
        ((args.pretty ind).zipIdx.map fun (e, i) => s!"{fieldKey i}: {e}")) ++ " }"

/-- Arguments. -/
partial def JsArgs.pretty {C M σs : List JsTy} (ind : String) : JsArgs C M σs → List String
  | .nil => []
  | .cons a as => a.pretty ind :: as.pretty ind

/-- The parts of an array literal. -/
partial def JsParts.pretty {C M : List JsTy} {A E : JsTy} (ind : String) :
    JsParts C M A E → List String
  | .nil => []
  | .elem e rest => e.pretty ind :: rest.pretty ind
  | .spread a rest => ("..." ++ a.pretty ind) :: rest.pretty ind

/-- A block, each statement indented by `ind` and ending in a new line. -/
partial def JsBlock.pretty {C M J : List JsTy} {k : JsEnd} (ind : String) :
    JsBlock C M J k → String
  | .ret e => s!"{ind}return {e.pretty ind};\n"
  | .next => s!"{ind}next;\n"
  | .jump j e => s!"{ind}jump {j.index} {e.pretty ind};\n"
  | .throw msg => s!"{ind}throw new Error({msg.quote});\n"
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
  | .lastIter i _ n body rest =>
    s!"{ind}last ({i} < {n.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind
  | .forOf x _ xs body rest =>
    s!"{ind}for ({x} of {xs.pretty ind}) \{\n" ++ body.pretty (ind ++ "  ") ++ ind ++ "}\n" ++
      rest.pretty ind

/-- The arms of a case analysis on an enum. -/
partial def JsEnumArms.pretty {C M J : List JsTy} {k : JsEnd} {n : Nat} (ind : String) (i : Nat) :
    JsEnumArms C M J k n → String
  | .nil => ""
  | .cons b rest => s!"{ind}case {i}:\n" ++ b.pretty (ind ++ "  ") ++ rest.pretty ind (i + 1)

/-- The arms of a case analysis on a union. -/
partial def JsUnionArms.pretty {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (ind : String) (i : Nat) : JsUnionArms C M J k cs → String
  | .nil => ""
  | .cons sel b rest =>
    let bs := sel.binds.map fun (j, x) => s!"{fieldKey j}: {x}"
    s!"{ind}case {i} \{ {", ".intercalate bs} }:\n" ++ b.pretty (ind ++ "  ") ++
      rest.pretty ind (i + 1)
end

/-- A function, for the dump (its parameters are its outermost constants). -/
def JsFun.pretty (f : JsFun) : String :=
  if let some g := f.alias then s!"// {f.leanName}\nexport const {f.name} = {g};\n" else
  let ps := f.params.map fun (x, t) => s!"{x} : {t}"
  s!"// {f.leanName}\nexport const {f.name} = ({", ".intercalate ps}) : {f.ret} => \{\n" ++
    f.body.pretty "  " ++ "};\n"

/-- A module, for the dump. -/
def JsModule.pretty (m : JsModule) : String :=
  (if m.imports.isEmpty then "" else
    s!"import \{ {", ".intercalate m.imports} } from \"runtime.js\";\n\n") ++
  String.join (m.consts.map fun c => s!"const {c.name} : {c.ty} = {c.e.pretty ""};\n") ++
  (if m.consts.isEmpty then "" else "\n") ++
  "\n".intercalate (m.funs.map JsFun.pretty)

end MoreJs

end
