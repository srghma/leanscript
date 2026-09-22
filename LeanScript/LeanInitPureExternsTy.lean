module

public import LeanScript.Den
public import LeanScript.LeanInitPureExterns

@[expose] public section

namespace LeanScript

/-!
# The catalogue of pure externs, at the type language

`LeanScript.LeanInitPureExterns` lists the pure `@[extern]` functions of the Lean runtime
as one inductive family indexed by *some* type language `MyTy`, with the type formers it
needs taken as parameters: `option`, `list`, `prod`, and `ordering`.  This module says
what those are when the type language is `LeanScript.Ty`, the one a compiled program is
typed by, so the question "what comes to `ordering`?" is answered here in code and
checked by the elaborator:

| parameter  | at `Ty`                                                    |
| :--------- | :--------------------------------------------------------- |
| `denote`   | `Ty.den`, the values of a type                              |
| `option`   | `Ty.option`, the non-recursive tagged union `none \| some`   |
| `list`     | `Ty.list`, the recursive tagged union `nil \| cons`          |
| `prod`     | `Ty.prod`, the record of two fields                         |
| `ordering` | `Ty.ordering`, the enum `.enum ⟨0, -1⟩` — `lt`, `eq`, `gt`  |

`name` is not a parameter of the catalogue: no entry of it answers with a `Lean.Name`.
`Ty.name` is in `LeanScript.Ty` all the same — it is the recursive tagged union
`anonymous | str | num` caching its own `hash` — and the elaborator produces it for
`Lean.Name` without being told to, since it reads the computed fields off the
declaration (`LeanScript.Term.Elab.computedFieldPrimTys`).

`LeanScript.LeanInitPureExternsEval` instantiates the same catalogue at `ETy`, the
*evaluation* type language, which is where each entry is given the Lean function it
stands for.
-/

/-- A terminal type is a type. -/
instance : Coe LeanPrimTy Ty := ⟨.prim⟩
/-- A type former over terminal types is a type. -/
instance : Coe (LeanPrimTyCovariant LeanPrimTy) Ty :=
  ⟨fun s => .primCovariant (s.map Ty.prim)⟩
/-- A type former over types is a type. -/
instance : Coe (LeanPrimTyCovariant Ty) Ty := ⟨.primCovariant⟩

/-- The catalogue of the pure externs, indexed by the `Ty` each answers with. -/
abbrev TyExtern : Ty → Type :=
  LeanInitPureExtern Ty.den Ty.option Ty.list Ty.prod Ty.ordering

/-- `ordering` is the three-constructor enum whose constructors print as `-1`, `0` and
    `1`: what `#leanjs_ty_for Ordering` answers. -/
theorem ordering_eq : Ty.ordering = .enum ⟨0, -1⟩ := rfl

/-- `list α` is the recursive tagged union with a field-less `nil` and a `cons` carrying
    the head and, as an occurrence of the declaration itself, the tail. -/
theorem list_schema (α : Ty) :
    (Ty.list α) = Ty.recTaggedUnion ⟨.skip (.here ⟨Ty.toRTy α, [.self]⟩ []), Ty.list_wf α⟩ :=
  rfl

/-- An entry that answers with a comparison is typed by `Ty.ordering`, so the parameter
    `ordering` of the catalogue really is met by the enum above. -/
theorem ordering_is_the_answer_of_string_compare : Nonempty (TyExtern Ty.ordering) :=
  ⟨.lean_string_compare "" ""⟩

/-- An entry that answers with a list of characters is typed by `Ty.list Ty.char`. -/
theorem list_is_the_answer_of_string_data : Nonempty (TyExtern (Ty.list Ty.char)) :=
  ⟨.lean_string_data__String_data ""⟩

end LeanScript

end
