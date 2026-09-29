module

public import JsTerm.Lower.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The fold of a declared datatype in JavaScript

`Comp.data_rec b ρ us branches j e` (and `Comp.data_brec … 0 …`, the same fold) becomes one local
function per member of the block, all mutually recursive (`JsBlock.funs`), and a call:

```js
const go0 = (v) => { /- member 0 -/ };
const go1 = (v) => { /- member 1 -/ };
const x = go_j(e);
```

The function of member `i` takes one layer of its value apart (`JsExpr.unfold`, nothing at run
time) and rebuilds it at the body the branch expects (`DSig.Block.recBody ρ i`): the layer is the
same, but every hole (a subvalue `c` of member `i'`) becomes the pair `{ _1: c, _2: go_i'(c) }`
of the subvalue and the answer at it.  A field is mapped by its declaration (`Fld`):

| field | mapped |
| --- | --- |
| a hole `i'` | `{ _1: c, _2: go_i'(c) }` |
| an older type, or any field without a hole | itself |
| an array of a field with holes | a loop pushing the mapped elements to a new array |
| a function (from older types) to a field with holes | `(y…) => mapped(c(y…))` |

A wrapper member maps its one field; a record member takes its fields apart
(`const { _1: a, _2: b } = v;`) and builds the mapped record; a union member is a case analysis
whose arms build the same constructor, mapped, into a join point.  The branch of member `i` then
runs on the mapped layer and returns the answer.

The recursion follows the value, as the fold does (`DSig.dataRec`): it is structural, so it ends
on every value (JavaScript's stack permitting).
-/

namespace LeanScript

variable {ks : List Nat} {n : Nat}

/-- The fields, in order. -/
def Flds.toList' {g : Nat} : Flds ks n g → List (Fld ks n g)
  | .one f => [f]
  | .cons f fs => f :: fs.toList'

/-- The fields of a constructor, each with its grounding index. -/
def BCtor.flds {g : Nat} {b : Bool} : BCtor ks n g b → List (Σ g', Fld ks n g')
  | .nullary => []
  | .fields fs => fs.toList'.map (⟨g, ·⟩)

/-- The fields of each guarded constructor. -/
def BCtors.fldLists {bs : List Bool} : BCtors ks n bs → List (List (Σ g', Fld ks n g'))
  | .two c d => [c.flds, d.flds]
  | .cons c cs => c.flds :: cs.fldLists

/-- The fields of each constructor of a union member. -/
def Alts.fldLists {g : Nat} {bs : List Bool} : Alts ks n g bs → List (List (Σ g', Fld ks n g'))
  | .two₁ c d => [c.flds, d.flds]
  | .two₂ c d => [c.flds, d.flds]
  | .here c cs => c.flds :: cs.fldLists
  | .there c u => c.flds :: u.fldLists

/-- Does the field mention a member of its block? -/
def Fld.hasHole {g : Nat} : Fld ks n g → Bool
  | .hole .. => true
  | .old _ => false
  | .array f => f.hasHole
  | .fn _ f => f.hasHole

/-- The field a function field answers, after all its (older) domains. -/
def Fld.fnCore {g : Nat} : Fld ks n g → Fld ks n g
  | .fn _ f => f.fnCore
  | f => f

/-- Member `g + i` of a block, with its grounding index. -/
def Mems.decl? {g : Nat} : Mems ks n g → Nat → Option (Σ g', Decl ks n g')
  | .nil, _ => none
  | .cons d _, 0 => some ⟨_, d⟩
  | .cons _ bs, i + 1 => bs.decl? i

end LeanScript

namespace MoreJs

variable {S : JsSig}

open LeanScript

section
variable (cfg : JsConfig) {ks ks' : List Nat} {n : Nat} (w : LeanScript.Ref ks' → LeanScript.Ref ks)
  (σs σt : Fin n → Ty ks) (go : Fin n → Ref) (R : Fin n → JsTy)

/-- The field `f` of a layer, the constant `x` (at the field's type in the source layer,
    `Fld.inst w σs f`), mapped to the field's type in the target layer (`Fld.inst w σt f`). -/
partial def mapFld {C M : List JsTy} {g : Nat} (f : Fld ks' n g) (x : Ref) :
    ConvM (JsExpr S C M (lowerTy cfg (Fld.inst w σt f))) := do
  let src := lowerTy cfg (Fld.inst w σs f)
  let tgt := lowerTy cfg (Fld.inst w σt f)
  if !f.hasHole then return (← castE (← x.get (C := C) (M := M) src) tgt)
  match f with
  | .hole i _ =>
    let T := lowerTy cfg (σs i)
    let c ← x.get (C := C) (M := M) T
    let call : JsExpr S C M (R i) := .app (← (go i).get (.fn [T] (R i))) (.cons c .nil)
    recordLit (.cons c (.cons call .nil)) tgt
  | .array f' =>
    let some ⟨E, l⟩ := JsArrayLayout.of? src | throw "internal: the layout of an array field"
    match tgt with
    | .array α =>
      -- `((a) => { let acc = []; for (const e of a) { const c = acc; acc = push(c, f'(e)); }
      --   return acc; })(x)`
      let C₁ := src :: C
      let M₁ := JsTy.array α :: M
      let elem ← mapFld (C := JsTy.array α :: E :: C₁) (M := M₁) f' (.c (C.length + 1))
      let elem ← castE elem α
      let push : JsExpr S (JsTy.array α :: E :: C₁) M₁ (.array α) :=
        .imported (.array__lean_array_push_mutable α) (.cons (.cvar .zero) (.cons elem .nil))
      let body : JsBlock S C₁ M [] (.ret (.array α)) :=
        .letMut "acc" (.array_mk (.generic α) .nil)
          (.forOf "e" l (.cvar .zero) (loopBody .zero (.ret push)) (.ret (.mvar .zero)))
      let fn : JsExpr S C M (.fn [src] (.array α)) := .lam ["a"] body
      castE (.app fn (.cons (← x.get src) .nil)) tgt
    | _ => throw "internal: the layout of an array field"
  | .fn _ _ =>
    match src, tgt with
    | .fn ds cs, .fn ds' ct =>
      if ds != ds' then throw "internal: the parameters of a function field" else
      let C₁ := pushAll ds C
      let args ← castArgs (← refArgs (C := C₁) (M := M) (paramRefs C ds)) ds
      let call : JsExpr S C₁ M cs := .app (← x.get (.fn ds cs)) args
      let core := f.fnCore
      let r ← mapFld (C := cs :: C₁) (M := M) core (.c C₁.length)
      let r ← castE r ct
      let fn : JsExpr S C M (.fn ds ct) := .lam (ds.map fun _ => "y") (.const "r" call (.ret r))
      castE fn tgt
    | _, _ => throw "internal: the layout of a function field"
  | .old _ => throw "internal: an older field with a hole"

/-- The fields `fs` of a layer (bound at `xs`), mapped. -/
partial def mapFlds {C M : List JsTy} :
    List (Σ g, Fld ks' n g) → List Ref → ConvM (Σ τs, JsArgs S C M τs)
  | [], _ => pure ⟨[], .nil⟩
  | ⟨_, f⟩ :: fs, x :: xs => do
    let e ← mapFld cfg w σs σt go R (C := C) (M := M) f x
    let ⟨_, es⟩ ← mapFlds fs xs
    return ⟨_, .cons e es⟩
  | _ :: _, [] => throw "internal: the fields of a layer"

/-- The arms of the case analysis of a union member: each takes its constructor apart and jumps
    to the join point with the same constructor, its fields mapped, at the target type `tgt`. -/
partial def mapArms {C M : List JsTy} {τ : JsTy} (tgt : JsTy) :
    (cs : List (List JsTy)) → List (List (Σ g, Fld ks' n g)) → Nat →
    ConvM (JsUnionArms S C M [tgt] (.ret τ) cs)
  | [], _, _ => pure .nil
  | fs :: cs, flds :: fls, idx => do
    let (⟨us, sel⟩, refs) := mkSel fs [] C
    let ⟨_, args⟩ ← mapFlds cfg w σs σt go R (C := pushAll us C) (M := M) flds refs
    let mk ← unionMk tgt idx args
    return .cons sel (.jump .zero mk) (← mapArms tgt cs fls (idx + 1))
  | _ :: _, [], _ => throw "internal: the constructors of a layer"

/-- The body of the function of member `i`, of declaration `d`, whose parameter (a value of the
    member) is the constant `v`: the layer mapped (`mapFld`), then `rest`, from where the mapped
    layer lives. -/
partial def recMember {C M : List JsTy} {τ : JsTy} {g : Nat} (d : Decl ks' n g) (T : JsTy)
    (v : Ref) (rest : Ref → (C' : List JsTy) → ConvM (JsBlock S C' M [] (.ret τ))) :
    ConvM (JsBlock S C M [] (.ret τ)) := do
  let src := lowerTy cfg (Decl.inst w σs d)
  let tgt := lowerTy cfg (Decl.inst w σt d)
  let ue : JsExpr S C M src ← unfoldE (← v.get T) src
  match d with
  | .wrap f (h := _) =>
    let src' := lowerTy cfg (Fld.inst w σs f)
    let ue ← castE ue src'
    let x ← mapFld cfg w σs σt go R (C := src' :: C) (M := M) f (.c C.length)
    return .const "u" ue (.const "x" x (← rest (.c (C.length + 1)) _))
  | .record f fs =>
    destructureAny ue [] fun refs C' => do
      let ⟨_, args⟩ ← mapFlds cfg w σs σt go R (C := C') (M := M) (⟨_, f⟩ :: fs.toList'.map (⟨_, ·⟩)) refs
      let x ← recordLit args tgt
      return .const "x" x (← rest (.c C'.length) (tgt :: C'))
  | .union u (h := _) =>
    match src, ue with
    | .obj id args, ue =>
      let arms ← mapArms cfg w σs σt go R (C := C) (M := M) (τ := τ) tgt (S.ctorsOf id args)
        u.fldLists 0
      let block := JsBlock.unionCases ue arms
      return .join "x" block (← rest (.c C.length) (tgt :: C))
    | _, _ => throw "internal: the layout of a union member"

end

/-- The fold of a block of `n` members: the mutually recursive functions `go_i` of the members
    (`JsBlock.funs`), then `rest`, which calls them (`go_i` lives at level `C.length + i`).
    `members` are the declarations of the members, `T i` and `R i` the types of the value and
    of the answer of member `i`, `σs` and `σt` the holes of the source and target layers, and
    `branch i` the branch of member `i`, from where its mapped layer lives. -/
def recFuns (cfg : JsConfig) {ks ks' : List Nat} {n : Nat} (w : LeanScript.Ref ks' → LeanScript.Ref ks)
    (σs σt : Fin n → Ty ks) (members : Fin n → Σ g, Decl ks' n g) (T R : Fin n → JsTy)
    {C M J : List JsTy} {k : JsEnd}
    (branch : (i : Fin n) → Ref → (C' : List JsTy) → ConvM (JsBlock S C' M [] (.ret (R i))))
    (rest : (C' : List JsTy) → ConvM (JsBlock S C' M J k)) : ConvM (JsBlock S C M J k) := do
  let is := List.finRange n
  let τs := is.map fun i => JsTy.fn [T i] (R i)
  let C' := pushAll τs C
  let go : Fin n → Ref := fun i => .c (C.length + i.val)
  let rec mkDefs : (is : List (Fin n)) → ConvM (JsArgs S C' M (is.map fun i => JsTy.fn [T i] (R i)))
    | [] => pure .nil
    | i :: is => do
      let ⟨_, d⟩ := members i
      let body ← recMember cfg w σs σt go R (C := T i :: C') (M := M) d (T i) (.c C'.length)
        (branch i)
      return .cons (.lam ["v"] body) (← mkDefs is)
  let defs ← mkDefs is
  return .funs ((List.range n).map fun i => s!"go{i}") defs (← rest C')

end MoreJs

end
