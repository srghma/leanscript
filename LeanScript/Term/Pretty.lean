module

public import LeanScript.Term.Term
public import LeanScript.Term.ExternName

@[expose] public section

set_option autoImplicit false

/-!
# A pretty printer for normal-form terms

`Term.pretty t` renders a statement as text, with its de Bruijn variables named: unknowns
`x1, x2, …`, known values `k1, …`, join points `j1, …`, the fields of a case analysis
`f1, …`.  Every binder shows its type and its usage (`[1]`, `[ω]`, `[0]`).  This is the
format of the `-Term-unoptimized.txt` and `-Term-optimized.txt` files the `leanscript` tool
writes.

```
val k1 [1] := fun x2 : Nat => (closed)
  let x3 [ω] : Nat := share lean_nat_add(x2, 1)
  ret x3
ret k1
```
-/

namespace LeanScript

/-! ## Types -/

mutual
/-- A type, as text. -/
partial def Ty.pretty {ks : List Nat} {d : Bool} : Ty ks d → String
  | .prim p => match p with
    | .nat => "Nat" | .int => "Int" | .bool => "Bool" | .string => "String" | .char => "Char"
    | .uint8 => "UInt8" | .uint16 => "UInt16" | .uint32 => "UInt32" | .uint64 => "UInt64"
    | .int8 => "Int8" | .int16 => "Int16" | .int32 => "Int32" | .int64 => "Int64"
    | .float => "Float" | .float32 => "Float32"
    | .bitvec n _ => s!"(BitVec {n})"
    | p => p.pretty
  | .fn a b => s!"({a.pretty} → {b.pretty})"
  | .array t => s!"(Array {t.pretty})"
  | .list t => s!"(List {t.pretty})"
  | .enum s => s!"(enum {s.nOfConstructors} @{s.shift})"
  | .record t fs => "(" ++ " × ".intercalate (t.pretty :: Fields.prettyList fs) ++ ")"
  | .union cs (h := _) => "(" ++ " | ".intercalate (Ctors.prettyList cs) ++ ")"
  | .data r => s!"(data {repr r})"
  | .thunk t => s!"(Thunk {t.pretty})"
  | .lazy t => s!"(Unit → {t.pretty})"
/-- The fields of a record, as text. -/
partial def Fields.prettyList {ks : List Nat} : Fields ks → List String
  | .one t => [t.pretty]
  | .cons t fs => t.pretty :: Fields.prettyList fs
/-- The constructors of a union, as text. -/
partial def Ctors.prettyList {ks : List Nat} {bs : List Bool} : Ctors ks bs → List String
  | .two a b => [Ctor.prettyOne a, Ctor.prettyOne b]
  | .cons c cs => Ctor.prettyOne c :: Ctors.prettyList cs
/-- A constructor, as text. -/
partial def Ctor.prettyOne {ks : List Nat} {b : Bool} : Ctor ks b → String
  | .nullary => "•"
  | .fields fs => "[" ++ ", ".intercalate (Fields.prettyList fs) ++ "]"
end

/-- A literal, as text. -/
def LeanPrimTy.prettyLit : (p : LeanPrimTy) → p.denote → String
  | .bool, b => toString b
  | .nat, n => toString n
  | .int, n => toString n
  | .bitvec w _, v => s!"{v.toNat}#{w}"
  | .uint8, v => toString v
  | .uint16, v => toString v
  | .uint32, v => toString v
  | .uint64, v => toString v
  | .int8, v => toString v
  | .int16, v => toString v
  | .int32, v => toString v
  | .int64, v => toString v
  | .char, c => repr c |>.pretty
  | .string, s => s.quote
  | .stringPos _ _, p => s!"⟨{p.offset.byteIdx}⟩"
  | .stringPosRaw, p => s!"⟨{p.byteIdx}⟩"
  | .substringRaw, s => s!"{s.str.quote}[{s.startPos.byteIdx}:{s.stopPos.byteIdx}]"
  | .stringSlice, s =>
    s!"{s.str.quote}[{s.startInclusive.offset.byteIdx}:{s.endExclusive.offset.byteIdx}]"
  | .float, f => toString f.toFloat
  | .float32, f => toString f.toFloat32
  | .floatModel, _ => "<Float.Model>"
  | .float32Model, _ => "<Float32.Model>"

/-! ## Terms -/

namespace TermPretty

/-- The names of the three contexts, innermost first. -/
structure Names where
  u : List String := []
  k : List String := []
  j : List String := []

/-- The printer's monad: a counter for fresh names. -/
abbrev PM := StateM Nat

/-- A fresh name. -/
def fresh (pfx : String) : PM String :=
  modifyGet fun n => (s!"{pfx}{n + 1}", n + 1)

/-- A usage, as text. -/
def use1 : Usage1ω → String
  | .one => "[1]" | .many => "[ω]"

/-- A usage of a pattern binder, as text. -/
def use01 : Usage01ω → String
  | .zero => "[0]" | .one => "[1]" | .many => "[ω]"

/-- The position of a constructor in a union. -/
def ctorIx {ks : List Nat} : {bs : List Bool} → {b : Bool} → {cs : Ctors ks bs} →
    {c : Ctor ks b} → CtorIx cs c → Nat
  | _, _, _, _, .two₁ => 0
  | _, _, _, _, .two₂ => 1
  | _, _, _, _, .head => 0
  | _, _, _, _, .tail ix => ctorIx ix + 1

variable {ks : List Nat} {Δ : DSig ks}

/-- Names for the fields a pattern binds. -/
def fields (tys : List (Ty ks)) (us : List Usage01ω) : PM (List String × String) := do
  let mut names := #[]
  let mut shown := #[]
  for i in [0:tys.length] do
    let x ← fresh "f"
    names := names.push x
    let u := match us[i]? with
      | some u => use01 u
      | none => "[ω]"
    shown := shown.push s!"{x} {u} : {tys[i]!.pretty}"
  return (names.toList, ", ".intercalate shown.toList)

mutual
/-- A neutral expression. -/
partial def neu {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ Γ τ ℓ → Names → PM String
  | .var x, n => pure (n.u.getD x.index "?")
  | .data_out _ j e, n => do return s!"out#{j.val}({← neu e n})"
  | .cond c a b, n => do return s!"cond({← neu c n}, {← pexpr a n}, {← pexpr b n})"
  | .extern e args _, n => do return s!"{externName e}({", ".intercalate (← argList args n)})"

/-- A pure expression. -/
partial def pexpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    PExpr Δ Φ Γ τ o → Names → PM String
  | .neu e, n => neu e n
  | .kvar k, n => pure (n.k.getD k.index "?")
  | .lit p v, _ => pure (p.prettyLit v)
  | .enum_mk _ i, _ => pure s!"enum#{i.val}"
  | .record_mk args, n => do return "⟨" ++ ", ".intercalate (← argList args n) ++ "⟩"
  | .union_mk ix args, n => do
    return s!"ctor#{ctorIx ix}(" ++ ", ".intercalate (← argList args n) ++ ")"
  | .array_mk es, n => do return "#[" ++ ", ".intercalate (← elemList es n) ++ "]"
  | .list_mk es, n => do return "[" ++ ", ".intercalate (← elemList es n) ++ "]"
  | .data_in _ j e, n => do return s!"in#{j.val}({← pexpr e n})"

/-- Arguments. -/
partial def argList {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} :
    Args Δ Φ Γ σs o → Names → PM (List String)
  | .nil, _ => pure []
  | .cons a as, n => return (← pexpr a n) :: (← argList as n)

/-- Elements. -/
partial def elemList {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} :
    Elems Δ Φ Γ t o → Names → PM (List String)
  | .nil, _ => pure []
  | .cons a as, n => return (← pexpr a n) :: (← elemList as n)

/-- A value of known shape, at indentation `ind`. -/
partial def val {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Val Δ d Φ Γ τ o → Names → String → PM String
  | Val.lam (σ := σ) (u := u) b, n, ind => do
    let x ← fresh "x"
    return s!"fun {x} {use01 u} : {σ.pretty} => " ++ (← body b n [x] ind)
  | .thunk_mk b, n, ind => do return "thunk " ++ (← body b n [] ind)
  | .lazy_mk b, n, ind => do return "lazy " ++ (← body b n [] ind)
  | .record_mk args, n, _ => do return "⟨" ++ ", ".intercalate (← argList args n) ++ "⟩"
  | .union_mk ix args, n, _ => do
    return s!"ctor#{ctorIx ix}(" ++ ", ".intercalate (← argList args n) ++ ")"
  | .array_mk es, n, _ => do return "#[" ++ ", ".intercalate (← elemList es n) ++ "]"
  | .list_mk es, n, _ => do return "[" ++ ", ".intercalate (← elemList es n) ++ "]"
  | .data_in _ j e, n, _ => do return s!"in#{j.val}({← pexpr e n})"

/-- The body of a closure, a delay or a loop, binding `xs`: `(closed)`/`(open)`, then the
    statement on the next lines. -/
partial def body {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Body Δ d Φ Γ bs τ o → Names → List String → String → PM String
  | .closed t, n, xs, ind => do
    return "(closed)\n" ++ (← term t { u := xs, k := n.k, j := [] } (ind ++ "  "))
  | .opened t _, n, xs, ind => do
    return "(open)\n" ++ (← term t { u := xs ++ n.u, k := n.k, j := [] } (ind ++ "  "))

/-- A computation. -/
partial def comp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ τ ℓ → Names → String → PM String
  | .app f a _, n, _ => do return s!"{← pexpr f n} {← pexpr a n}"
  | .share e, n, _ => do return s!"share {← neu e n}"
  | .nat_rec c z s _, n, ind => do
    let acc ← fresh "acc"
    let i ← fresh "i"
    return s!"nat_rec {← pexpr c n} {← pexpr z n} fun {acc} {i} => " ++ (← body s n [acc, i] ind)
  | .array_foldl a z s _, n, ind => do
    let e ← fresh "e"
    let acc ← fresh "acc"
    return s!"array_foldl {← pexpr a n} {← pexpr z n} fun {e} {acc} => " ++
      (← body s n [e, acc] ind)
  | .data_rec _ _ _ brs j e _, n, ind => do
    let mut out := s!"data_rec#{j.val} {← pexpr e n}"
    for i in List.finRange _ do
      let r ← fresh "r"
      out := out ++ s!"\n{ind}  | branch {i.val} fun {r} => " ++ (← body (brs i) n [r] (ind ++ "  "))
    return out
  | .data_brec _ _ k _ brs j e _, n, ind => do
    let mut out := s!"data_brec#{j.val} (depth {k}) {← pexpr e n}"
    for i in List.finRange _ do
      let r ← fresh "r"
      out := out ++ s!"\n{ind}  | branch {i.val} fun {r} => " ++ (← body (brs i) n [r] (ind ++ "  "))
    return out
  | .thunk_force p, n, _ => do return s!"force {← pexpr p n}"
  | .lazy_force p, n, _ => do return s!"{← pexpr p n} ()"

/-- A statement, each line indented by `ind`. -/
partial def term {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Term Δ d Φ Γ τ js o → Names → String → PM String
  | .ret p, n, ind => do return s!"{ind}ret {← pexpr p n}"
  | Term.letV (σ := σ) u v t, n, ind => do
    let k ← fresh "k"
    let vs ← val v n ind
    return s!"{ind}val {k} {use1 u} : {σ.pretty} := {vs}\n" ++
      (← term t { n with k := k :: n.k } ind)
  | Term.letE (σ := σ) u c t, n, ind => do
    let cs ← comp c n ind
    let x ← fresh "x"
    return s!"{ind}let {x} {use1 u} : {σ.pretty} := {cs}\n" ++
      (← term t { n with u := x :: n.u } ind)
  | Term.record_casesOn (t := tt) (fs := fs) us e t, n, ind => do
    let es ← neu e n
    let (xs, shown) ← fields (tt :: fs.toList) us
    return s!"{ind}let ⟨{shown}⟩ := {es}\n" ++ (← term t { n with u := xs ++ n.u } ind)
  | .branch b, n, ind => branch b n ind
  | .jump j p, n, ind => do return s!"{ind}jump {n.j.getD j.index "?"} {← pexpr p n}"

/-- A branch. -/
partial def branch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
    Branch Δ d Φ Γ τ js ℓ → Names → String → PM String
  | .ite c t e, n, ind => do
    return s!"{ind}if {← neu c n} then\n{← term t n (ind ++ "  ")}\n{ind}else\n" ++
      (← term e n (ind ++ "  "))
  | .enum_casesOn c bs, n, ind => do
    let mut out := s!"{ind}case {← neu c n} of"
    for i in List.finRange _ do
      out := out ++ s!"\n{ind}| enum#{i.val} =>\n" ++ (← term (bs i) n (ind ++ "  "))
    return out
  | .union_casesOn e brs, n, ind => do
    let mut out := s!"{ind}case {← neu e n} of"
    for s in ← branches brs n ind 0 do
      out := out ++ "\n" ++ s
    return out
  | Branch.join σ u ux b br, n, ind => do
    let j ← fresh "j"
    let x ← fresh "x"
    let bs ← term b { n with u := x :: n.u } (ind ++ "  ")
    return s!"{ind}join {j} {use1 u} ({x} {use01 ux} : {σ.pretty}) :=\n{bs}\n" ++
      (← branch br { n with j := j :: n.j } ind)

/-- The arms of a union's case analysis. -/
partial def branches {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Branches Δ d Φ Γ cs τ js o → Names → String → Nat → PM (List String)
  | Branches.two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂, n, ind, i => do
    let (xs₁, s₁) ← fields c₁.binds us₁
    let a₁ ← term b₁ { n with u := xs₁ ++ n.u } (ind ++ "  ")
    let (xs₂, s₂) ← fields c₂.binds us₂
    let a₂ ← term b₂ { n with u := xs₂ ++ n.u } (ind ++ "  ")
    return [s!"{ind}| ctor#{i}({s₁}) =>\n{a₁}", s!"{ind}| ctor#{i + 1}({s₂}) =>\n{a₂}"]
  | Branches.cons (c := c) us b rest, n, ind, i => do
    let (xs, s) ← fields c.binds us
    let a ← term b { n with u := xs ++ n.u } (ind ++ "  ")
    return s!"{ind}| ctor#{i}({s}) =>\n{a}" :: (← branches rest n ind (i + 1))
end

end TermPretty

/-- A statement as text, its variables named. -/
def Term.pretty {ks : List Nat} {Δ : DSig ks} {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : String :=
  (TermPretty.term t {} "").run' 0

end LeanScript

end
