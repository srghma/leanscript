module

public import LeanScript.Term
public import LeanScript.TyNotation
public meta import Lean.Meta.Match.MatcherInfo

@[expose] public section

set_option autoImplicit false

/-!
# `[Term| …]`: a thin notation for terms, with de Bruijn variables, and its pretty-printer

`[Term| e]` elaborates the surface syntax `e` to a `LeanScript.Term Δ Γ τ` (the signature,
context and type are left to unification with the expected type).  The notation follows the
datatype closely: variables are **de Bruijn indices** `#i` (no names are bound or captured),
binders are written `_`, and the forms without dedicated syntax are the constructors' own
names with the constructors' own argument order.  Every `Term` built from its constructors is
printed back in the same notation (`set_option pp.leanscript false` turns that off).

| surface syntax                           | `Term`                                           |
|------------------------------------------|--------------------------------------------------|
| `#i`                                     | `.bvar i` (`.var` of de Bruijn index `i`)         |
| `fun _ (_ : τ) => e`                     | `.lam (.lam e)` (`τ` in the `[Ty| …]` syntax)    |
| `f a b`                                  | `.app (.app f a) b`                              |
| `let _ := e; b`, `let _ : τ := e; b`     | `.letE e b`                                      |
| `3`, `"s"`, `true`, `false`              | `Term.ofNat 3`, `.lit .string "s"`, `.lit .bool true`, … |
| `lit p v`                                | `.lit p v`                                       |
| `extern "name" f a b`                    | `.extern "name" f` of the arguments `a`, `b` (`Term.externOf`) |
| `if c then a else b`                     | `.ite c a b`                                     |
| `nat_rec n z s`                          | `.nat_rec n z s`                                 |
| `enum_mk i`                              | `.enum_mk _ i`                                   |
| `match e with \| 0 => a \| 1 => b \| _ => c` | `.enum_casesOn` (the last branch is the default) |
| `(a, b, c)`                              | `.record_mk` of the fields `a`, `b`, `c`         |
| `let (_, _, _) := e; b`                  | `.record_casesOn e b`                            |
| `union_mk i a b`                         | `.union_mk` of constructor `i` (by position) of the arguments `a`, `b` (`Term.inj`) |
| `match e with \| · => a \| _ => b \| (_, _) => c` | `.union_casesOn e` of the branches `a`, `b`, `c` |
| `#[a, b]`                                | `.array_mk` of the elements                      |
| `array_foldl arr init s`                 | `.array_foldl arr init s`                        |
| `data_in b j e`, `data_out b j e`        | `.data_in b j e`, `.data_out b j e`              |
| `data_rec b ρ br₀ … brₖ j e`             | `.data_rec b ρ brs j e`, branch `i` of `brs` is `brᵢ` |
| `data_brec b ρ k br₀ … brₖ j e`          | `.data_brec b ρ k brs j e`                       |
| `thunk_mk e`, `thunk_force e`           | `.thunk_mk e`, `.thunk_force e` (a `Thunk τ`)    |
| `lazy_mk e`, `lazy_force e`              | `.lazy_mk e`, `.lazy_force e` (a `Unit → τ`)     |
| `(e : τ)`                                | `e`, at the type `τ` (in the `[Ty| …]` syntax)   |
| `‹t›`                                    | the Lean term `t : Term Δ Γ τ`                   |
| `‹f›(a, b)`                              | the Lean term `f a b`: a Lean function of terms  |

**Variables and binders.**  A variable is only ever `#i`, the de Bruijn index of the
constructors (`0` is the innermost binder); an identifier is never a variable, and never a
Lean term either: every Lean term, even a single name, is written `‹t›`.  The binders follow
the constructors: in `nat_rec n z s` the step `s` sees the answer as `#0` and the predecessor
as `#1`; in `array_foldl arr init s` it sees the element as `#0` and the accumulator as `#1`;
`let (_, _) := e; b` and the patterns of a union see the fields with the first field innermost
(`#0`); a branch of `data_rec`/`data_brec` sees the member's body as `#0`.  The `_`s of a pattern only show how many
variables it binds: the number is fixed by the type, and it is not checked against the
pattern.

**Lean arguments.**  In `lit`, `extern`, `enum_mk`, `union_mk`, `data_in`, `data_out`,
`data_rec` and `data_brec` the leaf, value, name, function, constructor number, block,
member, answer types and depth are Lean terms: a number, a string or `‹t›`.  The branches of
`data_rec`/`data_brec` can also be given as one Lean function `‹brs›`.

**Delays.**  The type of `thunk_force e` / `lazy_force e` does not fix the type of `e` (the
contents `τ` of the delay are not recovered from the result type `τ.relax` by unification), so
when nothing else does, `e` is written with its type: `thunk_force (#0 : Thunk Nat)`.

A numeral takes its leaf type from the expected type (`Term.ofNat`), so its type must be known
from the context: `let _ := 3; ‹addT›(#0, #0)` works, a lone `let _ := 3; #0` needs
`let _ : Nat := 3; #0`.
-/

namespace LeanScript

/-! ## Constructors of a union by position -/

/-- Constructor `i` of a union (a field-less one past the end). -/
def Ctors.nth {ks : List Nat} : {bs : List Bool} → Ctors ks bs → (i : Nat) → Ctor ks (bs.getD i false)
  | _, .two c _, 0 => c
  | _, .two _ d, 1 => d
  | _, .two _ _, _ + 2 => .nullary
  | _, .cons c _, 0 => c
  | _, .cons _ cs, i + 1 => cs.nth i

/-- Constructor `i` of a union is one of its constructors. -/
def Ctors.ix {ks : List Nat} : {bs : List Bool} → (cs : Ctors ks bs) → (i : Nat) →
    i < bs.length → CtorIx cs (cs.nth i)
  | _, .two _ _, 0, _ => .two₁
  | _, .two _ _, 1, _ => .two₂
  | _, .two _ _, _ + 2, h => absurd h (by simp)
  | _, .cons _ _, 0, _ => .head
  | _, .cons _ cs, i + 1, h => .tail (cs.ix i (by simp at h; omega))

/-- Constructor `i` of a union, from its fields: `Term.inj 1 (.cons x .nil)`. -/
abbrev Term.inj {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} (i : Nat) (hi : i < bs.length := by decide)
    (args : Args Δ Γ (cs.nth i).binds) : Term Δ Γ (.union cs (h := h)) :=
  .union_mk (cs.ix i hi) args

/-- A numeral of a leaf type: `Term.ofNat 3 : Term Δ Γ .nat`.  Unlike `Term.lit`, the leaf and
    its side condition are found by unification with the expected type, so the numeral can be
    written before its type is known. -/
abbrev Term.ofNat {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {p : LeanPrimTy}
    (n : Nat) [OfNat p.denote n] : Term Δ Γ (.prim p) :=
  .lit p (OfNat.ofNat n)

/-- `Term.extern` with the arguments before the function: the types of the arguments are
    known when the function is elaborated, so `fun v => Nat.add v.1 v.2.1` needs no annotation. -/
abbrev Term.externOf {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {σs : List (Ty ks)} {τ : Ty ks}
    (name : String) (args : Args Δ Γ σs) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) :
    Term Δ Γ τ :=
  .extern name f args

/-! ## Syntax -/

/-- The surface syntax of a term (`[Term| …]`). -/
declare_syntax_cat lsterm
/-- A binder of `fun`: `_`, or `(_ : τ)`. -/
declare_syntax_cat lsbinder
/-- A placeholder for a bound variable: `_`. -/
declare_syntax_cat lshole
/-- A pattern of `match`. -/
declare_syntax_cat lspat

/-- A variable, by de Bruijn index. -/
syntax:max (name := lstermBVar) "#" noWs num : lsterm
/-- A constructor name (`nat_rec`, …), or `true`/`false`. -/
syntax:max ident : lsterm
/-- A literal. -/
syntax:max num : lsterm
/-- A literal. -/
syntax:max str : lsterm
/-- A Lean term of type `Term Δ Γ τ`. -/
syntax:max (name := lstermEmbed) "‹" term "›" : lsterm
/-- A Lean function of terms, applied: `‹f›(a, b)` is `f a b`. -/
syntax:max "‹" term "›" noWs "(" lsterm,* ")" : lsterm
syntax:max "(" lsterm ")" : lsterm
/-- A type ascription. -/
syntax:max "(" lsterm " : " lsty ")" : lsterm
/-- A record. -/
syntax:max (name := lstermTuple) "(" lsterm ", " lsterm,+ ")" : lsterm
/-- An array. -/
syntax:max "#[" lsterm,* "]" : lsterm
/-- Application. -/
syntax:100 (name := lstermApp) lsterm:100 ppSpace lsterm:101 : lsterm

syntax "_" : lshole

syntax "_" : lsbinder
syntax "(" "_" " : " lsty ")" : lsbinder

syntax (name := lstermFun) "fun" (ppSpace lsbinder)+ " => " lsterm : lsterm
syntax (name := lstermLet) "let " "_" (" : " lsty)? " := " lsterm "; " lsterm : lsterm
syntax (name := lstermLetTuple) "let " "(" lshole ", " lshole,+ ")" " := " lsterm "; " lsterm : lsterm
syntax (name := lstermIf) "if " lsterm " then " lsterm " else " lsterm : lsterm

syntax "·" : lspat
syntax "_" : lspat
syntax "(" lshole ", " lshole,+ ")" : lspat
syntax num : lspat
syntax (name := lstermMatch) "match " lsterm " with" (ppDedent(ppLine) " | " lspat " => " lsterm)+ : lsterm

/-- `[Term| e]`: the term written in the surface syntax `e` (see the module doc). -/
syntax:max "[Term| " lsterm "]" : term

end LeanScript

meta section

namespace LeanScript.Notation

open Lean

/-! ## Elaboration -/

/-- The constructors written as an application of their name. -/
def specialForms : List Name :=
  [`lit, `extern, `nat_rec, `enum_mk, `union_mk, `array_foldl, `data_in, `data_out, `data_rec,
   `data_brec, `thunk_mk, `thunk_force, `lazy_mk, `lazy_force]

/-- The arguments of a constructor or an extern. -/
def mkArgs : List Lean.Term → MacroM Lean.Term
  | [] => `(LeanScript.Args.nil)
  | t :: ts => do `(LeanScript.Args.cons $t $(← mkArgs ts))

/-- The elements of an array. -/
def mkElems : List Lean.Term → MacroM Lean.Term
  | [] => `(LeanScript.Elems.nil)
  | t :: ts => do `(LeanScript.Elems.cons $t $(← mkElems ts))

/-- The head and the arguments of an application. -/
partial def appSpine (e : TSyntax `lsterm) (args : List (TSyntax `lsterm) := []) :
    TSyntax `lsterm × List (TSyntax `lsterm) :=
  match e with
  | `(lsterm| $f $a) => appSpine f (a :: args)
  | _ => (e, args)

/-- A Lean term given as an argument of a constructor: a number, a string or `‹t›`. -/
partial def leanArg : TSyntax `lsterm → MacroM Lean.Term
  | `(lsterm| $n:num) => pure n
  | `(lsterm| $s:str) => pure s
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ($t)) => leanArg t
  | t => Macro.throwErrorAt t "expected a Lean term here: a number, a string or `‹term›`"

/-- The components of a record literal `(a, b, …)`, or `none`. -/
def tupleElems? (e : TSyntax `lsterm) : Option (List (TSyntax `lsterm)) :=
  if e.raw.isOfKind ``LeanScript.lstermTuple then
    some (e.raw[1] :: e.raw[3].getSepArgs.toList |>.map (⟨·⟩))
  else none

mutual

/-- The `Term` a surface term denotes. -/
partial def elabLsterm : TSyntax `lsterm → MacroM Lean.Term
  | `(lsterm| #$n:num) => `(LeanScript.Term.bvar $n)
  | `(lsterm| $n:num) => `(LeanScript.Term.ofNat $n)
  | `(lsterm| $s:str) => `(LeanScript.Term.lit LeanScript.LeanPrimTy.string $s)
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ‹$f›($as,*)) => do
      let as ← as.getElems.mapM elabLsterm
      `($f $as*)
  | `(lsterm| ($e)) => elabLsterm e
  | `(lsterm| ($e : $τ)) => do
      `(($(← elabLsterm e) : LeanScript.Term _ _ [Ty| $τ]))
  | `(lsterm| #[$es,*]) => do
      `(LeanScript.Term.array_mk $(← mkElems (← es.getElems.toList.mapM elabLsterm)))
  | `(lsterm| fun $bs* => $b) => elabFun bs.toList b
  | `(lsterm| let _ := $e; $b) => do
      `(LeanScript.Term.letE $(← elabLsterm e) $(← elabLsterm b))
  | `(lsterm| let _ : $τ := $e; $b) => do
      `(LeanScript.Term.letE (σ := [Ty| $τ]) $(← elabLsterm e) $(← elabLsterm b))
  | `(lsterm| let ($_, $_,*) := $e; $b) => do
      `(LeanScript.Term.record_casesOn $(← elabLsterm e) $(← elabLsterm b))
  | `(lsterm| if $c then $a else $b) => do
      `(LeanScript.Term.ite $(← elabLsterm c) $(← elabLsterm a) $(← elabLsterm b))
  | `(lsterm| match $e with $[| $ps => $bs]*) => elabMatch e ps.toList bs.toList
  | `(lsterm| $id:ident) =>
      match id.getId.eraseMacroScopes with
      | `true => `(LeanScript.Term.lit LeanScript.LeanPrimTy.bool true)
      | `false => `(LeanScript.Term.lit LeanScript.LeanPrimTy.bool false)
      | _ => elabSpecial id []
  | e@`(lsterm| $_ $_) => do
      match tupleElems? e with
      | some _ => elabTuple e
      | none =>
      let (f, args) := appSpine e
      if let `(lsterm| $id:ident) := f then
        if specialForms.contains id.getId.eraseMacroScopes then
          return ← elabSpecial id args
      let mut r ← elabLsterm f
      for a in args do
        r ← `(LeanScript.Term.app $r $(← elabLsterm a))
      return r
  | e => if (tupleElems? e).isSome then elabTuple e
      else Macro.throwErrorAt e "unsupported term syntax"

/-- A record literal. -/
partial def elabTuple (e : TSyntax `lsterm) : MacroM Lean.Term := do
  let some es := tupleElems? e | Macro.throwErrorAt e "expected a record"
  `(LeanScript.Term.record_mk $(← mkArgs (← es.mapM elabLsterm)))

/-- `fun _ … _ => b`. -/
partial def elabFun : List (TSyntax `lsbinder) → TSyntax `lsterm → MacroM Lean.Term
  | [], b => elabLsterm b
  | x :: xs, b => do
      match x with
      | `(lsbinder| (_ : $τ)) => `(LeanScript.Term.lam (σ := [Ty| $τ]) $(← elabFun xs b))
      | `(lsbinder| _) => `(LeanScript.Term.lam $(← elabFun xs b))
      | _ => Macro.throwErrorAt x "unsupported binder"

/-- The branches of `data_rec`/`data_brec`: one term per member, or one Lean function
    `‹brs›`. -/
partial def elabRecBranches : List (TSyntax `lsterm) → MacroM Lean.Term
  | brs => do
      if let [t] := brs then
        if t.raw.isOfKind ``LeanScript.lstermEmbed then return ⟨t.raw[1]⟩
      let rhss ← brs.toArray.mapM elabLsterm
      let pats ← (List.range brs.length).toArray.mapM fun i => `(⟨$(quote i), _⟩)
      `(fun $[| $pats => $rhss]*)

/-- `match e with | p => b …`: an enum when the patterns are numbers, a union otherwise. -/
partial def elabMatch (e : TSyntax `lsterm) (ps : List (TSyntax `lspat))
    (bs : List (TSyntax `lsterm)) : MacroM Lean.Term := do
  let e' ← elabLsterm e
  let isEnum := ps.any fun | `(lspat| $_:num) => true | _ => false
  let rhss ← bs.toArray.mapM elabLsterm
  if isEnum then
    let n := ps.length
    let pats ← ps.toArray.mapIdxM fun i p => do
      if i + 1 == n then `(_)
      else match p with
        | `(lspat| $k:num) => `($k:num)
        | _ => Macro.throwErrorAt p "expected a constructor number (only the last branch \
            may be `_`)"
    `(LeanScript.Term.enum_casesOn $e' (fun i => match i.val with $[| $pats => $rhss]*))
  else
    if ps.length < 2 then Macro.throwErrorAt e "a union has at least two constructors"
    for p in ps do
      match p with
      | `(lspat| ·) | `(lspat| _) | `(lspat| ($_, $_,*)) => pure ()
      | _ => Macro.throwErrorAt p "expected `·`, `_` or `(_, _, …)`"
    let rec mk : List Lean.Term → MacroM Lean.Term
      | [a, b] => `(LeanScript.Branches.two $a $b)
      | a :: rest => do `(LeanScript.Branches.cons $a $(← mk rest))
      | [] => Macro.throwError "unreachable"
    `(LeanScript.Term.union_casesOn $e' $(← mk rhss.toList))

/-- A constructor, applied to `args`. -/
partial def elabSpecial (id : Ident) (args : List (TSyntax `lsterm)) : MacroM Lean.Term := do
  let f := id.getId.eraseMacroScopes
  let bad {α : Type} (usage : String) : MacroM α :=
    Macro.throwErrorAt id s!"`{f}` is used as `{usage}`"
  match f, args with
  | `lit, [p, v] => do `(LeanScript.Term.lit $(← leanArg p) $(← leanArg v))
  | `lit, _ => bad "lit p v"
  | `extern, name :: fn :: as => do
      `(LeanScript.Term.externOf $(← leanArg name) $(← mkArgs (← as.mapM elabLsterm))
          $(← leanArg fn))
  | `extern, _ => bad "extern \"name\" f a₁ … aₙ"
  | `nat_rec, [n, z, s] => do
      `(LeanScript.Term.nat_rec $(← elabLsterm n) $(← elabLsterm z) $(← elabLsterm s))
  | `nat_rec, _ => bad "nat_rec n z s"
  | `enum_mk, [i] => do `(LeanScript.Term.enum_mk _ $(← leanArg i))
  | `enum_mk, _ => bad "enum_mk i"
  | `union_mk, i :: as => do
      `(LeanScript.Term.inj $(← leanArg i) (args := $(← mkArgs (← as.mapM elabLsterm))))
  | `union_mk, _ => bad "union_mk i a₁ … aₙ"
  | `array_foldl, [arr, init, s] => do
      `(LeanScript.Term.array_foldl $(← elabLsterm arr) $(← elabLsterm init) $(← elabLsterm s))
  | `array_foldl, _ => bad "array_foldl arr init s"
  | `data_in, [b, j, e] => do
      `(LeanScript.Term.data_in $(← leanArg b) $(← leanArg j) $(← elabLsterm e))
  | `data_in, _ => bad "data_in b j e"
  | `data_out, [b, j, e] => do
      `(LeanScript.Term.data_out $(← leanArg b) $(← leanArg j) $(← elabLsterm e))
  | `data_out, _ => bad "data_out b j e"
  | `data_rec, b :: ρ :: rest@(_ :: _ :: _ :: _) => do
      let brs := rest.take (rest.length - 2)
      let j := rest[rest.length - 2]!
      let e := rest[rest.length - 1]!
      `(LeanScript.Term.data_rec $(← leanArg b) $(← leanArg ρ) $(← elabRecBranches brs)
          $(← leanArg j) $(← elabLsterm e))
  | `data_rec, _ => bad "data_rec b ρ br₀ … brₖ j e"
  | `data_brec, b :: ρ :: k :: rest@(_ :: _ :: _ :: _) => do
      let brs := rest.take (rest.length - 2)
      let j := rest[rest.length - 2]!
      let e := rest[rest.length - 1]!
      `(LeanScript.Term.data_brec $(← leanArg b) $(← leanArg ρ) $(← leanArg k)
          $(← elabRecBranches brs) $(← leanArg j) $(← elabLsterm e))
  | `data_brec, _ => bad "data_brec b ρ k br₀ … brₖ j e"
  | `thunk_mk, [e] => do `(LeanScript.Term.thunk_mk $(← elabLsterm e))
  | `thunk_mk, _ => bad "thunk_mk e"
  | `thunk_force, [e] => do `(LeanScript.Term.thunk_force $(← elabLsterm e))
  | `thunk_force, _ => bad "thunk_force e"
  | `lazy_mk, [e] => do `(LeanScript.Term.lazy_mk $(← elabLsterm e))
  | `lazy_mk, _ => bad "lazy_mk e"
  | `lazy_force, [e] => do `(LeanScript.Term.lazy_force $(← elabLsterm e))
  | `lazy_force, _ => bad "lazy_force e"
  | _, _ => Macro.throwErrorAt id s!"unknown constructor `{f}`: a variable is written `#i` \
      and a Lean term `‹{f}›`"

end

macro_rules
  | `([Term| $e]) => elabLsterm e

/-! ## Pretty-printing -/

open Meta PrettyPrinter Delaborator SubExpr

/-- A surface term with its precedence. -/
abbrev TSyn := TSyntax `lsterm × Nat

/-- The precedence of an application. -/
def appPrec : Nat := 100

/-- Parenthesize `s` when its precedence is below `req`. -/
def tparen (req : Nat) : TSyn → DelabM (TSyntax `lsterm)
  | (s, p) => if p < req then `(lsterm| ($s)) else pure s

/-- The de Bruijn index of a variable (`DeBruijn.head`/`tail`/`ofIndex`). -/
partial def dbIndex? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``DeBruijn.head 3 then some 0
  else if e.isAppOfArity ``DeBruijn.tail 5 then (dbIndex? e.appArg!).map (· + 1)
  else if e.isAppOfArity ``DeBruijn.ofIndex 5 then natLit? (e.getArg! 3)
  else none

/-- The position of a constructor of a union (`CtorIx`, or `Ctors.ix cs i _`). -/
partial def ctorIxIndex? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  match e.getAppFn.constName? with
  | some ``CtorIx.two₁ | some ``CtorIx.head => some 0
  | some ``CtorIx.two₂ => some 1
  | some ``CtorIx.tail => (ctorIxIndex? e.appArg!).map (· + 1)
  | some ``Ctors.ix => natLit? (e.getArg! (e.getAppNumArgs - 2))
  | _ => none

/-- The number of fields of a `Fields`. -/
partial def fieldsLen (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOfArity ``Fields.one 2 then return 1
  else if e.isAppOfArity ``Fields.cons 3 then return 1 + (← fieldsLen e.appArg!)
  else failure

/-- The number of fields a constructor of a union binds. -/
def ctorBinds (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOfArity ``Ctor.nullary 1 then return 0
  else if e.isAppOfArity ``Ctor.fields 2 then fieldsLen e.appArg!
  else failure

/-- Navigate to argument `k` counted from the end (`1` is the last). -/
def withArgFromEnd {α : Type} (k : Nat) (x : DelabM α) : DelabM α := do
  withNaryArg ((← getExpr).getAppNumArgs - k) x

/-- Navigate under all the leading `fun`s of the current expression. -/
partial def underLams {α : Type} (x : DelabM α) : DelabM α := do
  if (← getExpr).consumeMData.isLambda then withBindingBody' `_ (fun _ => pure ()) fun _ => underLams x
  else x

/-- The heads the notation prints, with their arity. -/
def termHeads : List (Name × Nat) :=
  [(``Term.var, 5), (``Term.letE, 7), (``Term.lam, 6), (``Term.app, 7), (``Term.lit, 5),
   (``Term.extern, 8), (``Term.ite, 7), (``Term.nat_rec, 7), (``Term.enum_mk, 5),
   (``Term.enum_casesOn, 7), (``Term.record_mk, 6), (``Term.record_casesOn, 8),
   (``Term.union_mk, 10), (``Term.union_casesOn, 9), (``Term.array_mk, 5),
   (``Term.array_foldl, 8), (``Term.data_in, 6), (``Term.data_out, 6), (``Term.data_rec, 8),
   (``Term.data_brec, 9), (``Term.bvar, 6), (``Term.ofNat, 6), (``Term.inj, 9),
   (``Term.externOf, 8), (``Term.thunk_mk, 5), (``Term.thunk_force, 5), (``Term.lazy_mk, 5),
   (``Term.lazy_force, 5)]

/-- The placeholders `_, …, _` of `n` bound variables. -/
def holes (n : Nat) : DelabM (Array (TSyntax `lshole)) :=
  (List.range n).toArray.mapM fun _ => `(lshole| _)

/-- The pattern of a constructor that binds `n` fields: `·`, `_` or `(_, …, _)`. -/
def patOf (n : Nat) : DelabM (TSyntax `lspat) := do
  match n with
  | 0 => `(lspat| ·)
  | 1 => `(lspat| _)
  | n + 1 => do `(lspat| ($(← `(lshole| _)), $(← holes n),*))

/-- A Lean term, as an argument of a constructor: a number, a string, or `‹t›`. -/
def leanArgSyn : DelabM (TSyntax `lsterm) := do
  let s ← delab
  match s with
  | `($n:num) => `(lsterm| $n:num)
  | `($str:str) => `(lsterm| $str:str)
  | _ => `(lsterm| ‹$s›)

/-- The application of the constructor `f` to `args` (already parenthesized). -/
def mkAppSyn (f : Name) (args : List (TSyntax `lsterm)) : DelabM (TSyntax `lsterm) := do
  let mut r ← `(lsterm| $(mkIdent f):ident)
  for a in args do
    r ← `(lsterm| $r $a)
  return r

/-- A record literal `(a, b, …)` from at least two components. -/
def mkTupleSyn (a : TSyntax `lsterm) (bs : Array (TSyntax `lsterm)) : DelabM (TSyntax `lsterm) :=
  `(lsterm| ($a, $bs,*))

mutual

/-- A Lean function applied to terms, `‹f›(a, b)`: the current expression is a global
    constant applied to implicit arguments, then to explicit arguments that are `Term`s. -/
partial def embedCall? : DelabM (Option (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let some c := e.getAppFn.constName? | return none
  if (termHeads.lookup c).isSome then return none
  let args := e.getAppArgs
  let n := args.size
  if n == 0 then return none
  let info ← getFunInfoNArgs e.getAppFn n
  let explicit (i : Nat) : Bool := (info.paramInfo[i]?.map (·.binderInfo.isExplicit)).getD false
  let mut k := 0
  for i in (List.range n).reverse do
    let ty ← whnfR (← inferType args[i]!)
    if ty.isAppOf ``LeanScript.Term && explicit i then k := k + 1 else break
  if k == 0 then return none
  for i in [0:n - k] do
    if explicit i then return none
  let f := mkIdent (← unresolveNameGlobal c)
  let as ← (List.range k).toArray.mapM fun j =>
    withNaryArg (n - k + j) do return (← delabLsterm false).1
  return some (← `(lsterm| ‹$f›($as,*)))

/-- The current expression, a `Term`, as a surface term; `root` is whether it is the whole
    printed term (then an expression that is not in the notation fails, instead of being
    embedded as `‹…›`). -/
partial def delabLsterm (root : Bool) : DelabM TSyn := do
  let e := (← getExpr).consumeMData
  let other : DelabM TSyn := do
    if root then failure
    if let some s ← embedCall? then return (s, atomPrec)
    return (← leanArgSyn, atomPrec)
  let some c := e.getAppFn.constName? | other
  let some arity := termHeads.lookup c | other
  if e.getAppNumArgs != arity then return ← other
  let sub (k : Nat) : DelabM TSyn := withArgFromEnd k (delabLsterm false)
  -- an argument of an application
  let arg (k : Nat) : DelabM (TSyntax `lsterm) := do tparen (appPrec + 1) (← sub k)
  let r : DelabM TSyn := do
    match c with
    | ``Term.var | ``Term.bvar =>
        let i ← if c == ``Term.var then (dbIndex? e.appArg!).getDM failure
          else (natLit? (e.getArg! 4)).getDM failure
        return (← `(lsterm| #$(Syntax.mkNumLit (toString i)):num), atomPrec)
    | ``Term.ofNat =>
        let some n := natLit? (e.getArg! 4) | failure
        return (← `(lsterm| $(Syntax.mkNumLit (toString n)):num), atomPrec)
    | ``Term.lit =>
        let p := (e.getArg! 3).consumeMData
        let v := (e.getArg! 4).consumeMData
        if let some n := natLit? v then
          return (← `(lsterm| $(Syntax.mkNumLit (toString n)):num), atomPrec)
        if let .lit (.strVal str) := v then
          return (← `(lsterm| $(Syntax.mkStrLit str):str), atomPrec)
        if p.isConstOf ``LeanPrimTy.bool && (v.isConstOf ``Bool.true || v.isConstOf ``Bool.false) then
          return (← `(lsterm| $(mkIdent (if v.isConstOf ``Bool.true then `true else `false)):ident),
            atomPrec)
        let p ← withArgFromEnd 2 leanArgSyn
        let v ← withArgFromEnd 1 leanArgSyn
        return (← mkAppSyn `lit [p, v], appPrec)
    | ``Term.lam =>
        -- merge the `fun`s
        let rec go (bs : Array (TSyntax `lsbinder)) : DelabM TSyn := do
          let e := (← getExpr).consumeMData
          if e.isAppOfArity ``Term.lam 6 then
            let b ← if ← getPPOption getPPFunBinderTypes then do
                let (τ, _) ← withArgFromEnd 3 (delabLsty false)
                `(lsbinder| (_ : $τ))
              else `(lsbinder| _)
            withArgFromEnd 1 (go (bs.push b))
          else
            let (body, _) ← delabLsterm false
            return (← `(lsterm| fun $bs* => $body), 0)
        go #[]
    | ``Term.app =>
        let f ← tparen appPrec (← sub 2)
        return (← `(lsterm| $f $(← arg 1)), appPrec)
    | ``Term.letE =>
        let (v, _) ← sub 2
        let (b, _) ← sub 1
        return (← `(lsterm| let _ := $v; $b), 0)
    | ``Term.ite =>
        let (a, _) ← sub 3
        let (b, _) ← sub 2
        let (c, _) ← sub 1
        return (← `(lsterm| if $a then $b else $c), 0)
    | ``Term.nat_rec => return (← mkAppSyn `nat_rec [← arg 3, ← arg 2, ← arg 1], appPrec)
    | ``Term.enum_mk => return (← mkAppSyn `enum_mk [← withArgFromEnd 1 leanArgSyn], appPrec)
    | ``Term.record_mk =>
        let as ← withArgFromEnd 1 delabArgs
        match as with
        | a :: bs@(_ :: _) => return (← mkTupleSyn a bs.toArray, atomPrec)
        | _ => failure
    | ``Term.record_casesOn =>
        let n := (← fieldsLen (e.getArg! 4))
        let (v, _) ← sub 2
        let (b, _) ← sub 1
        return (← `(lsterm| let ($(← `(lshole| _)), $(← holes n),*) := $v; $b), 0)
    | ``Term.union_mk | ``Term.inj =>
        let i ← if c == ``Term.inj then (natLit? (e.getArg! 6)).getDM failure
          else (ctorIxIndex? (e.getArg! 8)).getDM failure
        let as ← withArgFromEnd 1 delabArgs
        let as ← as.mapM fun a => do tparen (appPrec + 1) (a, ← precOf a)
        let i : TSyntax `lsterm ← `(lsterm| $(Syntax.mkNumLit (toString i)):num)
        return (← mkAppSyn `union_mk (i :: as), appPrec)
    | ``Term.union_casesOn =>
        let (v, _) ← sub 2
        let brs ← withArgFromEnd 1 delabBranches
        let ps := (brs.map (·.1)).toArray
        let bs := (brs.map (·.2)).toArray
        return (← `(lsterm| match $v with $[| $ps => $bs]*), 0)
    | ``Term.enum_casesOn =>
        let (v, _) ← sub 2
        let bs ← withArgFromEnd 1 (underLams delabMatchAlts)
        let n := bs.length
        let bs := bs.toArray
        let ps ← (List.range n).toArray.mapM fun i => do
          if i + 1 == n then `(lspat| _)
          else `(lspat| $(Syntax.mkNumLit (toString i)):num)
        return (← `(lsterm| match $v with $[| $ps => $bs]*), 0)
    | ``Term.array_mk =>
        let es ← withArgFromEnd 1 delabElems
        return (← `(lsterm| #[$es.toArray,*]), atomPrec)
    | ``Term.thunk_mk => return (← mkAppSyn `thunk_mk [← arg 1], appPrec)
    | ``Term.thunk_force => return (← mkAppSyn `thunk_force [← arg 1], appPrec)
    | ``Term.lazy_mk => return (← mkAppSyn `lazy_mk [← arg 1], appPrec)
    | ``Term.lazy_force => return (← mkAppSyn `lazy_force [← arg 1], appPrec)
    | ``Term.array_foldl => return (← mkAppSyn `array_foldl [← arg 3, ← arg 2, ← arg 1], appPrec)
    | ``Term.data_in | ``Term.data_out =>
        let b ← withArgFromEnd 3 leanArgSyn
        let j ← withArgFromEnd 2 leanArgSyn
        return (← mkAppSyn (if c == ``Term.data_in then `data_in else `data_out) [b, j, ← arg 1],
          appPrec)
    | ``Term.data_rec | ``Term.data_brec =>
        let brec := c == ``Term.data_brec
        let b ← withArgFromEnd (if brec then 6 else 5) leanArgSyn
        let ρ ← withArgFromEnd (if brec then 5 else 4) leanArgSyn
        let k ← if brec then (fun k => [k]) <$> withArgFromEnd 4 leanArgSyn else pure []
        let brs ← withArgFromEnd 3 (do
            let alts ← underLams delabMatchAlts
            alts.mapM fun br => do tparen (appPrec + 1) (br, ← precOf br))
          <|> (do return [← withArgFromEnd 3 (do `(lsterm| ‹$(← delab)›))])
        let j ← withArgFromEnd 2 leanArgSyn
        return (← mkAppSyn (if brec then `data_brec else `data_rec)
          ([b, ρ] ++ k ++ brs ++ [j, ← arg 1]), appPrec)
    | ``Term.extern | ``Term.externOf =>
        let ext := c == ``Term.extern
        let name ← withArgFromEnd 3 leanArgSyn
        let f ← withArgFromEnd (if ext then 2 else 1) leanArgSyn
        let as ← withArgFromEnd (if ext then 1 else 2) delabArgs
        let as ← as.mapM fun a => do tparen (appPrec + 1) (a, ← precOf a)
        return (← mkAppSyn `extern ([name, f] ++ as), appPrec)
    | _ => failure
  r <|> other

/-- The arguments of a constructor or an extern. -/
partial def delabArgs : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Args.nil 3 then return []
  else if e.isAppOfArity ``Args.cons 7 then
    return (← withArgFromEnd 2 (delabLsterm false)).1 :: (← withArgFromEnd 1 delabArgs)
  else failure

/-- The elements of an array literal. -/
partial def delabElems : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Elems.nil 4 then return []
  else if e.isAppOfArity ``Elems.cons 6 then
    return (← withArgFromEnd 2 (delabLsterm false)).1 :: (← withArgFromEnd 1 delabElems)
  else failure

/-- The branches of a union's case analysis, with their patterns. -/
partial def delabBranches : DelabM (List (TSyntax `lspat × TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let branch (c : Expr) (k : Nat) : DelabM (TSyntax `lspat × TSyntax `lsterm) := do
    return (← patOf (← ctorBinds c), (← withArgFromEnd k (delabLsterm false)).1)
  if e.isAppOfArity ``Branches.two 10 then
    return [← branch (e.getArg! 5) 2, ← branch (e.getArg! 6) 1]
  else if e.isAppOfArity ``Branches.cons 10 then
    return (← branch (e.getArg! 5) 2) :: (← withArgFromEnd 1 delabBranches)
  else failure

/-- The right-hand sides of the alternatives of a `match` (the current expression), each a
    `Term`. -/
partial def delabMatchAlts : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let some c := e.getAppFn.constName? | failure
  let some info ← getMatcherInfo? c | failure
  let first := info.numParams + 1 + info.numDiscrs
  unless e.getAppNumArgs == first + info.numAlts do failure
  (List.range info.numAlts).mapM fun i =>
    withNaryArg (first + i) (underLams do return (← delabLsterm false).1)

/-- The precedence of a surface term that was built by `delabLsterm`. -/
partial def precOf (s : TSyntax `lsterm) : DelabM Nat := do
  let k := s.raw.getKind
  if k == ``LeanScript.lstermApp then return appPrec
  if [``LeanScript.lstermFun, ``LeanScript.lstermLet, ``LeanScript.lstermLetTuple,
      ``LeanScript.lstermIf, ``LeanScript.lstermMatch].contains k then return 0
  return atomPrec

end

open PrettyPrinter.Parenthesizer in
/-- Parentheses in the surface syntax of terms, where the precedences require them. -/
@[category_parenthesizer lsterm]
def lsterm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `lsterm true (fun stx => Unhygienic.run `(lsterm| ($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `lsterm prec

/-- Print a `Term` in the `[Term| …]` notation. -/
def delabTerm : Delab := do
  unless ← ppNotation do failure
  let (s, _) ← delabLsterm true
  `([Term| $s])

@[delab app.LeanScript.Term.var] def delabTermVar : Delab := delabTerm
@[delab app.LeanScript.Term.letE] def delabTermLetE : Delab := delabTerm
@[delab app.LeanScript.Term.lam] def delabTermLam : Delab := delabTerm
@[delab app.LeanScript.Term.app] def delabTermApp : Delab := delabTerm
@[delab app.LeanScript.Term.lit] def delabTermLit : Delab := delabTerm
@[delab app.LeanScript.Term.extern] def delabTermExtern : Delab := delabTerm
@[delab app.LeanScript.Term.ite] def delabTermIte : Delab := delabTerm
@[delab app.LeanScript.Term.nat_rec] def delabTermNatRec : Delab := delabTerm
@[delab app.LeanScript.Term.enum_mk] def delabTermEnumMk : Delab := delabTerm
@[delab app.LeanScript.Term.enum_casesOn] def delabTermEnumCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.record_mk] def delabTermRecordMk : Delab := delabTerm
@[delab app.LeanScript.Term.record_casesOn] def delabTermRecordCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.union_mk] def delabTermUnionMk : Delab := delabTerm
@[delab app.LeanScript.Term.union_casesOn] def delabTermUnionCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.array_mk] def delabTermArrayMk : Delab := delabTerm
@[delab app.LeanScript.Term.array_foldl] def delabTermArrayFoldl : Delab := delabTerm
@[delab app.LeanScript.Term.data_in] def delabTermDataIn : Delab := delabTerm
@[delab app.LeanScript.Term.data_out] def delabTermDataOut : Delab := delabTerm
@[delab app.LeanScript.Term.data_rec] def delabTermDataRec : Delab := delabTerm
@[delab app.LeanScript.Term.data_brec] def delabTermDataBrec : Delab := delabTerm
@[delab app.LeanScript.Term.bvar] def delabTermBVar : Delab := delabTerm
@[delab app.LeanScript.Term.ofNat] def delabTermOfNat : Delab := delabTerm
@[delab app.LeanScript.Term.inj] def delabTermInj : Delab := delabTerm
@[delab app.LeanScript.Term.externOf] def delabTermExternOf : Delab := delabTerm
@[delab app.LeanScript.Term.thunk_mk] def delabTermThunkMk : Delab := delabTerm
@[delab app.LeanScript.Term.thunk_force] def delabTermThunkForce : Delab := delabTerm
@[delab app.LeanScript.Term.lazy_mk] def delabTermLazyMk : Delab := delabTerm
@[delab app.LeanScript.Term.lazy_force] def delabTermLazyForce : Delab := delabTerm

end LeanScript.Notation

end
