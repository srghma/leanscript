module

public import LeanScript.Term
public import LeanScript.TyNotation
public meta import Lean.Meta.Match.MatcherInfo

@[expose] public section

set_option autoImplicit false

/-!
# `[Term| …]`: a notation for terms with named variables, and its pretty-printer

`[Term| e]` elaborates the surface syntax `e`, whose variables are **names**, to a
`LeanScript.Term Δ Γ τ` with de Bruijn variables (the signature, context and type are left to
unification with the expected type).  Every `Term` built from its constructors is printed back
in the same notation, with generated names `x₀`, `x₁`, … (`set_option pp.leanscript false`
turns that off).

| surface syntax                         | `Term`                                               |
|----------------------------------------|------------------------------------------------------|
| `x` (bound by the notation)            | `.bvar i`, the de Bruijn index of `x`                |
| `#i`                                   | `.bvar i` (a variable of the enclosing context)      |
| `fun x (y : τ) => e`                   | `.lam (.lam e)` (`τ` in the `[Ty| …]` syntax)        |
| `f a b`                                | `.app (.app f a) b`                                  |
| `let x := e; b`, `let x : τ := e; b`   | `.letE e b`                                          |
| `3`, `"s"`, `true`, `false`            | `Term.ofNat 3`, `.lit .string "s"`, `.lit .bool true`, … |
| `lit p v`                              | `.lit p v`                                           |
| `if c then a else b`                   | `.ite c a b`                                         |
| `(a, b, c)`                            | `.record_mk` of the fields `a`, `b`, `c`             |
| `let (x, y, z) := e; b`                | `.record_casesOn e b`                                |
| `inj i`, `inj i a`, `inj i (a, b)`     | constructor `i` of a union (no, one, two fields)     |
| `match e with \| · => a \| x => b \| (y, z) => c` | `.union_casesOn`: one branch per constructor |
| `enum i`                               | `.enum_mk _ i`                                       |
| `match e with \| 0 => a \| 1 => b \| _ => c` | `.enum_casesOn` (the last branch is the default) |
| `#[a, b]`                              | `.array_mk` of the elements                          |
| `foldl (fun acc x => s) init arr`      | `.array_foldl arr init s`                            |
| `natRec n z (fun m ih => s)`           | `.nat_rec n z s`                                     |
| `roll b j e`, `unroll b j e`           | `.data_in b j e`, `.data_out b j e`                  |
| `fold b ρ j e (fun x => br₀) …`        | `.data_rec b ρ brs j e`, branch `i` of `brs` is `brᵢ` |
| `brec b ρ k j e (fun x => br₀) …`      | `.data_brec b ρ k brs j e`                           |
| `extern "name" f a b`                  | `.extern "name" f` of the arguments `a`, `b` (`Term.externOf`) |
| `(e : τ)`                              | `e`, at the type `τ` (in the `[Ty| …]` syntax)       |
| `‹t›`                                  | the Lean term `t : Term Δ Γ τ`                       |
| `‹f›(a, b)`                            | the Lean term `f a b`: a Lean function of terms      |

An identifier that the notation does not bind is a Lean term (`sumT xs` applies the Lean
term `sumT`).  In `roll`, `unroll`, `fold`, `brec`, `extern` and `lit`, the block, member,
answer types, depth, name and function are Lean terms: a number, a string, an identifier or
`‹t›`.  In `fold` and `brec` the branches can also be given as one Lean function `‹brs›`.

The binders follow the constructors: `fun m ih => s` of `natRec` binds the predecessor `m`
and the answer `ih` (index `0`), `fun acc x => s` of `foldl` binds the accumulator and the
element `x` (index `0`); `let (x, y) := e; b` and the patterns of a union bind the fields,
the first field `x` innermost (index `0`).

A numeral takes its leaf type from the expected type (`Term.ofNat`), so its type must be known
from the context: `let x := 3; ‹addT›(x, x)` works (the use of `x` fixes it), a lone
`let x := 3; x` needs `let x : Nat := 3; x`.  A Lean term that is not a number, a string or an
identifier (`.int`, `-3`, `listB.there`) is written `‹t›`.
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
abbrev Term.ofNat {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {p : LeanPrimTy} {h : p.Nondeg = true}
    (n : Nat) [OfNat p.denote n] : Term Δ Γ (.prim p h) :=
  .lit p (OfNat.ofNat n) h

/-- `Term.extern` with the arguments before the function: the types of the arguments are
    known when the function is elaborated, so `fun v => Nat.add v.1 v.2.1` needs no annotation. -/
abbrev Term.externOf {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {σs : List (Ty ks)} {τ : Ty ks}
    (name : String) (args : Args Δ Γ σs) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) :
    Term Δ Γ τ :=
  .extern name f args

/-! ## Syntax -/

/-- The surface syntax of a term (`[Term| …]`). -/
declare_syntax_cat lsterm
/-- A binder of `fun`: a name, or a name with its type. -/
declare_syntax_cat lsbinder
/-- A pattern of `match`. -/
declare_syntax_cat lspat

/-- A variable bound by the notation, or a Lean term. -/
syntax:max ident : lsterm
/-- A variable of the enclosing context, by de Bruijn index. -/
syntax:max (name := lstermBVar) "#" noWs num : lsterm
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

syntax Lean.binderIdent : lsbinder
syntax "(" Lean.binderIdent " : " lsty ")" : lsbinder

syntax (name := lstermFun) "fun" (ppSpace lsbinder)+ " => " lsterm : lsterm
syntax (name := lstermLet) "let " Lean.binderIdent (" : " lsty)? " := " lsterm "; " lsterm : lsterm
syntax (name := lstermLetTuple) "let " "(" Lean.binderIdent ", " Lean.binderIdent,+ ")" " := " lsterm "; " lsterm : lsterm
syntax (name := lstermIf) "if " lsterm " then " lsterm " else " lsterm : lsterm

syntax "·" : lspat
syntax Lean.binderIdent : lspat
syntax "(" Lean.binderIdent ", " Lean.binderIdent,+ ")" : lspat
syntax num : lspat
syntax (name := lstermMatch) "match " lsterm " with" (ppDedent(ppLine) " | " lspat " => " lsterm)+ : lsterm

/-- `[Term| e]`: the term written in the surface syntax `e` (see the module doc). -/
syntax:max "[Term| " lsterm "]" : term

end LeanScript

meta section

namespace LeanScript.Notation

open Lean

/-! ## Elaboration -/

/-- The name a binder binds (`_` binds a name that cannot be referred to). -/
def binderName : TSyntax ``Lean.binderIdent → Name
  | `(binderIdent| $id:ident) => id.getId
  | _ => .anonymous

/-- The names in scope, innermost first. -/
abbrev Scope := List Name

/-- The special forms, written as an application of their name. -/
def specialForms : List Name :=
  [`inj, `enum, `natRec, `foldl, `roll, `unroll, `fold, `brec, `extern, `lit]

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

/-- A Lean term given as an argument of a special form: a number, a string, an identifier
    (not bound by the notation) or `‹t›`. -/
partial def leanArg (sc : Scope) : TSyntax `lsterm → MacroM Lean.Term
  | `(lsterm| $n:num) => pure n
  | `(lsterm| $s:str) => pure s
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ($t)) => leanArg sc t
  | `(lsterm| $id:ident) =>
      if sc.contains id.getId then
        Macro.throwErrorAt id "expected a Lean term here, not a variable of the term"
      else pure id
  | t => Macro.throwErrorAt t "expected a Lean term here: a number, a string, an identifier \
      or `‹term›`"

/-- The components of a record literal `(a, b, …)`, or `none`. -/
def tupleElems? (e : TSyntax `lsterm) : Option (List (TSyntax `lsterm)) :=
  if e.raw.isOfKind ``LeanScript.lstermTuple then
    some (e.raw[1] :: e.raw[3].getSepArgs.toList |>.map (⟨·⟩))
  else none

mutual

/-- The `Term` a surface term denotes, in the scope `sc`. -/
partial def elabLsterm (sc : Scope) : TSyntax `lsterm → MacroM Lean.Term
  | `(lsterm| #$n:num) => `(LeanScript.Term.bvar $n)
  | `(lsterm| $n:num) => `(LeanScript.Term.ofNat $n)
  | `(lsterm| $s:str) => `(LeanScript.Term.lit LeanScript.LeanPrimTy.string $s rfl)
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ‹$f›($as,*)) => do
      let as ← as.getElems.mapM (elabLsterm sc)
      `($f $as*)
  | `(lsterm| ($e)) => elabLsterm sc e
  | `(lsterm| ($e : $τ)) => do
      `(($(← elabLsterm sc e) : LeanScript.Term _ _ [Ty| $τ]))
  | `(lsterm| #[$es,*]) => do
      `(LeanScript.Term.array_mk $(← mkElems (← es.getElems.toList.mapM (elabLsterm sc))))
  | `(lsterm| fun $bs* => $b) => elabFun sc bs.toList b
  | `(lsterm| let $x:binderIdent := $e; $b) => do
      `(LeanScript.Term.letE $(← elabLsterm sc e) $(← elabLsterm (binderName x :: sc) b))
  | `(lsterm| let $x:binderIdent : $τ := $e; $b) => do
      `(LeanScript.Term.letE (σ := [Ty| $τ]) $(← elabLsterm sc e)
          $(← elabLsterm (binderName x :: sc) b))
  | `(lsterm| let ($x, $xs,*) := $e; $b) => do
      let names := (x :: xs.getElems.toList).map binderName
      `(LeanScript.Term.record_casesOn $(← elabLsterm sc e) $(← elabLsterm (names ++ sc) b))
  | `(lsterm| if $c then $a else $b) => do
      `(LeanScript.Term.ite $(← elabLsterm sc c) $(← elabLsterm sc a) $(← elabLsterm sc b))
  | `(lsterm| match $e with $[| $ps => $bs]*) => elabMatch sc e ps.toList bs.toList
  | `(lsterm| $id:ident) =>
      match sc.idxOf? id.getId with
      | some i => `(LeanScript.Term.bvar $(quote i))
      | none =>
        match id.getId.eraseMacroScopes with
        | `true => `(LeanScript.Term.lit LeanScript.LeanPrimTy.bool true rfl)
        | `false => `(LeanScript.Term.lit LeanScript.LeanPrimTy.bool false rfl)
        | _ =>
          if specialForms.contains id.getId.eraseMacroScopes then elabSpecial sc id []
          else pure id
  | e@`(lsterm| $_ $_) => do
      match tupleElems? e with
      | some _ => elabTuple sc e
      | none =>
      let (f, args) := appSpine e
      if let `(lsterm| $id:ident) := f then
        if !sc.contains id.getId && specialForms.contains id.getId.eraseMacroScopes then
          return ← elabSpecial sc id args
      let mut r ← elabLsterm sc f
      for a in args do
        r ← `(LeanScript.Term.app $r $(← elabLsterm sc a))
      return r
  | e => if (tupleElems? e).isSome then elabTuple sc e
      else Macro.throwErrorAt e "unsupported term syntax"

/-- A record literal. -/
partial def elabTuple (sc : Scope) (e : TSyntax `lsterm) : MacroM Lean.Term := do
  let some es := tupleElems? e | Macro.throwErrorAt e "expected a record"
  `(LeanScript.Term.record_mk $(← mkArgs (← es.mapM (elabLsterm sc))))

/-- `fun x₁ … xₙ => b`. -/
partial def elabFun (sc : Scope) : List (TSyntax `lsbinder) → TSyntax `lsterm → MacroM Lean.Term
  | [], b => elabLsterm sc b
  | x :: xs, b => do
      match x with
      | `(lsbinder| ($x:binderIdent : $τ)) =>
          `(LeanScript.Term.lam (σ := [Ty| $τ]) $(← elabFun (binderName x :: sc) xs b))
      | `(lsbinder| $x:binderIdent) =>
          `(LeanScript.Term.lam $(← elabFun (binderName x :: sc) xs b))
      | _ => Macro.throwErrorAt x "unsupported binder"

/-- The body of a `fun x₁ … xₙ => b` given to a special form that binds `n` names. -/
partial def elabBinderBody (sc : Scope) (n : Nat) (form : String) :
    TSyntax `lsterm → MacroM Lean.Term
  | `(lsterm| ($e)) => elabBinderBody sc n form e
  | `(lsterm| fun $bs* => $b) => do
      let bs : Array (TSyntax `lsbinder) := bs
      let names ← bs.toList.mapM fun (x : TSyntax `lsbinder) => match x with
        | `(lsbinder| $x:binderIdent) => pure (binderName x)
        | x => Macro.throwErrorAt x s!"the binders of `{form}` take no type"
      unless names.length == n do
        Macro.throwErrorAt bs[0]! s!"`{form}` binds {n} name(s) here"
      elabLsterm (names.reverse ++ sc) b
  | e => Macro.throwErrorAt e s!"`{form}` expects `fun` binding {n} name(s) here"

/-- The branches of a fold (`data_rec`/`data_brec`): one `fun x => b` per member, or one
    Lean function `‹brs›`. -/
partial def elabFoldBranches (sc : Scope) (form : String) :
    List (TSyntax `lsterm) → MacroM Lean.Term
  | brs => do
      if let [t] := brs then
        if t.raw.isOfKind ``LeanScript.lstermEmbed then return ⟨t.raw[1]⟩
      let rhss ← brs.toArray.mapM (elabBinderBody sc 1 form)
      let pats ← (List.range brs.length).toArray.mapM fun i => `(⟨$(quote i), _⟩)
      `(fun $[| $pats => $rhss]*)

/-- `match e with | p => b …`: an enum when the patterns are numbers, a union otherwise. -/
partial def elabMatch (sc : Scope) (e : TSyntax `lsterm) (ps : List (TSyntax `lspat))
    (bs : List (TSyntax `lsterm)) : MacroM Lean.Term := do
  let e' ← elabLsterm sc e
  let isEnum := ps.any fun | `(lspat| $_:num) => true | _ => false
  if isEnum then
    let n := ps.length
    let rhss ← bs.toArray.mapM (elabLsterm sc)
    let pats ← ps.toArray.mapIdxM fun i p => do
      if i + 1 == n then `(_)
      else match p with
        | `(lspat| $k:num) => `($k:num)
        | _ => Macro.throwErrorAt p "expected a constructor number (only the last branch \
            may be `_`)"
    `(LeanScript.Term.enum_casesOn $e' (fun i => match i.val with $[| $pats => $rhss]*))
  else
    if ps.length < 2 then Macro.throwErrorAt e "a union has at least two constructors"
    let brs ← (ps.zip bs).mapM fun (p, b) => do
      let names ← match p with
        | `(lspat| ·) => pure []
        | `(lspat| $x:binderIdent) => pure [binderName x]
        | `(lspat| ($x, $xs,*)) => pure ((x :: xs.getElems.toList).map binderName)
        | _ => Macro.throwErrorAt p "expected `·`, a name or `(x, y, …)`"
      elabLsterm (names ++ sc) b
    let rec mk : List Lean.Term → MacroM Lean.Term
      | [a, b] => `(LeanScript.Branches.two $a $b)
      | a :: rest => do `(LeanScript.Branches.cons $a $(← mk rest))
      | [] => Macro.throwError "unreachable"
    `(LeanScript.Term.union_casesOn $e' $(← mk brs))

/-- A special form, applied to `args`. -/
partial def elabSpecial (sc : Scope) (id : Ident) (args : List (TSyntax `lsterm)) :
    MacroM Lean.Term := do
  let f := id.getId.eraseMacroScopes
  let bad {α : Type} (usage : String) : MacroM α :=
    Macro.throwErrorAt id s!"`{f}` is used as `{usage}`"
  match f, args with
  | `inj, [i] => do `(LeanScript.Term.inj $(← leanArg sc i) (args := LeanScript.Args.nil))
  | `inj, [i, a] => do
      let as ← match tupleElems? a with
        | some as => as.mapM (elabLsterm sc)
        | none => pure [← elabLsterm sc a]
      `(LeanScript.Term.inj $(← leanArg sc i) (args := $(← mkArgs as)))
  | `inj, _ => bad "inj i`, `inj i a` or `inj i (a, b, …)"
  | `enum, [i] => do `(LeanScript.Term.enum_mk _ $(← leanArg sc i))
  | `enum, _ => bad "enum i"
  | `natRec, [n, z, s] => do
      `(LeanScript.Term.nat_rec $(← elabLsterm sc n) $(← elabLsterm sc z)
          $(← elabBinderBody sc 2 "natRec" s))
  | `natRec, _ => bad "natRec n z (fun m ih => s)"
  | `foldl, [s, init, arr] => do
      `(LeanScript.Term.array_foldl $(← elabLsterm sc arr) $(← elabLsterm sc init)
          $(← elabBinderBody sc 2 "foldl" s))
  | `foldl, _ => bad "foldl (fun acc x => s) init arr"
  | `roll, [b, j, e] => do
      `(LeanScript.Term.data_in $(← leanArg sc b) $(← leanArg sc j) $(← elabLsterm sc e))
  | `roll, _ => bad "roll b j e"
  | `unroll, [b, j, e] => do
      `(LeanScript.Term.data_out $(← leanArg sc b) $(← leanArg sc j) $(← elabLsterm sc e))
  | `unroll, _ => bad "unroll b j e"
  | `fold, b :: ρ :: j :: e :: brs@(_ :: _) => do
      `(LeanScript.Term.data_rec $(← leanArg sc b) $(← leanArg sc ρ)
          $(← elabFoldBranches sc "fold" brs) $(← leanArg sc j) $(← elabLsterm sc e))
  | `fold, _ => bad "fold b ρ j e (fun x => br₀) …"
  | `brec, b :: ρ :: k :: j :: e :: brs@(_ :: _) => do
      `(LeanScript.Term.data_brec $(← leanArg sc b) $(← leanArg sc ρ) $(← leanArg sc k)
          $(← elabFoldBranches sc "brec" brs) $(← leanArg sc j) $(← elabLsterm sc e))
  | `brec, _ => bad "brec b ρ k j e (fun x => br₀) …"
  | `extern, name :: fn :: as => do
      `(LeanScript.Term.externOf $(← leanArg sc name) $(← mkArgs (← as.mapM (elabLsterm sc)))
          $(← leanArg sc fn))
  | `extern, _ => bad "extern \"name\" f a₁ … aₙ"
  | `lit, [p, v] => do `(LeanScript.Term.lit $(← leanArg sc p) $(← leanArg sc v) rfl)
  | `lit, _ => bad "lit p v"
  | _, _ => Macro.throwErrorAt id "unknown special form"

end

macro_rules
  | `([Term| $e]) => elabLsterm [] e

/-! ## Pretty-printing -/

open Meta PrettyPrinter Delaborator SubExpr

/-- A surface term with its precedence. -/
abbrev TSyn := TSyntax `lsterm × Nat

/-- The precedence of an application. -/
def appPrec : Nat := 100

/-- Parenthesize `s` when its precedence is below `req`. -/
def tparen (req : Nat) : TSyn → DelabM (TSyntax `lsterm)
  | (s, p) => if p < req then `(lsterm| ($s)) else pure s

/-- The name given to the variable bound at depth `d`: `x₀`, `x₁`, …. -/
def varName (d : Nat) : Name :=
  let sub := (toString d).toList.map fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080)
  Name.mkSimple ("x" ++ String.ofList sub)

/-- The names bound at depths `d`, `d + 1`, …, `d + n - 1`. -/
def freshNames (d n : Nat) : List Name := (List.range n).map (varName <| d + ·)

/-- A binder of the surface syntax. -/
def binderOf (x : Name) : DelabM (TSyntax ``Lean.binderIdent) := `(binderIdent| $(mkIdent x):ident)

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
  [(``Term.var, 5), (``Term.letE, 7), (``Term.lam, 6), (``Term.app, 7), (``Term.lit, 6),
   (``Term.extern, 8), (``Term.ite, 7), (``Term.nat_rec, 7), (``Term.enum_mk, 5),
   (``Term.enum_casesOn, 7), (``Term.record_mk, 6), (``Term.record_casesOn, 8),
   (``Term.union_mk, 10), (``Term.union_casesOn, 9), (``Term.array_mk, 5),
   (``Term.array_foldl, 8), (``Term.data_in, 6), (``Term.data_out, 6), (``Term.data_rec, 8),
   (``Term.data_brec, 9), (``Term.bvar, 6), (``Term.ofNat, 7), (``Term.inj, 9),
   (``Term.externOf, 8)]

/-- A pattern of `match` binding `names`. -/
def patOf : List Name → DelabM (TSyntax `lspat)
  | [] => `(lspat| ·)
  | [x] => do `(lspat| $(← binderOf x):binderIdent)
  | x :: xs => do
      let xs ← xs.toArray.mapM binderOf
      `(lspat| ($(← binderOf x), $xs,*))

/-- A Lean term, as an argument of a special form. -/
def leanArgSyn (sc : List Name) : DelabM (TSyntax `lsterm) := do
  let s ← delab
  match s with
  | `($n:num) => `(lsterm| $n:num)
  | `($str:str) => `(lsterm| $str:str)
  | `($id:ident) => if sc.contains id.getId then `(lsterm| ‹$s›) else `(lsterm| $id:ident)
  | _ => `(lsterm| ‹$s›)

/-- The application of the special form `f` to `args` (already parenthesized). -/
def mkAppSyn (f : Ident) (args : List (TSyntax `lsterm)) : DelabM (TSyntax `lsterm) := do
  let mut r ← `(lsterm| $f:ident)
  for a in args do
    r ← `(lsterm| $r $a)
  return r

/-- A record literal `(a, b, …)` from at least two components. -/
def mkTupleSyn (a : TSyntax `lsterm) (bs : Array (TSyntax `lsterm)) : DelabM (TSyntax `lsterm) :=
  `(lsterm| ($a, $bs,*))

mutual

/-- A Lean function applied to terms, `‹f›(a, b)`: the current expression is a global
    constant applied to implicit arguments, then to explicit arguments that are `Term`s. -/
partial def embedCall? (sc : List Name) : DelabM (Option (TSyntax `lsterm)) := do
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
    withNaryArg (n - k + j) do return (← delabLsterm sc false).1
  return some (← `(lsterm| ‹$f›($as,*)))

/-- The current expression, a `Term`, as a surface term in the scope `sc` (innermost
    first); `root` is whether it is the whole printed term (then an expression that is not
    in the notation fails, instead of being embedded as `‹…›`). -/
partial def delabLsterm (sc : List Name) (root : Bool) : DelabM TSyn := do
  let e := (← getExpr).consumeMData
  let other : DelabM TSyn := do
    if root then failure
    if let some s ← embedCall? sc then return (s, atomPrec)
    return (← leanArgSyn sc, atomPrec)
  let some c := e.getAppFn.constName? | other
  let some arity := termHeads.lookup c | other
  if e.getAppNumArgs != arity then return ← other
  let d := sc.length
  let sub (k : Nat) (sc' : List Name := sc) : DelabM TSyn := withArgFromEnd k (delabLsterm sc' false)
  let r : DelabM TSyn := do
    match c with
    | ``Term.var | ``Term.bvar =>
        let i ← if c == ``Term.var then (dbIndex? e.appArg!).getDM failure
          else (natLit? (e.getArg! 4)).getDM failure
        match sc[i]? with
        | some x => return (← `(lsterm| $(mkIdent x):ident), atomPrec)
        | none => return (← `(lsterm| #$(Syntax.mkNumLit (toString i)):num), atomPrec)
    | ``Term.ofNat =>
        let some n := natLit? (e.getArg! 5) | failure
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
        let p ← withArgFromEnd 3 (leanArgSyn sc)
        let v ← withArgFromEnd 2 (leanArgSyn sc)
        return (← `(lsterm| $(mkIdent `lit):ident $p $v), appPrec)
    | ``Term.lam =>
        -- merge the `fun`s
        let rec go (sc : List Name) (bs : Array (TSyntax `lsbinder)) : DelabM TSyn := do
          let e := (← getExpr).consumeMData
          if e.isAppOfArity ``Term.lam 6 then
            let x := varName sc.length
            let b ← if ← getPPOption getPPFunBinderTypes then do
                let (τ, _) ← withArgFromEnd 3 (delabLsty false)
                `(lsbinder| ($(← binderOf x) : $τ))
              else `(lsbinder| $(← binderOf x):binderIdent)
            withArgFromEnd 1 (go (x :: sc) (bs.push b))
          else
            let (body, _) ← delabLsterm sc false
            return (← `(lsterm| fun $bs* => $body), 0)
        go sc #[]
    | ``Term.app =>
        let f ← tparen appPrec (← sub 2)
        let a ← tparen (appPrec + 1) (← sub 1)
        return (← `(lsterm| $f $a), appPrec)
    | ``Term.letE =>
        let x := varName d
        let (v, _) ← sub 2
        let (b, _) ← sub 1 (x :: sc)
        return (← `(lsterm| let $(← binderOf x):binderIdent := $v; $b), 0)
    | ``Term.ite =>
        let (a, _) ← sub 3
        let (b, _) ← sub 2
        let (c, _) ← sub 1
        return (← `(lsterm| if $a then $b else $c), 0)
    | ``Term.nat_rec =>
        let n ← tparen (appPrec + 1) (← sub 3)
        let z ← tparen (appPrec + 1) (← sub 2)
        let m := varName d
        let ih := varName (d + 1)
        let (s, _) ← sub 1 (ih :: m :: sc)
        let f ← `(lsterm| (fun $(← `(lsbinder| $(← binderOf m):binderIdent)) $(← `(lsbinder| $(← binderOf ih):binderIdent)) => $s))
        return (← `(lsterm| $(mkIdent `natRec):ident $n $z $f), appPrec)
    | ``Term.enum_mk =>
        let i ← withArgFromEnd 1 (leanArgSyn sc)
        return (← `(lsterm| $(mkIdent `enum):ident $i), appPrec)
    | ``Term.record_mk =>
        let as ← withArgFromEnd 1 (delabArgs sc)
        match as with
        | a :: bs@(_ :: _) => return (← mkTupleSyn a bs.toArray, atomPrec)
        | _ => failure
    | ``Term.record_casesOn =>
        let n := 1 + (← fieldsLen (e.getArg! 4))
        let xs := freshNames d n
        let (v, _) ← sub 2
        let (b, _) ← sub 1 (xs ++ sc)
        match ← xs.mapM binderOf with
        | x :: ys@(_ :: _) => return (← `(lsterm| let ($x, $ys.toArray,*) := $v; $b), 0)
        | _ => failure
    | ``Term.union_mk | ``Term.inj =>
        let i ← if c == ``Term.inj then (natLit? (e.getArg! 6)).getDM failure
          else (ctorIxIndex? (e.getArg! 8)).getDM failure
        let as ← withArgFromEnd 1 (delabArgs sc)
        let i : TSyntax `lsterm ← `(lsterm| $(Syntax.mkNumLit (toString i)):num)
        match as with
        | [] => return (← `(lsterm| $(mkIdent `inj):ident $i), appPrec)
        | [a] =>
            let a ← if a.raw.isOfKind ``LeanScript.lstermTuple then `(lsterm| ($a))
              else do tparen (appPrec + 1) (a, ← precOf a)
            return (← `(lsterm| $(mkIdent `inj):ident $i $a), appPrec)
        | a :: bs => return (← `(lsterm| $(mkIdent `inj):ident $i $(← mkTupleSyn a bs.toArray)), appPrec)
    | ``Term.union_casesOn =>
        let (v, _) ← sub 2
        let brs ← withArgFromEnd 1 (delabBranches sc)
        let ps := (brs.map (·.1)).toArray
        let bs := (brs.map (·.2)).toArray
        return (← `(lsterm| match $v with $[| $ps => $bs]*), 0)
    | ``Term.enum_casesOn =>
        let (v, _) ← sub 2
        let bs ← withArgFromEnd 1 (underLams (delabMatchAlts sc))
        let n := bs.length
        let bs := bs.toArray
        let ps ← (List.range n).toArray.mapM fun i => do
          if i + 1 == n then `(lspat| $(← `(binderIdent| _)):binderIdent)
          else `(lspat| $(Syntax.mkNumLit (toString i)):num)
        return (← `(lsterm| match $v with $[| $ps => $bs]*), 0)
    | ``Term.array_mk =>
        let es ← withArgFromEnd 1 (delabElems sc)
        return (← `(lsterm| #[$es.toArray,*]), atomPrec)
    | ``Term.array_foldl =>
        let arr ← tparen (appPrec + 1) (← sub 3)
        let init ← tparen (appPrec + 1) (← sub 2)
        let acc := varName d
        let x := varName (d + 1)
        let (s, _) ← sub 1 (x :: acc :: sc)
        let f ← `(lsterm| (fun $(← `(lsbinder| $(← binderOf acc):binderIdent)) $(← `(lsbinder| $(← binderOf x):binderIdent)) => $s))
        return (← `(lsterm| $(mkIdent `foldl):ident $f $init $arr), appPrec)
    | ``Term.data_in | ``Term.data_out =>
        let b ← withArgFromEnd 3 (leanArgSyn sc)
        let j ← withArgFromEnd 2 (leanArgSyn sc)
        let v ← tparen (appPrec + 1) (← sub 1)
        let f := mkIdent (if c == ``Term.data_in then `roll else `unroll)
        return (← `(lsterm| $f:ident $b $j $v), appPrec)
    | ``Term.data_rec | ``Term.data_brec =>
        let brec := c == ``Term.data_brec
        let b ← withArgFromEnd (if brec then 6 else 5) (leanArgSyn sc)
        let ρ ← withArgFromEnd (if brec then 5 else 4) (leanArgSyn sc)
        let k ← if brec then some <$> withArgFromEnd 4 (leanArgSyn sc) else pure none
        let j ← withArgFromEnd 2 (leanArgSyn sc)
        let v ← tparen (appPrec + 1) (← sub 1)
        let x := varName d
        let brs ← withArgFromEnd 3 (do
            let alts ← underLams (delabMatchAlts (x :: sc))
            alts.toArray.mapM fun br => do
              `(lsterm| (fun $(← `(lsbinder| $(← binderOf x):binderIdent)) => $br)))
          <|> (do return #[← withArgFromEnd 3 (do `(lsterm| ‹$(← delab)›))])
        match k with
        | some k => return (← mkAppSyn (mkIdent `brec) ([b, ρ, k, j, v] ++ brs.toList), appPrec)
        | none => return (← mkAppSyn (mkIdent `fold) ([b, ρ, j, v] ++ brs.toList), appPrec)
    | ``Term.extern | ``Term.externOf =>
        let ext := c == ``Term.extern
        let name ← withArgFromEnd 3 (leanArgSyn sc)
        let f ← withArgFromEnd (if ext then 2 else 1) (leanArgSyn sc)
        let as ← withArgFromEnd (if ext then 1 else 2) (delabArgs sc)
        let as ← as.toArray.mapM fun a => do tparen (appPrec + 1) (a, ← precOf a)
        return (← mkAppSyn (mkIdent `extern) ([name, f] ++ as.toList), appPrec)
    | _ => failure
  r <|> other

/-- The arguments of a constructor or an extern. -/
partial def delabArgs (sc : List Name) : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Args.nil 3 then return []
  else if e.isAppOfArity ``Args.cons 7 then
    return (← withArgFromEnd 2 (delabLsterm sc false)).1 :: (← withArgFromEnd 1 (delabArgs sc))
  else failure

/-- The elements of an array literal. -/
partial def delabElems (sc : List Name) : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Elems.nil 4 then return []
  else if e.isAppOfArity ``Elems.cons 6 then
    return (← withArgFromEnd 2 (delabLsterm sc false)).1 :: (← withArgFromEnd 1 (delabElems sc))
  else failure

/-- The branches of a union's case analysis, with their patterns. -/
partial def delabBranches (sc : List Name) :
    DelabM (List (TSyntax `lspat × TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let branch (c : Expr) (k : Nat) : DelabM (TSyntax `lspat × TSyntax `lsterm) := do
    let xs := freshNames sc.length (← ctorBinds c)
    return (← patOf xs, (← withArgFromEnd k (delabLsterm (xs ++ sc) false)).1)
  if e.isAppOfArity ``Branches.two 10 then
    return [← branch (e.getArg! 5) 2, ← branch (e.getArg! 6) 1]
  else if e.isAppOfArity ``Branches.cons 10 then
    return (← branch (e.getArg! 5) 2) :: (← withArgFromEnd 1 (delabBranches sc))
  else failure

/-- The right-hand sides of the alternatives of a `match` (the current expression), each a
    `Term` in the scope `sc`. -/
partial def delabMatchAlts (sc : List Name) : DelabM (List (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let some c := e.getAppFn.constName? | failure
  let some info ← getMatcherInfo? c | failure
  let first := info.numParams + 1 + info.numDiscrs
  unless e.getAppNumArgs == first + info.numAlts do failure
  (List.range info.numAlts).mapM fun i =>
    withNaryArg (first + i) (underLams do return (← delabLsterm sc false).1)

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
  let (s, _) ← delabLsterm [] true
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

end LeanScript.Notation

end
