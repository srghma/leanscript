module

public import LeanScript.Term.TermSubst
public import LeanScript.TyElab.Notation
public meta import LeanScript.TermElab.Anf
public meta import Lean.Meta.Match.MatcherInfo

@[expose] public section

set_option autoImplicit false

/-!
# `[Term| …]`: a thin direct-style notation for A-normal terms, and its pretty-printer

`[Term| e]` elaborates the surface syntax `e` to a `LeanScript.Term Δ Γ τ js` (the signature,
context, type and join points are left to unification with the expected type).  When the
expected type is a `PExpr` or a `Comp`, it elaborates to one of those instead.

The surface syntax is in **direct style**: any term can be an operand of any other.  It is
normalised (`LeanScript.TermElab.Anf`) into the strictly A-normal and B-normal grammar of `Term`: every
call, closure, fold and delay is named by a `let` in evaluation order, a pure value bound by a
`let` is used in place when it is a variable or a literal and shared otherwise, and a branch in
the middle of a computation gets a join point for the rest of it.  A term that is already
A-normal is read back unchanged, so every printed term reads back as the same term.

The notation follows the datatype closely: variables are **de Bruijn indices** `#i` (no names
are bound or captured), join points `^i`, binders are written `_`, and the forms without
dedicated syntax are the constructors' own names with the constructors' own argument order.
Every term built from the constructors of the three layers is printed back in the same
notation (`set_option pp.leanscript false` turns that off).

| surface syntax                           | A-normal term                                    |
|------------------------------------------|--------------------------------------------------|
| `#i`                                     | `PExpr.bvar i` (`.var` of de Bruijn index `i`)    |
| `fun _ (_ : τ) => e`                     | `Comp.lam (let _ := Comp.lam e; #0)` (`τ` in the `[Ty| …]` syntax) |
| `f a b`                                  | `let _ := Comp.app f a; let _ := Comp.app #0 b; #0` |
| `let _ := e; b`, `let _ : τ := e; b`     | `Term.letE e b`; `Comp.share e` for a compound pure `e`; `b` with `e` in place for a variable or a literal |
| `3`, `"s"`, `true`, `false`              | `PExpr.ofNat 3`, `.lit .string "s"`, `.lit .bool true`, … |
| `lit p v`                                | `PExpr.lit p v`                                  |
| `extern "name" f a b`                    | `Comp.extern "name" f` of the arguments `a`, `b` (`Comp.externOf`) |
| `pextern "name" f a b`                   | the cheap extern `PExpr.extern "name" f` of the arguments `a`, `b` (`PExpr.externOf`), a pure expression |
| `if c then a else b`                     | `Term.ite c a b` (with a join point when not in tail position) |
| `cond c a b`                             | the pure conditional `PExpr.cond c a b` (`a`, `b` must be pure) |
| `nat_rec n z s`                          | `Comp.nat_rec n z s`                             |
| `enum_mk i`                              | `PExpr.enum_mk _ i`                              |
| `match e with \| 0 => a \| 1 => b \| _ => c` | `Term.enum_casesOn` (the last branch is the default) |
| `(a, b, c)`                              | `PExpr.record_mk` of the fields `a`, `b`, `c`    |
| `let (_, _, _) := e; b`                  | `Term.record_casesOn e b`                        |
| `union_mk i a b`                         | `PExpr.union_mk` of constructor `i` (by position) of the arguments `a`, `b` (`PExpr.inj`) |
| `match e with \| · => a \| _ => b \| (_, _) => c` | `Term.union_casesOn e` of the branches `a`, `b`, `c` |
| `#[a, b]`                                | `PExpr.array_mk` of the elements                 |
| `array_foldl arr init s`                 | `Comp.array_foldl arr init s`                    |
| `data_in b j e`, `data_out b j e`        | `PExpr.data_in b j e`, `PExpr.data_out b j e`    |
| `data_rec b ρ br₀ … brₖ j e`             | `Comp.data_rec b ρ brs j e`, branch `i` of `brs` is `brᵢ` |
| `data_brec b ρ k br₀ … brₖ j e`          | `Comp.data_brec b ρ k brs j e`                   |
| `thunk_mk e`, `thunk_force e`           | `Comp.thunk_mk e`, `Comp.thunk_force e` (a `Thunk τ`) |
| `lazy_mk e`, `lazy_force e`              | `Comp.lazy_mk e`, `Comp.lazy_force e` (a `Unit → τ`) |
| `join _ (_ : τ) := b; m`                 | `Term.join τ b m`: `b` sees the parameter as `#0`, `m` the join point as `^0` |
| `jump ^j e`                              | `Term.jump j e`                                  |
| `(e : τ)`                                | `e`, at the type `τ` (in the `[Ty| …]` syntax)   |
| `‹t›`                                    | the Lean term `t`: a `PExpr`, a `Comp` (named by a `let`) or a `Term Δ Γ τ []` (in tail position itself, elsewhere bound by a join point, `Term.retJump`) |
| `‹f›(a, b)`                              | the Lean term `f a b`: a Lean function of pure expressions, to a `PExpr` or a `Comp` |

**Variables and binders.**  A variable is only ever `#i`, the de Bruijn index of the
source (`0` is the innermost binder); an identifier is never a variable, and never a Lean
term either: every Lean term, even a single name, is written `‹t›`.  The binders follow the
constructors: in `nat_rec n z s` the step `s` sees the answer as `#0` and the predecessor as
`#1`; in `array_foldl arr init s` it sees the element as `#0` and the accumulator as `#1`;
`let (_, _) := e; b` and the patterns of a union see the fields with the first field innermost
(`#0`); a branch of `data_rec`/`data_brec` sees the member's body as `#0`.  The `_`s of a
pattern give the number of variables it binds, which must be the number of fields.  The
indices are those of the source: the normaliser renumbers them past the `let`s and join points
it adds.  A Lean term `‹t›` is in the enclosing context: it is shifted past all the binders
around it (`PExpr.shift`), unless it is generic in its context (`sumT : {Γ : Ctx ks} → …`),
when it is used as it is.

**Lean arguments.**  In `lit`, `extern`, `pextern`, `enum_mk`, `union_mk`, `data_in`, `data_out`,
`data_rec` and `data_brec` the leaf, value, name, function, constructor number, block,
member, answer types and depth are Lean terms: a number, a string or `‹t›`.  The branches of
`data_rec`/`data_brec` can also be given as one Lean function `‹brs›`.

**Delays.**  The type of `thunk_force e` / `lazy_force e` does not fix the type of `e` (the
contents `τ` of the delay are not recovered from the result type `τ.relax` by unification), so
when nothing else does, `e` is written with its type: `thunk_force (#0 : Thunk Nat)`.

A numeral takes its leaf type from the expected type (`PExpr.ofNat`), so its type must be
known from the context: `let _ := 3; ‹addT›(#0, #0)` works.
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

/-- Constructor `i` of a union, from its fields: `PExpr.inj 1 (.cons x .nil)`. -/
abbrev PExpr.inj {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} (i : Nat) (hi : i < bs.length := by decide)
    (args : Args Δ Γ (cs.nth i).binds) : PExpr Δ Γ (.union cs (h := h)) :=
  .union_mk (cs.ix i hi) args

/-- A numeral of a leaf type: `PExpr.ofNat 3 : PExpr Δ Γ .nat`.  Unlike `PExpr.lit`, the leaf
    is found by unification with the expected type, so the numeral can be written before its
    type is known. -/
abbrev PExpr.ofNat {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {p : LeanPrimTy}
    (n : Nat) [OfNat p.denote n] : PExpr Δ Γ (.prim p) :=
  .lit p (OfNat.ofNat n)

/-- `Comp.extern` with the arguments before the function: the types of the arguments are
    known when the function is elaborated, so `fun v => Nat.add v.1 v.2` needs no annotation. -/
abbrev Comp.externOf {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {σs : List (Ty ks)} {τ : Ty ks}
    (name : String) (args : Args Δ Γ σs) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) :
    Comp Δ Γ τ :=
  .extern name f args

/-- `PExpr.extern` (a cheap extern) with the arguments before the function, as
    `Comp.externOf`. -/
abbrev PExpr.externOf {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {σs : List (Ty ks)} {τ : Ty ks}
    (name : String) (args : Args Δ Γ σs) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) :
    PExpr Δ Γ τ :=
  .extern name f args

/-! ## Syntax -/

/-- The surface syntax of a term (`[Term| …]`). -/
declare_syntax_cat lsterm
/-- A binder of `fun` and `join`: `_`, or `(_ : τ)`. -/
declare_syntax_cat lsbinder
/-- A placeholder for a bound variable: `_`. -/
declare_syntax_cat lshole
/-- A pattern of `match`. -/
declare_syntax_cat lspat

/-- A variable, by de Bruijn index. -/
syntax:max (name := lstermBVar) "#" noWs num : lsterm
/-- A join point, by de Bruijn index (only as the first argument of `jump`). -/
syntax:max (name := lstermJVar) "^" noWs num : lsterm
/-- A constructor name (`nat_rec`, …), or `true`/`false`. -/
syntax:max ident : lsterm
/-- A literal. -/
syntax:max num : lsterm
/-- A literal. -/
syntax:max str : lsterm
/-- A Lean term of type `PExpr Δ Γ τ`, `Comp Δ Γ τ` or `Term Δ Γ τ []`. -/
syntax:max (name := lstermEmbed) "‹" term "›" : lsterm
/-- A Lean function of pure expressions, applied: `‹f›(a, b)` is `f a b`. -/
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
/-- `join _ x := body; main`: a join point (the first `_`), whose parameter is `x`. -/
syntax (name := lstermJoin) "join " "_ " lsbinder " := " lsterm "; " lsterm : lsterm

syntax "·" : lspat
syntax "_" : lspat
syntax "(" lshole ", " lshole,+ ")" : lspat
syntax num : lspat
syntax (name := lstermMatch) "match " lsterm " with" (ppDedent(ppLine) " | " lspat " => " lsterm)+ : lsterm

/-- `[Term| e]`: the term written in the surface syntax `e` (see the module doc). -/
syntax:max (name := lstermQuote) "[Term| " lsterm "]" : term

end LeanScript

meta section

namespace LeanScript.Notation

open Lean Meta Elab Term
open LeanScript.Anf (Src Atom)

/-! ## Elaboration: surface syntax → source tree → A-normal term -/

/-- The constructors written as an application of their name. -/
def specialForms : List Name :=
  [`lit, `extern, `pextern, `cond, `nat_rec, `enum_mk, `union_mk, `array_foldl, `data_in, `data_out, `data_rec,
   `data_brec, `thunk_mk, `thunk_force, `lazy_mk, `lazy_force, `jump]

/-- The arguments of a constructor or an extern. -/
def mkArgs : List Lean.Term → MetaM Lean.Term
  | [] => `(LeanScript.Args.nil)
  | t :: ts => do `(LeanScript.Args.cons $t $(← mkArgs ts))

/-- The elements of an array. -/
def mkElems : List Lean.Term → MetaM Lean.Term
  | [] => `(LeanScript.Elems.nil)
  | t :: ts => do `(LeanScript.Elems.cons $t $(← mkElems ts))

/-- The head and the arguments of an application. -/
partial def appSpine (e : TSyntax `lsterm) (args : List (TSyntax `lsterm) := []) :
    TSyntax `lsterm × List (TSyntax `lsterm) :=
  match e with
  | `(lsterm| $f $a) => appSpine f (a :: args)
  | _ => (e, args)

/-- A Lean term given as an argument of a constructor: a number, a string or `‹t›`. -/
partial def leanArg : TSyntax `lsterm → TermElabM Lean.Term
  | `(lsterm| $n:num) => pure n
  | `(lsterm| $s:str) => pure s
  | `(lsterm| ‹$t›) => pure t
  | `(lsterm| ($t)) => leanArg t
  | t => throwErrorAt t "expected a Lean term here: a number, a string or `‹term›`"

/-- The components of a record literal `(a, b, …)`, or `none`. -/
def tupleElems? (e : TSyntax `lsterm) : Option (List (TSyntax `lsterm)) :=
  if e.raw.isOfKind ``LeanScript.lstermTuple then
    some (e.raw[1] :: e.raw[3].getSepArgs.toList |>.map (⟨·⟩))
  else none

/-- Which layer a Lean term (or the result of a Lean function) belongs to: `PExpr`, `Comp` or
    `Term`, from its type; `PExpr` when the type cannot be found alone.  Also whether the term
    is generic in its context (the context in its type is still unknown), so that it can be
    used at any depth without a shift. -/
def layerOf (t : Lean.Term) : TermElabM (Name × Bool) := do
  let r ← try
      withoutModifyingState <| withoutErrToSorry do
        let e ← elabTerm t none
        let ty ← instantiateMVars (← inferType e)
        forallTelescopeReducing ty fun _ r => do
          let r ← whnfR r
          let poly := r.getAppNumArgs > 2 && (r.getArg! 2).consumeMData.getAppFn.isMVar
          return some (r.getAppFn.constName?, poly)
    catch _ => pure none
  let (c, poly) := r.getD (none, false)
  match c with
  | some ``LeanScript.Comp => return (``LeanScript.Comp, poly)
  | some ``LeanScript.Term => return (``LeanScript.Term, poly)
  | _ => return (``LeanScript.PExpr, poly)

/-- An application of a function value, as a computation. -/
def appSrc (f a : Src) : Src :=
  .comp (fun as _ => `(LeanScript.Comp.app $(as[0]!) $(as[1]!))) #[f, a] #[]

/-- `fun x => body`, as a computation; `ty?` the type of `x`. -/
def lamSrc (ty? : Option Lean.Term) (body : Src) : Src :=
  .comp (fun _ bs => match ty? with
      | some τ => `(LeanScript.Comp.lam (σ := $τ) $(bs[0]!))
      | none => `(LeanScript.Comp.lam $(bs[0]!)))
    #[] #[(1, body)]

/-- The number of variables a pattern of a union binds. -/
def patBinds (p : TSyntax `lspat) : TermElabM Nat :=
  match p with
  | `(lspat| ·) => pure 0
  | `(lspat| _) => pure 1
  | `(lspat| ($_, $hs,*)) => pure (hs.getElems.size + 1)
  | _ => throwErrorAt p "expected `·`, `_` or `(_, _, …)`"

mutual

/-- The source tree of a surface term. -/
partial def toSrc : TSyntax `lsterm → TermElabM Src
  | `(lsterm| #$n:num) => pure (.var n.getNat)
  | `(lsterm| ^$n:num) => throwErrorAt n "a join point `^i` is only the first argument of `jump`"
  | `(lsterm| $n:num) => do return .atom (.leaf (← `(LeanScript.PExpr.ofNat $n)))
  | `(lsterm| $s:str) => do
      return .atom (.leaf (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.string $s)))
  | `(lsterm| ‹$t›) => do
      let (layer, poly) ← layerOf t
      match layer with
      | ``LeanScript.Comp => return .embedComp t poly
      | ``LeanScript.Term => return .embedTerm t poly
      | _ => return .atom (.embed t poly)
  | `(lsterm| ‹$f›($as,*)) => do
      let as ← as.getElems.mapM toSrc
      match (← layerOf f).1 with
      | ``LeanScript.Comp => return .comp (fun xs _ => `($f $xs*)) as #[]
      | ``LeanScript.Term => throwErrorAt f "a Lean function to `Term` cannot be applied in the \
          notation: embed its application `‹f a b›` instead"
      | _ => return .pnode (fun xs => `($f $xs*)) as
  | `(lsterm| ($e)) => toSrc e
  | `(lsterm| ($e : $τ)) => do return .ascribe (← toSrc e) (← `([Ty| $τ]))
  | `(lsterm| #[$es,*]) => do
      return .pnode (fun xs => do `(LeanScript.PExpr.array_mk $(← mkElems xs.toList)))
        (← es.getElems.mapM toSrc)
  | `(lsterm| fun $bs* => $b) => funSrc bs.toList b
  | `(lsterm| let _ := $e; $b) => do return .letE (← toSrc e) (← toSrc b)
  | `(lsterm| let _ : $τ := $e; $b) => do
      return .letE (.ascribe (← toSrc e) (← `([Ty| $τ]))) (← toSrc b)
  | `(lsterm| let ($_, $hs,*) := $e; $b) => do
      return .destruct (← toSrc e) (hs.getElems.size + 1) (← toSrc b)
        fun p body => `(LeanScript.Term.record_casesOn $p $body)
  | `(lsterm| if $c then $a else $b) => do
      return .cases none (← toSrc c) #[(0, ← toSrc a), (0, ← toSrc b)] none
        fun c bs => `(LeanScript.Term.ite $c $(bs[0]!) $(bs[1]!))
  | `(lsterm| join _ $x := $body; $main) => do
      let ty? ← match x with
        | `(lsbinder| (_ : $τ)) => some <$> `([Ty| $τ])
        | _ => pure none
      return .join ty? (← toSrc body) (← toSrc main)
  | `(lsterm| match $e with $[| $ps => $bs]*) => matchSrc e ps.toList bs.toList
  | `(lsterm| $id:ident) =>
      match id.getId.eraseMacroScopes with
      | `true => do return .atom (.leaf (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)))
      | `false => do
          return .atom (.leaf (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)))
      | _ => specialSrc id []
  | e@`(lsterm| $_ $_) => do
      match tupleElems? e with
      | some _ => tupleSrc e
      | none =>
      let (f, args) := appSpine e
      if let `(lsterm| $id:ident) := f then
        if specialForms.contains id.getId.eraseMacroScopes then
          return ← specialSrc id args
      let mut r ← toSrc f
      for a in args do
        r := appSrc r (← toSrc a)
      return r
  | e => if (tupleElems? e).isSome then tupleSrc e
      else throwErrorAt e "unsupported term syntax"

/-- A record literal. -/
partial def tupleSrc (e : TSyntax `lsterm) : TermElabM Src := do
  let some es := tupleElems? e | throwErrorAt e "expected a record"
  return .pnode (fun xs => do `(LeanScript.PExpr.record_mk $(← mkArgs xs.toList)))
    (← es.toArray.mapM toSrc)

/-- `fun _ … _ => b`. -/
partial def funSrc : List (TSyntax `lsbinder) → TSyntax `lsterm → TermElabM Src
  | [], b => toSrc b
  | x :: xs, b => do
      match x with
      | `(lsbinder| (_ : $τ)) => return lamSrc (some (← `([Ty| $τ]))) (← funSrc xs b)
      | `(lsbinder| _) => return lamSrc none (← funSrc xs b)
      | _ => throwErrorAt x "unsupported binder"

/-- The branches of `data_rec`/`data_brec`: one statement per member (binding its body), or
    one Lean function `‹brs›`. -/
partial def recBranches (brs : List (TSyntax `lsterm)) :
    TermElabM (Array (Nat × Src) × Option Lean.Term) := do
  if let [t] := brs then
    if t.raw.isOfKind ``LeanScript.lstermEmbed then return (#[], some ⟨t.raw[1]⟩)
  return ((← brs.toArray.mapM toSrc).map (1, ·), none)

/-- `fun | ⟨0, _⟩ => b₀ | ⟨1, _⟩ => b₁ | …`, or the Lean function given. -/
partial def recBranchFun (bs : Array Lean.Term) (given? : Option Lean.Term) :
    MetaM Lean.Term := do
  if let some f := given? then return f
  let pats ← (List.range bs.size).toArray.mapM fun i => `(⟨$(quote i), _⟩)
  `(fun $[| $pats => $bs]*)

/-- `match e with | p => b …`: an enum when the patterns are numbers, a union otherwise. -/
partial def matchSrc (e : TSyntax `lsterm) (ps : List (TSyntax `lspat))
    (bs : List (TSyntax `lsterm)) : TermElabM Src := do
  let e' ← toSrc e
  let isEnum := ps.any fun | `(lspat| $_:num) => true | _ => false
  if isEnum then
    let n := ps.length
    let pats ← ps.toArray.mapIdxM fun i p => do
      if i + 1 == n then `(_)
      else match p with
        | `(lspat| $k:num) => `($k:num)
        | _ => throwErrorAt p "expected a constructor number (only the last branch may be `_`)"
    let brs ← bs.toArray.mapM fun b => return (0, ← toSrc b)
    return .cases none e' brs none fun c rhss =>
      `(LeanScript.Term.enum_casesOn $c (fun i => match i.val with $[| $pats => $rhss]*))
  else
    if ps.length < 2 then throwErrorAt e "a union has at least two constructors"
    let brs ← (ps.zip bs).toArray.mapM fun (p, b) => return (← patBinds p, ← toSrc b)
    let rec mk : List Lean.Term → MetaM Lean.Term
      | [a, b] => `(LeanScript.Branches.two $a $b)
      | a :: rest => do `(LeanScript.Branches.cons $a $(← mk rest))
      | [] => throwError "unreachable"
    return .cases none e' brs none fun c rhss => do
      `(LeanScript.Term.union_casesOn $c $(← mk rhss.toList))

/-- A constructor, applied to `args`. -/
partial def specialSrc (id : Ident) (args : List (TSyntax `lsterm)) : TermElabM Src := do
  let f := id.getId.eraseMacroScopes
  let bad {α : Type} (usage : String) : TermElabM α :=
    throwErrorAt id s!"`{f}` is used as `{usage}`"
  match f, args with
  | `lit, [p, v] => do return .atom (.leaf (← `(LeanScript.PExpr.lit $(← leanArg p) $(← leanArg v))))
  | `lit, _ => bad "lit p v"
  | `extern, name :: fn :: as => do
      let name ← leanArg name
      let fn ← leanArg fn
      return .comp (fun xs _ => do `(LeanScript.Comp.externOf $name $(← mkArgs xs.toList) $fn))
        (← as.toArray.mapM toSrc) #[]
  | `extern, _ => bad "extern \"name\" f a₁ … aₙ"
  | `pextern, name :: fn :: as => do
      let name ← leanArg name
      let fn ← leanArg fn
      return .pnode (fun xs => do `(LeanScript.PExpr.externOf $name $(← mkArgs xs.toList) $fn))
        (← as.toArray.mapM toSrc)
  | `pextern, _ => bad "pextern \"name\" f a₁ … aₙ"
  | `cond, [c, a, b] => do
      return .pnode (fun xs => `(LeanScript.PExpr.cond $(xs[0]!) $(xs[1]!) $(xs[2]!)))
        #[← toSrc c, ← toSrc a, ← toSrc b]
  | `cond, _ => bad "cond c a b"
  | `nat_rec, [n, z, s] => do
      return .comp (fun xs bs => `(LeanScript.Comp.nat_rec $(xs[0]!) $(xs[1]!) $(bs[0]!)))
        #[← toSrc n, ← toSrc z] #[(2, ← toSrc s)]
  | `nat_rec, _ => bad "nat_rec n z s"
  | `enum_mk, [i] => do return .atom (.leaf (← `(LeanScript.PExpr.enum_mk _ $(← leanArg i))))
  | `enum_mk, _ => bad "enum_mk i"
  | `union_mk, i :: as => do
      let i ← leanArg i
      return .pnode (fun xs => do `(LeanScript.PExpr.inj $i (args := $(← mkArgs xs.toList))))
        (← as.toArray.mapM toSrc)
  | `union_mk, _ => bad "union_mk i a₁ … aₙ"
  | `array_foldl, [arr, init, s] => do
      return .comp (fun xs bs => `(LeanScript.Comp.array_foldl $(xs[0]!) $(xs[1]!) $(bs[0]!)))
        #[← toSrc arr, ← toSrc init] #[(2, ← toSrc s)]
  | `array_foldl, _ => bad "array_foldl arr init s"
  | `data_in, [b, j, e] => do
      let b ← leanArg b
      let j ← leanArg j
      return .pnode (fun xs => `(LeanScript.PExpr.data_in $b $j $(xs[0]!))) #[← toSrc e]
  | `data_in, _ => bad "data_in b j e"
  | `data_out, [b, j, e] => do
      let b ← leanArg b
      let j ← leanArg j
      return .pnode (fun xs => `(LeanScript.PExpr.data_out $b $j $(xs[0]!))) #[← toSrc e]
  | `data_out, _ => bad "data_out b j e"
  | `data_rec, b :: ρ :: rest@(_ :: _ :: _ :: _) => do
      let b ← leanArg b
      let ρ ← leanArg ρ
      let (brs, given?) ← recBranches (rest.take (rest.length - 2))
      let j ← leanArg rest[rest.length - 2]!
      let e ← toSrc rest[rest.length - 1]!
      return .comp (fun xs bs => do
          `(LeanScript.Comp.data_rec $b $ρ $(← recBranchFun bs given?) $j $(xs[0]!)))
        #[e] brs
  | `data_rec, _ => bad "data_rec b ρ br₀ … brₖ j e"
  | `data_brec, b :: ρ :: k :: rest@(_ :: _ :: _ :: _) => do
      let b ← leanArg b
      let ρ ← leanArg ρ
      let k ← leanArg k
      let (brs, given?) ← recBranches (rest.take (rest.length - 2))
      let j ← leanArg rest[rest.length - 2]!
      let e ← toSrc rest[rest.length - 1]!
      return .comp (fun xs bs => do
          `(LeanScript.Comp.data_brec $b $ρ $k $(← recBranchFun bs given?) $j $(xs[0]!)))
        #[e] brs
  | `data_brec, _ => bad "data_brec b ρ k br₀ … brₖ j e"
  | `thunk_mk, [e] => do
      return .comp (fun _ bs => `(LeanScript.Comp.thunk_mk $(bs[0]!))) #[] #[(0, ← toSrc e)]
  | `thunk_mk, _ => bad "thunk_mk e"
  | `thunk_force, [e] => do
      return .comp (fun xs _ => `(LeanScript.Comp.thunk_force $(xs[0]!))) #[← toSrc e] #[]
  | `thunk_force, _ => bad "thunk_force e"
  | `lazy_mk, [e] => do
      return .comp (fun _ bs => `(LeanScript.Comp.lazy_mk $(bs[0]!))) #[] #[(0, ← toSrc e)]
  | `lazy_mk, _ => bad "lazy_mk e"
  | `lazy_force, [e] => do
      return .comp (fun xs _ => `(LeanScript.Comp.lazy_force $(xs[0]!))) #[← toSrc e] #[]
  | `lazy_force, _ => bad "lazy_force e"
  | `jump, [j, e] =>
      match j with
      | `(lsterm| ^$n:num) => do return .jump n.getNat (← toSrc e)
      | _ => bad "jump ^j e"
  | `jump, _ => bad "jump ^j e"
  | _, _ => throwErrorAt id s!"unknown constructor `{f}`: a variable is written `#i` \
      and a Lean term `‹{f}›`"

end

/-- `[Term| e]`: normalised to a pure expression, a computation or a statement, following the
    expected type (a statement when it is not known). -/
@[term_elab lstermQuote]
def elabTermQuote : TermElab := fun stx expected? => do
  -- the layer is chosen by the expected type: wait for it when it is not known yet
  tryPostponeIfNoneOrMVar expected?
  let s ← toSrc ⟨stx[1]⟩
  let layer ← match expected? with
    | some t => pure (← whnfR (← instantiateMVars t)).getAppFn.constName?
    | none => pure none
  let out ← match layer with
    | some ``LeanScript.PExpr => s.toPExpr
    | some ``LeanScript.Comp => s.toComp
    | _ => s.toTerm
  let e ← withRef stx <| elabTerm out expected?
  Anf.unfoldOfComp e

/-! ## Pretty-printing -/

open PrettyPrinter Delaborator SubExpr

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

/-- The heads the notation prints, in the three layers. -/
def termHeads : List Name :=
  [``PExpr.var, ``PExpr.bvar, ``PExpr.lit, ``PExpr.ofNat, ``PExpr.enum_mk, ``PExpr.record_mk,
   ``PExpr.union_mk, ``PExpr.inj, ``PExpr.array_mk, ``PExpr.data_in, ``PExpr.data_out,
   ``PExpr.cond, ``PExpr.extern, ``PExpr.externOf,
   ``Comp.app, ``Comp.lam, ``Comp.share, ``Comp.extern, ``Comp.externOf, ``Comp.nat_rec,
   ``Comp.array_foldl, ``Comp.data_rec, ``Comp.data_brec, ``Comp.thunk_mk, ``Comp.thunk_force,
   ``Comp.lazy_mk, ``Comp.lazy_force,
   ``Term.ret, ``Term.letE, ``Term.record_casesOn, ``Term.ite, ``Term.enum_casesOn,
   ``Term.union_casesOn, ``Term.join, ``Term.jump, ``Term.ofComp]

/-- The number of arguments of a fully applied head. -/
def headArity (c : Name) : MetaM Nat := do
  return (← getConstInfo c).type.getForallBinderNames.length

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

/-- Is `e` one of the three layers, `Args` or `Elems`? -/
def isLayerType (ty : Expr) : Bool :=
  ty.isAppOf ``LeanScript.PExpr || ty.isAppOf ``LeanScript.Comp || ty.isAppOf ``LeanScript.Term

/-- Is `e` the statement `ret #0`? -/
def isRetVar0 (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``Term.ret 6 &&
    ((e.getArg! 5).consumeMData.isAppOfArity ``PExpr.var 5 &&
      dbIndex? (e.getArg! 5).consumeMData.appArg! == some 0)

mutual

/-- A Lean function applied to pure expressions, `‹f›(a, b)`: the current expression is a
    global constant applied to implicit arguments, then to explicit arguments that are pure
    expressions. -/
partial def embedCall? : DelabM (Option (TSyntax `lsterm)) := do
  let e := (← getExpr).consumeMData
  let some c := e.getAppFn.constName? | return none
  if termHeads.contains c then return none
  let args := e.getAppArgs
  let n := args.size
  if n == 0 then return none
  let info ← getFunInfoNArgs e.getAppFn n
  let explicit (i : Nat) : Bool := (info.paramInfo[i]?.map (·.binderInfo.isExplicit)).getD false
  let mut k := 0
  for i in (List.range n).reverse do
    let ty ← whnfR (← inferType args[i]!)
    if ty.isAppOf ``LeanScript.PExpr && explicit i then k := k + 1 else break
  if k == 0 then return none
  for i in [0:n - k] do
    if explicit i then return none
  let f := mkIdent (← unresolveNameGlobal c)
  let as ← (List.range k).toArray.mapM fun j =>
    withNaryArg (n - k + j) do return (← delabLsterm false).1
  return some (← `(lsterm| ‹$f›($as,*)))

/-- The current expression, of one of the three layers, as a surface term; `root` is whether
    it is the whole printed term (then an expression that is not in the notation fails,
    instead of being embedded as `‹…›`). -/
partial def delabLsterm (root : Bool) : DelabM TSyn := do
  let e := (← getExpr).consumeMData
  let other : DelabM TSyn := do
    if root then failure
    if let some s ← embedCall? then return (s, atomPrec)
    return (← leanArgSyn, atomPrec)
  let some c := e.getAppFn.constName? | other
  unless termHeads.contains c do return ← other
  if e.getAppNumArgs != (← headArity c) then return ← other
  let sub (k : Nat) : DelabM TSyn := withArgFromEnd k (delabLsterm false)
  -- an argument of an application
  let arg (k : Nat) : DelabM (TSyntax `lsterm) := do tparen (appPrec + 1) (← sub k)
  let r : DelabM TSyn := do
    match c with
    | ``PExpr.var =>
        let i ← (dbIndex? e.appArg!).getDM failure
        return (← `(lsterm| #$(Syntax.mkNumLit (toString i)):num), atomPrec)
    | ``PExpr.bvar =>
        let i ← (natLit? (e.getArg! 4)).getDM failure
        return (← `(lsterm| #$(Syntax.mkNumLit (toString i)):num), atomPrec)
    | ``PExpr.ofNat =>
        let some n := natLit? (e.getArg! 4) | failure
        return (← `(lsterm| $(Syntax.mkNumLit (toString n)):num), atomPrec)
    | ``PExpr.lit =>
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
    | ``PExpr.enum_mk => return (← mkAppSyn `enum_mk [← withArgFromEnd 1 leanArgSyn], appPrec)
    | ``PExpr.record_mk =>
        let as ← withArgFromEnd 1 delabArgs
        match as with
        | a :: bs@(_ :: _) => return (← mkTupleSyn a bs.toArray, atomPrec)
        | _ => failure
    | ``PExpr.union_mk | ``PExpr.inj =>
        let i ← if c == ``PExpr.inj then (natLit? (e.getArg! 6)).getDM failure
          else (ctorIxIndex? (e.getArg! 8)).getDM failure
        let as ← withArgFromEnd 1 delabArgs
        let as ← as.mapM fun a => do tparen (appPrec + 1) (a, ← precOf a)
        let i : TSyntax `lsterm ← `(lsterm| $(Syntax.mkNumLit (toString i)):num)
        return (← mkAppSyn `union_mk (i :: as), appPrec)
    | ``PExpr.array_mk =>
        let es ← withArgFromEnd 1 delabElems
        return (← `(lsterm| #[$es.toArray,*]), atomPrec)
    | ``PExpr.data_in | ``PExpr.data_out =>
        let b ← withArgFromEnd 3 leanArgSyn
        let j ← withArgFromEnd 2 leanArgSyn
        return (← mkAppSyn (if c == ``PExpr.data_in then `data_in else `data_out) [b, j, ← arg 1],
          appPrec)
    | ``PExpr.cond => return (← mkAppSyn `cond [← arg 3, ← arg 2, ← arg 1], appPrec)
    | ``Comp.app =>
        let f ← tparen appPrec (← sub 2)
        return (← `(lsterm| $f $(← arg 1)), appPrec)
    | ``Comp.lam =>
        -- merge the `fun`s: `fun x => let f := fun y => b; f` is `fun x y => b`
        let rec go (bs : Array (TSyntax `lsbinder)) : DelabM TSyn := do
          let e := (← getExpr).consumeMData
          let b ← if ← getPPOption getPPFunBinderTypes then do
              let (τ, _) ← withArgFromEnd 3 (delabLsty false)
              `(lsbinder| (_ : $τ))
            else `(lsbinder| _)
          let bs := bs.push b
          let body := e.appArg!.consumeMData
          if body.isAppOfArity ``Term.letE 8 && isRetVar0 (body.getArg! 7) &&
              (body.getArg! 6).consumeMData.isAppOfArity ``Comp.lam 6 then
            withArgFromEnd 1 (withArgFromEnd 2 (go bs))
          else if body.isAppOfArity ``Term.ofComp 6 &&
              (body.getArg! 5).consumeMData.isAppOfArity ``Comp.lam 6 then
            withArgFromEnd 1 (withArgFromEnd 1 (go bs))
          else
            let (b, _) ← withArgFromEnd 1 (delabLsterm false)
            return (← `(lsterm| fun $bs* => $b), 0)
        go #[]
    | ``Comp.share => sub 1
    | ``Comp.extern | ``Comp.externOf | ``PExpr.extern | ``PExpr.externOf =>
        let ext := c == ``Comp.extern || c == ``PExpr.extern
        let name ← withArgFromEnd 3 leanArgSyn
        let f ← withArgFromEnd (if ext then 2 else 1) leanArgSyn
        let as ← withArgFromEnd (if ext then 1 else 2) delabArgs
        let as ← as.mapM fun a => do tparen (appPrec + 1) (a, ← precOf a)
        let kw := if c == ``PExpr.extern || c == ``PExpr.externOf then `pextern else `extern
        return (← mkAppSyn kw ([name, f] ++ as), appPrec)
    | ``Comp.nat_rec => return (← mkAppSyn `nat_rec [← arg 3, ← arg 2, ← arg 1], appPrec)
    | ``Comp.array_foldl => return (← mkAppSyn `array_foldl [← arg 3, ← arg 2, ← arg 1], appPrec)
    | ``Comp.data_rec | ``Comp.data_brec =>
        let brec := c == ``Comp.data_brec
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
    | ``Comp.thunk_mk => return (← mkAppSyn `thunk_mk [← arg 1], appPrec)
    | ``Comp.thunk_force => return (← mkAppSyn `thunk_force [← arg 1], appPrec)
    | ``Comp.lazy_mk => return (← mkAppSyn `lazy_mk [← arg 1], appPrec)
    | ``Comp.lazy_force => return (← mkAppSyn `lazy_force [← arg 1], appPrec)
    | ``Term.ret | ``Term.ofComp => sub 1
    | ``Term.letE =>
        -- `let x := c; x` is written `c` (unless `c` shares a pure expression)
        if isRetVar0 (e.getArg! 7) && !(e.getArg! 6).consumeMData.isAppOf ``Comp.share then
          return ← sub 2
        let (v, _) ← sub 2
        let (b, _) ← sub 1
        return (← `(lsterm| let _ := $v; $b), 0)
    | ``Term.record_casesOn =>
        let n := (← fieldsLen (e.getArg! 4))
        let (v, _) ← sub 2
        let (b, _) ← sub 1
        return (← `(lsterm| let ($(← `(lshole| _)), $(← holes n),*) := $v; $b), 0)
    | ``Term.ite =>
        let (a, _) ← sub 3
        let (b, _) ← sub 2
        let (c, _) ← sub 1
        return (← `(lsterm| if $a then $b else $c), 0)
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
    | ``Term.join =>
        let x ← if ← getPPOption getPPFunBinderTypes then do
            let (τ, _) ← withArgFromEnd 3 (delabLsty false)
            `(lsbinder| (_ : $τ))
          else `(lsbinder| _)
        let (b, _) ← sub 2
        let (m, _) ← sub 1
        return (← `(lsterm| join _ $x := $b; $m), 0)
    | ``Term.jump =>
        let j ← (dbIndex? (e.getArg! 6)).getDM failure
        let j : TSyntax `lsterm ← `(lsterm| ^$(Syntax.mkNumLit (toString j)):num)
        return (← mkAppSyn `jump [j, ← arg 1], appPrec)
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
  if e.isAppOfArity ``Branches.two 11 then
    return [← branch (e.getArg! 5) 2, ← branch (e.getArg! 6) 1]
  else if e.isAppOfArity ``Branches.cons 11 then
    return (← branch (e.getArg! 5) 2) :: (← withArgFromEnd 1 delabBranches)
  else failure

/-- The right-hand sides of the alternatives of a `match` (the current expression), each a
    statement. -/
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
      ``LeanScript.lstermIf, ``LeanScript.lstermMatch, ``LeanScript.lstermJoin].contains k then
    return 0
  return atomPrec

end

open PrettyPrinter.Parenthesizer in
/-- Parentheses in the surface syntax of terms, where the precedences require them. -/
@[category_parenthesizer lsterm]
def lsterm.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `lsterm true (fun stx => Unhygienic.run `(lsterm| ($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `lsterm prec

/-- Print a pure expression, a computation or a statement in the `[Term| …]` notation. -/
def delabTerm : Delab := do
  unless ← ppNotation do failure
  let (s, _) ← delabLsterm true
  `([Term| $s])

@[delab app.LeanScript.PExpr.var] def delabPExprVar : Delab := delabTerm
@[delab app.LeanScript.PExpr.bvar] def delabPExprBVar : Delab := delabTerm
@[delab app.LeanScript.PExpr.lit] def delabPExprLit : Delab := delabTerm
@[delab app.LeanScript.PExpr.ofNat] def delabPExprOfNat : Delab := delabTerm
@[delab app.LeanScript.PExpr.enum_mk] def delabPExprEnumMk : Delab := delabTerm
@[delab app.LeanScript.PExpr.record_mk] def delabPExprRecordMk : Delab := delabTerm
@[delab app.LeanScript.PExpr.union_mk] def delabPExprUnionMk : Delab := delabTerm
@[delab app.LeanScript.PExpr.inj] def delabPExprInj : Delab := delabTerm
@[delab app.LeanScript.PExpr.array_mk] def delabPExprArrayMk : Delab := delabTerm
@[delab app.LeanScript.PExpr.data_in] def delabPExprDataIn : Delab := delabTerm
@[delab app.LeanScript.PExpr.data_out] def delabPExprDataOut : Delab := delabTerm
@[delab app.LeanScript.PExpr.cond] def delabPExprCond : Delab := delabTerm
@[delab app.LeanScript.PExpr.extern] def delabPExprExtern : Delab := delabTerm
@[delab app.LeanScript.PExpr.externOf] def delabPExprExternOf : Delab := delabTerm
@[delab app.LeanScript.Comp.app] def delabCompApp : Delab := delabTerm
@[delab app.LeanScript.Comp.lam] def delabCompLam : Delab := delabTerm
@[delab app.LeanScript.Comp.share] def delabCompShare : Delab := delabTerm
@[delab app.LeanScript.Comp.extern] def delabCompExtern : Delab := delabTerm
@[delab app.LeanScript.Comp.externOf] def delabCompExternOf : Delab := delabTerm
@[delab app.LeanScript.Comp.nat_rec] def delabCompNatRec : Delab := delabTerm
@[delab app.LeanScript.Comp.array_foldl] def delabCompArrayFoldl : Delab := delabTerm
@[delab app.LeanScript.Comp.data_rec] def delabCompDataRec : Delab := delabTerm
@[delab app.LeanScript.Comp.data_brec] def delabCompDataBrec : Delab := delabTerm
@[delab app.LeanScript.Comp.thunk_mk] def delabCompThunkMk : Delab := delabTerm
@[delab app.LeanScript.Comp.thunk_force] def delabCompThunkForce : Delab := delabTerm
@[delab app.LeanScript.Comp.lazy_mk] def delabCompLazyMk : Delab := delabTerm
@[delab app.LeanScript.Comp.lazy_force] def delabCompLazyForce : Delab := delabTerm
@[delab app.LeanScript.Term.ret] def delabTermRet : Delab := delabTerm
@[delab app.LeanScript.Term.letE] def delabTermLetE : Delab := delabTerm
@[delab app.LeanScript.Term.record_casesOn] def delabTermRecordCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.ite] def delabTermIte : Delab := delabTerm
@[delab app.LeanScript.Term.enum_casesOn] def delabTermEnumCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.union_casesOn] def delabTermUnionCasesOn : Delab := delabTerm
@[delab app.LeanScript.Term.join] def delabTermJoin : Delab := delabTerm
@[delab app.LeanScript.Term.jump] def delabTermJump : Delab := delabTerm
@[delab app.LeanScript.Term.ofComp] def delabTermOfComp : Delab := delabTerm

end LeanScript.Notation

end
